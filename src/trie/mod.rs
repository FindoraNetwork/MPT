use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use bytes::{Bytes, BytesMut};
use rlp::{Prototype, Rlp, RlpStream};

use crate::db::{Database, MemoryDB};
use crate::errors::TrieError;
use crate::hasher::Hasher;
use crate::nibbles::Nibbles;
use iterator::TrieIterator;
use node::{BranchNode, Node};

pub type TrieResult<T> = Result<T, TrieError>;

mod iterator;
mod node;

#[derive(Debug)]
pub struct PatriciaTrie<D, H>
where
    D: Database,
    H: Hasher,
{
    root: Option<Box<Node>>,
    root_hash: Vec<u8>,

    db: Arc<D>,
    hasher: H,
    backup_db: Option<Arc<D>>,
    cache: HashMap<Vec<u8>, Bytes>,
    passing_keys: HashSet<Vec<u8>>,
    gen_keys: HashSet<Vec<u8>>,

    //interal error.
    error: Option<TrieError>,
}

impl<D, H> PatriciaTrie<D, H>
where
    D: Database,
    H: Hasher + Clone,
{
    pub fn iter(&self) -> TrieIterator<D, H> {
        TrieIterator::new(self)
    }

    pub fn new(db: Arc<D>, hasher: H) -> Self {
        Self {
            root: None,
            root_hash: hasher.digest(&rlp::NULL_RLP.to_vec()),

            cache: HashMap::new(),
            passing_keys: HashSet::new(),
            gen_keys: HashSet::new(),

            db,
            hasher,
            backup_db: None,
            error: None,
        }
    }

    pub fn from(db: Arc<D>, hasher: H, root_hash: Vec<u8>) -> TrieResult<Self> {
        match db
            .get(&root_hash)
            .map_err(|e| TrieError::DataBaseError(Box::new(e)))?
        {
            Some(data) => {
                let root = Self::decode_node(&data)?.map(Box::new);
                Ok(Self {
                    root,
                    root_hash,
                    cache: HashMap::new(),
                    passing_keys: HashSet::new(),
                    gen_keys: HashSet::new(),
                    db,
                    hasher,
                    backup_db: None,
                    error: None,
                })
            }
            None => Err(TrieError::InvalidStateRoot),
        }
    }

    /// extract specified height statedb in full node mode
    pub fn extract_backup(
        db: Arc<D>,
        backup_db: Option<Arc<D>>,
        hasher: H,
        root_hash: &[u8],
    ) -> TrieResult<(Self, Vec<Vec<u8>>)> {
        let mut pt = Self {
            root: None,
            root_hash: hasher.digest(&rlp::NULL_RLP.to_vec()),
            cache: HashMap::new(),
            passing_keys: HashSet::new(),
            gen_keys: HashSet::new(),
            db,
            hasher,
            backup_db,
            error: None,
        };

        let root = pt.recover_from_db(root_hash)?;
        let encoded = pt.cache_node(root.as_ref())?;
        pt.root = root.map(Box::new);
        pt.root_hash = root_hash.to_vec();

        let mut addr_list = vec![];
        for (k, _v) in pt.iter() {
            addr_list.push(k)
        }

        pt.cache
            .insert(pt.hasher.digest(&encoded), Bytes::from(encoded));

        let mut keys = Vec::with_capacity(pt.cache.len());
        let mut values = Vec::with_capacity(pt.cache.len());
        for (k, v) in pt.cache.drain() {
            keys.push(k);
            values.push(v);
        }

        // store data in backup db
        pt.backup_db
            .clone()
            .unwrap()
            .insert_batch(&keys, &values)
            .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;
        pt.backup_db
            .clone()
            .unwrap()
            .flush()
            .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;
        Ok((pt, addr_list))
    }
}

impl<D, H> PatriciaTrie<D, H>
where
    D: Database,
    H: Hasher + Clone,
{
    /// Returns the value for key stored in the trie.
    pub fn get(&self, key: &[u8]) -> TrieResult<Option<Cow<Vec<u8>>>> {
        self.get_at(self.root.as_deref(), &Nibbles::from_bytes(key, true))
    }

    /// Checks that the key is present in the trie
    pub fn contains(&self, key: &[u8]) -> TrieResult<bool> {
        Ok(self
            .get_at(self.root.as_deref(), &Nibbles::from_bytes(key, true))?
            .map_or(false, |_| true))
    }

    /// Inserts value into trie and modifies it if it exists
    pub fn insert(&mut self, key: &[u8], value: Vec<u8>) -> TrieResult<()> {
        if value.is_empty() {
            self.remove(&key)?;
            return Ok(());
        }
        let key = Nibbles::from_bytes(key, true);
        let child = self.root.take();
        let node = self.insert_at(child, key, value).into_box();
        self.root = Some(node);
        if let Some(err) = self.error.take() {
            return Err(err);
        }
        Ok(())
    }

    /// Removes any existing value for key from the trie.
    pub fn remove(&mut self, key: &[u8]) -> TrieResult<bool> {
        let child = self.root.take();
        let (n, removed) = self.delete_at(child, &Nibbles::from_bytes(key, true));
        self.root = n.map(Node::into_box);
        if let Some(err) = self.error.take() {
            return Err(err);
        }
        Ok(removed)
    }

    /// Saves all the nodes in the db, clears the cache data, recalculates the root.
    /// Returns the root hash of the trie.
    pub fn root(&mut self) -> TrieResult<Vec<u8>> {
        self.commit()
    }

    /// Prove constructs a merkle proof for key. The result contains all encoded nodes
    /// on the path to the value at key. The value itself is also included in the last
    /// node and can be retrieved by verifying the proof.
    ///
    /// If the trie does not contain a value for key, the returned proof contains all
    /// nodes of the longest existing prefix of the key (at least the root node), ending
    /// with the node that proves the absence of the key.
    pub fn get_proof(&mut self, key: &[u8]) -> TrieResult<Vec<BytesMut>> {
        let root = self.root.take(); //bypass borrow checker.
        let mut path = self.get_path_at(root.as_deref(), &Nibbles::from_bytes(key, true))?;
        match &root {
            None => {}
            Some(node) => path.push(self.encode_raw(Some(node.as_ref()))),
        }
        self.root = root;
        Ok(path.into_iter().rev().collect())
    }

    /// return value if key exists, None if key not exist, Error if proof is wrong
    pub fn verify_proof(
        &self,
        root_hash: Vec<u8>,
        key: &[u8],
        proof: Vec<impl AsRef<[u8]>>,
    ) -> TrieResult<Option<Vec<u8>>> {
        let memdb = Arc::new(MemoryDB::new(true));
        for node_encoded in proof.into_iter() {
            let hash = self.hasher.digest(node_encoded.as_ref());

            if root_hash.eq(&hash) || node_encoded.as_ref().len() >= H::LENGTH {
                memdb.insert(&hash, node_encoded.as_ref()).unwrap();
            }
        }
        let trie = PatriciaTrie::from(memdb, self.hasher.clone(), root_hash)?;

        let res = trie.get(key).map_err(|_| TrieError::InvalidProof)?;

        Ok(res.map(|res| res.into_owned()))
    }

    fn get_at<'a>(
        &self,
        n: Option<&'a Node>,
        partial: &Nibbles,
    ) -> TrieResult<Option<Cow<'a, Vec<u8>>>> {
        if let Some(node) = &n {
            match node {
                Node::Leaf(leaf) => {
                    if &leaf.key == partial {
                        Ok(Some(Cow::Borrowed(&leaf.value)))
                    } else {
                        Ok(None)
                    }
                }
                Node::Branch(branch) => {
                    if partial.is_empty() || partial.hex_at(0) == 16 {
                        Ok(branch.value.as_ref().map(Cow::Borrowed))
                    } else {
                        let index = partial.hex_at(0);
                        self.get_at(branch.get_child(index), &partial.offset(1))
                    }
                }
                Node::Extension(extension) => {
                    let prefix = &extension.prefix;
                    let match_len = partial.common_prefix(prefix);
                    if match_len == prefix.len() {
                        self.get_at(extension.node.as_deref(), &partial.offset(match_len))
                    } else {
                        Ok(None)
                    }
                }
                Node::Hash(hash_node) => {
                    if let Some(n) = self.recover_from_db(&hash_node.hash)? {
                        let res = self
                            .get_at(Some(&n), partial)?
                            .map(|x| Cow::Owned(x.into_owned()));
                        Ok(res)
                    } else {
                        Ok(None)
                    }
                }
            }
        } else {
            Ok(None)
        }
    }

    fn insert_at(&mut self, ptr: Option<Box<Node>>, partial: Nibbles, value: Vec<u8>) -> Node {
        if let Some(node) = ptr {
            match *node {
                Node::Leaf(mut leaf) => {
                    let match_index = partial.common_prefix(&leaf.key);
                    if match_index == leaf.key.len() {
                        // replace leaf value
                        leaf.value = value;
                        return Node::Leaf(leaf);
                    }

                    let old_partial = leaf.key;
                    //need to split the node.
                    let mut branch = BranchNode::new();

                    let leaf_node = Node::new_leaf(old_partial.offset(match_index + 1), leaf.value);

                    branch.insert(old_partial.hex_at(match_index), Some(leaf_node));

                    let node = Node::new_leaf(partial.offset(match_index + 1), value);
                    branch.insert(partial.hex_at(match_index), Some(node));

                    //Extension node is not needed.
                    if match_index == 0 {
                        return Node::Branch(branch);
                    }

                    // if there is a common prefix.
                    Node::new_extension(partial.slice(0, match_index), Node::Branch(branch))
                }
                Node::Branch(mut branch) => {
                    // 0x10 thus: 16
                    if partial.hex_at(0) == 0x10 {
                        branch.value = Some(value);
                        return Node::Branch(branch);
                    }

                    let branch_idx = partial.hex_at(0);
                    let child = branch.take_child(branch_idx);
                    let new_child = self.insert_at(child, partial.offset(1), value);
                    branch.insert(branch_idx, Some(new_child));
                    Node::Branch(branch)
                }
                Node::Extension(mut ext) => {
                    let match_index = partial.common_prefix(&ext.prefix);
                    let sub_node = ext.node.take().unwrap();

                    if match_index == 0 {
                        let prefix = ext.prefix;
                        // 1. split node
                        let mut branch = BranchNode::new();
                        branch.insert(
                            prefix.hex_at(0),
                            Some(if prefix.len() == 1 {
                                //eliminate a extension node.
                                *sub_node
                            } else {
                                Node::new_extension(prefix.offset(1), *sub_node)
                            }),
                        );
                        let branch_node = Node::Branch(branch);
                        // 2. insert it.
                        return self.insert_at(Some(branch_node.into_box()), partial, value);
                    }

                    if match_index == ext.prefix.len() {
                        let next_node = self.insert_at(
                            Some((sub_node).into_box()),
                            partial.offset(match_index),
                            value,
                        );
                        return Node::new_extension(ext.prefix, next_node);
                    }

                    //                  Ext(aaabbb) -> Bar
                    //(partial key)  aaacccc -^
                    //                  Ext (aaa) -> Ext(bbb)->Bar
                    //                              cccc -^
                    let new_ext =
                        Node::new_extension(ext.prefix.offset(match_index), *sub_node).into_box();
                    let new_node =
                        self.insert_at(Some(new_ext), partial.offset(match_index), value);
                    ext.prefix = ext.prefix.slice(0, match_index);
                    ext.node = Some(new_node.into_box());
                    Node::Extension(ext)
                }
                Node::Hash(hash_node) => match self.recover_from_db(&hash_node.hash) {
                    Ok(n) => {
                        self.passing_keys.insert(hash_node.hash);
                        self.insert_at(n.map(|x| x.into_box()), partial, value)
                    }
                    Err(e) => {
                        self.error = Some(e);
                        Node::Hash(hash_node)
                    }
                },
            }
        } else {
            Node::new_leaf(partial, value)
        }
    }

    //after delete_at, the ptr must be assgined a new one.
    fn delete_at(&mut self, n: Option<Box<Node>>, partial: &Nibbles) -> (Option<Node>, bool) {
        let (new_n, deleted) = if let Some(node) = n {
            match *node {
                Node::Leaf(leaf) => {
                    if &leaf.key == partial {
                        return (None, true);
                    }
                    (Node::Leaf(leaf), false)
                }
                Node::Branch(mut branch) => {
                    if partial.hex_at(0) == 0x10 {
                        branch.value = None;
                        return (Some(Node::Branch(branch)), true);
                    }

                    let index = partial.hex_at(0);
                    let node = branch.take_child(index);

                    let (new_n, deleted) = self.delete_at(node, &partial.offset(1));
                    branch.insert(index, new_n);

                    (Node::Branch(branch), deleted)
                }
                Node::Extension(mut ext) => {
                    let prefix = &ext.prefix;
                    let match_len = partial.common_prefix(prefix);

                    if match_len == prefix.len() {
                        let (new_n, deleted) = self.delete_at(ext.node, &partial.offset(match_len));

                        ext.node = new_n.map(Node::into_box);
                        (Node::Extension(ext), deleted)
                    } else {
                        (Node::Extension(ext), false)
                    }
                }
                Node::Hash(hash_node) => match self.recover_from_db(&hash_node.hash) {
                    Ok(n) => {
                        self.passing_keys.insert(hash_node.hash);
                        match self.delete_at(n.map(Node::into_box), partial) {
                            (None, d) => return (None, d),
                            (Some(n), d) => (n, d),
                        }
                    }
                    Err(e) => {
                        self.error = Some(e);
                        (Node::Hash(hash_node), false)
                    }
                },
            }
        } else {
            return (None, false);
        };

        if deleted {
            (self.degenerate(new_n), deleted)
        } else {
            (Some(new_n), deleted)
        }
    }

    //must return a node or None
    fn degenerate(&mut self, n: Node) -> Option<Node> {
        match n {
            Node::Branch(mut branch) => {
                let used_indexs = branch.used_indexes();
                if used_indexs.is_empty() {
                    // if only have a value node. make an extension.
                    if let Some(value) = branch.value.take() {
                        let key = Nibbles::from_bytes(&[], true);
                        Some(Node::new_leaf(key, value))
                    } else {
                        None
                    }
                } else if used_indexs.len() == 1 && branch.value.is_none() {
                    let used_index = used_indexs[0];
                    //must not be null
                    let n = branch.take_child(used_index).unwrap();

                    let new_node = Node::new_extension(
                        Nibbles::from_hex_unchecked(vec![used_index as u8]),
                        *n,
                    );
                    self.degenerate(new_node)
                } else {
                    Some(Node::Branch(branch))
                }
            }
            Node::Extension(ext) => {
                if let Some(next_node) = ext.node {
                    match *next_node {
                        Node::Extension(sub_ext) => {
                            let new_prefix = ext.prefix.join(&sub_ext.prefix);
                            match sub_ext.node {
                                None => None,
                                Some(next_node) => {
                                    let new_n = Node::new_extension(new_prefix, *next_node);
                                    self.degenerate(new_n)
                                }
                            }
                        }
                        Node::Leaf(mut leaf) => {
                            let new_prefix = ext.prefix.join(&leaf.key);
                            leaf.key = new_prefix;
                            Some(Node::Leaf(leaf))
                        }
                        // try again after recovering node from the db.
                        Node::Hash(hash_node) => match self.recover_from_db(&hash_node.hash) {
                            Ok(node) => {
                                let hash = hash_node.hash;
                                self.passing_keys.insert(hash);
                                if let Some(new_node) = node {
                                    let n = Node::new_extension(ext.prefix, new_node);
                                    self.degenerate(n)
                                } else {
                                    None
                                }
                            }
                            Err(e) => {
                                self.error = Some(e);
                                Some(Node::Hash(hash_node))
                            }
                        },
                        Node::Branch(node) => {
                            Some(Node::new_extension(ext.prefix, Node::Branch(node)))
                        }
                    }
                } else {
                    None
                }
            }
            _ => Some(n),
        }
    }

    /// Get nodes path along the key, only the nodes whose encode length is greater than
    /// hash length are added.
    /// For embedded nodes whose data are already contained in their parent node, we don't need to
    /// add them in the path.
    /// In the code below, we only add the nodes get by `get_node_from_hash`, because they contains
    /// all data stored in db, including nodes whose encoded data is less than hash length.
    fn get_path_at<'a>(
        &'a mut self,
        n: Option<&Node>,
        partial: &Nibbles,
    ) -> TrieResult<Vec<BytesMut>> {
        if let Some(b) = n {
            match b {
                Node::Leaf(_) => Ok(vec![]),
                Node::Branch(branch) => {
                    if partial.is_empty() || partial.hex_at(0) == 16 {
                        Ok(vec![])
                    } else {
                        let node = unsafe { branch.get_child_uncheckd(partial.hex_at(0)) };
                        self.get_path_at(node, &partial.offset(1))
                    }
                }
                Node::Extension(ext) => {
                    let prefix = &ext.prefix;
                    let match_len = partial.common_prefix(prefix);

                    if match_len == prefix.len() {
                        self.get_path_at(ext.node.as_deref(), &partial.offset(match_len))
                    } else {
                        Ok(vec![])
                    }
                }
                Node::Hash(hash_node) => {
                    let n = self.recover_from_db(&hash_node.hash)?;
                    let mut rest = self.get_path_at(n.as_ref(), partial)?;
                    rest.push(self.encode_raw(n.as_ref()));
                    Ok(rest)
                }
            }
        } else {
            Ok(vec![])
        }
    }

    fn commit(&mut self) -> TrieResult<Vec<u8>> {
        let root = self.root.take();
        let encoded = self.encode_node(root.as_deref());
        let root_hash = if encoded.len() < H::LENGTH {
            let hash = self.hasher.digest(&encoded);
            self.cache.insert(hash.clone(), Bytes::from(encoded));
            hash
        } else {
            encoded
        };

        let mut keys: Vec<Vec<u8>> = Vec::with_capacity(self.cache.len());
        let mut values: Vec<Bytes> = Vec::with_capacity(self.cache.len());

        for (k, v) in self.cache.drain() {
            keys.push(k);
            values.push(v);
        }

        self.db
            .insert_batch(&keys, &values)
            .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;

        let removed_keys: Vec<&[u8]> = self
            .passing_keys
            .iter()
            .filter(|h| !self.gen_keys.contains(&**h))
            .map(|x| x.as_slice())
            .collect();

        self.db
            .remove_batch(&removed_keys)
            .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;

        self.root_hash = root_hash.to_vec();
        self.gen_keys.clear();
        self.passing_keys.clear();
        match self.recover_from_db(&root_hash) {
            Ok(node) => self.root = node.map(Box::new),
            Err(e) => {
                self.root = root;
                return Err(e);
            }
        };
        Ok(root_hash)
    }

    fn encode_node(&mut self, n: Option<&Node>) -> Vec<u8> {
        //Returns the hash value directly to avoid double counting.
        if let Some(Node::Hash(hash_node)) = n {
            return hash_node.hash.clone();
        }

        let data = self.encode_raw(n);

        // Nodes smaller than 32 bytes are stored inside their parent,
        // Nodes equal to 32 bytes are returned directly
        if data.len() < H::LENGTH {
            data.to_vec()
        } else {
            let hash = self.hasher.digest(&data);
            self.cache.insert(hash.clone(), data.into());
            self.gen_keys.insert(hash.clone());
            hash
        }
    }

    fn encode_raw(&mut self, n: Option<&Node>) -> BytesMut {
        match n {
            None => BytesMut::from(&rlp::NULL_RLP[..]),
            Some(node) => match node {
                Node::Leaf(leaf) => {
                    let mut stream = RlpStream::new_list(2);
                    stream.append(&leaf.key.encode_compact());
                    stream.append(&leaf.value);
                    stream.out()
                }
                Node::Branch(branch) => {
                    let mut stream = RlpStream::new_list(17);
                    for i in 0..16 {
                        let n = unsafe { branch.get_child_uncheckd(i) };
                        let data = self.encode_node(n);
                        if data.len() == H::LENGTH {
                            stream.append(&data);
                        } else {
                            stream.append_raw(&data, 1);
                        }
                    }

                    match &branch.value {
                        Some(v) => stream.append(&*v),
                        None => stream.append_empty_data(),
                    };
                    stream.out()
                }
                Node::Extension(ext) => {
                    let mut stream = RlpStream::new_list(2);
                    stream.append(&ext.prefix.encode_compact());
                    let data = self.encode_node(ext.node.as_deref());
                    if data.len() == H::LENGTH {
                        stream.append(&data);
                    } else {
                        stream.append_raw(&data, 1);
                    }
                    stream.out()
                }
                Node::Hash(_hash) => unreachable!(),
            },
        }
    }

    fn decode_node(data: &[u8]) -> TrieResult<Option<Node>> {
        let r = Rlp::new(data);

        //may becauase
        match r.prototype()? {
            Prototype::Data(0) => Ok(None),
            Prototype::List(2) => {
                let key = r.at(0)?.data()?;
                let key = Nibbles::from_compact(key.to_vec())?;

                if key.is_leaf() {
                    Ok(Some(Node::new_leaf(key, r.at(1)?.data()?.to_vec())))
                } else if let Some(n) = Self::decode_node(r.at(1)?.as_raw())? {
                    Ok(Some(Node::new_extension(key, n)))
                } else {
                    Ok(None)
                }
            }
            Prototype::List(17) => {
                let mut node = BranchNode::new();
                #[allow(clippy::needless_range_loop)]
                for i in 0..16 {
                    let rlp_data = r.at(i)?;
                    let n = Self::decode_node(rlp_data.as_raw())?;
                    node.insert(i, n);
                }

                // The last element is a value node.
                let value_rlp = r.at(16)?;
                node.value = if value_rlp.is_empty() {
                    None
                } else {
                    Some(value_rlp.data()?.to_vec())
                };
                Ok(Some(Node::Branch(node)))
            }
            _ => {
                if r.is_data() && r.size() == H::LENGTH {
                    Ok(Some(Node::new_hash(r.data()?.to_vec())))
                } else {
                    Err(TrieError::InvalidData)
                }
            }
        }
    }

    fn recover_from_db(&self, key: &[u8]) -> TrieResult<Option<Node>> {
        let value = self
            .db
            .get(key)
            .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;

        Ok(if let Some(data) = value {
            Self::decode_node(&data)?
        } else {
            None
        })
    }

    fn cache_node(&mut self, n: Option<&Node>) -> TrieResult<Vec<u8>> {
        if let Some(node) = n {
            match &node {
                Node::Leaf(leaf) => {
                    let mut stream = RlpStream::new_list(2);
                    stream.append(&leaf.key.encode_compact());
                    stream.append(&leaf.value);
                    Ok(stream.out().to_vec())
                }
                Node::Branch(branch) => {
                    let mut stream = RlpStream::new_list(17);
                    for i in 0..16 {
                        let n = unsafe { branch.get_child_uncheckd(i) };
                        let data = self.cache_node(n)?;
                        if data.len() == H::LENGTH {
                            stream.append(&data);
                        } else {
                            stream.append_raw(&data, 1);
                        }
                    }

                    match &branch.value {
                        Some(v) => stream.append(v),
                        None => stream.append_empty_data(),
                    };
                    Ok(stream.out().to_vec())
                }
                Node::Extension(ext) => {
                    let mut stream = RlpStream::new_list(2);
                    stream.append(&ext.prefix.encode_compact());
                    let data = self.cache_node(ext.node.as_deref())?;
                    if data.len() == H::LENGTH {
                        stream.append(&data);
                    } else {
                        stream.append_raw(&data, 1);
                    }
                    Ok(stream.out().to_vec())
                }
                Node::Hash(hash_node) => {
                    let hash = hash_node.hash.to_vec();
                    let next_node = self.recover_from_db(&hash)?;
                    let data = self.cache_node(next_node.as_ref().as_deref())?;
                    self.cache.insert(hash.clone(), Bytes::from(data));
                    Ok(hash)
                }
            }
        } else {
            Ok(rlp::NULL_RLP.to_vec())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PatriciaTrie;
    use crate::db::{Database, MemoryDB};
    use crate::hasher::{Hasher, HasherKeccak};
    use rand::distributions::Alphanumeric;
    use rand::seq::SliceRandom;
    use rand::{thread_rng, Rng};
    use std::collections::{HashMap, HashSet};
    use std::sync::Arc;

    #[test]
    fn test_trie_insert() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());
        trie.insert(b"test", b"test".to_vec()).unwrap();
    }

    #[test]
    fn test_trie_get() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());
        trie.insert(b"test", b"test".to_vec()).unwrap();
        let v = trie.get(b"test").unwrap();

        assert_eq!(b"test", v.unwrap().as_slice())
    }

    #[test]
    fn test_trie_random_insert() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());

        for _ in 0..10000 {
            let rand_str: String = thread_rng().sample_iter(&Alphanumeric).take(30).collect();
            let val = rand_str.as_bytes();
            trie.insert(val, val.to_vec()).unwrap();

            let v = trie.get(val).unwrap();
            assert_eq!(v.as_deref().map(|v| &**v), Some(val));
        }
    }

    #[test]
    fn test_trie_contains() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());
        trie.insert(b"test", b"test".to_vec()).unwrap();
        assert!(trie.contains(b"test").unwrap());
        assert!(!trie.contains(b"test2").unwrap());
    }

    #[test]
    fn test_trie_remove() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());
        trie.insert(b"test", b"test".to_vec()).unwrap();
        let removed = trie.remove(b"test").unwrap();
        assert!(removed)
    }

    #[test]
    fn test_trie_random_remove() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());

        for _ in 0..10000 {
            let rand_str: String = thread_rng().sample_iter(&Alphanumeric).take(30).collect();
            let val = rand_str.as_bytes();
            trie.insert(val, val.to_vec()).unwrap();

            let removed = trie.remove(val).unwrap();
            assert!(removed);
            assert!(trie.get(val).unwrap().is_none());
        }
    }

    #[test]
    fn test_trie_from_root() {
        let memdb = Arc::new(MemoryDB::new(true));
        let root = {
            let mut trie = PatriciaTrie::new(memdb.clone(), HasherKeccak::new());
            trie.insert(b"test", b"test".to_vec()).unwrap();
            trie.insert(b"test1", b"test".to_vec()).unwrap();
            trie.insert(b"test2", b"test".to_vec()).unwrap();
            trie.insert(b"test23", b"test".to_vec()).unwrap();
            trie.insert(b"test33", b"test".to_vec()).unwrap();
            trie.insert(b"test44", b"test".to_vec()).unwrap();
            trie.root().unwrap()
        };

        let mut trie =
            PatriciaTrie::from(memdb.clone(), HasherKeccak::new(), root.clone()).unwrap();
        let v1 = trie.get(b"test33").unwrap().map(|x| x.into_owned());
        assert_eq!(Some(b"test".to_vec()), v1);
        let v2 = trie.get(b"test44").unwrap().map(|x| x.into_owned());
        assert_eq!(Some(b"test".to_vec()), v2);
        let root2 = trie.root().unwrap();
        assert_eq!(hex::encode(root), hex::encode(root2));
    }

    #[test]
    fn test_trie_from_root_and_insert() {
        let memdb = Arc::new(MemoryDB::new(true));
        let root = {
            let mut trie = PatriciaTrie::new(Arc::clone(&memdb), HasherKeccak::new());
            trie.insert(b"test", b"test".to_vec()).unwrap();
            trie.insert(b"test1", b"test".to_vec()).unwrap();
            trie.insert(b"test2", b"test".to_vec()).unwrap();
            trie.insert(b"test23", b"test".to_vec()).unwrap();
            trie.insert(b"test33", b"test".to_vec()).unwrap();
            trie.insert(b"test44", b"test".to_vec()).unwrap();
            trie.commit().unwrap()
        };

        let mut trie = PatriciaTrie::from(Arc::clone(&memdb), HasherKeccak::new(), root).unwrap();
        trie.insert(b"test55", b"test55".to_vec()).unwrap();
        trie.commit().unwrap();
        let v = trie.get(b"test55").unwrap().map(|x| x.into_owned());
        assert_eq!(Some(b"test55".to_vec()), v);
    }

    #[test]
    fn test_trie_from_root_and_delete() {
        let memdb = Arc::new(MemoryDB::new(true));
        let root = {
            let mut trie = PatriciaTrie::new(Arc::clone(&memdb), HasherKeccak::new());
            trie.insert(b"test", b"test".to_vec()).unwrap();
            trie.insert(b"test1", b"test".to_vec()).unwrap();
            trie.insert(b"test2", b"test".to_vec()).unwrap();
            trie.insert(b"test23", b"test".to_vec()).unwrap();
            trie.insert(b"test33", b"test".to_vec()).unwrap();
            trie.insert(b"test44", b"test".to_vec()).unwrap();
            trie.commit().unwrap()
        };

        let mut trie = PatriciaTrie::from(Arc::clone(&memdb), HasherKeccak::new(), root).unwrap();

        assert!(trie.get(b"test").unwrap().is_some());
        assert!(trie.get(b"test1").unwrap().is_some());
        assert!(trie.get(b"test2").unwrap().is_some());
        assert!(trie.get(b"test23").unwrap().is_some());
        assert!(trie.get(b"test33").unwrap().is_some());
        assert!(trie.get(b"test44").unwrap().is_some());

        let removed = trie.remove(b"test44").unwrap();
        assert!(removed);
        let removed = trie.remove(b"test33").unwrap();
        assert!(removed);
        let removed = trie.remove(b"test23").unwrap();
        assert!(removed);
    }

    #[test]
    fn test_multiple_trie_roots() {
        let k0: ethereum_types::H256 = 0.into();
        let k1: ethereum_types::H256 = 1.into();
        let v: ethereum_types::H256 = 0x1234.into();

        let root1 = {
            let memdb = Arc::new(MemoryDB::new(true));
            let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());
            trie.insert(k0.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie.root().unwrap()
        };

        let root2 = {
            let memdb = Arc::new(MemoryDB::new(true));
            let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());
            trie.insert(k0.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie.insert(k1.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie.root().unwrap();
            trie.remove(k1.as_ref()).unwrap();
            trie.root().unwrap()
        };

        let root3 = {
            let memdb = Arc::new(MemoryDB::new(true));
            let mut trie1 = PatriciaTrie::new(Arc::clone(&memdb), HasherKeccak::new());
            trie1.insert(k0.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie1.insert(k1.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie1.root().unwrap();
            let root = trie1.root().unwrap();
            let mut trie2 =
                PatriciaTrie::from(Arc::clone(&memdb), HasherKeccak::new(), root).unwrap();
            trie2.remove(&k1.as_bytes().to_vec()).unwrap();
            trie2.root().unwrap()
        };

        assert_eq!(root1, root2);
        assert_eq!(root2, root3);
    }

    #[test]
    fn test_delete_stale_keys_with_random_insert_and_delete() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());

        let mut rng = rand::thread_rng();
        let mut keys = vec![];
        for _ in 0..100 {
            let random_bytes: Vec<u8> = (0..rng.gen_range(2, 30))
                .map(|_| rand::random::<u8>())
                .collect();
            trie.insert(&random_bytes, random_bytes.clone()).unwrap();
            keys.push(random_bytes.clone());
        }
        trie.commit().unwrap();
        let slice = &mut keys;
        slice.shuffle(&mut rng);

        for key in slice.iter() {
            trie.remove(key).unwrap();
        }
        trie.commit().unwrap();

        let empty_node_key = HasherKeccak::new().digest(&rlp::NULL_RLP);
        let value = trie.db.get(empty_node_key.as_ref()).unwrap().unwrap();
        assert_eq!(value, &rlp::NULL_RLP)
    }

    #[test]
    fn insert_full_branch() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = PatriciaTrie::new(memdb, HasherKeccak::new());

        trie.insert(b"test", b"test".to_vec()).unwrap();
        trie.insert(b"test1", b"test".to_vec()).unwrap();
        trie.insert(b"test2", b"test".to_vec()).unwrap();
        trie.insert(b"test23", b"test".to_vec()).unwrap();
        trie.insert(b"test33", b"test".to_vec()).unwrap();
        trie.insert(b"test44", b"test".to_vec()).unwrap();
        trie.root().unwrap();

        let v = trie.get(b"test").unwrap().map(|x| x.into_owned());
        assert_eq!(Some(b"test".to_vec()), v);
    }

    #[test]
    fn iterator_trie() {
        let memdb = Arc::new(MemoryDB::new(true));
        let root1;
        let mut kv = HashMap::new();
        kv.insert(b"test".to_vec(), b"test".to_vec());
        kv.insert(b"test1".to_vec(), b"test1".to_vec());
        kv.insert(b"test11".to_vec(), b"test2".to_vec());
        kv.insert(b"test14".to_vec(), b"test3".to_vec());
        kv.insert(b"test16".to_vec(), b"test4".to_vec());
        kv.insert(b"test18".to_vec(), b"test5".to_vec());
        kv.insert(b"test2".to_vec(), b"test6".to_vec());
        kv.insert(b"test23".to_vec(), b"test7".to_vec());
        kv.insert(b"test9".to_vec(), b"test8".to_vec());
        {
            let mut trie = PatriciaTrie::new(memdb.clone(), HasherKeccak::new());
            let mut kv = kv.clone();
            kv.iter().for_each(|(k, v)| {
                trie.insert(&k, v.clone()).unwrap();
            });
            root1 = trie.root().unwrap();

            trie.iter()
                .for_each(|(k, v)| assert_eq!(kv.remove(&k).unwrap(), v));
            assert!(kv.is_empty());
        }

        {
            let mut trie = PatriciaTrie::new(memdb.clone(), HasherKeccak::new());
            let mut kv2 = HashMap::new();
            kv2.insert(b"test".to_vec(), b"test11".to_vec());
            kv2.insert(b"test1".to_vec(), b"test12".to_vec());
            kv2.insert(b"test14".to_vec(), b"test13".to_vec());
            kv2.insert(b"test22".to_vec(), b"test14".to_vec());
            kv2.insert(b"test9".to_vec(), b"test15".to_vec());
            kv2.insert(b"test16".to_vec(), b"test16".to_vec());
            kv2.insert(b"test2".to_vec(), b"test17".to_vec());
            kv2.iter().for_each(|(k, v)| {
                trie.insert(&k, v.clone()).unwrap();
            });

            trie.root().unwrap();

            let mut kv_delete = HashSet::new();
            kv_delete.insert(b"test".to_vec());
            kv_delete.insert(b"test1".to_vec());
            kv_delete.insert(b"test14".to_vec());

            kv_delete.iter().for_each(|k| {
                trie.remove(&k).unwrap();
            });

            kv2.retain(|k, _| !kv_delete.contains(k));

            trie.root().unwrap();
            trie.iter()
                .for_each(|(k, v)| assert_eq!(kv2.remove(&k).unwrap(), v));
            assert!(kv2.is_empty());
        }

        let trie = PatriciaTrie::from(memdb, HasherKeccak::new(), root1).unwrap();
        trie.iter()
            .for_each(|(k, v)| assert_eq!(kv.remove(&k).unwrap(), v));
        assert!(kv.is_empty());
    }
}
