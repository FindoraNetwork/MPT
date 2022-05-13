use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::mem::forget;
use std::sync::Arc;

use core::ptr::NonNull;

use bytes::Bytes;
use hasher::Hasher;
use rlp::{Prototype, Rlp, RlpStream};

use crate::db::{Database, MemoryDB};
use crate::errors::TrieError;
use crate::nibbles::Nibbles;
use node::{BranchNode, Node};

pub type TrieResult<T> = Result<T, TrieError>;

mod node;

#[derive(Debug)]
pub struct PatriciaTrie<D, H>
where
    D: Database,
    H: Hasher,
{
    root: Option<NonNull<Node>>,
    root_hash: Vec<u8>,

    db: Arc<D>,
    hasher: H,
    // backup_db: Option<Arc<D>>,
    cache: HashMap<Vec<u8>, Vec<u8>>,
    passing_keys: HashSet<Vec<u8>>,
    gen_keys: HashSet<Vec<u8>>,
}

// #[derive(Clone, Debug)]
// enum TraceStatus {
//     Start,
//     Doing,
//     Child(u8),
//     End,
// }

// #[derive(Clone, Debug)]
// struct TraceNode {
//     node: Node,
//     status: TraceStatus,
// }

// impl TraceNode {
//     fn advance(&mut self) {
//         self.status = match &self.status {
//             TraceStatus::Start => TraceStatus::Doing,
//             TraceStatus::Doing => match self.node {
//                 Node::Branch(_) => TraceStatus::Child(0),
//                 _ => TraceStatus::End,
//             },
//             TraceStatus::Child(i) if *i < 15 => TraceStatus::Child(i + 1),
//             _ => TraceStatus::End,
//         }
//     }
// }

// impl From<Node> for TraceNode {
//     fn from(node: Node) -> TraceNode {
//         TraceNode {
//             node,
//             status: TraceStatus::Start,
//         }
//     }
// }

// pub struct TrieIterator<'a, D, H>
// where
//     D: Database,
//     H: Hasher,
// {
//     trie: &'a PatriciaTrie<D, H>,
//     nibble: Nibbles,
//     nodes: Vec<TraceNode>,
// }

// impl<'a, D, H> Iterator for TrieIterator<'a, D, H>
// where
//     D: Database,
//     H: Hasher,
// {
//     type Item = (Vec<u8>, Vec<u8>);

//     fn next(&mut self) -> Option<Self::Item> {
//         loop {
//             let mut now = self.nodes.last().cloned();
//             if let Some(ref mut now) = now {
//                 self.nodes.last_mut().unwrap().advance();

//                 match (now.status.clone(), &now.node) {
//                     (TraceStatus::End, node) => {
//                         match *node {
//                             Node::Leaf(ref leaf) => {
//                                 let cur_len = self.nibble.len();
//                                 self.nibble.truncate(cur_len - leaf.borrow().key.len());
//                             }

//                             Node::Extension(ref ext) => {
//                                 let cur_len = self.nibble.len();
//                                 self.nibble.truncate(cur_len - ext.borrow().prefix.len());
//                             }

//                             Node::Branch(_) => {
//                                 self.nibble.pop();
//                             }
//                             _ => {}
//                         }
//                         self.nodes.pop();
//                     }

//                     (TraceStatus::Doing, Node::Extension(ref ext)) => {
//                         self.nibble.extend(&ext.borrow().prefix);
//                         self.nodes.push((ext.borrow().node.clone()).into());
//                     }

//                     (TraceStatus::Doing, Node::Leaf(ref leaf)) => {
//                         self.nibble.extend(&leaf.borrow().key);
//                         return Some((self.nibble.encode_raw().0, leaf.borrow().value.clone()));
//                     }

//                     (TraceStatus::Doing, Node::Branch(ref branch)) => {
//                         let value = branch.borrow().value.clone();
//                         if let Some(data) = value {
//                             return Some((self.nibble.encode_raw().0, data));
//                         } else {
//                             continue;
//                         }
//                     }

//                     (TraceStatus::Doing, Node::Hash(ref hash_node)) => {
//                         if let Ok(n) = self.trie.recover_from_db(&hash_node.borrow().hash.clone()) {
//                             self.nodes.pop();
//                             self.nodes.push(n.into());
//                         } else {
//                             //error!();
//                             return None;
//                         }
//                     }

//                     (TraceStatus::Child(i), Node::Branch(ref branch)) => {
//                         if i == 0 {
//                             self.nibble.push(0);
//                         } else {
//                             self.nibble.pop();
//                             self.nibble.push(i);
//                         }
//                         self.nodes
//                             .push((branch.borrow().children[i as usize].clone()).into());
//                     }

//                     (_, Node::Empty) => {
//                         self.nodes.pop();
//                     }
//                     _ => {}
//                 }
//             } else {
//                 return None;
//             }
//         }
//     }
// }

impl<D, H> PatriciaTrie<D, H>
where
    D: Database,
    H: Hasher,
{
    // pub fn iter(&self) -> TrieIterator<D, H> {
    //     let nodes = vec![self.root.clone().into()];
    //     TrieIterator {
    //         trie: self,
    //         nibble: Nibbles::from_raw(vec![], false),
    //         nodes,
    //     }
    // }
    pub fn new(db: Arc<D>, hasher: H) -> Self {
        Self {
            root: None,
            root_hash: hasher.digest(&rlp::NULL_RLP.to_vec()),

            cache: HashMap::new(),
            passing_keys: HashSet::new(),
            gen_keys: HashSet::new(),

            db,
            hasher,
            // backup_db: None,
        }
    }

    // pub fn from(db: Arc<D>, hasher: H, root: &[u8]) -> TrieResult<Self> {
    //     match db
    //         .get(root)
    //         .map_err(|e| TrieError::DataBaseError(Box::new(e)))?
    //     {
    //         Some(data) => {
    //             let mut trie = Self {
    //                 root:None,
    //                 root_hash: root.to_vec(),

    //                 cache: HashMap::new(),
    //                 passing_keys: HashSet::new(),
    //                 gen_keys: HashSet::new(),
    //                 db,
    //                 hasher,
    //                 // backup_db: None,
    //             };

    //             trie.root = trie.decode_node(&data)?;
    //             Ok(trie)
    //         }
    //         None => Err(TrieError::InvalidStateRoot),
    //     }
    // }

    // extract specified height statedb in full node mode
    // pub fn extract_backup(
    //     db: Arc<D>,
    //     backup_db: Option<Arc<D>>,
    //     hasher: Arc<H>,
    //     root_hash: &[u8],
    // ) -> TrieResult<(Self, Vec<Vec<u8>>)> {
    //     let mut pt = Self {
    //         root: Node::Empty,
    //         root_hash: hasher.digest(&rlp::NULL_RLP.to_vec()),

    //         cache: RefCell::new(HashMap::new()),
    //         passing_keys: RefCell::new(HashSet::new()),
    //         gen_keys: RefCell::new(HashSet::new()),

    //         db,
    //         hasher,
    //         backup_db,
    //     };

    //     let root = pt.recover_from_db(root_hash)?;
    //     pt.root = root.clone();
    //     pt.root_hash = root_hash.to_vec();

    //     let mut addr_list = vec![];
    //     pt.iter().for_each(|(k, _v)| addr_list.push(k));
    //     let encoded = pt.cache_node(root)?;
    //     pt.cache
    //         .borrow_mut()
    //         .insert(pt.hasher.digest(&encoded), encoded);

    //     let mut keys = Vec::with_capacity(pt.cache.borrow().len());
    //     let mut values = Vec::with_capacity(pt.cache.borrow().len());
    //     for (k, v) in pt.cache.borrow_mut().drain() {
    //         keys.push(k.to_vec());
    //         values.push(v);
    //     }

    //     // store data in backup db
    //     pt.backup_db
    //         .clone()
    //         .unwrap()
    //         .insert_batch(keys, values)
    //         .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;
    //     pt.backup_db
    //         .clone()
    //         .unwrap()
    //         .flush()
    //         .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;
    //     Ok((pt, addr_list))
    // }
}

impl<D, H> PatriciaTrie<D, H>
where
    D: Database,
    H: Hasher,
{
    /// Returns the value for key stored in the trie.
    pub fn get(&self, key: &[u8]) -> TrieResult<Option<Cow<Vec<u8>>>> {
        self.get_at(self.root, &Nibbles::from_bytes(key, true))
    }

    // /// Checks that the key is present in the trie
    // pub fn contains(&self, key: &[u8]) -> TrieResult<bool> {
    //     Ok(self
    //         .get_at(self.root.clone(), &Nibbles::from_raw(key.to_vec(), true))?
    //         .map_or(false, |_| true))
    // }

    /// Inserts value into trie and modifies it if it exists
    pub fn insert(&mut self, key: &[u8], value: Vec<u8>) -> TrieResult<()> {
        // if value.is_empty() {
        //     self.remove(&key)?;
        //     return Ok(());
        // } [TODO]
        let key = Nibbles::from_bytes(key, true);
        let node = self.insert_at(self.root, key, value).into_raw();
        self.root = Some(node);
        Ok(())
    }

    /// Removes any existing value for key from the trie.
    pub fn remove(&mut self, key: &[u8]) -> bool {
        let (n, removed) = self.delete_at(self.root, &Nibbles::from_bytes(key, true));
        self.root = n.map(Node::into_raw);
        removed
    }

    // /// Saves all the nodes in the db, clears the cache data, recalculates the root.
    // /// Returns the root hash of the trie.
    // pub fn root(&mut self) -> TrieResult<Vec<u8>> {
    //     self.commit()
    // }

    // /// Prove constructs a merkle proof for key. The result contains all encoded nodes
    // /// on the path to the value at key. The value itself is also included in the last
    // /// node and can be retrieved by verifying the proof.
    // ///
    // /// If the trie does not contain a value for key, the returned proof contains all
    // /// nodes of the longest existing prefix of the key (at least the root node), ending
    // /// with the node that proves the absence of the key.
    // pub fn get_proof(&self, key: &[u8]) -> TrieResult<Vec<Vec<u8>>> {
    //     let mut path =
    //         self.get_path_at(self.root.clone(), &Nibbles::from_raw(key.to_vec(), true))?;
    //     match self.root {
    //         Node::Empty => {}
    //         _ => path.push(self.root.clone()),
    //     }
    //     Ok(path.into_iter().rev().map(|n| self.encode_raw(n)).collect())
    // }

    // /// return value if key exists, None if key not exist, Error if proof is wrong
    // pub fn verify_proof(
    //     &self,
    //     root_hash: Vec<u8>,
    //     key: &[u8],
    //     proof: Vec<Vec<u8>>,
    // ) -> TrieResult<Option<Vec<u8>>> {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     for node_encoded in proof.into_iter() {
    //         let hash = self.hasher.digest(&node_encoded);

    //         if root_hash.eq(&hash) || node_encoded.len() >= H::LENGTH {
    //             memdb.insert(hash, node_encoded).unwrap();
    //         }
    //     }
    //     let trie = PatriciaTrie::from(memdb, Arc::clone(&self.hasher), &root_hash)
    //         .or(Err(TrieError::InvalidProof))?;
    //     trie.get(key).or(Err(TrieError::InvalidProof))
    // }

    fn get_at(
        &self,
        n: Option<NonNull<Node>>,
        partial: &Nibbles,
    ) -> TrieResult<Option<Cow<Vec<u8>>>> {
        if let Some(ptr) = n {
            match unsafe { ptr.as_ref() } {
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
                        self.get_at(branch.children[index], &partial.offset(1))
                    }
                }
                Node::Extension(extension) => {
                    let prefix = &extension.prefix;
                    let match_len = partial.common_prefix(prefix);
                    if match_len == prefix.len() {
                        self.get_at(extension.node, &partial.offset(match_len))
                    } else {
                        Ok(None)
                    }
                }
                Node::Hash(hash_node) => {
                    if let Some(n) = self.recover_from_db(&hash_node.hash)? {
                        let mut ptr = n.into_raw();
                        let res = self
                            .get_at(Some(ptr), partial)?
                            .map(|x| Cow::Owned(x.into_owned()));
                        //free memory.
                        unsafe { Box::from_raw(ptr.as_mut()) };
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

    fn insert_at(&mut self, ptr: Option<NonNull<Node>>, partial: Nibbles, value: Vec<u8>) -> Node {
        if let Some(ptr) = ptr {
            let node = unsafe { Node::from_raw(ptr.as_ptr()) };
            match node {
                Node::Leaf(mut leaf) => {
                    let match_index = partial.common_prefix(&leaf.key);
                    if match_index == leaf.key.len() {
                        // replace leaf value
                        leaf.value = value;
                        return Node::Leaf(leaf);
                    }

                    let old_partial = leaf.key;
                    //need to split the node.
                    let mut branch = BranchNode::new_empty();

                    let leaf_node = Node::new_leaf(old_partial.offset(match_index + 1), leaf.value);

                    branch.insert(old_partial.hex_at(match_index), leaf_node);

                    let node = Node::new_leaf(partial.offset(match_index + 1), value);
                    branch.insert(partial.hex_at(match_index), node);

                    //Extension node is not needed.
                    if match_index == 0 {
                        return Node::Branch(branch);
                    }

                    // if there is a common prefix.
                    Node::new_extension(partial.slice(0..match_index), Node::Branch(branch))
                }
                Node::Branch(mut branch) => {
                    // 0x10 thus: 16
                    if partial.hex_at(0) == 0x10 {
                        branch.value = Some(value);
                        return Node::Branch(branch);
                    }

                    let branch_idx = partial.hex_at(0);
                    let child = branch.children[branch_idx];
                    let new_child = self.insert_at(child, partial.offset(1), value);
                    branch.children[branch_idx] = Some(new_child.into_raw());
                    Node::Branch(branch)
                }
                Node::Extension(mut ext) => {
                    let prefix = &ext.prefix;
                    let sub_node = unsafe { Node::from_raw(ext.node.unwrap().as_ptr()) };
                    let match_index = partial.common_prefix(prefix);

                    if match_index == 0 {
                        let mut branch = BranchNode::new_empty();
                        branch.insert(
                            prefix.hex_at(0),
                            if prefix.len() == 1 {
                                sub_node
                            } else {
                                Node::new_extension(prefix.offset(1), sub_node)
                            },
                        );
                        let branch_node = Node::Branch(branch);

                        return self.insert_at(Some(branch_node.into_raw()), partial, value);
                    }

                    if match_index == prefix.len() {
                        let next_node = self.insert_at(
                            Some((sub_node).into_raw()),
                            partial.offset(match_index),
                            value,
                        );
                        return Node::new_extension(prefix.clone(), next_node);
                    }

                    //                  Ext(aaabbb) -> Bar
                    //(partial key)  aaacccc -^
                    //                  Ext (aaa) -> Ext(bbb)->Bar
                    //                              cccc -^
                    let new_ext =
                        Node::new_extension(prefix.offset(match_index), sub_node).into_raw();
                    let new_node =
                        self.insert_at(Some(new_ext), partial.offset(match_index), value);
                    ext.prefix = prefix.slice(0..match_index);
                    ext.node = Some(new_node.into_raw());
                    Node::Extension(ext)
                }
                Node::Hash(hash_node) => {
                    if let Ok(n) = self.recover_from_db(&hash_node.hash) {
                        self.passing_keys.insert(hash_node.hash);
                        self.insert_at(n.map(|x| x.into_raw()), partial, value)
                    } else {
                        Node::Hash(hash_node)
                    }
                }
            }
        } else {
            Node::new_leaf(partial, value)
        }
    }

    //after delete_at, the ptr must be assgined a new one.
    fn delete_at(&mut self, n: Option<NonNull<Node>>, partial: &Nibbles) -> (Option<Node>, bool) {
        let (new_n, deleted) = if let Some(ptr) = n {
            let node = unsafe { Node::from_raw(ptr.as_ptr()) };
            match node {
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
                    let node = branch.children[index];

                    let (new_n, deleted) = self.delete_at(node, &partial.offset(1));
                    branch.children[index] = new_n.map(Node::into_raw);

                    (Node::Branch(branch), deleted)
                }
                Node::Extension(mut ext) => {
                    let prefix = &ext.prefix;
                    let match_len = partial.common_prefix(prefix);

                    if match_len == prefix.len() {
                        let (new_n, deleted) = self.delete_at(ext.node, &partial.offset(match_len));

                        ext.node = new_n.map(Node::into_raw);
                        (Node::Extension(ext), deleted)
                    } else {
                        (Node::Extension(ext), false)
                    }
                }
                Node::Hash(hash_node) => {
                    if let Ok(n) = self.recover_from_db(&hash_node.hash) {
                        self.passing_keys.insert(hash_node.hash);
                        match self.delete_at(n.map(Node::into_raw), partial) {
                            (None, d) => return (None, d),
                            (Some(n), d) => (n, d),
                        }
                    } else {
                        (Node::Hash(hash_node), false)
                    }
                }
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
                let mut used_indexs = Vec::with_capacity(16);
                for (index, node) in branch.children.iter().enumerate() {
                    if node.is_some() {
                        used_indexs.push(index);
                    }
                }

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
                    let n =
                        unsafe { Node::from_raw(branch.children[used_index].unwrap().as_ptr()) };

                    let new_node = Node::new_extension(
                        Nibbles::from_hex_unchecked(Bytes::from(vec![used_index as u8])),
                        n,
                    );
                    self.degenerate(new_node)
                } else {
                    Some(Node::Branch(branch))
                }
            }
            Node::Extension(ext) => {
                if let Some(mut next_node) = ext.node {
                    let prefix = &ext.prefix;
                    match unsafe { Node::from_raw(next_node.as_mut()) } {
                        Node::Extension(sub_ext) => {
                            let new_prefix = prefix.join(&sub_ext.prefix);
                            match sub_ext.node {
                                None => None,
                                Some(ptr) => {
                                    let next_node = unsafe { Node::from_raw(ptr.as_ptr()) };
                                    let new_n = Node::new_extension(new_prefix, next_node);
                                    self.degenerate(new_n)
                                }
                            }
                        }
                        Node::Leaf(mut leaf) => {
                            let new_prefix = prefix.join(&leaf.key);
                            leaf.key = new_prefix;
                            Some(Node::Leaf(leaf))
                        }
                        // try again after recovering node from the db.
                        Node::Hash(hash_node) => {
                            match self.recover_from_db(&hash_node.hash) {
                                Ok(node) => {
                                    let hash = hash_node.hash;
                                    self.passing_keys.insert(hash);
                                    if let Some(new_node) = node {
                                        let n = Node::new_extension(ext.prefix.clone(), new_node);
                                        self.degenerate(n)
                                    } else {
                                        None
                                    }
                                }
                                Err(_e) => {
                                    //[TODO]
                                    Some(Node::Hash(hash_node))
                                }
                            }
                        }
                        _ => Some(Node::Extension(ext)),
                    }
                } else {
                    None
                }
            }
            _ => Some(n),
        }
    }

    // // Get nodes path along the key, only the nodes whose encode length is greater than
    // // hash length are added.
    // // For embedded nodes whose data are already contained in their parent node, we don't need to
    // // add them in the path.
    // // In the code below, we only add the nodes get by `get_node_from_hash`, because they contains
    // // all data stored in db, including nodes whose encoded data is less than hash length.
    // fn get_path_at(&self, n: Node, partial: &Nibbles) -> TrieResult<Vec<Node>> {
    //     match n {
    //         Node::Empty | Node::Leaf(_) => Ok(vec![]),
    //         Node::Branch(branch) => {
    //             let borrow_branch = branch.borrow();

    //             if partial.is_empty() || partial.at(0) == 16 {
    //                 Ok(vec![])
    //             } else {
    //                 let node = borrow_branch.children[partial.at(0)].clone();
    //                 self.get_path_at(node, &partial.offset(1))
    //             }
    //         }
    //         Node::Extension(ext) => {
    //             let borrow_ext = ext.borrow();

    //             let prefix = &borrow_ext.prefix;
    //             let match_len = partial.common_prefix(prefix);

    //             if match_len == prefix.len() {
    //                 self.get_path_at(borrow_ext.node.clone(), &partial.offset(match_len))
    //             } else {
    //                 Ok(vec![])
    //             }
    //         }
    //         Node::Hash(hash_node) => {
    //             let n = self.recover_from_db(&hash_node.borrow().hash.clone())?;
    //             let mut rest = self.get_path_at(n.clone(), partial)?;
    //             rest.push(n);
    //             Ok(rest)
    //         }
    //     }
    // }

    // fn commit(&mut self) -> TrieResult<Vec<u8>> {
    //     let encoded = self.encode_node(self.root.clone());
    //     let root_hash = if encoded.len() < H::LENGTH {
    //         let hash = self.hasher.digest(&encoded);
    //         self.cache.borrow_mut().insert(hash.clone(), encoded);
    //         hash
    //     } else {
    //         encoded
    //     };

    //     let mut keys = Vec::with_capacity(self.cache.borrow().len());
    //     let mut values = Vec::with_capacity(self.cache.borrow().len());
    //     for (k, v) in self.cache.borrow_mut().drain() {
    //         keys.push(k.to_vec());
    //         values.push(v);
    //     }

    //     self.db
    //         .insert_batch(keys, values)
    //         .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;

    //     let passing_keys = self.passing_keys.borrow();

    //     let removed_keys: Vec<&[u8]> = passing_keys
    //         .iter()
    //         .filter(|h| !self.gen_keys.borrow().contains(&**h))
    //         .map(|x| x.as_slice())
    //         .collect();

    //     self.db
    //         .remove_batch(&removed_keys)
    //         .map_err(|e| TrieError::DataBaseError(Box::new(e)))?;

    //     self.root_hash = root_hash.to_vec();
    //     self.gen_keys.borrow_mut().clear();
    //     self.passing_keys.borrow_mut().clear();
    //     self.root = self.recover_from_db(&root_hash)?;
    //     Ok(root_hash)
    // }

    // fn encode_node(&self, n: Node) -> Vec<u8> {
    //     // Returns the hash value directly to avoid double counting.
    //     if let Node::Hash(hash_node) = n {
    //         return hash_node.borrow().hash.clone();
    //     }

    //     let data = self.encode_raw(n.clone());
    //     // Nodes smaller than 32 bytes are stored inside their parent,
    //     // Nodes equal to 32 bytes are returned directly
    //     if data.len() < H::LENGTH {
    //         data
    //     } else {
    //         let hash = self.hasher.digest(&data);
    //         self.cache.borrow_mut().insert(hash.clone(), data);

    //         self.gen_keys.borrow_mut().insert(hash.clone());
    //         hash
    //     }
    // }

    // fn encode_raw(&self, n: Node) -> Vec<u8> {
    //     match n {
    //         Node::Empty => rlp::NULL_RLP.to_vec(),
    //         Node::Leaf(leaf) => {
    //             let borrow_leaf = leaf.borrow();

    //             let mut stream = RlpStream::new_list(2);
    //             stream.append(&borrow_leaf.key.encode_compact());
    //             stream.append(&borrow_leaf.value);
    //             stream.out().to_vec()
    //         }
    //         Node::Branch(branch) => {
    //             let borrow_branch = branch.borrow();

    //             let mut stream = RlpStream::new_list(17);
    //             for i in 0..16 {
    //                 let n = borrow_branch.children[i].clone();
    //                 let data = self.encode_node(n);
    //                 if data.len() == H::LENGTH {
    //                     stream.append(&data);
    //                 } else {
    //                     stream.append_raw(&data, 1);
    //                 }
    //             }

    //             match &borrow_branch.value {
    //                 Some(v) => stream.append(v),
    //                 None => stream.append_empty_data(),
    //             };
    //             stream.out().to_vec()
    //         }
    //         Node::Extension(ext) => {
    //             let borrow_ext = ext.borrow();

    //             let mut stream = RlpStream::new_list(2);
    //             stream.append(&borrow_ext.prefix.encode_compact());
    //             let data = self.encode_node(borrow_ext.node.clone());
    //             if data.len() == H::LENGTH {
    //                 stream.append(&data);
    //             } else {
    //                 stream.append_raw(&data, 1);
    //             }
    //             stream.out().to_vec()
    //         }
    //         Node::Hash(_hash) => unreachable!(),
    //     }
    // }

    fn decode_node(&self, data: &[u8]) -> TrieResult<Option<Node>> {
        let r = Rlp::new(data);

        //may becauase
        match r.prototype()? {
            Prototype::Data(0) => Ok(None),
            Prototype::List(2) => {
                let key = r.at(0)?.data()?;
                let key = Nibbles::from_compact(key.to_vec())?;

                if key.is_leaf() {
                    Ok(Some(Node::new_leaf(key, r.at(1)?.data()?.to_vec())))
                } else if let Some(n) = self.decode_node(r.at(1)?.as_raw())? {
                    Ok(Some(Node::new_extension(key, n)))
                } else {
                    Ok(None)
                }
            }
            Prototype::List(17) => {
                let mut node = BranchNode::new_empty();
                #[allow(clippy::needless_range_loop)]
                for i in 0..16 {
                    let rlp_data = r.at(i)?;
                    let n = self.decode_node(rlp_data.as_raw())?;
                    node.children[i] = n.map(|x| x.into_raw());
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
            self.decode_node(&data)?
        } else {
            None
        })
    }

    // fn cache_node(&self, n: Node) -> TrieResult<Vec<u8>> {
    //     match n {
    //         Node::Empty => Ok(rlp::NULL_RLP.to_vec()),
    //         Node::Leaf(leaf) => {
    //             let borrow_leaf = leaf.borrow();

    //             let mut stream = RlpStream::new_list(2);
    //             stream.append(&borrow_leaf.key.encode_compact());
    //             stream.append(&borrow_leaf.value);
    //             Ok(stream.out().to_vec())
    //         }
    //         Node::Branch(branch) => {
    //             let borrow_branch = branch.borrow();

    //             let mut stream = RlpStream::new_list(17);
    //             for i in 0..16 {
    //                 let n = borrow_branch.children[i].clone();
    //                 let data = self.cache_node(n)?;
    //                 if data.len() == H::LENGTH {
    //                     stream.append(&data);
    //                 } else {
    //                     stream.append_raw(&data, 1);
    //                 }
    //             }

    //             match &borrow_branch.value {
    //                 Some(v) => stream.append(v),
    //                 None => stream.append_empty_data(),
    //             };
    //             Ok(stream.out().to_vec())
    //         }
    //         Node::Extension(ext) => {
    //             let borrow_ext = ext.borrow();

    //             let mut stream = RlpStream::new_list(2);
    //             stream.append(&borrow_ext.prefix.encode_compact());
    //             let data = self.cache_node(borrow_ext.node.clone())?;
    //             if data.len() == H::LENGTH {
    //                 stream.append(&data);
    //             } else {
    //                 stream.append_raw(&data, 1);
    //             }
    //             Ok(stream.out().to_vec())
    //         }
    //         Node::Hash(hash_node) => {
    //             let hash = hash_node.borrow().hash.clone();
    //             let next_node = self.recover_from_db(&hash)?;
    //             let data = self.cache_node(next_node)?;
    //             self.cache.borrow_mut().insert(hash.clone(), data);
    //             Ok(hash)
    //         }
    //     }
    // }
}

impl<D: Database, H: Hasher> Drop for PatriciaTrie<D, H> {
    fn drop(&mut self) {
        if let Some(mut ptr) = self.root {
            unsafe { Box::from_raw(ptr.as_mut()) };
        }
    }
}

#[cfg(test)]
mod tests {
    // use rand::distributions::Alphanumeric;
    // use rand::seq::SliceRandom;
    // use rand::{thread_rng, Rng};
    // use std::collections::{HashMap, HashSet};
    // use std::sync::Arc;

    // use hasher::{Hasher, HasherKeccak};

    // use super::PatriciaTrie;
    // use crate::db::{Database, MemoryDB};

    // #[test]
    // fn test_trie_insert() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));
    //     trie.insert(b"test".to_vec(), b"test".to_vec()).unwrap();
    // }

    // #[test]
    // fn test_trie_get() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));
    //     trie.insert(b"test".to_vec(), b"test".to_vec()).unwrap();
    //     let v = trie.get(b"test").unwrap();

    //     assert_eq!(Some(b"test".to_vec()), v)
    // }

    // #[test]
    // fn test_trie_random_insert() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));

    //     for _ in 0..1000 {
    //         let rand_str: String = thread_rng().sample_iter(&Alphanumeric).take(30).collect();
    //         let val = rand_str.as_bytes();
    //         trie.insert(val.to_vec(), val.to_vec()).unwrap();

    //         let v = trie.get(val).unwrap();
    //         assert_eq!(v.map(|v| v.to_vec()), Some(val.to_vec()));
    //     }
    // }

    // #[test]
    // fn test_trie_contains() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));
    //     trie.insert(b"test".to_vec(), b"test".to_vec()).unwrap();
    //     assert!(trie.contains(b"test").unwrap());
    //     assert!(!trie.contains(b"test2").unwrap());
    // }

    // #[test]
    // fn test_trie_remove() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));
    //     trie.insert(b"test".to_vec(), b"test".to_vec()).unwrap();
    //     let removed = trie.remove(b"test").unwrap();
    //     assert!(removed)
    // }

    // #[test]
    // fn test_trie_random_remove() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));

    //     for _ in 0..1000 {
    //         let rand_str: String = thread_rng().sample_iter(&Alphanumeric).take(30).collect();
    //         let val = rand_str.as_bytes();
    //         trie.insert(val.to_vec(), val.to_vec()).unwrap();

    //         let removed = trie.remove(val).unwrap();
    //         assert!(removed);
    //     }
    // }

    // #[test]
    // fn test_trie_from_root() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let root = {
    //         let mut trie = PatriciaTrie::new(Arc::clone(&memdb), Arc::new(HasherKeccak::new()));
    //         trie.insert(b"test".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test1".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test2".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test23".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test33".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test44".to_vec(), b"test".to_vec()).unwrap();
    //         trie.root().unwrap()
    //     };

    //     let mut trie =
    //         PatriciaTrie::from(Arc::clone(&memdb), Arc::new(HasherKeccak::new()), &root).unwrap();
    //     let v1 = trie.get(b"test33").unwrap();
    //     assert_eq!(Some(b"test".to_vec()), v1);
    //     let v2 = trie.get(b"test44").unwrap();
    //     assert_eq!(Some(b"test".to_vec()), v2);
    //     let root2 = trie.root().unwrap();
    //     assert_eq!(hex::encode(root), hex::encode(root2));
    // }

    // #[test]
    // fn test_trie_from_root_and_insert() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let root = {
    //         let mut trie = PatriciaTrie::new(Arc::clone(&memdb), Arc::new(HasherKeccak::new()));
    //         trie.insert(b"test".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test1".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test2".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test23".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test33".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test44".to_vec(), b"test".to_vec()).unwrap();
    //         trie.commit().unwrap()
    //     };

    //     let mut trie =
    //         PatriciaTrie::from(Arc::clone(&memdb), Arc::new(HasherKeccak::new()), &root).unwrap();
    //     trie.insert(b"test55".to_vec(), b"test55".to_vec()).unwrap();
    //     trie.commit().unwrap();
    //     let v = trie.get(b"test55").unwrap();
    //     assert_eq!(Some(b"test55".to_vec()), v);
    // }

    // #[test]
    // fn test_trie_from_root_and_delete() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let root = {
    //         let mut trie = PatriciaTrie::new(Arc::clone(&memdb), Arc::new(HasherKeccak::new()));
    //         trie.insert(b"test".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test1".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test2".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test23".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test33".to_vec(), b"test".to_vec()).unwrap();
    //         trie.insert(b"test44".to_vec(), b"test".to_vec()).unwrap();
    //         trie.commit().unwrap()
    //     };

    //     let mut trie =
    //         PatriciaTrie::from(Arc::clone(&memdb), Arc::new(HasherKeccak::new()), &root).unwrap();
    //     let removed = trie.remove(b"test44").unwrap();
    //     assert!(removed);
    //     let removed = trie.remove(b"test33").unwrap();
    //     assert!(removed);
    //     let removed = trie.remove(b"test23").unwrap();
    //     assert!(removed);
    // }

    // #[test]
    // fn test_multiple_trie_roots() {
    //     let k0: ethereum_types::H256 = 0.into();
    //     let k1: ethereum_types::H256 = 1.into();
    //     let v: ethereum_types::H256 = 0x1234.into();

    //     let root1 = {
    //         let memdb = Arc::new(MemoryDB::new(true));
    //         let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));
    //         trie.insert(k0.as_bytes().to_vec(), v.as_bytes().to_vec())
    //             .unwrap();
    //         trie.root().unwrap()
    //     };

    //     let root2 = {
    //         let memdb = Arc::new(MemoryDB::new(true));
    //         let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));
    //         trie.insert(k0.as_bytes().to_vec(), v.as_bytes().to_vec())
    //             .unwrap();
    //         trie.insert(k1.as_bytes().to_vec(), v.as_bytes().to_vec())
    //             .unwrap();
    //         trie.root().unwrap();
    //         trie.remove(k1.as_ref()).unwrap();
    //         trie.root().unwrap()
    //     };

    //     let root3 = {
    //         let memdb = Arc::new(MemoryDB::new(true));
    //         let mut trie1 = PatriciaTrie::new(Arc::clone(&memdb), Arc::new(HasherKeccak::new()));
    //         trie1
    //             .insert(k0.as_bytes().to_vec(), v.as_bytes().to_vec())
    //             .unwrap();
    //         trie1
    //             .insert(k1.as_bytes().to_vec(), v.as_bytes().to_vec())
    //             .unwrap();
    //         trie1.root().unwrap();
    //         let root = trie1.root().unwrap();
    //         let mut trie2 =
    //             PatriciaTrie::from(Arc::clone(&memdb), Arc::new(HasherKeccak::new()), &root)
    //                 .unwrap();
    //         trie2.remove(&k1.as_bytes().to_vec()).unwrap();
    //         trie2.root().unwrap()
    //     };

    //     assert_eq!(root1, root2);
    //     assert_eq!(root2, root3);
    // }

    // #[test]
    // fn test_delete_stale_keys_with_random_insert_and_delete() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));

    //     let mut rng = rand::thread_rng();
    //     let mut keys = vec![];
    //     for _ in 0..100 {
    //         let random_bytes: Vec<u8> = (0..rng.gen_range(2, 30))
    //             .map(|_| rand::random::<u8>())
    //             .collect();
    //         trie.insert(random_bytes.clone(), random_bytes.clone())
    //             .unwrap();
    //         keys.push(random_bytes.clone());
    //     }
    //     trie.commit().unwrap();
    //     let slice = &mut keys;
    //     slice.shuffle(&mut rng);

    //     for key in slice.iter() {
    //         trie.remove(key).unwrap();
    //     }
    //     trie.commit().unwrap();

    //     let empty_node_key = HasherKeccak::new().digest(&rlp::NULL_RLP);
    //     let value = trie.db.get(empty_node_key.as_ref()).unwrap().unwrap();
    //     assert_eq!(value, &rlp::NULL_RLP)
    // }

    // #[test]
    // fn insert_full_branch() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(memdb, Arc::new(HasherKeccak::new()));

    //     trie.insert(b"test".to_vec(), b"test".to_vec()).unwrap();
    //     trie.insert(b"test1".to_vec(), b"test".to_vec()).unwrap();
    //     trie.insert(b"test2".to_vec(), b"test".to_vec()).unwrap();
    //     trie.insert(b"test23".to_vec(), b"test".to_vec()).unwrap();
    //     trie.insert(b"test33".to_vec(), b"test".to_vec()).unwrap();
    //     trie.insert(b"test44".to_vec(), b"test".to_vec()).unwrap();
    //     trie.root().unwrap();

    //     let v = trie.get(b"test").unwrap();
    //     assert_eq!(Some(b"test".to_vec()), v);
    // }

    // #[test]
    // fn iterator_trie() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut root1;
    //     let mut kv = HashMap::new();
    //     kv.insert(b"test".to_vec(), b"test".to_vec());
    //     kv.insert(b"test1".to_vec(), b"test1".to_vec());
    //     kv.insert(b"test11".to_vec(), b"test2".to_vec());
    //     kv.insert(b"test14".to_vec(), b"test3".to_vec());
    //     kv.insert(b"test16".to_vec(), b"test4".to_vec());
    //     kv.insert(b"test18".to_vec(), b"test5".to_vec());
    //     kv.insert(b"test2".to_vec(), b"test6".to_vec());
    //     kv.insert(b"test23".to_vec(), b"test7".to_vec());
    //     kv.insert(b"test9".to_vec(), b"test8".to_vec());
    //     {
    //         let mut trie = PatriciaTrie::new(memdb.clone(), Arc::new(HasherKeccak::new()));
    //         let mut kv = kv.clone();
    //         kv.iter().for_each(|(k, v)| {
    //             trie.insert(k.clone(), v.clone()).unwrap();
    //         });
    //         root1 = trie.root().unwrap();

    //         trie.iter()
    //             .for_each(|(k, v)| assert_eq!(kv.remove(&k).unwrap(), v));
    //         assert!(kv.is_empty());
    //     }

    //     {
    //         let mut trie = PatriciaTrie::new(memdb.clone(), Arc::new(HasherKeccak::new()));
    //         let mut kv2 = HashMap::new();
    //         kv2.insert(b"test".to_vec(), b"test11".to_vec());
    //         kv2.insert(b"test1".to_vec(), b"test12".to_vec());
    //         kv2.insert(b"test14".to_vec(), b"test13".to_vec());
    //         kv2.insert(b"test22".to_vec(), b"test14".to_vec());
    //         kv2.insert(b"test9".to_vec(), b"test15".to_vec());
    //         kv2.insert(b"test16".to_vec(), b"test16".to_vec());
    //         kv2.insert(b"test2".to_vec(), b"test17".to_vec());
    //         kv2.iter().for_each(|(k, v)| {
    //             trie.insert(k.clone(), v.clone()).unwrap();
    //         });

    //         trie.root().unwrap();

    //         let mut kv_delete = HashSet::new();
    //         kv_delete.insert(b"test".to_vec());
    //         kv_delete.insert(b"test1".to_vec());
    //         kv_delete.insert(b"test14".to_vec());

    //         kv_delete.iter().for_each(|k| {
    //             trie.remove(&k).unwrap();
    //         });

    //         kv2.retain(|k, _| !kv_delete.contains(k));

    //         trie.root().unwrap();
    //         trie.iter()
    //             .for_each(|(k, v)| assert_eq!(kv2.remove(&k).unwrap(), v));
    //         assert!(kv2.is_empty());
    //     }

    //     let trie = PatriciaTrie::from(memdb, Arc::new(HasherKeccak::new()), &root1).unwrap();
    //     trie.iter()
    //         .for_each(|(k, v)| assert_eq!(kv.remove(&k).unwrap(), v));
    //     assert!(kv.is_empty());
    // }
}
