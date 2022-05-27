use bytes::BytesMut;

use crate::PatriciaTrie;
use crate::{hasher::Hasher, Database};
use std::borrow::Cow;
use std::sync::Arc;

use super::TrieResult;

pub struct SecureTrie<D: Database, H: Hasher, HK: Hasher> {
    tire: PatriciaTrie<D, H>,
    key_hasher: HK,
}

impl<D: Database, H: Hasher, HK: Hasher> SecureTrie<D, H, HK> {
    pub fn new(db: Arc<D>, hasher: H, key_hasher: HK) -> Self {
        let tire = PatriciaTrie::new(db, hasher);
        SecureTrie { tire, key_hasher }
    }

    //hash the key for security.
    fn hash_key(&self, key: impl AsRef<[u8]>) -> Vec<u8> {
        self.key_hasher.digest(key.as_ref())
    }

    /// Inserts value into trie and modifies it if it exists
    pub fn insert(&mut self, key: &[u8], value: Vec<u8>) -> TrieResult<()> {
        self.tire.insert(&self.hash_key(key), value)
    }

    /// Returns the value for key stored in the trie.
    pub fn get(&mut self, key: &[u8]) -> TrieResult<Option<Cow<Vec<u8>>>> {
        self.tire.get(&self.hash_key(key))
    }

    /// Checks that the key is present in the trie
    pub fn contains(&self, key: &[u8]) -> TrieResult<bool> {
        self.tire.contains(&self.hash_key(key))
    }

    /// Removes any existing value for key from the trie.
    pub fn remove(&mut self, key: &[u8]) -> TrieResult<bool> {
        self.tire.remove(&self.hash_key(key))
    }
    /// Saves all the nodes in the db, clears the cache data, recalculates the root.
    /// Returns the root hash of the trie.
    pub fn root(&mut self) -> TrieResult<Vec<u8>> {
        self.tire.root()
    }

    pub fn from(db:Arc<D>, hasher: H, key_hasher: HK, root_hash: Vec<u8>) -> TrieResult<Self> {
        let tire = PatriciaTrie::from(db, hasher, root_hash)?;
        Ok(SecureTrie{
            tire,
            key_hasher,
        })
    }

    /// Prove constructs a merkle proof for key. The result contains all encoded nodes
    /// on the path to the value at key. The value itself is also included in the last
    /// node and can be retrieved by verifying the proof.
    ///
    /// If the trie does not contain a value for key, the returned proof contains all
    /// nodes of the longest existing prefix of the key (at least the root node), ending
    /// with the node that proves the absence of the key.
    pub fn get_proof(&mut self, key: &[u8]) -> TrieResult<Vec<BytesMut>> {
        self.tire.get_proof(&self.hash_key(&key))
    }

    /// return value if key exists, None if key not exist, Error if proof is wrong
    pub fn verify_proof(
        &self,
        root_hash: Vec<u8>,
        key: &[u8],
        proof: Vec<impl AsRef<[u8]>>,
    ) -> TrieResult<Option<Vec<u8>>> {
        self.tire
            .verify_proof(root_hash, &self.hash_key(key), proof)
    }
}

#[cfg(test)]
mod test{
    use std::sync::Arc;

    use super::SecureTrie;

    use crate::hasher::{HasherKeccak, Blake3};
    use crate::db::MemoryDB;

    use rand::{
        thread_rng,
        distributions::Alphanumeric,
        Rng,
        seq::SliceRandom,
    };

    #[test]
    fn test_insert() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = SecureTrie::new(memdb, HasherKeccak::new(), Blake3::new());
        trie.insert(b"test", b"test".to_vec()).unwrap();
    }

    #[test]
    fn test_trie_get() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = SecureTrie::new(memdb, HasherKeccak::new(), Blake3::new());
        trie.insert(b"test", b"test".to_vec()).unwrap();
        let v = trie.get(b"test").unwrap();
        assert_eq!(b"test", v.unwrap().as_slice())
    }

    #[test]
    fn test_trie_random_insert() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = SecureTrie::new(memdb, HasherKeccak::new(), Blake3::new());

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
        let mut trie = SecureTrie::new(memdb, HasherKeccak::new(), Blake3::new());
        trie.insert(b"test", b"test".to_vec()).unwrap();
        assert!(trie.contains(b"test").unwrap());
        assert!(!trie.contains(b"test2").unwrap());
    }

    #[test]
    fn test_trie_remove() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = SecureTrie::new(memdb, HasherKeccak::new(), Blake3::new());
        trie.insert(b"test", b"test".to_vec()).unwrap();
        let removed = trie.remove(b"test").unwrap();
        assert!(removed)
    }

    #[test]
    fn test_trie_random_remove() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = SecureTrie::new(memdb, HasherKeccak::new(), Blake3::new());

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
            let mut trie = SecureTrie::new(memdb.clone(), HasherKeccak::new(), Blake3::new());
            trie.insert(b"test", b"test".to_vec()).unwrap();
            trie.insert(b"test1", b"test".to_vec()).unwrap();
            trie.insert(b"test2", b"test".to_vec()).unwrap();
            trie.insert(b"test23", b"test".to_vec()).unwrap();
            trie.insert(b"test33", b"test".to_vec()).unwrap();
            trie.insert(b"test44", b"test".to_vec()).unwrap();
            trie.root().unwrap()
        };

        let mut trie =
            SecureTrie::from(memdb.clone(), HasherKeccak::new(), Blake3::new(), root.clone()).unwrap();
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
            let mut trie = SecureTrie::new(Arc::clone(&memdb), HasherKeccak::new(), Blake3::new());
            trie.insert(b"test1", b"test".to_vec()).unwrap();
            trie.insert(b"test2", b"test".to_vec()).unwrap();
            trie.insert(b"test23", b"test".to_vec()).unwrap();
            trie.insert(b"test33", b"test".to_vec()).unwrap();
            trie.insert(b"test44", b"test".to_vec()).unwrap();
            trie.root().unwrap()
        };

        let mut trie = SecureTrie::from(Arc::clone(&memdb), HasherKeccak::new(), Blake3::new(),root).unwrap();
        trie.insert(b"test55", b"test55".to_vec()).unwrap();
        trie.root().unwrap();
        let v = trie.get(b"test55").unwrap().map(|x| x.into_owned());
        assert_eq!(Some(b"test55".to_vec()), v);
    }

    #[test]
    fn test_trie_from_root_and_delete() {
        let memdb = Arc::new(MemoryDB::new(true));
        let root = {
            let mut trie = SecureTrie::new(Arc::clone(&memdb), HasherKeccak::new(), Blake3::new());
            trie.insert(b"test", b"test".to_vec()).unwrap();
            trie.insert(b"test1", b"test".to_vec()).unwrap();
            trie.insert(b"test2", b"test".to_vec()).unwrap();
            trie.insert(b"test23", b"test".to_vec()).unwrap();
            trie.insert(b"test33", b"test".to_vec()).unwrap();
            trie.insert(b"test44", b"test".to_vec()).unwrap();
            trie.root().unwrap()
        };

        let mut trie = SecureTrie::from(Arc::clone(&memdb), HasherKeccak::new(), Blake3::new(),  root).unwrap();

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
            let mut trie = SecureTrie::new(memdb, HasherKeccak::new(), Blake3::new());
            trie.insert(k0.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie.root().unwrap()
        };

        let root2 = {
            let memdb = Arc::new(MemoryDB::new(true));
            let mut trie = SecureTrie::new(memdb, HasherKeccak::new(), Blake3::new());
            trie.insert(k0.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie.insert(k1.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie.root().unwrap();
            trie.remove(k1.as_ref()).unwrap();
            trie.root().unwrap()
        };

        let root3 = {
            let memdb = Arc::new(MemoryDB::new(true));
            let mut trie1 = SecureTrie::new(Arc::clone(&memdb), HasherKeccak::new(), Blake3::new());
            trie1.insert(k0.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie1.insert(k1.as_bytes(), v.as_bytes().to_vec()).unwrap();
            trie1.root().unwrap();
            let root = trie1.root().unwrap();
            let mut trie2 =
                SecureTrie::from(Arc::clone(&memdb), HasherKeccak::new(), Blake3::new(),root).unwrap();
            trie2.remove(&k1.as_bytes().to_vec()).unwrap();
            trie2.root().unwrap()
        };

        assert_eq!(root1, root2);
        assert_eq!(root2, root3);
    }

    #[test]
    fn insert_full_branch() {
        let memdb = Arc::new(MemoryDB::new(true));
        let mut trie = SecureTrie::new(memdb, HasherKeccak::new(),Blake3::new());

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

    // #[test]
    // fn test_proof_random() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(Arc::clone(&memdb), HasherKeccak::new());
    //     let mut rng = rand::thread_rng();
    //     let mut keys = vec![];
    //     for _ in 0..100 {
    //         let random_bytes: Vec<u8> = (0..rng.gen_range(2, 30))
    //             .map(|_| rand::random::<u8>())
    //             .collect();
    //         trie.insert(&random_bytes, random_bytes.clone()).unwrap();
    //         keys.push(random_bytes.clone());
    //     }
    //     for k in keys.clone().into_iter() {
    //         trie.insert(&k, k.clone()).unwrap();
    //     }
    //     let root = trie.root().unwrap();
    //     for k in keys.into_iter() {
    //         let proof = trie.get_proof(&k).unwrap();
    //         let value = trie.verify_proof(root.clone(), &k, proof).unwrap().unwrap();
    //         assert_eq!(value, k);
    //     }
    // }

    // #[test]
    // fn test_proof_empty_trie() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(Arc::clone(&memdb), HasherKeccak::new());
    //     trie.root().unwrap();
    //     let proof = trie.get_proof(b"not-exist").unwrap();
    //     assert_eq!(proof.len(), 0);
    // }

    // #[test]
    // fn test_proof_one_element() {
    //     let memdb = Arc::new(MemoryDB::new(true));
    //     let mut trie = PatriciaTrie::new(Arc::clone(&memdb), HasherKeccak::new());
    //     trie.insert(b"k", b"v".to_vec()).unwrap();
    //     let root = trie.root().unwrap();
    //     let proof = trie.get_proof(b"k").unwrap();
    //     assert_eq!(proof.len(), 1);
    //     let value = trie
    //         .verify_proof(root.clone(), b"k", proof.clone())
    //         .unwrap();
    //     assert_eq!(value, Some(b"v".to_vec()));

    //     // remove key does not affect the verify process
    //     trie.remove(b"k").unwrap();
    //     let _root = trie.root().unwrap();
    //     let value = trie.verify_proof(root, b"k", proof).unwrap();
    //     assert_eq!(value, Some(b"v".to_vec()));
    // }
}