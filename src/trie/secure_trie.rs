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
