use crate::errors::TrieError;

pub type TrieResult<T> = Result<T, TrieError>;

mod iterator;
mod node;
mod secure_trie;
mod tire;

pub use secure_trie::SecureTrie;
pub use tire::PatriciaTrie;
