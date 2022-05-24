#![allow(clippy::needless_doctest_main)]
//! ## Usage
//!
//! ```rust
//! 
//! use std::sync::Arc;
//!
//! use cita_trie::MemoryDB;
//! use cita_trie::PatriciaTrie;
//! use cita_trie::hasher::{Hasher, HasherKeccak};
//! 
//! fn main() {
//!     let memdb = Arc::new(MemoryDB::new(true));
//!     let hasher = HasherKeccak::new();
//!
//!     let key = b"test-key";
//!     let value = b"test-value";
//!
//!     let root = {
//!         let mut trie = PatriciaTrie::new(Arc::clone(&memdb), hasher);
//!         trie.insert(key, value.to_vec()).unwrap();
//!
//!         let v = trie.get(key).unwrap().map(|v|v.into_owned());
//!         assert_eq!(Some(value.to_vec()), v);
//!         trie.root().unwrap()
//!     };
//!
//!     let mut trie = PatriciaTrie::from(Arc::clone(&memdb), hasher, root.clone()).unwrap();
//!     let exists = trie.contains(key).unwrap();
//!     assert!(exists);
//!     let removed = trie.remove(key).unwrap();
//!     assert!(removed);
//!     let new_root = trie.root().unwrap();
//!     println!("new root = {:?}", new_root);
//! }
//! ```
//! 
//! This data structure combines Patricia tree nad Merkle Tree together to obtain a  deterministic state.
//! It's a rust version of Ethereum MPT tree.
//! 
//! Patricia tree is a kind of Radix trees.
//! 
//! It's looks like:
//!             
//!                                   [..]
//!                                 /     \
//!                               [t]     [slow *]
//!                              /  \           \
//!                         [oast]   [est *]     [ly *]
//!                        /     \        
//!                     [er *]  [ing *]      
//!                              
//!      Patricia tree that contains {"slow", "slowly", "test", "toasting", "toaster"}.        
//! 
//! 
//! This crate is similar to a K-V database that store data of bytes.
//! The key is hex-encoded so that the tree is a 16-branch lookup tree, it looks like:
//! 
//!                            root -> Branch[0..f] -> None
//!                                   / b       \ f
//!                           Leaf[3,f]->data1    Extension[a,b,c]
//!                                                |
//!                                             Branch[0..f]->Some(data2)
//!                                             / 1        \ 2
//!                                     Leaf[a]->data3    Leaf[b]->data4
//! 
//! This MPT tree  contains data pair: {0xb3f: data1, 0xfabc: data2, 0xfabc1a: data3, 0xfabc2b:data4}.
//! The root hash is just the hash of Rlp-encoded data of the root node.
//!
mod nibbles;
mod tests;

mod db;
mod errors;
pub mod hasher;
mod trie;

pub use db::{Database, MemoryDB};
pub use errors::TrieError;
pub use trie::PatriciaTrie;
