/// This file define the error type that used in this crate.
use rlp::DecoderError;
use thiserror::Error;

use std::error::Error as StdError;

///Error types for this crate.
#[derive(Error, Debug)]
pub enum TrieError {
    //Error for customized database.
    #[error("Database error: {0}.")]
    DataBaseError(Box<dyn StdError>),
    #[error("rlp decode error: {0}.")]
    Decoder(#[from] DecoderError),
    #[error("Trie error: Invalid data.")]
    InvalidData,
    #[error("Trie error: Invalid state root.")]
    InvalidStateRoot,
    #[error("Trie error: Invalid proof.")]
    InvalidProof,
    #[error("Invalid hex: {0}, [0,16) expected.")]
    InvalidHex(u8),
}
