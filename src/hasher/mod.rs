pub trait Hasher {
    const LENGTH: usize;

    fn digest(&self, data: &[u8]) -> Vec<u8>;
}

pub mod keccak;
pub mod blake3;

pub use keccak::HasherKeccak;