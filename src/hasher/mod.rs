pub trait Hasher {
    const LENGTH: usize;

    fn digest(&self, data: &[u8]) -> Vec<u8>;
}

pub mod blake3;
pub mod keccak;

pub use keccak::HasherKeccak;
