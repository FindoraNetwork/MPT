pub trait Hasher {
    const LENGTH: usize;

    fn digest(&self, data: &[u8]) -> Vec<u8>;
}

mod blake3;
mod keccak;

pub use keccak::HasherKeccak;
