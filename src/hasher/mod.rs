pub trait Hasher: Clone {
    const LENGTH: usize;

    fn digest(&self, data: &[u8]) -> Vec<u8>;
}

mod blake3;
mod keccak;
mod sha2;

pub use self::blake3::HasherBlake3;
pub use self::keccak::HasherKeccak;
pub use self::sha2::{HasherSha256, HasherSha512};
