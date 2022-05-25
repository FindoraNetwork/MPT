use sha2::Digest;

use super::Hasher;

///Hasher of Sha256
#[derive(Clone, Copy, Debug)]
pub struct Sha256;

impl Hasher for Sha256 {
    const LENGTH: usize = 32;

    fn digest(&self, data: &[u8]) -> Vec<u8> {
        let mut hasher = sha2::Sha256::new();
        hasher.update(data);
        let result = hasher.finalize();
        result[..].to_vec()
    }
}

///Hasher of Sha512
#[derive(Clone, Copy, Debug)]
pub struct Sha512;

impl Hasher for Sha512 {
    const LENGTH: usize = 64;

    fn digest(&self, data: &[u8]) -> Vec<u8> {
        let mut hasher = sha2::Sha512::new();
        hasher.update(data);
        let result = hasher.finalize();
        result[..].to_vec()
    }
}
