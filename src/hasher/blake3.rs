use super::Hasher;

///Hasher of Blake3.
#[derive(Clone, Copy, Debug)]
pub struct Blake3;

impl Hasher for Blake3 {
    const LENGTH: usize = 32;

    fn digest(&self, data: &[u8]) -> Vec<u8> {
        let hash = blake3::hash(data);
        hash.as_bytes().to_vec()
    }
}
