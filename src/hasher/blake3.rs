use super::Hasher;

///Hasher of Blake3.
#[derive(Clone, Copy, Debug)]
pub struct HasherBlake3;

impl HasherBlake3 {
    pub fn new() -> Self {
        HasherBlake3{}
    }
}

impl Hasher for HasherBlake3 {
    const LENGTH: usize = 32;

    fn digest(&self, data: &[u8]) -> Vec<u8> {
        let hash = blake3::hash(data);
        hash.as_bytes().to_vec()
    }
}
