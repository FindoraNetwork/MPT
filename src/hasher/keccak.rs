use tiny_keccak::Hasher as H;

use super::Hasher;

///Hasher of Keccak.
#[derive(Clone, Copy, Debug)]
pub struct HasherKeccak;

impl HasherKeccak {
    pub fn new() -> Self {
        Self {}
    }
}

impl Hasher for HasherKeccak {
    const LENGTH: usize = 32;

    fn digest(&self, data: &[u8]) -> Vec<u8> {
        let mut hasher = tiny_keccak::Keccak::v256();
        let mut result: [u8; 32] = [0; 32];
        hasher.update(data);
        hasher.finalize(&mut result);
        result.to_vec()
    }
}
