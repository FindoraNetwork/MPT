pub trait Hasher {
    const LENGTH: usize;

    fn digest(&self, data: &[u8]) -> Vec<u8>;
}

