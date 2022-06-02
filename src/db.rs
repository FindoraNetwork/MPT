use std::collections::HashMap;
use std::convert::Infallible;
use std::error::Error as StdError;
use std::sync::Arc;

use parking_lot::RwLock;

/// "Database" defines the "trait" of trie and database interaction.
/// You should first write the data to the cache and write the data
/// to the database in bulk after the end of a set of operations.
pub trait Database: Send + Sync {
    type Error: 'static + StdError;

    /// Returns a the data corresponding to the key.
    fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error>;

    /// Returns true if the map contains data for the specified key.
    fn contains(&self, key: &[u8]) -> Result<bool, Self::Error>;

    /// Insert data into the cache.
    fn insert(&self, key: &[u8], value: &[u8]) -> Result<(), Self::Error>;

    /// Removes a key from the cache, returning the data at the key if the key was previously in the map.
    fn remove(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error>;

    /// Insert a batch of data into the cache.
    fn insert_batch<K, V>(&self, keys: &[K], values: &[V]) -> Result<(), Self::Error>
    where
        K: AsRef<[u8]>,
        V: AsRef<[u8]>,
    {
        for (key, value) in keys.iter().zip(values) {
            self.insert(key.as_ref(), value.as_ref())?;
        }
        Ok(())
    }

    /// Remove a batch of data into the cache, drop the data at the keys.
    fn remove_batch(&self, keys: &[&[u8]]) -> Result<(), Self::Error> {
        for key in keys {
            self.remove(key)?;
        }
        Ok(())
    }

    /// Flush data to the DB from the cache.
    fn flush(&self) -> Result<(), Self::Error>;

    #[cfg(test)]
    fn len(&self) -> Result<usize, Self::Error>;
    #[cfg(test)]
    fn is_empty(&self) -> Result<bool, Self::Error>;
}

/// Memeory based database, implemented via a HashMap.
///  If "light" is true, the data is deleted from the database at the time of submission.
#[derive(Default, Debug)]
pub struct MemoryDB {
    light: bool,
    storage: Arc<RwLock<HashMap<Vec<u8>, Vec<u8>>>>,
}

impl MemoryDB {
    pub fn new(light: bool) -> Self {
        MemoryDB {
            light,
            storage: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl Database for MemoryDB {
    //HashMap based database will not fail.
    type Error = Infallible;

    fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
        Ok(self.storage.read().get(key).cloned())
    }

    fn insert(&self, key: &[u8], value: &[u8]) -> Result<(), Self::Error> {
        self.storage.write().insert(key.to_vec(), value.to_vec());
        Ok(())
    }

    fn contains(&self, key: &[u8]) -> Result<bool, Self::Error> {
        Ok(self.storage.read().contains_key(key))
    }

    fn remove(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
        Ok(if self.light {
            self.storage.write().remove(key)
        } else {
            None
        })
    }

    fn flush(&self) -> Result<(), Self::Error> {
        Ok(())
    }

    #[cfg(test)]
    fn len(&self) -> Result<usize, Self::Error> {
        Ok(self.storage.try_read().unwrap().len())
    }
    #[cfg(test)]
    fn is_empty(&self) -> Result<bool, Self::Error> {
        Ok(self.storage.try_read().unwrap().is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memdb_get() {
        let memdb = MemoryDB::new(true);
        memdb.insert(b"test-key", b"test-value").unwrap();
        let v = memdb.get(b"test-key").unwrap().unwrap();

        assert_eq!(v, b"test-value")
    }

    #[test]
    fn test_memdb_contains() {
        let memdb = MemoryDB::new(true);
        memdb.insert(b"test", b"test").unwrap();

        let contains = memdb.contains(b"test").unwrap();
        assert!(contains)
    }

    #[test]
    fn test_memdb_remove() {
        let memdb = MemoryDB::new(true);
        memdb.insert(b"test", b"test").unwrap();

        memdb.remove(b"test").unwrap();
        let contains = memdb.contains(b"test").unwrap();
        assert!(!contains)
    }
}
