## CITA-Trie

Rust implementation of the Modified Patricia Tree (aka Trie),

The implementation is strongly inspired by [go-ethereum trie](https://github.com/ethereum/go-ethereum/tree/master/trie)

## Features

- Implementation of the Modified Patricia Tree
- Custom hash algorithm (Keccak, Blake3, SHA2 is provided by default)
- Custom storage interface
- Is Sync.

## Example

```rust
 use std::sync::Arc;

 use cita_trie::MemoryDB;
 use cita_trie::PatriciaTrie;
 use cita_trie::hasher::{Hasher, HasherKeccak};

 fn main() {
     let memdb = Arc::new(MemoryDB::new(true));
     let hasher = HasherKeccak::new();

     let key = b"test-key";
     let value = b"test-value";

     let root = {
         let mut trie = PatriciaTrie::new(Arc::clone(&memdb), hasher);
         trie.insert(key, value.to_vec()).unwrap();

         let v = trie.get(key).unwrap().map(|v|v.into_owned());
         assert_eq!(Some(value.to_vec()), v);
         trie.commit().unwrap()
     };

     let mut trie = PatriciaTrie::from(Arc::clone(&memdb), hasher, root.clone()).unwrap();
     let exists = trie.contains(key).unwrap();
     assert!(exists);
     let removed = trie.remove(key).unwrap();
     assert!(removed);
     let new_root = trie.commit().unwrap();
     println!("new root = {:?}", new_root);
 }
```

## Benchmark
#### Environment: Ubuntu 20.04 (WSL2),  CPU: i7-8550U CPU @ 1.80GHz, Memory: 32G.

```sh
cargo bench

Gnuplot not found, disabling plotting
insert one              time:   [605.00 ns 641.90 ns 677.84 ns]
Found 3 outliers among 100 measurements (3.00%)
  1 (1.00%) high mild
  2 (2.00%) high severe

insert 1k               time:   [301.21 us 302.78 us 304.48 us]
Found 2 outliers among 100 measurements (2.00%)
  1 (1.00%) high mild
  1 (1.00%) high severe

insert 10k              time:   [3.8509 ms 3.8748 ms 3.8994 ms]
Found 5 outliers among 100 measurements (5.00%)
  5 (5.00%) high mild

get based 10k           time:   [214.48 ns 218.37 ns 222.90 ns]
Found 17 outliers among 100 measurements (17.00%)
  1 (1.00%) low severe
  7 (7.00%) low mild
  7 (7.00%) high mild
  2 (2.00%) high severe

remove 1k               time:   [114.27 us 116.46 us 119.23 us]
Found 7 outliers among 100 measurements (7.00%)
  4 (4.00%) high mild
  3 (3.00%) high severe

remove 10k              time:   [1.1713 ms 1.1823 ms 1.1953 ms]
Found 12 outliers among 100 measurements (12.00%)
  3 (3.00%) high mild
  9 (9.00%) high severe
```

### Custom Hasher
cita_trie::Hasher;

### Custom storage
cita_trie::db::Database;

