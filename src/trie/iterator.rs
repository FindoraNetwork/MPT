use super::{node::Node, Nibbles, PatriciaTrie};
use crate::db::Database;
use crate::hasher::Hasher;
use std::ptr::NonNull;

#[derive(Copy, Clone, Debug)]
enum TraceStatus {
    Start,
    Doing,
    Child(u8),
    End,
}

#[derive(Clone, Debug)]
struct TraceNode {
    node: Option<NonNull<Node>>,
    status: TraceStatus,
}

impl TraceNode {
    fn advance(&mut self) {
        self.status = match &self.status {
            TraceStatus::Start => TraceStatus::Doing,
            TraceStatus::Doing => match self.node.map(|x| unsafe { x.as_ref() }) {
                Some(Node::Branch(_)) => TraceStatus::Child(0),
                _ => TraceStatus::End,
            },
            TraceStatus::Child(i) if *i < 15 => TraceStatus::Child(i + 1),
            _ => TraceStatus::End,
        }
    }

    fn new(node: Option<NonNull<Node>>) -> Self {
        TraceNode {
            node,
            status: TraceStatus::Start,
        }
    }
}

impl From<Option<&Node>> for TraceNode {
    fn from(node: Option<&Node>) -> TraceNode {
        TraceNode {
            node: node.map(|n| unsafe { NonNull::new_unchecked(n as *const Node as *mut Node) }),
            status: TraceStatus::Start,
        }
    }
}

pub struct TrieIterator<'a, D, H>
where
    D: Database,
    H: Hasher + Clone,
{
    trie: &'a PatriciaTrie<D, H>,
    nibble: Nibbles,
    nodes: Vec<TraceNode>,
    drops: Vec<NonNull<Node>>,
}

impl<'a, D, H> TrieIterator<'a, D, H>
where
    D: Database,
    H: Hasher + Clone,
{
    pub fn new(trie: &'a PatriciaTrie<D, H>) -> Self {
        let nodes = vec![trie.root.as_deref().into()];
        TrieIterator {
            trie,
            nibble: Nibbles::from_bytes(&[], false),
            nodes,
            drops: Vec::with_capacity(32),
        }
    }
}

impl<'a, D, H> Drop for TrieIterator<'a, D, H>
where
    D: Database,
    H: Hasher + Clone,
{
    fn drop(&mut self) {
        while let Some(ptr) = self.drops.pop() {
            unsafe { Box::from_raw(ptr.as_ptr()) };
        }
    }
}

impl<'a, D, H> Iterator for TrieIterator<'a, D, H>
where
    D: Database,
    H: Hasher + Clone,
{
    type Item = (Vec<u8>, Vec<u8>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let now = self.nodes.last().cloned();
            if let Some(now) = now {
                self.nodes.last_mut().unwrap().advance();

                match (now.status, now.node.map(|ptr| unsafe { ptr.as_ref() })) {
                    (TraceStatus::End, node) => {
                        match node {
                            Some(Node::Leaf(ref leaf)) => {
                                let cur_len = self.nibble.len();
                                self.nibble.truncate(cur_len - leaf.key.len());
                            }

                            Some(Node::Extension(ref ext)) => {
                                let cur_len = self.nibble.len();
                                self.nibble.truncate(cur_len - ext.prefix.len());
                            }

                            Some(Node::Branch(_)) => {
                                self.nibble.pop();
                            }
                            _ => {}
                        }
                        self.nodes.pop();
                    }

                    (TraceStatus::Doing, Some(Node::Extension(ext))) => {
                        self.nibble.extend(&ext.prefix);
                        self.nodes.push(ext.node.as_deref().into());
                    }

                    (TraceStatus::Doing, Some(Node::Leaf(leaf))) => {
                        self.nibble.extend(&leaf.key);
                        return Some((self.nibble.encode_raw().0, leaf.value.clone()));
                    }

                    (TraceStatus::Doing, Some(Node::Branch(branch))) => {
                        let value = branch.value.clone();
                        if let Some(data) = value {
                            return Some((self.nibble.encode_raw().0, data));
                        } else {
                            continue;
                        }
                    }

                    (TraceStatus::Doing, Some(Node::Hash(hash_node))) => {
                        if let Ok(n) = self.trie.recover_from_db(&hash_node.hash.clone()) {
                            self.nodes.pop();
                            if let Some(node) = n {
                                let node_ptr = unsafe {
                                    NonNull::new_unchecked(Box::into_raw(Box::new(node)))
                                };
                                self.drops.push(node_ptr);
                                self.nodes.push(TraceNode::new(Some(node_ptr)));
                            } else {
                                self.nodes.push(None.into());
                            }
                        } else {
                            //error!();
                            return None;
                        }
                    }

                    (TraceStatus::Child(i), Some(Node::Branch(branch))) => {
                        if i == 0 {
                            self.nibble.push(0);
                        } else {
                            self.nibble.pop();
                            self.nibble.push(i);
                        }
                        self.nodes
                            .push(unsafe { branch.get_child_uncheckd(i as usize).into() });
                    }

                    (_, None) => {
                        self.nodes.pop();
                    }
                    _ => {}
                }
            } else {
                return None;
            }
        }
    }
}
