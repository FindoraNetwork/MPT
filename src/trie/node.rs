// use std::cell::RefCell;
// use std::rc::Rc;

use core::ptr::NonNull;

use crate::nibbles::Nibbles;

#[derive(Debug)]
pub enum Node {
    Leaf(LeafNode),
    Extension(ExtensionNode),
    Branch(BranchNode),
    Hash(HashNode),
}

impl Node {
    pub fn new_leaf(key: Nibbles, value: Vec<u8>) -> Self {
        Node::Leaf(LeafNode { key, value })
    }

    pub fn new_branch(children: [Option<NonNull<Node>>; 16], value: Option<Vec<u8>>) -> Self {
        Node::Branch(BranchNode { children, value })
    }

    pub fn new_extension(prefix: Nibbles, node: Node) -> Self {
        let node = Some(node.into_raw());
        Node::Extension(ExtensionNode { prefix, node })
    }

    pub fn new_hash(hash: Vec<u8>) -> Self {
        Node::Hash(HashNode { hash })
    }

    pub fn into_raw(self) -> NonNull<Self> {
        unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(self))) }
    }

    pub unsafe fn from_raw(ptr: *mut Self) -> Self {
        *Box::from_raw(ptr)
    }
}

#[derive(Debug)]
pub struct LeafNode {
    pub key: Nibbles,
    pub value: Vec<u8>,
}

#[derive(Debug)]
pub struct BranchNode {
    pub children: [Option<NonNull<Node>>; 16],
    pub value: Option<Vec<u8>>,
}

impl BranchNode {
    pub fn new_empty() -> Self {
        BranchNode {
            children: [None; 16],
            value: None,
        }
    }

    pub fn insert(&mut self, i: usize, node: Node) {
        if i == 16 {
            match node {
                Node::Leaf(leaf) => {
                    self.value = Some(leaf.value);
                }
                _ => panic!("The node must be leaf node"),
            }
        } else {
            self.children[i] = Some(node.into_raw());
        }
    }
}

impl Drop for BranchNode {
    fn drop(&mut self) {
        for c in self.children {
            if let Some(ptr) = c {
                unsafe { Box::from_raw(ptr.as_ptr()) };
            }
        }
    }
}

#[derive(Debug)]
pub struct ExtensionNode {
    pub prefix: Nibbles,
    //If node is None, it must be deleted.
    pub node: Option<NonNull<Node>>,
}

impl Drop for ExtensionNode {
    fn drop(&mut self) {
        if let Some(ptr) = self.node {
            unsafe { Box::from_raw(ptr.as_ptr()) };
        }
    }
}

#[derive(Debug)]
pub struct HashNode {
    pub hash: Vec<u8>,
}
