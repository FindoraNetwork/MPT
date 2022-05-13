// use std::cell::RefCell;
// use std::rc::Rc;

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

    // pub fn new_branch(childrens: [Option<Box<Node>>; 16], value: Option<Vec<u8>>) -> Self {
    //     Node::Branch(BranchNode {
    //         childrens,
    //         value,
    //     })
    // }

    pub fn new_extension(prefix: Nibbles, node: Node) -> Self {
        let node = Some(node.into_box());
        Node::Extension(ExtensionNode { prefix, node })
    }

    pub fn new_hash(hash: Vec<u8>) -> Self {
        Node::Hash(HashNode { hash })
    }

    pub fn into_box(self) -> Box<Self> {
        Box::new(self)
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
    //[Box<Node>;16] is very larger than others, this can reduce the size of Node.
    childrens: Vec<Option<Box<Node>>>,
    pub value: Option<Vec<u8>>,
}

impl BranchNode {
    ///Create a new empty boxed BranchNode.
    pub fn new() -> Self {
        let childrens = (0..16).map(|_| None).collect();
        BranchNode {
            childrens,
            value: None,
        }
    }

    pub fn insert(&mut self, i: usize, node: Option<Node>) {
        if i == 16 {
            match node {
                Some(Node::Leaf(leaf)) => {
                    self.value = Some(leaf.value);
                }
                _ => panic!("The node must be leaf node"),
            }
        } else {
            self.childrens[i] = node.map(Node::into_box);
        }
    }

    pub fn take_child(&mut self, index: usize) -> Option<Box<Node>> {
        self.childrens[index].take()
    }

    pub fn get_child(&self, index: usize) -> Option<&Node> {
        self.childrens[index].as_deref()
    }

    pub fn used_indexes(&self) -> Vec<usize> {
        let mut used_indexes = Vec::with_capacity(16);
        for (index, node) in self.childrens.iter().enumerate() {
            if node.is_some() {
                used_indexes.push(index);
            }
        }
        used_indexes
    }
}

#[derive(Debug)]
pub struct ExtensionNode {
    pub prefix: Nibbles,
    //If node is None, it must be deleted.
    pub node: Option<Box<Node>>,
}

// impl Drop for ExtensionNode {
//     fn drop(&mut self) {
//         if let Some(ptr) = self.node {
//             unsafe { Box::from_raw(ptr.as_ptr()) };
//         }
//     }
// }

#[derive(Debug)]
pub struct HashNode {
    pub hash: Vec<u8>,
}
