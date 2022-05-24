use crate::nibbles::Nibbles;

#[derive(Debug, Clone)]
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
}

/// Leaf Node, a leaf node means there must be a non-empty value,
/// insert a empty value means remove by the key.
#[derive(Debug, Clone)]
pub struct LeafNode {
    pub key: Nibbles,
    pub value: Vec<u8>,
}

/// A Branch node is a 16-way lookup node, it also can store a value if a "leaf" reachs here.
/// It looks like:
///    BranchNode[0,1,2,3,4,5,6,7,8,9,a,b,c,d,e,f] -> Option<V>
///                 /       /           \        \
///              1 /     5 /             \ b      \f
///               /       /               \        \
///            Child   Child             Child     Child
///
#[derive(Debug, Clone)]
pub struct BranchNode {
    //[Box<Option<Node>>;16] is very larger than others, this can reduce the size of Node,
    // Box<[Option<Node>;16]> looks unnecessary because it works like Vec<Option<Node>> (both on heap).
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

    pub unsafe fn get_child_uncheckd(&self, index: usize) -> Option<&Node> {
        self.childrens.get_unchecked(index).as_deref()
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

/// A ExtensionNode exist mean there will be branch after this.
/// There is some rules for Extension node.
/// 1. If `node` is None, it would be deleted.
/// 2. Extension(prefix1) -> Extension(prefix2) would be reduced to Extension(prefix1 + prefix2).
/// 3. Extension(prefix1) -> Leaf(prefix2) would be reduced to Leaf(prefix1 + prefix2).
#[derive(Debug, Clone)]
pub struct ExtensionNode {
    pub prefix: Nibbles,
    //If node is None, it must be deleted.
    pub node: Option<Box<Node>>,
}

#[derive(Debug, Clone)]
pub struct HashNode {
    pub hash: Vec<u8>,
}
