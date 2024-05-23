module bst

sig Node {
    value: Int,
    left: lone Node,
    right: lone Node
}

one sig BST {
    var root: lone Node,
    var elems: set Node,
    var deleted: set Node
}

// BST properties
fact invariants {
    // Each node except root has one parent
    all n: BST.elems - BST.root | one n.~(left + right)
    // Left child values are less
    all n: BST.elems | no n.left or n.left.value < n.value
    // Right child values are greater
    all n: BST.elems | no n.right or n.right.value > n.value
    // No cycles
    no n: BST.elems | n in n.^(left + right)
    // Non-crossing sets
    all n: BST.elems | n not in BST.deleted
    // Deleted nodes have no children
    all n: BST.deleted | no n.left and no n.right
}

pred add_node[newNode: Node, newVal: Int, parent: Node] {
    newNode in BST.deleted
    parent in BST.elems
    no n: BST.elems | n.value = newVal
    
    //! NOTE: Set new node's value and update state
    newNode.value' = newVal
    BST.elems' = BST.elems + newNode
    BST.deleted' = BST.deleted - newNode
    BST.root' = BST.root
    
    //! NOTE: retie parent-child
    newNode.left' = none
    newNode.right' = none
    (newVal < parent.value and no parent.left) => parent.left' = newNode
    (newVal > parent.value and no parent.right) => parent.right' = newNode
}

pred delete_node[elem: Node] {
    elem in BST.elems and elem not in BST.deleted

    //! NOTE: Update state to mark node as deleted
    BST.deleted' = BST.deleted + elem
    BST.elems' = BST.elems - elem
    
    //! NOTE: Adjust root if It will be deleted
    (BST.root = elem) => BST.root' = none

    //! NOTE: Retie left and right children if necessary
    all parent: BST.elems | {
        (parent.left = elem) => parent.left' = none else parent.left' = parent.left
        (parent.right = elem) => parent.right' = none else parent.right' = parent.right
    }
}

pred BSTIsValid {
    lone root
    no root or root in elems
    all n: BST.elems | n not in BST.deleted
    BST.elems + BST.deleted = Node
}

fact "init" {
    #Node > 4
    #BST.elems > 3
    BSTIsValid
}

pred transitions {
    (some n: BST.elems | delete_node[n]) or
    (some newNode: BST.deleted, parent: BST.elems, v: Int | add_node[newNode, v, parent]) or
    noChange
}

pred noChange {
    all n: BST.elems | n.left' = n.left and n.right' = n.right
    elems' = elems
    deleted' = deleted
    root' = root
}

run {
    always transitions
} for 5 but 1..2 steps