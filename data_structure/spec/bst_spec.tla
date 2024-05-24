----------------------------- MODULE bst_spec -----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    NodeIdTy,
    DataTy

VARIABLES nodes, parent, left, right, deleted, mutex

\* NullNode == [value |-> NodeValuePlaceholder, left |-> NULL, right |-> NULL]
FREE == FALSE
Node == [left: NodeIdTy, right: NodeIdTy, value: DataTy]
NULL == 0

Init ==
    /\ nodes = {}
    /\ parent = [n \in NodeIdTy |-> NULL]
    /\ left = [n \in NodeIdTy |-> NULL]
    /\ right = [n \in NodeIdTy |-> NULL]
    /\ deleted = {}
    /\ mutex = FREE

NodeInvariant ==
    /\ parent \in [NodeIdTy -> NodeIdTy]
    /\ left \in [NodeIdTy -> NodeIdTy]
    /\ right \in [NodeIdTy -> NodeIdTy]
    /\ deleted \subseteq nodes
    /\ \A n \in deleted : left[n] = NULL /\ right[n] = NULL

LockMutex ==
    /\ mutex = FREE
    /\ mutex' = 1

UnlockMutex ==
    /\ mutex # FREE
    /\ mutex' = FREE

Insert(node, value) ==
    /\ node \notin nodes
    /\ nodes' = nodes \cup {node}
    /\ parent' = [parent EXCEPT ![node] = value]
    /\ left' = left
    /\ right' = right
    /\ deleted' = deleted
    /\ UNCHANGED mutex

Delete(node) ==
    /\ node \in nodes
    /\ left' = [left EXCEPT ![node] = NULL]
    /\ right' = [right EXCEPT ![node] = NULL]
    /\ parent' = [p \in NodeIdTy |-> IF parent[p] = node THEN NULL ELSE parent[p]]
    /\ deleted' = deleted \cup {node}
    /\ nodes' = nodes
    /\ UNCHANGED mutex

AtomicInsert(node, value) ==
    /\ LockMutex
    /\ Insert(node, value)
    /\ UnlockMutex

AtomicDelete(node) ==
    /\ LockMutex
    /\ Delete(node)
    /\ UnlockMutex

Search(node) ==
    node \in nodes

isAcyclic(node) ==
    LET Path(n) == IF parent[n] = NULL THEN {n} ELSE {n \cup {parent[n]}}
    IN \A n \in nodes : parent[node] \notin Path(n)

AllNodesHaveParent == \A node \in nodes : (node # 0 => parent[node] \in nodes)
LeftChildValsLessThanParent == \A node \in nodes : (left[node] # NULL => left[node] < node)
RightChildValsGreaterThanParent == \A node \in nodes : (right[node] # NULL => right[node] > node)
Acyclic == \A n \in nodes : isAcyclic(n)
NoIntesectNodeAndDeleted == \A node \in nodes : (left[node] # right[node] \/ right[node] # node)
DeletedHaveNoChildred == \A n \in nodes : n \in deleted => left[n] = NULL /\ right[n] = NULL

BSTInvariants ==
    /\ AllNodesHaveParent
    /\ LeftChildValsLessThanParent
    /\ RightChildValsGreaterThanParent
    /\ Acyclic
    /\ NoIntesectNodeAndDeleted
    /\ DeletedHaveNoChildred

Next ==
    \/ \E node \in NodeIdTy: \E val \in NodeIdTy: node \notin nodes /\ AtomicInsert(node, val)
    \/ \E node \in nodes: AtomicDelete(node)

Spec ==
    Init /\ [][Next]_<<nodes, parent, left, right, deleted, mutex>> /\ NodeInvariant /\ BSTInvariants

======================================================================
