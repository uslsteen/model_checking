-------------------------- MODULE bst --------------------------
EXTENDS Naturals, TLC, Integers
CONSTANTS NodeValuePlaceholder, NULL

NullNode == [value |-> NodeValuePlaceholder, left |-> NULL, right |-> NULL]
====

-------------------------- MODULE bst --------------------------
(***** VARIABLES *****)
(* --algorithm bst
variables
    root = NullNode,
    nodes = {},
    deleted = {},
    found = NullNode,
    exists = FALSE;
    mutex = FALSE;

define
    Node == [left: NullNode, right: NullNode, value: NodeValuePlaceholder]
end define;

macro Lock()
begin
  await !mutex;
  mutex := TRUE;
end macro;

macro Unlock()
begin
  mutex := FALSE;
end macro;

procedure insert_node(new_value)
begin
    body:
        Lock();
        if root = NullNode then
            root := [left |-> NullNode, right |-> NullNode, value |-> new_value];
        else
            call insert_impl(root, new_value);
        end if;
    end_body:
        Unlock();
end procedure;

procedure insert_impl(node, new_value)
variable new_node;
begin
    impl:
        if new_value < node.value then
            if node.left = NullNode then
                new_node := [left |-> NullNode, right |-> NullNode, value |-> new_value];
                node.left := new_node;
            else
                call insert_impl(node.left, new_value);
            end if;
        else
            if node.right = NullNode then
                new_node := [left |-> NullNode, right |-> NullNode, value |-> new_value];
                node.right := new_node;
            else
                call insert_impl(node.right, new_value);
            end if;
        end if;
end procedure;

procedure delete_node(node)
begin
    impl:
        Lock();
        if node = root then
            root := NullNode;
        end if;
        nodes := nodes \ {node};
        deleted := deleted \union {node};
    end_body:
        Unlock();
end procedure;

procedure find_node(node, target_value)
begin
    impl:
        if node = NullNode then
            found := NullNode;
        elsif node.value = target_value then
            found := node;
        elsif target_value < node.value then
            call find_node(node.left, target_value);
        else
            call find_node(node.right, target_value);
        end if;
end procedure;

procedure contains(target_value)
begin
    impl:
        call find_node(root, target_value);
    init:
        exists := (result /= NullNode);
end procedure;

procedure clear()
begin
    impl:
       Lock();
       root := NullNode;
       nodes := {};
       deleted := {};
    end_body:
        Unlock();
end procedure;

fair process Main = "Main"
begin
    main_loop:
        while (TRUE) do
            with action_type \in {"insert", "find", "contains", "delete"}, value \in 0..10 do
                if action_type = "insert" then
                    call insert_node(value);
                elsif action_type = "find" then
                    call find_node(root, value);
                elsif action_type = "contains" then
                    call contains(value);
                elsif action_type = "clear" then
                    call clear();
                elsif action_type = "delete" then
                    with node \in nodes do
                        call delete_node(node);
                    end with;
                end if;
            end with;
        end while;
end process;

end algorithm;*)

(***** Invariant Definitions *****)
IsParent(node, child) ==
    (node.left = child) \/ (node.right = child)

    \* Each node except root has one parent
AllNodesHaveParents == (\A n \in nodes : n /= root => \E p \in nodes : IsParent(p, n))
    \* Left child values are less
LeftChildValsLessThanParent == (\A n \in nodes : (n.left /= NullNode => n.left.value < n.value))
    \* Right child values are greater
RightChildValsGreaterThanParent == (\A n \in nodes : (n.right /= NullNode => n.right.value > n.value))
    \* Acyclic
Acyclic == \A n \in nodes : ~ (n \in n.^(left \union right))
    \* Non-crossing sets, nodes and deleted aren't interesecting
NoIntesectNodeAndDeleted == nodes \cap deleted = {}
    \* Deleted nodes have no children
DeletedHaveNoChildred == \A n \in deleted : (n.left = NullNode) /\ (n.right = NullNode)

BSTInvariants == AllNodesHaveParents /\
                 LeftChildValsLessThanParent /\
                 RightChildValsGreaterThanParent  /\
                 Acyclic /\
                 NoIntesectNodeAndDeleted /\
                 DeletedHaveNoChildred

====

\* == Properties ==
ASSUME Init =>
         ([] BSTInvariants)

\* == Temporal Properties ==
SPECIFICATION == ([] BSTInvariants)

====
