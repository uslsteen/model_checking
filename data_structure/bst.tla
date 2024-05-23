-------------------------- MODULE bst --------------------------
EXTENDS Naturals, TLC, Integers
CONSTANTS NodeValuePlaceholder, NULL

NullNode == [value |-> NodeValuePlaceholder, left |-> NULL, right |-> NULL]
====

-------------------------- MODULE bst --------------------------
(***** VARIABLES *****)
(* --algorithm bst
variables
    nodes = {},
    root = NullNode,
    deleted = {};

define
    Node == [left: NullNode, right: NullNode, value: NodeValuePlaceholder]
end define;

procedure add_node(new_value)
begin
    impl_node:
        if root = NullNode then
            root := [left |-> NullNode, right |-> NullNode, value |-> new_value];
        else
            call insert_impl(root, new_value);
        end if;
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
    i:
       if node = root then
            root := NullNode;
       end if;
       nodes := nodes \ {node};
       deleted := deleted \union {node};
end procedure;

fair process Main = "Main"
begin
    main_loop:
        while (TRUE) do
            with action_type \in {"Add", "Delete"}, value \in 0..10 do
                if action_type = "Add" then
                    call add_node(value);
                else
                    with node \in nodes do
                        call delete_node(node);
                    end with;
                end if;
            end with;
        end while;
end process;

end algorithm;*)
====
