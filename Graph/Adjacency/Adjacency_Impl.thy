subsection \<open>Low level\<close>

theory Adjacency_Impl
  imports
    Adjacency
    Directed_Adjacency
    Undirected_Adjacency
    "HOL-Data_Structures.RBT_Map"
    "HOL-Data_Structures.RBT_Set2"
begin

text \<open>
On the medium level of abstraction, we specified a graph via the interface @{locale adjacency}. We
now show that, on the low level, this interface can be implemented via red-black trees.
\<close>

global_interpretation G: adjacency where
  Map_empty = empty and
  Map_update = update and
  Map_delete = RBT_Map.delete and
  Map_lookup = lookup and
  Map_inorder = inorder and
  Map_inv = rbt and
  Set_empty = empty and
  Set_insert = insert and
  Set_delete = delete and
  Set_isin = isin and
  Set_inorder = inorder and
  Set_inv = rbt
  defines invar = G.invar
  and adjacency_list = G.adjacency_list
  and insert = G.insert
  and insert' = G.insert'
  and insert_2 = G.insert_2
  and delete_2 = G.delete_2
  and union = G.union
  and difference = G.difference
  and dE = G.dE
  and dV = G.dV
  and E = G.E
  and V = G.V
  and insert_edge = G.insert_edge
  ..

value \<^marker>\<open>tag invisible\<close> "adjacency_list (update (1::nat) (RBT_Set.insert (2::nat) empty) empty) 1"
value \<^marker>\<open>tag invisible\<close> "difference (update (1::nat) (RBT_Set.insert (2::nat) empty) empty) (update (3::nat) (RBT_Set.insert (2::nat) empty) empty)"

end