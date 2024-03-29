theory Edmonds_Karp_Impl
  imports
    "../Alternating_BFS/Alternating_BFS_Impl"
    Edmonds_Karp_Partial
begin

text \<open>
We now show that our specification of the Edmonds-Karp algorithm in locale @{locale edmonds_karp}
can be implemented via red-black trees.
\<close>

global_interpretation E: edmonds_karp where
  Map_empty = empty and
  Map_update = update and
  Map_delete = RBT_Map.delete and
  Map_lookup = lookup and
  Map_inorder = inorder and
  Map_inv = rbt and
  Set_empty = empty and
  Set_insert = RBT_Set.insert and
  Set_delete = delete and
  Set_isin = isin and
  Set_inorder = inorder and
  Set_inv = rbt and
  P_empty = empty and
  P_update = update and
  P_delete = RBT_Map.delete and
  P_lookup = lookup and
  P_invar = M.invar and
  Q_empty = Queue.empty and
  Q_is_empty = is_empty and
  Q_snoc = snoc and
  Q_head = head and
  Q_tail = tail and
  Q_invar = Queue.invar and
  Q_list = list and
  M_empty = empty and
  M_update = update and
  M_delete = RBT_Map.delete and
  M_lookup = lookup and
  M_inorder = inorder and
  M_inv = rbt
  defines is_free_vertex = E.is_free_vertex
  and free_vertices = E.free_vertices
  and G2_1 = E.G2_1
  and G2_2 = E.G2_2
  and G2_3 = E.G2_3
  and G2 = E.G2
  and G1 = E.G1
  and done_1 = E.done_1
  and done_2 = E.done_2
  and augment = E.augment
  and loop'_partial = E.loop'_partial
  and edmonds_karp_partial = E.edmonds_karp_partial
  ..

declare rev_follow_partial.simps [code]
declare E.loop'_partial.simps [code]
thm \<^marker>\<open>tag invisible\<close> E.loop'_partial.simps
value \<^marker>\<open>tag invisible\<close> "alt_bfs_partial (update (4::nat) (RBT_Set.insert (3::nat) empty) (update (3::nat) (RBT_Set.insert (4::nat) empty) empty)) (update (2::nat) (RBT_Set.insert (1::nat) empty) (update (1::nat) (RBT_Set.insert (2::nat) empty) empty)) 1"
value \<^marker>\<open>tag invisible\<close> "loop'_partial (update (2::nat) (RBT_Set.insert (1::nat) empty) (update (1::nat) (RBT_Set.insert (2::nat) empty) empty)) (RBT_Set.insert (1::nat) empty) (RBT_Set.insert (2::nat) empty) 1 2 empty"
value \<^marker>\<open>tag invisible\<close> "edmonds_karp_partial (update (2::nat) (RBT_Set.insert (1::nat) empty) (update (1::nat) (RBT_Set.insert (2::nat) empty) empty))"

end