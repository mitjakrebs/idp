theory Alternating_BFS_Impl
  imports
    Alternating_BFS_Partial
    "../BFS/BFS_Impl"
begin

text \<open>
We now show that our specification of the modified BFS in locale @{locale alt_bfs} can be
implemented via red-black trees.
\<close>

global_interpretation A: alt_bfs where
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
  Q_list = list
  defines P = A.P
  and P' = A.P'
  and adjacency = A.adjacency
  and alt_loop_partial = A.alt_loop_partial
  and alt_bfs_partial = A.alt_bfs_partial
  ..

declare A.alt_loop_partial.simps [code]
thm \<^marker>\<open>tag invisible\<close> A.alt_loop_partial.simps
value \<^marker>\<open>tag invisible\<close> "alt_bfs_partial (update (4::nat) (RBT_Set.insert (3::nat) empty) (update (3::nat) (RBT_Set.insert (4::nat) empty) empty)) (update (2::nat) (RBT_Set.insert (1::nat) empty) (update (1::nat) (RBT_Set.insert (2::nat) empty) empty)) 1"

end