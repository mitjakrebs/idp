theory BFS_Impl
  imports
    BFS_Partial
    "HOL-Data_Structures.RBT_Set2"
    "../Queue/Queue"
    "../Graph/Adjacency/Adjacency_Impl"
begin

text \<open>
We now show that our specification of BFS in locale @{locale bfs} can be implemented via red-black
trees.
\<close>

global_interpretation B: bfs where
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
  defines init = B.init
  and DONE = B.DONE
  and is_discovered = B.is_discovered
  and discover = B.discover
  and traverse_edge = B.traverse_edge
  and loop_partial = B.loop_partial
  and bfs_partial = B.bfs_partial
  ..

declare B.loop_partial.simps [code]
thm \<^marker>\<open>tag invisible\<close> B.loop_partial.simps
value \<^marker>\<open>tag invisible\<close> "bfs_partial (update (1::nat) (RBT_Set.insert (2::nat) empty) empty) 1"

end