theory BFS_Impl
  imports
    BFS_Partial
    "HOL-Data_Structures.RBT_Set2"
    "../Queue"
    "../Graph_Theory/Adjacency_Impl"
begin

global_interpretation B: bfs where
  Map_empty = empty and
  Map_delete = RBT_Map.delete and
  Map_lookup = lookup and
  Map_inorder = inorder and
  Map_inv = rbt and
  Set_empty = empty and
  Set_insert = insert and
  Set_delete = delete and
  Set_isin = isin and
  Set_inorder = inorder and
  Set_inv = rbt and
  Map_update = update and
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
  Q_invar = invar and
  Q_list = list
  ..

(* value "B.bfs_partial (update (1::nat) (insert (2::nat) empty) empty) 1" *)

end