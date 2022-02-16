theory Adjacency_Impl
  imports
    Adjacency
    "HOL-Data_Structures.RBT_Map"
    "HOL-Data_Structures.RBT_Set2"
begin

interpretation G: adjacency where
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
  ..

end