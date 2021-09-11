theory BFS_Impl
  imports
    BFS
    "HOL-Data_Structures.RBT_Set2"
    Tbd_Graph_Tbd
begin

locale agublagu =
  fixes out_neighborhood :: "'a::linorder \<Rightarrow> 'a rbt"
  assumes invar_out_neighborhood: "v \<in> dVs G \<Longrightarrow> rbt (out_neighborhood v) \<and> sorted (inorder (out_neighborhood v))"
  assumes isin_out_neighborhood_iff_edge: "rbt (out_neighborhood u) \<and> sorted (inorder (out_neighborhood u)) \<Longrightarrow> isin (out_neighborhood u) v \<longleftrightarrow> (u, v) \<in> G"
begin

interpretation finite_dgraph_tbd empty delete isin inorder rbt G insert out_neighborhood
  using finite_dgraph_axioms RBT_Set2.S.Set_by_Ordered_axioms
  using invar_out_neighborhood isin_out_neighborhood_iff_edge
  by (intro finite_dgraph_tbd.intro finite_dgraph_tbd_axioms.intro) (simp_all add: RBT_Set2.S.invar_def)

end

end