theory Undirected_BFS
  imports
    "../Graph_Theory/Adaptors/Adjacency_Adaptor"
    BFS
    "../Graph_Theory/Adaptors/Shortest_Path_Adaptor"
begin

section \<open>Invariants\<close>

locale undirected_bfs_invar_tbd = bfs where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  fixes G :: 'n
  fixes src :: 'a
  assumes invar_G: "G.invar G"
  assumes symmetric: "v \<in> set (G.adjacency G u) \<longleftrightarrow> u \<in> set (G.adjacency G v)"
  assumes src_mem_V: "src \<in> G.V G"
begin

sublocale symmetric_adjacency
proof (standard, goal_cases)
  case 1
  show ?case using invar_G .
next
  case 2
  show ?case using symmetric .
qed

sublocale bfs_invar_tbd
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G
    .
next
  case 2
  show ?case
    using src_mem_V
    by (simp add: G.V_eq_dV)
qed

end

abbreviation (in bfs) undirected_bfs_invar_tbd' :: "'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "undirected_bfs_invar_tbd' G src \<equiv>
   undirected_bfs_invar_tbd
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update P_update Q_snoc G src"

section \<open>Correctness\<close>

abbreviation (in bfs) shortest_path_Map :: "'n \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "shortest_path_Map G src m \<equiv>
   \<forall>v. (discovered src m v \<longrightarrow> shortest_path (G.E G) (rev_follow m v) src v) \<and>
       (\<not> discovered src m v \<longrightarrow> \<not> reachable (G.E G) src v)"

lemma (in undirected_bfs_invar_tbd) undirected_bfs_correct:
  shows "shortest_dpath_Map G src (bfs G src)"
  using bfs_correct
  .

lemma (in undirected_bfs_invar_tbd) dist_eq_dist:
  shows "Shortest_Path.dist (G.E G) u v = dist G u v"
  using dist_eq_dist
  by (simp add: dE_eq_dEs)

lemma (in undirected_bfs_invar_tbd) shortest_path_iff_shortest_dpath:
  shows "shortest_path (G.E G) p u v \<longleftrightarrow> shortest_dpath G p u v"
  by (simp add: walk_betw_iff_dpath_bet dE_eq_dEs path_length_eq_dpath_length dist_eq_dist)

lemma (in undirected_bfs_invar_tbd) reachable_iff_reachable:
  shows "reachable (G.E G) u v \<longleftrightarrow> Noschinski_to_DDFS.reachable (G.dE G) u v"
  using reachable_iff_reachable
  by (simp add: dE_eq_dEs)

lemma (in bfs) undirected_bfs_correct:
  assumes "undirected_bfs_invar_tbd' G src"
  shows "shortest_path_Map G src (bfs G src)"
proof -
  have "shortest_dpath_Map G src (bfs G src)"
    using assms
    by (intro undirected_bfs_invar_tbd.undirected_bfs_correct)
  thus ?thesis
    using assms
    by (simp add: undirected_bfs_invar_tbd.shortest_path_iff_shortest_dpath undirected_bfs_invar_tbd.reachable_iff_reachable)
qed

end