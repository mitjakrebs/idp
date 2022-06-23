theory Undirected_BFS
  imports
    "../Graph/Adjacency/Adjacency_Adaptor"
    BFS
    "../Graph/Adaptors/Shortest_Path_Adaptor"
begin

section \<open>Invariants\<close>

locale undirected_bfs_valid_input = bfs where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  fixes G :: 'n
  fixes src :: 'a
  assumes invar_G: "G.invar G"
  assumes symmetric: "v \<in> set (G.adjacency_list G u) \<longleftrightarrow> u \<in> set (G.adjacency_list G v)"
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

sublocale bfs_valid_input
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

abbreviation (in bfs) undirected_bfs_valid_input' :: "'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "undirected_bfs_valid_input' G src \<equiv>
   undirected_bfs_valid_input
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update P_update Q_snoc G src"

section \<open>Correctness\<close>

abbreviation (in bfs) is_shortest_path_Map :: "'n \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "is_shortest_path_Map G src m \<equiv>
   \<forall>v. (is_discovered src m v \<longrightarrow> is_shortest_path (G.E G) (rev_follow m v) src v) \<and>
       (\<not> is_discovered src m v \<longrightarrow> \<not> reachable (G.E G) src v)"

lemma (in undirected_bfs_valid_input) dist_eq_dist:
  shows "Shortest_Path.dist (G.E G) u v = dist G u v"
  using dist_eq_dist
  by (simp add: dE_eq_dEs)

lemma (in undirected_bfs_valid_input) is_shortest_path_iff_is_shortest_dpath:
  shows "is_shortest_path (G.E G) p u v \<longleftrightarrow> is_shortest_dpath G p u v"
  by (simp add: walk_betw_iff_dpath_bet dE_eq_dEs path_length_eq_dpath_length dist_eq_dist)

lemma (in undirected_bfs_valid_input) reachable_iff_reachable:
  shows "reachable (G.E G) u v \<longleftrightarrow> Noschinski_to_DDFS.reachable (G.dE G) u v"
  using reachable_iff_reachable
  by (simp add: dE_eq_dEs)

lemma (in undirected_bfs_valid_input) undirected_bfs_correct:
  shows "is_shortest_path_Map G src (bfs G src)"
proof -
  have "is_shortest_dpath_Map G src (bfs G src)"
    using bfs_correct
    .
  thus ?thesis
    by (simp add: is_shortest_path_iff_is_shortest_dpath reachable_iff_reachable)
qed

lemma (in bfs) undirected_bfs_correct:
  assumes "undirected_bfs_valid_input' G src"
  shows "is_shortest_path_Map G src (bfs G src)"
  using assms
  by (intro undirected_bfs_valid_input.undirected_bfs_correct)

end