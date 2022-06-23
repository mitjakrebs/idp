theory Alternating_BFS_Partial
  imports
    Alternating_BFS
begin

partial_function (in alt_bfs) (tailrec) alt_loop_partial where
  "alt_loop_partial G1 G2 src s =
   (if \<not> DONE s
    then let
          u = Q_head (queue s);
          q = Q_tail (queue s)
         in alt_loop_partial G1 G2 src (List.fold (traverse_edge src u) (adjacency G1 G2 s u) (s\<lparr>queue := q\<rparr>))
    else s)"

definition (in alt_bfs) alt_bfs_partial :: "'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> 'm" where
  "alt_bfs_partial G1 G2 src \<equiv> parent (alt_loop_partial G1 G2 src (init src))"

lemma (in alt_bfs_valid_input) alt_loop_partial_eq_alt_loop:
  assumes "alt_bfs_invar'' s"
  shows "alt_loop_partial G1 G2 src s = alt_loop G1 G2 src s"
  using assms
proof (induct rule: alt_bfs_induct[OF assms])
  case (1 G1 G2 src s)
  show ?case
  proof (cases "DONE s")
    case True
    thus ?thesis
      using "1.prems"
      by (simp add: alt_loop_partial.simps alt_loop_psimps)
  next
    case False
    hence "alt_loop_partial G1 G2 src s = alt_loop_partial G1 G2 src (alt_fold G1 G2 src s)"
      by (metis alt_loop_partial.simps)
    also have "... = alt_loop G1 G2 src (alt_fold G1 G2 src s)"
      using False "1.prems"
      by (intro alt_bfs_invar_not_DONE'I alt_bfs_invar_not_DONE.alt_bfs_invar_alt_fold "1.hyps")
    also have "... = alt_loop G1 G2 src s"
      using "1.prems" False
      by (simp add: alt_loop_psimps)
    finally show ?thesis
      .
  qed
qed

lemma (in alt_bfs_valid_input) alt_bfs_partial_eq_alt_bfs:
  shows "alt_bfs_partial G1 G2 src = alt_bfs G1 G2 src"
  using alt_bfs_invar_init
  by (simp add: alt_bfs_partial_def alt_bfs_def alt_loop_partial_eq_alt_loop)

theorem (in alt_bfs_valid_input) alt_bfs_partial_correct:
  shows "is_shortest_alt_path_Map P'' G src (alt_bfs_partial G1 G2 src)"
  using alt_bfs_correct
  by (simp add: alt_bfs_partial_eq_alt_bfs)

corollary (in alt_bfs) alt_bfs_partial_correct:
  assumes "alt_bfs_valid_input' G1 G2 src"
  shows "is_shortest_alt_path_Map (\<lambda>e. e \<in> G.E G2) (G.union G1 G2) src (alt_bfs_partial G1 G2 src)"
  using assms
  by (intro alt_bfs_valid_input.alt_bfs_partial_correct)

end