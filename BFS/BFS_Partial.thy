theory BFS_Partial
  imports
    BFS
begin

partial_function (in bfs) (tailrec) loop_partial where
  "loop_partial G src s =
   (if \<not> DONE s
    then let
          u = Q_head (queue s);
          q = Q_tail (queue s)
         in loop_partial G src (List.fold (traverse_edge src u) (G.adjacency G u) (s\<lparr>queue := q\<rparr>))
    else s)"

abbreviation (in bfs) bfs_partial :: "'n \<Rightarrow> 'a \<Rightarrow> 'm" where
  "bfs_partial G src \<equiv> parent (loop_partial G src (init src))"

lemma (in bfs_invar_tbd) loop_partial_eq_loop:
  assumes "bfs_invar'' s"
  shows "loop_partial G src s = loop G src s"
  using assms
proof (induct rule: bfs_induct[OF assms])
  case (1 G src s)
  show ?case
  proof (cases "DONE s")
    case True
    thus ?thesis
      using "1.prems"
      by (simp add: loop_partial.simps loop_psimps)
  next
    case False
    hence "loop_partial G src s = loop_partial G src (fold G src s)"
      by (metis loop_partial.simps)
    also have "... = loop G src (fold G src s)"
      using False "1.prems"
      by (intro bfs_invar_not_DONE'I bfs_invar_not_DONE.bfs_invar_fold "1.hyps")
    also have "... = loop G src s"
      using "1.prems" False
      by (simp add: loop_psimps)
    finally show ?thesis
      .
  qed
qed

lemma (in bfs_invar_tbd) bfs_partial_eq_bfs:
  shows "bfs_partial G src = bfs G src"
  using bfs_invar_init
  by (simp add: loop_partial_eq_loop)

theorem (in bfs_invar_tbd) bfs_partial_correct:
  shows "shortest_dpath_Map G src (bfs_partial G src)"
  using bfs_correct
  by (simp add: bfs_partial_eq_bfs)

corollary (in bfs) bfs_partial_correct:
  assumes "bfs_invar_tbd' G src"
  shows "shortest_dpath_Map G src (bfs_partial G src)"
  using assms
  by (intro bfs_invar_tbd.bfs_partial_correct)

end