theory Ford_Fulkerson_Partial
  imports
    "../BFS/Alternating_BFS_Tbd"
    Ford_Fulkerson
begin

partial_function (in ford_fulkerson) (tailrec) loop'_partial where
  "loop'_partial G U V s t M =
   (if done_1 U V M then M
    else if done_2 t (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s) then M
         else loop'_partial G U V s t (augment M (butlast (tl (rev_follow (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s) t)))))"

abbreviation (in ford_fulkerson) ford_fulkerson_partial :: "'n \<Rightarrow> 'm" where
  "ford_fulkerson_partial G \<equiv> loop'_partial G (fst (bipartition G)) (snd (bipartition G)) (fst (new_vertices G)) (snd (new_vertices G)) M_empty"

lemma (in ford_fulkerson_valid_input_2) loop'_partial_eq_loop':
  assumes "ford_fulkerson_invar'' M"
  shows "loop'_partial G U V s t M = loop' G U V s t M"
  using assms
proof (induct rule: ford_fulkerson_induct[OF assms])
  case (1 G U V s t M)
  show ?case
  proof (cases "done_1 U V M")
    case True
    thus ?thesis
      using "1.prems"
      by (simp add: loop'_partial.simps ford_fulkerson_invar.loop'_psimps)
  next
    case not_done_1: False
    hence alt_bfs_partial_eq_alt_bfs: "alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s = alt_bfs (G1 G (G2 U V s t M)) (G2 U V s t M) s"
      using "1.prems"
      by
        (auto intro:
          ford_fulkerson_invar_not_done_1I
          ford_fulkerson_invar_not_done_1.alt_bfs_invar_tbd
          alt_bfs_invar_tbd.alt_bfs_partial_eq_alt_bfs)
    show ?thesis
    proof (cases "done_2 t (m_tbd G U V s t M)")
      case True
      hence "done_2 t (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s)"
        by (metis alt_bfs_partial_eq_alt_bfs)
      thus ?thesis
        using "1.prems" not_done_1 True
        by (metis loop'_partial.simps ford_fulkerson_invar.loop'_psimps)
    next
      case False
      hence "\<not> done_2 t (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s)"
        by (metis alt_bfs_partial_eq_alt_bfs)
      hence
        "loop'_partial G U V s t M =
         loop'_partial G U V s t (augment M (butlast (tl (rev_follow (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s) t))))"
        using not_done_1
        by (metis loop'_partial.simps)
      also have "... = loop'_partial G U V s t (augment M (p_tbd G U V s t M))"
        unfolding alt_bfs_partial_eq_alt_bfs
        by metis
      also have "... = loop' G U V s t (augment M (p_tbd G U V s t M))"
        using not_done_1 False "1.prems"
        by (intro ford_fulkerson_invar_not_done_2I_2 ford_fulkerson_invar_not_done_2.ford_fulkerson_invar_augment "1.hyps")
      also have "... = loop' G U V s t M"
        using not_done_1 False "1.prems"
        by (simp add: ford_fulkerson_invar.loop'_psimps)
      finally show ?thesis
        .
    qed
  qed
qed

lemma (in ford_fulkerson_valid_input) ford_fulkerson_partial_eq_ford_fulkerson:
  shows "ford_fulkerson_partial G = ford_fulkerson G"
  using F.ford_fulkerson_invar_empty
  by (simp add: F.loop'_partial_eq_loop')

theorem (in ford_fulkerson_valid_input) ford_fulkerson_partial_correct:
  shows "maximum_matching (G.E G) (M_tbd (ford_fulkerson_partial G))"
  using ford_fulkerson_correct
  by (simp add: ford_fulkerson_partial_eq_ford_fulkerson)

corollary (in ford_fulkerson) ford_fulkerson_partial_correct:
  assumes "ford_fulkerson_valid_input' G"
  shows "maximum_matching (G.E G) (M_tbd (ford_fulkerson_partial G))"
  using assms
  by (intro ford_fulkerson_valid_input.ford_fulkerson_partial_correct)

end