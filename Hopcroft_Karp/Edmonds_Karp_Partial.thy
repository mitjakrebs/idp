theory Edmonds_Karp_Partial
  imports
    "../Alternating_BFS/Alternating_BFS_Partial"
    Edmonds_Karp
    "../Map/Parent_Relation_Partial"
begin

partial_function (in edmonds_karp) (tailrec) loop'_partial where
  "loop'_partial G U V s t M =
   (if done_1 U V M then M
    else if done_2 t (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s) then M
         else loop'_partial G U V s t (augment M (butlast (tl (Parent_Relation_Partial.rev_follow (P_lookup (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s)) t)))))"

definition (in edmonds_karp) edmonds_karp_partial where
  "edmonds_karp_partial G L R s t \<equiv> loop'_partial G L R s t M_empty"

(* definition (in edmonds_karp) edmonds_karp_partial :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'm" where
  "edmonds_karp_partial G L R \<equiv> loop'_partial G L R (fst (new_vertices G)) (snd (new_vertices G)) M_empty"

lemma (in edmonds_karp_valid_input_2) loop'_partial_eq_loop':
  assumes "edmonds_karp_invar'' M"
  shows "loop'_partial G U V s t M = loop' G U V s t M"
  using assms
proof (induct rule: edmonds_karp_induct[OF assms])
  case (1 G U V s t M)
  show ?case
  proof (cases "done_1 U V M")
    case True
    thus ?thesis
      using "1.prems"
      by (simp add: loop'_partial.simps edmonds_karp_invar.loop'_psimps)
  next
    case not_done_1: False
    hence alt_bfs_partial_eq_alt_bfs: "alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s = alt_bfs (G1 G (G2 U V s t M)) (G2 U V s t M) s"
      using "1.prems"
      by
        (auto intro:
          edmonds_karp_invar_not_done_1I
          edmonds_karp_invar_not_done_1.alt_bfs_invar_tbd
          alt_bfs_invar_tbd.alt_bfs_partial_eq_alt_bfs)
    show ?thesis
    proof (cases "done_2 t (m_tbd G U V s t M)")
      case True
      hence "done_2 t (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s)"
        by (metis alt_bfs_partial_eq_alt_bfs)
      thus ?thesis
        using "1.prems" not_done_1 True
        by (metis loop'_partial.simps edmonds_karp_invar.loop'_psimps)
    next
      case False
      hence "\<not> done_2 t (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s)"
        by (metis alt_bfs_partial_eq_alt_bfs)
      hence
        "loop'_partial G U V s t M =
         loop'_partial G U V s t (augment M (butlast (tl (Parent_Relation_Partial.rev_follow (P_lookup (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s)) t))))"
        using not_done_1
        by (metis loop'_partial.simps)
      also have "... = loop'_partial G U V s t (augment M (butlast (tl (rev_follow (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s) t))))"
      proof -
        have "edmonds_karp_invar_not_done_1' G U V s t M"
          using "1.prems" not_done_1
          by (intro edmonds_karp_invar_not_done_1I)
        hence "Parent_Relation.parent (P_lookup (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s))"
          unfolding alt_bfs_partial_eq_alt_bfs
          by (metis edmonds_karp_invar_not_done_1.parent)
        thus ?thesis
          by (simp add: rev_follow_eq_rev_follow)
      qed
      also have "... = loop'_partial G U V s t (augment M (p_tbd G U V s t M))"
        unfolding alt_bfs_partial_eq_alt_bfs
        by metis
      also have "... = loop' G U V s t (augment M (p_tbd G U V s t M))"
        using not_done_1 False "1.prems"
        by (intro edmonds_karp_invar_not_done_2I_2 edmonds_karp_invar_not_done_2.edmonds_karp_invar_augment "1.hyps")
      also have "... = loop' G U V s t M"
        using not_done_1 False "1.prems"
        by (simp add: edmonds_karp_invar.loop'_psimps)
      finally show ?thesis
        .
    qed
  qed
qed

lemma (in edmonds_karp_valid_input) edmonds_karp_partial_eq_edmonds_karp:
  shows "edmonds_karp_partial G = edmonds_karp G"
  using F.edmonds_karp_invar_empty
  by (simp add: edmonds_karp_partial_def F.loop'_partial_eq_loop')

theorem (in edmonds_karp_valid_input) edmonds_karp_partial_correct:
  shows "maximum_matching (G.E G) (M_tbd (edmonds_karp_partial G))"
  using edmonds_karp_correct
  by (simp add: edmonds_karp_partial_eq_edmonds_karp)

corollary (in edmonds_karp) edmonds_karp_partial_correct:
  assumes "edmonds_karp_valid_input' G"
  shows "maximum_matching (G.E G) (M_tbd (edmonds_karp_partial G))"
  using assms
  by (intro edmonds_karp_valid_input.edmonds_karp_partial_correct)
*)

(*
partial_function (in edmonds_karp) (tailrec) loop'_partial where
  "loop'_partial G U V s t M =
   (if done_1 U V M then M
    else if done_2 t (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s) then M
         else loop'_partial G U V s t (augment M (butlast (tl (rev_follow (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s) t)))))"

lemma (in edmonds_karp_valid_input_2) loop'_partial_eq_loop':
  assumes "edmonds_karp_invar'' M"
  shows "loop'_partial G U V s t M = loop' G U V s t M"
  using assms
proof (induct rule: edmonds_karp_induct[OF assms])
  case (1 G U V s t M)
  show ?case
  proof (cases "done_1 U V M")
    case True
    thus ?thesis
      using "1.prems"
      by (simp add: loop'_partial.simps edmonds_karp_invar.loop'_psimps)
  next
    case not_done_1: False
    hence alt_bfs_partial_eq_alt_bfs: "alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s = alt_bfs (G1 G (G2 U V s t M)) (G2 U V s t M) s"
      using "1.prems"
      by
        (auto intro:
          edmonds_karp_invar_not_done_1I
          edmonds_karp_invar_not_done_1.alt_bfs_invar_tbd
          alt_bfs_invar_tbd.alt_bfs_partial_eq_alt_bfs)
    show ?thesis
    proof (cases "done_2 t (m_tbd G U V s t M)")
      case True
      hence "done_2 t (alt_bfs_partial (G1 G (G2 U V s t M)) (G2 U V s t M) s)"
        by (metis alt_bfs_partial_eq_alt_bfs)
      thus ?thesis
        using "1.prems" not_done_1 True
        by (metis loop'_partial.simps edmonds_karp_invar.loop'_psimps)
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
        by (intro edmonds_karp_invar_not_done_2I_2 edmonds_karp_invar_not_done_2.edmonds_karp_invar_augment "1.hyps")
      also have "... = loop' G U V s t M"
        using not_done_1 False "1.prems"
        by (simp add: edmonds_karp_invar.loop'_psimps)
      finally show ?thesis
        .
    qed
  qed
qed

lemma (in edmonds_karp_valid_input) edmonds_karp_partial_eq_edmonds_karp:
  shows "edmonds_karp_partial G = edmonds_karp G"
  using F.edmonds_karp_invar_empty
  by (simp add: edmonds_karp_partial_def F.loop'_partial_eq_loop')

theorem (in edmonds_karp_valid_input) edmonds_karp_partial_correct:
  shows "maximum_matching (G.E G) (M_tbd (edmonds_karp_partial G))"
  using edmonds_karp_correct
  by (simp add: edmonds_karp_partial_eq_edmonds_karp)

corollary (in edmonds_karp) edmonds_karp_partial_correct:
  assumes "edmonds_karp_valid_input' G"
  shows "maximum_matching (G.E G) (M_tbd (edmonds_karp_partial G))"
  using assms
  by (intro edmonds_karp_valid_input.edmonds_karp_partial_correct)
*)

end