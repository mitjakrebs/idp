theory Edmonds_Karp_Tbd
  imports
    "../../matching/Blossom_Algo"
    Edmonds_Karp
begin

text \<open>This theory connects @{term ford_fulkerson.loop'} to @{term find_max_match.find_max_matching}\<close>

section \<open>Convenience lemmas\<close>

lemma edges_of_path_conv:
  shows "Graph.edges_of_path l = edges_of_path l"
  by (induct l rule: edges_of_path.induct) simp+

lemma symmetric_diff_conv:
  shows "Berge2.symmetric_diff = symmetric_diff"
  unfolding Berge2.symmetric_diff_def symmetric_diff_def
  ..

lemma matching_conv:
  shows "Berge2.matching = matching"
  unfolding Berge2.matching_def matching_def
  ..

section \<open>Definitions\<close>

definition (in ford_fulkerson) f' :: "'a \<times> 'a \<Rightarrow> 'm \<Rightarrow> 'm" where
  "f' p \<equiv> M_update (fst p) (snd p)"

definition (in ford_fulkerson) M_tbd_inv :: "'a set set \<Rightarrow> 'm" where
  "M_tbd_inv M \<equiv> Finite_Set.fold f' M_empty (graph.dEs M)"

definition (in ford_fulkerson) search_aug_path :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'a list option" where
  "search_aug_path G U V s t M \<equiv>
   if done_1 U V M then None
   else if done_2 t (m_tbd G U V s t M) then None
        else Some (p_tbd G U V s t M)"

abbreviation (in ford_fulkerson_valid_input_2) search_aug_path' :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a list option" where
  "search_aug_path' _ M \<equiv> search_aug_path G U V s t (M_tbd_inv M)"

section \<open>Basic lemmas\<close>

context ford_fulkerson_valid_input_2
begin
sublocale find_max_match search_aug_path' "G.E G"
proof (standard, goal_cases)
  case (1 M)
  then show ?case sorry
next
  case (2 M p)
  then show ?case sorry
next
  case 3
  then show ?case sorry
next
  case 4
  then show ?case sorry
qed
end

find_theorems "Finite_Set.fold _ _ (set _) = fold _ _ _"

lemma (in ford_fulkerson) lookup_conv:
  shows "M_lookup (M_tbd_inv (M_tbd M)) = M_lookup M"
  sorry

lemma (in ford_fulkerson_invar) done_1_conv:
  shows "done_1 U V (M_tbd_inv (M_tbd M)) = done_1 U V M"
  sorry

lemma (in ford_fulkerson_invar) done_2_conv:
  shows "done_2 t (m_tbd G U V s t (M_tbd_inv (M_tbd M))) = done_2 t (m_tbd G U V s t M)"
  sorry

lemma (in ford_fulkerson_invar) p_tbd_conv:
  shows "p_tbd G U V s t (M_tbd_inv (M_tbd M)) = p_tbd G U V s t M"
  sorry

lemma (in ford_fulkerson_invar) find_max_matching_psimps:
  shows
    "find_max_matching (M_tbd M) =
     (if done_1 U V M then (M_tbd M)
      else if done_2 t (m_tbd G U V s t M) then (M_tbd M)
           else find_max_matching (M_tbd (augment M (p_tbd G U V s t M))))"
proof -
  have find_max_matching_psimps:
    "find_max_matching (M_tbd M) =
     (case search_aug_path' (G.E G) (M_tbd M) of
        None \<Rightarrow> M_tbd M |
        Some p \<Rightarrow> find_max_matching (symmetric_diff (M_tbd M) (P_tbd p)))"
  proof -
    have
      "find_max_matching (M_tbd M) = 
       (if \<exists>p. search_aug_path' (G.E G) (M_tbd M) = Some p
        then find_max_matching (Berge2.symmetric_diff (M_tbd M) (set (Graph.edges_of_path (the (search_aug_path' (G.E G) (M_tbd M))))))
        else M_tbd M)"
    using graph_matching_M_tbd finite_M_tbd
    by (intro find_max_matching_dom find_max_matching.psimps) (simp_all add: matching_conv)
    hence
      "find_max_matching (M_tbd M) = 
       (if \<exists>p. search_aug_path' (G.E G) (M_tbd M) = Some p
        then find_max_matching (symmetric_diff (M_tbd M) (set (edges_of_path (the (search_aug_path' (G.E G) (M_tbd M))))))
        else M_tbd M)"
      by (simp add: symmetric_diff_conv edges_of_path_conv)
    thus ?thesis
      by force
  qed
  show ?thesis
  proof (cases "done_1 U V M")
    case True
    hence "done_1 U V (M_tbd_inv (M_tbd M))"
      by (simp add: done_1_conv)
    hence "search_aug_path' _ (M_tbd M) = None"
      by (simp add: search_aug_path_def)
    thus ?thesis
      using True
      by (simp add: find_max_matching_psimps)
  next
    case not_done_1: False
    show ?thesis
    proof (cases "done_2 t (m_tbd G U V s t M)")
      case True
      hence "done_2 t (m_tbd G U V s t (M_tbd_inv (M_tbd M)))"
        by (simp add: done_2_conv)
      hence "search_aug_path' _ (M_tbd M) = None"
        by (simp add: search_aug_path_def)
      thus ?thesis
        using True
        by (simp add: find_max_matching_psimps)
    next
      case False
      hence ford_fulkerson_invar_not_done_2: "ford_fulkerson_invar_not_done_2'' M"
        using ford_fulkerson_invar_axioms not_done_1 False
        by (intro ford_fulkerson_invar_not_done_2I_2)

      have
        "\<not> done_1 U V (M_tbd_inv (M_tbd M))"
        "\<not> done_2 t (m_tbd G U V s t (M_tbd_inv (M_tbd M)))"
        using not_done_1 False
        by (simp_all add: done_1_conv done_2_conv)
      hence "search_aug_path' _ (M_tbd M) = Some (p_tbd G U V s t (M_tbd_inv (M_tbd M)))"
        by (simp add: search_aug_path_def)
      hence
        "find_max_matching (M_tbd M) =
         find_max_matching (symmetric_diff (M_tbd M) (P_tbd (p_tbd G U V s t (M_tbd_inv (M_tbd M)))))"
        using not_done_1 False
        by (simp add: find_max_matching_psimps)
      thus ?thesis
        unfolding p_tbd_conv
        using not_done_1 False
        using invar_M symmetric_M
        using ford_fulkerson_invar_not_done_2.augmenting_path_p_tbd[OF ford_fulkerson_invar_not_done_2]
        using ford_fulkerson_invar_not_done_2.distinct_p_tbd[OF ford_fulkerson_invar_not_done_2]
        using ford_fulkerson_invar_not_done_2.even_length_p_tbd[OF ford_fulkerson_invar_not_done_2]
        by (simp add: M_tbd_augment_cong)
    qed
  qed
qed

lemma (in ford_fulkerson_invar_done_1) find_max_matching_psimps:
  shows "find_max_matching (M_tbd M) = M_tbd M"
  using done_1
  by (simp add: find_max_matching_psimps)

lemma (in ford_fulkerson_invar_done_2) find_max_matching_psimps:
  shows "find_max_matching (M_tbd M) = M_tbd M"
  using not_done_1 done_2
  by (simp add: find_max_matching_psimps)

lemma (in ford_fulkerson_invar_not_done_2) find_max_matching_psimps:
  shows "find_max_matching (M_tbd M) = find_max_matching (M_tbd (augment M (p_tbd G U V s t M)))"
  using not_done_1 not_done_2
  by (simp add: find_max_matching_psimps)

lemma (in ford_fulkerson_valid_input_2) loop'_find_max_matching_conv:
  assumes "ford_fulkerson_invar'' M"
  shows
    "M_tbd (loop' G U V s t M) =
     find_max_match.find_max_matching search_aug_path' (G.E G) (M_tbd M)"
  using assms
proof (induct rule: ford_fulkerson_induct[OF assms])
  case (1 G U V s t M)
  show ?case
  proof (cases "done_1 U V M")
    case True
    with "1.prems"
    have "ford_fulkerson_invar_done_1' G U V s t M"
      by (intro ford_fulkerson_invar_done_1I)
    thus ?thesis
      by (simp add: ford_fulkerson_invar_done_1.loop'_psimps ford_fulkerson_invar_done_1.find_max_matching_psimps)
  next
    case not_done_1: False
    show ?thesis
    proof (cases "done_2 t (m_tbd G U V s t M)")
      case True
      with "1.prems" not_done_1
      have "ford_fulkerson_invar_done_2' G U V s t M"
        by (intro ford_fulkerson_invar_done_2I_2)
      thus ?thesis
        by (simp add: ford_fulkerson_invar_done_2.loop'_psimps ford_fulkerson_invar_done_2.find_max_matching_psimps)
    next
      case False
      with "1.prems" not_done_1
      have "ford_fulkerson_invar_not_done_2' G U V s t M"
        by (intro ford_fulkerson_invar_not_done_2I_2)
      thus ?thesis
        using not_done_1 False
        by
          (auto
           simp add: ford_fulkerson_invar_not_done_2.loop'_psimps ford_fulkerson_invar_not_done_2.find_max_matching_psimps
           dest: "1.hyps"(2)
           intro: ford_fulkerson_invar_not_done_2.ford_fulkerson_invar_augment)
    qed
  qed
qed

lemma (in find_max_match) maximum_matching_find_max_matching:
  shows "maximum_matching G (find_max_matching {})"
proof -
  { fix M
    assume "graph_matching G M"
    hence "finite M"
      using finite_G
      by (auto intro: finite_subset) }
  thus ?thesis
    using find_max_matching_works
    by (simp add: Berge2.matching_def matching_def)
qed

theorem (in ford_fulkerson_valid_input_2)
  shows "maximum_matching (G.E G) (M_tbd (loop' G U V s t M_empty))"
proof -
  have "M_tbd (loop' G U V s t M_empty) = find_max_matching {}"
    using ford_fulkerson_invar_empty
    by (simp add: loop'_find_max_matching_conv M.map_empty)
  thus ?thesis
    using maximum_matching_find_max_matching
    by presburger
qed

end