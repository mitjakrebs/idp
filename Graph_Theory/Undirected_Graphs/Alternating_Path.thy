theory Alternating_Path
  imports
    "../Adaptors/Path_Adaptor"
    Odd_Cycle
begin

section \<open>Alternating lists\<close>

lemma alt_list_tl:
  assumes "l \<noteq> []"
  assumes "alt_list P1 P2 l"
  shows "alt_list P2 P1 (tl l)"
  using assms
  by (auto intro: alt_list_split_2[where ?l1.0 = "[hd l]"])

lemma alt_list_butlast:
  assumes "l \<noteq> []"
  assumes "alt_list P1 P2 l"
  shows "alt_list P1 P2 (butlast l)"
proof (rule conjunct1, rule alt_list_append_1)
  show "alt_list P1 P2 (butlast l @ [last l])"
    using assms
    by simp
qed

lemma alt_list_append_2':
  assumes "alt_list P1 P2 l1"
  assumes "alt_list P2 P1 l2"
  assumes "l1 \<noteq> []"
  assumes "P1 (last l1)"
  assumes "\<forall>x\<in>set l1. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "alt_list P1 P2 (l1 @ l2)"
proof -
  have "odd (length l1)"
    using assms
    by (auto intro: alternating_list_even_last)
  thus ?thesis
    using assms(1, 2)
    by (intro alt_list_append_2)
qed

lemma alt_list_append_3':
  assumes "alt_list P1 P2 l1"
  assumes "alt_list P1 P2 l2"
  assumes "l1 \<noteq> []"
  assumes "P2 (last l1)"
  assumes "\<forall>x\<in>set l1. P1 x \<longleftrightarrow> \<not> P2 x"
  shows "alt_list P1 P2 (l1 @ l2)"
proof -
  have "even (length l1)"
    using assms
    by (auto intro: alternating_list_odd_last)
  thus ?thesis
    using assms(1, 2)
    by (intro alt_list_append_3)
qed

section \<open>Alternating paths\<close>

definition alt_path :: "('a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "alt_path P Q G p u v \<equiv> alt_list P Q (edges_of_path p) \<and> walk_betw G u p v"

lemma alt_pathD:
  assumes "alt_path P Q G p u v"
  shows
    "alt_list P Q (edges_of_path p)"
    "walk_betw G u p v"
  using assms
  by (simp add: alt_path_def)+

lemma alt_pathI:
  assumes "alt_list P Q (edges_of_path p)"
  assumes "walk_betw G u p v"
  shows "alt_path P Q G p u v"
  using assms
  by (simp add: alt_path_def)

lemma alt_path_snoc_snoc:
  assumes "alt_path P Q G (p @ [v, v']) u w"
  shows "alt_path P Q G (p @ [v, w]) u w"
proof -
  have "v' = w"
    using assms
    by (fastforce dest: alt_pathD(2) walk_between_nonempty_path(4))
  thus ?thesis
    using assms
    by simp
qed

subsection \<open>\<close>

lemma alt_path_refl:
  assumes "v \<in> Vs G"
  shows "alt_path P Q G [v] v v"
  using assms
  by (auto simp add: alt_list_empty intro: walk_reflexive alt_pathI)

subsection \<open>\<close>

(* TODO *)
lemma alt_path_ConsI:
  assumes "alt_path P Q G p v w"
  assumes "{u, v} \<in> G"
  assumes "Q {u, v}"
  shows "alt_path Q P G (u # p) u w"
proof (rule alt_pathI, goal_cases)
  case 1
  have "alt_list Q P (edges_of_path [u, v])"
    using assms(3)
    by (simp add: alt_list_step alt_list_empty)
  hence "alt_list Q P (edges_of_path [u, v] @ edges_of_path p)"
    using assms(1)
    by (auto dest: alt_pathD(1) alt_list_append_2)
  thus ?case
    using assms(1) edges_of_path_append_2[of p "[u]"]
    by (auto simp add: walk_between_nonempty_path(3) dest: alt_pathD(2) walk_between_nonempty_path(2))
next
  case 2
  show ?case
    using assms(1, 2)
    by (auto intro: walk_betw_ConsI dest: alt_pathD(2))
qed

subsection \<open>\<close>

lemma alt_path_snoc:
  assumes alt_path: "alt_path P (Not \<circ> P) G (vs @ [v'', v']) u v'"
  assumes alt: "P {v'', v'} = (Not \<circ> P) {v', v}"
  assumes edge: "{v', v} \<in> G"
  shows "alt_path P (Not \<circ> P) G (vs @ [v'', v', v]) u v"
proof (rule alt_pathI, goal_cases)
  case 1
  have "alt_list P (Not \<circ> P) (edges_of_path (vs @ [v'', v']) @ edges_of_path [v', v])"
  proof (cases "P {v'', v'}")
    case True
    hence "alt_list (Not \<circ> P) P (edges_of_path [v', v])"
      by (simp add: alt alt_list_step alt_list_empty)
    moreover have "edges_of_path (vs @ [v'', v']) \<noteq> []"
      by (subst edges_of_path_append_2) simp+
    moreover have "P (last (edges_of_path (vs @ [v'', v'])))"
      using True
      by (subst edges_of_path_append_2) simp+
    ultimately show ?thesis
      using alt_path
      by (auto dest: alt_pathD(1) intro: alt_list_append_2')
  next
    case False
    hence "alt_list P (Not \<circ> P) (edges_of_path [v', v])"
      by (simp add: alt alt_list_step alt_list_empty)
    moreover have "edges_of_path (vs @ [v'', v']) \<noteq> []"
      by (subst edges_of_path_append_2) simp+
    moreover have "(Not \<circ> P) (last (edges_of_path (vs @ [v'', v'])))"
      using False
      by (subst edges_of_path_append_2) simp+
    ultimately show ?thesis
      using alt_path
      by (auto dest: alt_pathD(1) intro: alt_list_append_3')
  qed
  thus ?case
    using edges_of_path_append_2[of "[v', v]" "vs @ [v'']"]
    by simp
next
  case 2
  have "walk_betw G u (vs @ [v''] @ [v']) v'"
    using alt_path
    by (auto dest: alt_pathD(2))
  thus ?case
    using edge
    by (auto dest: edges_are_walks walk_transitive)
qed

(**)

subsection \<open>\<close>

lemma alt_path_pref:
  assumes "alt_path P Q G (p @ v # q) u w"
  shows "alt_path P Q G (p @ [v]) u v"
proof (rule alt_pathI, goal_cases)
  case 1
  have "alt_list P Q (edges_of_path (p @ [v]) @ edges_of_path (v # q))"
    using assms edges_of_path_append_2[of "v # q" p]
    by (auto dest: alt_pathD(1))
  thus ?case
    using alt_list_append_1[where ?l1.0 = "edges_of_path (p @ [v])"]
    by simp
next
  case 2
  show ?case
    using assms
    by (force dest: alt_pathD(2) intro: walk_pref)
qed

lemma alt_path_pref_2:
  assumes "alt_path P Q G (p @ q) u w"
  assumes "p \<noteq> []"
  shows "alt_path P Q G p u (last p)"
  using assms
  by (auto simp add: append_butlast_last_cancel[symmetric] dest: alt_path_pref)

lemma alt_path_suf:
  assumes "alt_path P (Not \<circ> P) G (p @ [v, v'] @ q) u w"
  assumes "P {v, v'}"
  shows "alt_path P (Not \<circ> P) G ([v, v'] @ q) v w"
proof (rule alt_pathI, goal_cases)
  case 1
  let ?p' = "[v, v'] @ q"
  have "alt_list P (Not \<circ> P) (edges_of_path ?p') \<or> alt_list (Not \<circ> P) P (edges_of_path ?p')"
    using assms(1) edges_of_path_append[of p ?p']
    by (fastforce dest: alt_pathD(1) dest: alt_list_append_1)
  thus ?case
    using assms(2)
    by (simp add: alt_list_step)
next
  case 2
  show ?case
    using assms(1)
    by (fastforce dest: alt_pathD(2) intro: walk_suff)
qed

lemma alt_path_suf_2:
  assumes "alt_path P (Not \<circ> P) G (p @ [v, v'] @ q) u w"
  assumes "\<not> P {v, v'}"
  shows "alt_path (Not \<circ> P) P G ([v, v'] @ q) v w"
proof (rule alt_pathI, goal_cases)
  case 1
  let ?p' = "[v, v'] @ q"
  have "alt_list P (Not \<circ> P) (edges_of_path ?p') \<or> alt_list (Not \<circ> P) P (edges_of_path ?p')"
    using assms(1) edges_of_path_append[of p ?p']
    by (fastforce dest: alt_pathD(1) dest: alt_list_append_1)
  thus ?case
    using assms(2)
    by (simp add: alt_list_step)
next
  case 2
  show ?case
    using assms(1)
    by (fastforce dest: alt_pathD(2) intro: walk_suff)
qed

subsection \<open>\<close>

lemma even_if_last:
  assumes "alt_list P Q l"
  assumes "\<forall>x\<in>set l. P x \<longleftrightarrow> \<not> Q x"
  assumes "Q (last l)"
  shows "even (length l)"
  using assms
  by (cases "l = []") (auto intro: alternating_list_odd_last)

lemma odd_if_last:
  assumes "alt_list P Q l"
  assumes "\<forall>x\<in>set l. P x \<longleftrightarrow> \<not> Q x"
  assumes "P (last l)"
  assumes "l \<noteq> []"
  shows "odd (length l)"
  using assms
  by (auto intro: alternating_list_even_last)

section \<open>Reversing alternating paths\<close>

(* TODO Move. *)
lemma alt_list_revI:
  assumes "alt_list P Q l"
  shows "alt_list P Q (rev l) \<or> alt_list Q P (rev l)"
  using assms
  by (auto intro: alt_list_rev alt_list_rev_even)

lemma alt_path_rev_oddI:
  assumes "alt_path P Q G p u v"
  assumes "odd (path_length p)"
  shows "alt_path P Q G (rev p) v u"
proof (rule alt_pathI, goal_cases)
  case 1
  show ?case
    using assms
    by (auto simp add: edges_of_path_rev[symmetric] dest: alt_pathD(1) intro: alt_list_rev)
next
  case 2
  show ?case
    using assms(1)
    by (intro alt_pathD(2) walk_symmetric)
qed

lemma alt_path_rev_evenI:
  assumes "alt_path P Q G p u v"
  assumes "even (path_length p)"
  shows "alt_path Q P G (rev p) v u"
proof (rule alt_pathI, goal_cases)
  case 1
  show ?case
    using assms
    by (auto simp add: edges_of_path_rev[symmetric] dest: alt_pathD(1) intro: alt_list_rev_even)
next
  case 2
  show ?case
    using assms(1)
    by (intro alt_pathD(2) walk_symmetric)
qed

lemma alt_path_revI:
  assumes "alt_path P Q G p u v"
  shows "alt_path P Q G (rev p) v u \<or> alt_path Q P G (rev p) v u"
  using assms
  by (auto intro: alt_path_rev_oddI alt_path_rev_evenI)

section \<open>\<close>

(**)
lemma alt_path_snoc_oddI:
  assumes "alt_path P Q G p u v"
  assumes "odd (path_length p)"
  assumes "{v, w} \<in> G"
  assumes "Q {v, w}"
  shows "alt_path P Q G (p @ [w]) u w"
proof -
  have "alt_path P Q G (rev p) v u"
    using assms(1, 2)
    by (intro alt_path_rev_oddI)
  moreover have
    "{w, v} \<in> G"
    "Q {w, v}"
    using assms(3, 4)
    by (metis doubleton_eq_iff)+
  ultimately have "alt_path Q P G (w # rev p) w u"
    by (intro alt_path_ConsI)
  thus ?thesis
    using assms(2)
    by (auto simp add: edges_of_path_length dest: alt_path_rev_evenI)
qed

(* TODO Rename. *)
lemma tbd':
  assumes "alt_path P Q G p u v"
  assumes "alt_path P Q G q u v"
  assumes "\<nexists>c. path G c \<and> odd_cycle c"
  shows "odd (path_length p) = odd (path_length q)"
proof (standard, goal_cases)
  case odd: 1
  show ?case
  proof (rule ccontr)
    assume not_odd: "\<not> odd (path_length q)"
    have path: "walk_betw G u (p @ tl (rev q)) u"
      using assms(1, 2)
      by (auto dest: alt_pathD(2) intro: walk_symmetric walk_transitive)
    moreover have "odd_cycle (p @ tl (rev q))"
    proof (rule odd_cycleI, goal_cases)
      case 1
      show ?case
        using odd not_odd
        by (simp add: edges_of_path_length)
    next
      case 2
      show ?case
        using path
        by (simp add: walk_between_nonempty_path(3, 4))
    qed
    ultimately show False
      using assms(3)
      by fast
  qed
next
  case odd: 2
  show ?case
  proof (rule ccontr)
  assume not_odd: "\<not> odd (path_length p)"
    have path: "walk_betw G u (q @ tl (rev p)) u"
      using assms(1, 2)
      by (auto dest: alt_pathD(2) intro: walk_symmetric walk_transitive)
    moreover have "odd_cycle (q @ tl (rev p))"
    proof (rule odd_cycleI, goal_cases)
      case 1
      show ?case
        using odd not_odd
        by (simp add: edges_of_path_length)
    next
      case 2
      show ?case
        using path
        by (simp add: walk_between_nonempty_path(3, 4))
    qed
    ultimately show False
      using assms(3)
      by fast
  qed
qed

lemma alt_path_subst_pref:
  assumes "alt_path P Q G (p @ v # q) u w"
  assumes "alt_path P Q G p' u v"
  assumes "\<nexists>c. path G c \<and> odd_cycle c"
  shows "alt_path P Q G (p' @ q) u w"
proof (rule alt_pathI, goal_cases)
  case 1
  show ?case
  proof (cases "odd (path_length (p @ [v]))")
    case True
    hence "alt_list Q P (edges_of_path (v # q))"
      using assms(1)
      by (fastforce simp add: edges_of_path_append_2[of "v # q"] dest: alt_pathD(1) intro: alt_list_split_2)
    moreover have "odd (path_length p')"
      using assms True
      by (auto dest: alt_path_pref tbd')
    ultimately have "alt_list P Q (edges_of_path p' @ edges_of_path (v # q))"
      using assms(2)
      by (auto dest: alt_pathD(1) intro: alt_list_append_2)
    thus ?thesis
      using assms(2)
      by (auto simp add: walk_between_nonempty_path(4) edges_of_path_append_3 dest: alt_pathD(2))
  next
    case False
    hence "alt_list P Q (edges_of_path (v # q))"
      using assms(1)
      by (fastforce simp add: edges_of_path_append_2[of "v # q"] dest: alt_pathD(1) intro: alt_list_split_1)
    moreover have "even (path_length p')"
      using assms False
      by (auto dest: alt_path_pref tbd')
    ultimately have "alt_list P Q (edges_of_path p' @ edges_of_path (v # q))"
      using assms(2)
      by (auto dest: alt_pathD(1) intro: alt_list_append_3)
    thus ?thesis
      using assms(2)
      by (auto simp add: walk_between_nonempty_path(4) edges_of_path_append_3 dest: alt_pathD(2))
  qed
next
  case 2
  have "walk_betw G u p' v"
    using assms(2)
    by (intro alt_pathD(2))
  moreover have "walk_betw G v (v # q) w"
    using assms(1)
    by (intro alt_pathD(2) walk_suff) simp
  ultimately show ?case
    by (auto dest: walk_transitive)
qed

section \<open>Distinct alternating directed paths\<close>

definition distinct_alt_path :: "('a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "distinct_alt_path P Q G p u v \<equiv> alt_path P Q G p u v \<and> distinct p"

lemma distinct_alt_pathD:
  assumes "distinct_alt_path P Q G p u v"
  shows
    "alt_path P Q G p u v"
    "distinct p"
  using assms
  by (simp add: distinct_alt_path_def)+

lemma distinct_alt_pathI:
  assumes "alt_path P Q G p u v"
  assumes "distinct p"
  shows "distinct_alt_path P Q G p u v"
  using assms
  by (simp add: distinct_alt_path_def)

lemma (in finite_graph) distinct_alt_paths_finite:
  shows "finite {p. distinct_alt_path P Q G p u v}"
proof -
  have "{p. distinct_alt_path P Q G p u v} \<subseteq> {p. distinct_path G p u v}"
    by (auto simp add: distinct_alt_path_def alt_path_def distinct_path_def)
  moreover have "finite ..."
    using finite_edges
    by (intro distinct_paths_finite)
  ultimately show ?thesis
    by (rule finite_subset)
qed

subsection \<open>\<close>

(* TODO Move somewhere else. *)
lemma alt_list_decomp:
  assumes alt_list: "alt_list P Q (l1 @ l2 @ l3)"
  assumes even: "even (length l2)"
  shows "alt_list P Q (l1 @ l3)"
proof (cases "odd (length l1)")
  case True
  hence "alt_list Q P (l2 @ l3)"
    using alt_list
    by (blast intro: alt_list_split_2)
  hence "alt_list Q P l3"
    using even
    by (rule alt_list_split_1)
  moreover have "alt_list P Q l1"
    using alt_list
    by (blast dest: alt_list_append_1)
  ultimately show ?thesis
    using True
    by (intro alt_list_append_2)
next
  case False
  hence "alt_list P Q (l2 @ l3)"
    using alt_list
    by (blast intro: alt_list_split_1)
  hence "alt_list P Q l3"
    using even
    by (rule alt_list_split_1)
  moreover have "alt_list P Q l1"
    using alt_list
    by (blast dest: alt_list_append_1)
  ultimately show ?thesis
    using False
    by (intro alt_list_append_3) simp+
qed

lemma (in graph) alt_path_decomp:
  assumes "alt_path P Q G p u v"
  assumes "\<not> distinct p"
  assumes "closed_path_decomp G p = (q, r, s)"
  assumes "even (path_length r)"
  shows "alt_path P Q G (q @ tl s) u v"
proof (rule alt_pathI, goal_cases)
  case 1
  have "edges_of_path p = edges_of_path q @ edges_of_path r @ edges_of_path s"
    using assms(1-3)
    by (blast dest: alt_pathD(2) intro: edges_of_path_decomp)
  hence "alt_list P Q (edges_of_path q @ edges_of_path s)"
    using assms(1, 4)
    by (fastforce dest: alt_pathD(1) intro: alt_list_decomp)
  thus ?case
    using assms
    by (auto simp add: edges_of_path_append_3 dest: alt_pathD(2) intro: closed_path_decompE_3)
next
  case 2
  have "walk_betw G u p v"
    using assms(1)
    by (blast dest: alt_pathD(2))
  then obtain w where
    "walk_betw G u q w"
    "walk_betw G w s v"
    using assms(1-3)
    by (blast elim: closed_path_decompE_2)
  thus ?case
    by (intro walk_transitive)
qed

lemma (in graph) alt_path_to_distinct_is_distinct_alt_path:
  assumes "alt_path P Q G p u v"
  assumes "\<nexists>c. path G c \<and> odd_cycle c"
  shows "distinct_alt_path P Q G (path_to_distinct p) u v"
proof -
  have "walk_betw G u p v"
    using assms(1)
    by (elim alt_pathD(2))
  thus ?thesis
    using assms
  proof (induction rule: path_to_distinct_induct)
    case (path p)
    thus ?case
      by (simp add: distinct_alt_path_def)
  next
    case (decomp p q r s)
    hence "even (path_length r)"
      by (force elim: closed_path_decompE_2 intro: tbd)
    with decomp.prems(1) decomp.hyps(2, 3)
    have "alt_path P Q G (q @ tl s) u v"
      by (intro alt_path_decomp)
    with decomp.prems(2)
    have "distinct_alt_path P Q G (path_to_distinct (q @ tl s)) u v"
      by (intro decomp.IH)
    thus ?case
      using decomp.hyps
      by auto
  qed
qed

section \<open>Reachability\<close>

definition alt_reachable :: "('a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "alt_reachable P Q G u v \<equiv> \<exists>p. alt_path P Q G p u v"

end