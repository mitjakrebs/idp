theory Alternating_Dpath
  imports
    Odd_Cycle
begin

section \<open>Alternating directed paths\<close>

definition alt_dpath_bet :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a dgraph \<Rightarrow> 'a dpath \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "alt_dpath_bet P Q G p u v \<equiv> Alternating_Lists.alt_list P Q (edges_of_dpath p) \<and> dpath_bet G p u v"

lemma alt_dpath_betD:
  assumes "alt_dpath_bet P Q G p u v"
  shows
    "Alternating_Lists.alt_list P Q (edges_of_dpath p)"
    "dpath_bet G p u v"
  using assms
  by (simp add: alt_dpath_bet_def)+

lemma alt_dpath_betI:
  assumes "Alternating_Lists.alt_list P Q (edges_of_dpath p)"
  assumes "dpath_bet G p u v"
  shows "alt_dpath_bet P Q G p u v"
  using assms
  by (simp add: alt_dpath_bet_def)

subsection \<open>\<close>

lemma alt_dpath_bet_refl:
  assumes "v \<in> dVs G"
  shows "alt_dpath_bet P Q G [v] v v"
  using assms
  by (auto simp add: Alternating_Lists.alt_list_empty intro: dpath_bet_reflexive alt_dpath_betI)

subsection \<open>\<close>

lemma alt_dpath_bet_snoc_edge:
  assumes alt_dpath: "alt_dpath_bet P (Not \<circ> P) G (vs @ [v'', v']) u v'"
  assumes alt: "P (v'', v') = (Not \<circ> P) (v', v)"
  assumes edge: "(v', v) \<in> G"
  shows "alt_dpath_bet P (Not \<circ> P) G (vs @ [v'', v', v]) u v"
proof (rule alt_dpath_betI, goal_cases)
  case 1
  have "Alternating_Lists.alt_list P (Not \<circ> P) (edges_of_dpath (vs @ [v'', v']) @ edges_of_dpath [v', v])"
  proof (cases "P (v'', v')")
    case True
    hence "Alternating_Lists.alt_list (Not \<circ> P) P (edges_of_dpath [v', v])"
      by (simp add: alt Alternating_Lists.alt_list_step Alternating_Lists.alt_list_empty)
    moreover have "edges_of_dpath (vs @ [v'', v']) \<noteq> []"
      by (subst edges_of_dpath_append_2) simp+
    moreover have "P (last (edges_of_dpath (vs @ [v'', v'])))"
      using True
      by (subst edges_of_dpath_append_2) simp+
    ultimately show ?thesis
      using alt_dpath
      by (auto dest: alt_dpath_betD(1) intro: Alternating_Lists.alt_list_append_2)
  next
    case False
    hence "Alternating_Lists.alt_list P (Not \<circ> P) (edges_of_dpath [v', v])"
      by (simp add: alt Alternating_Lists.alt_list_step Alternating_Lists.alt_list_empty)
    moreover have "edges_of_dpath (vs @ [v'', v']) \<noteq> []"
      by (subst edges_of_dpath_append_2) simp+
    moreover have "(Not \<circ> P) (last (edges_of_dpath (vs @ [v'', v'])))"
      using False
      by (subst edges_of_dpath_append_2) simp+
    ultimately show ?thesis
      using alt_dpath
      by (auto dest: alt_dpath_betD(1) intro: Alternating_Lists.alt_list_append_3)
  qed
  thus ?case
    using edges_of_dpath_append_2[of "[v', v]" "vs @ [v'']"]
    by simp
next
  case 2
  have "dpath_bet G (vs @ [v''] @ [v']) u v'"
    using alt_dpath
    by (auto dest: alt_dpath_betD(2))
  from dpath_bet_snoc_edge[OF this edge]
  show ?case
    by simp
qed

subsection \<open>\<close>

lemma alt_dpath_bet_pref:
  assumes "alt_dpath_bet P Q G (p @ v # q) u w"
  shows "alt_dpath_bet P Q G (p @ [v]) u v"
proof (rule alt_dpath_betI, goal_cases)
  case 1
  have "Alternating_Lists.alt_list P Q (edges_of_dpath (p @ [v]) @ edges_of_dpath (v # q))"
    using assms edges_of_dpath_append_2[of "v # q" p]
    by (auto dest: alt_dpath_betD(1))
  thus ?case
    using Alternating_Lists.alt_list_append_1[where ?l1.0 = "edges_of_dpath (p @ [v])"]
    by simp
next
  case 2
  show ?case
    using assms
    by (force dest: alt_dpath_betD(2) intro: dpath_bet_pref)
qed

section \<open>Distinct alternating directed paths\<close>

definition distinct_alt_dpath_bet :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a dgraph \<Rightarrow> 'a dpath \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "distinct_alt_dpath_bet P Q G p u v \<equiv> alt_dpath_bet P Q G p u v \<and> distinct p"

lemma distinct_alt_dpath_betD:
  assumes "distinct_alt_dpath_bet P Q G p u v"
  shows
    "alt_dpath_bet P Q G p u v"
    "distinct p"
  using assms
  by (simp add: distinct_alt_dpath_bet_def)+

lemma (in finite_dgraph) distinct_alt_dpaths_finite:
  shows "finite {p. distinct_alt_dpath_bet P Q G p u v}"
proof -
  have "{p. distinct_alt_dpath_bet P Q G p u v} \<subseteq> {p. distinct_dpath_bet G p u v}"
    by (auto simp add: distinct_alt_dpath_bet_def alt_dpath_bet_def distinct_dpath_bet_def)
  moreover have "finite ..."
    using finite_edges
    by (intro distinct_dpath_bets_finite)
  ultimately show ?thesis
    by (rule finite_subset)
qed

subsection \<open>\<close>

(* TODO Move somewhere else. *)
lemma alt_list_split_1:
  assumes "Alternating_Lists.alt_list P Q (l1 @ l2)"
  assumes "even (length l1)"
  shows "Alternating_Lists.alt_list P Q l2"
  using assms
  by (induct l1 rule: induct_list012) (simp_all add: Alternating_Lists.alt_list_step)

(* TODO Move somewhere else. *)
lemma alt_list_split_2:
  assumes "Alternating_Lists.alt_list P Q (l1 @ l2)"
  assumes "odd (length l1)"
  shows "Alternating_Lists.alt_list Q P l2"
  using assms
  by (induct l1 rule: induct_list012) (simp_all add: Alternating_Lists.alt_list_step)

(* TODO Move somewhere else. *)
lemma alt_list_append_2:
  assumes "Alternating_Lists.alt_list P Q l1"
  assumes "Alternating_Lists.alt_list Q P l2"
  assumes "odd (length l1)"
  shows "Alternating_Lists.alt_list P Q (l1 @ l2)"
  using assms
  sorry

(* TODO Move somewhere else. *)
lemma alt_list_append_3:
  assumes "Alternating_Lists.alt_list P Q l1"
  assumes "Alternating_Lists.alt_list P Q l2"
  assumes "even (length l1)"
  shows "Alternating_Lists.alt_list P Q (l1 @ l2)"
  using assms
  sorry

(* TODO Move somewhere else. *)
lemma alt_list_decomp:
  assumes alt_list: "Alternating_Lists.alt_list P Q (l1 @ l2 @ l3)"
  assumes even: "even (length l2)"
  shows "Alternating_Lists.alt_list P Q (l1 @ l3)"
proof (cases "odd (length l1)")
  case True
  hence "Alternating_Lists.alt_list Q P (l2 @ l3)"
    using alt_list
    by (blast intro: alt_list_split_2)
  hence "Alternating_Lists.alt_list Q P l3"
    using even
    by (rule alt_list_split_1)
  moreover have "Alternating_Lists.alt_list P Q l1"
    using alt_list
    by (blast dest: Alternating_Lists.alt_list_append_1)
  ultimately show ?thesis
    using True
    by (intro alt_list_append_2)
next
  case False
  hence "Alternating_Lists.alt_list P Q (l2 @ l3)"
    using alt_list
    by (blast intro: alt_list_split_1)
  hence "Alternating_Lists.alt_list P Q l3"
    using even
    by (rule alt_list_split_1)
  moreover have "Alternating_Lists.alt_list P Q l1"
    using alt_list
    by (blast dest: Alternating_Lists.alt_list_append_1)
  ultimately show ?thesis
    using False
    by (intro alt_list_append_3) simp+
qed

lemma alt_dpath_bet_decomp:
  assumes p_alt_dpath: "alt_dpath_bet P Q G p u v"
  assumes p_not_distinct: "\<not> distinct p"
  assumes qrs_def: "closed_dpath_bet_decomp G p = (q, r, s)"
  assumes r_even: "even (dpath_length r)"
  shows "alt_dpath_bet P Q G (q @ tl s) u v"
proof (rule alt_dpath_betI, goal_cases)
  case 1
  have "edges_of_dpath p = edges_of_dpath q @ edges_of_dpath r @ edges_of_dpath s"
    using assms(1-3)
    by (blast dest: alt_dpath_betD(2) intro: edges_of_dpath_decomp)
  hence "Alternating_Lists.alt_list P Q (edges_of_dpath q @ edges_of_dpath s)"
    using p_alt_dpath r_even
    by (fastforce dest: alt_dpath_betD(1) intro: alt_list_decomp)
  thus ?case
    using assms
    by (auto simp add: edges_of_dpath_append_3 dest: alt_dpath_betD(2) intro: closed_dpath_bet_decompE_3)
next
  case 2
  have "dpath_bet G p u v"
    using p_alt_dpath
    by (blast dest: alt_dpath_betD(2))
  then obtain w where
    "dpath_bet G q u w"
    "dpath_bet G s w v"
    using assms(1-3)
    by (blast elim: closed_dpath_bet_decompE_2)
  thus ?case
    by (intro dpath_bet_transitive)
qed

lemma alt_dpath_bet_to_distinct_is_distinct_alt_dpath_bet:
  assumes no_odd_cycle: "\<nexists>c. dpath G c \<and> odd_cycle c"
  assumes alt_dpath_bet: "alt_dpath_bet P Q G p u v"
  shows "distinct_alt_dpath_bet P Q G (dpath_bet_to_distinct G p) u v"
proof -
  have "dpath_bet G p u v"
    using alt_dpath_bet
    by (elim alt_dpath_betD(2))
  thus ?thesis
    using assms
  proof (induction rule: dpath_bet_to_distinct_induct)
    case (path p)
    thus ?case
      by (simp add: distinct_alt_dpath_bet_def)
  next
    case (decomp p q r s)
    hence "even (dpath_length r)"
      by (force elim: closed_dpath_bet_decompE_2 intro: tbd)
    with decomp.prems(2) decomp.hyps(2, 3)
    have "alt_dpath_bet P Q G (q @ tl s) u v"
      by (intro alt_dpath_bet_decomp)
    with decomp.prems(1)
    have "distinct_alt_dpath_bet P Q G (dpath_bet_to_distinct G (q @ tl s)) u v"
      by (intro decomp.IH)
    thus ?case
      using decomp.hyps
      by auto
  qed
qed

section \<open>Reachability\<close>

definition alt_reachable :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "alt_reachable P Q G u v \<equiv> \<exists>p. alt_dpath_bet P Q G p u v"

end