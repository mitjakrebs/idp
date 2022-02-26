theory Bipartite_Graph
  imports
    Odd_Cycle
    "../Adaptors/Path_Adaptor"
begin

section \<open>Bipartite graphs\<close>

locale bipartite_graph = graph G for G +
  fixes U V :: "'a set"
  assumes U_union_V_eq_Vs: "U \<union> V = Vs G"
  assumes U_V_disjoint: "U \<inter> V = {}"
  assumes tbd: "{u, v} \<in> G \<Longrightarrow> u \<in> U \<longleftrightarrow> v \<in> V"

subsection \<open>Convenience Lemmas\<close>

lemma (in bipartite_graph) U_subset_Vs:
  shows "U \<subseteq> Vs G"
  unfolding U_union_V_eq_Vs[symmetric]
  by (intro Un_upper1)

lemma (in bipartite_graph) V_subset_Vs:
  shows "V \<subseteq> Vs G"
  unfolding U_union_V_eq_Vs[symmetric]
  by (intro Un_upper2)

lemma (in bipartite_graph) mem_U_imp_not_mem_V:
  assumes "u \<in> U"
  shows "u \<notin> V"
  using assms U_V_disjoint
  by fast

lemma (in bipartite_graph) mem_V_imp_not_mem_U:
  assumes "v \<in> V"
  shows "v \<notin> U"
  using assms U_V_disjoint
  by fast

lemma (in bipartite_graph) not_mem_U_imp_mem_V:
  assumes "v \<in> Vs G"
  assumes "v \<notin> U"
  shows "v \<in> V"
  using assms U_union_V_eq_Vs U_V_disjoint
  by fast

lemma (in bipartite_graph) not_mem_V_imp_mem_U:
  assumes "u \<in> Vs G"
  assumes "u \<notin> V"
  shows "u \<in> U"
  using assms U_union_V_eq_Vs U_V_disjoint
  by fast

subsection \<open>Basic Lemmas\<close>

lemma (in bipartite_graph) U_independent:
  shows "\<forall>u\<in>U. \<forall>v\<in>U. {u, v} \<notin> G"
proof (standard, standard, standard)
  fix u v
  assume
    "u \<in> U"
    "v \<in> U"
    "{u, v} \<in> G"
  thus False
    by (auto simp add: tbd dest: mem_U_imp_not_mem_V)
qed

lemma (in bipartite_graph) V_independent:
  shows "\<forall>u\<in>V. \<forall>v\<in>V. {u, v} \<notin> G"
proof (standard, standard, standard)
  fix u v
  assume
    "u \<in> V"
    "v \<in> V"
    "{u, v} \<in> G"
  thus False
    by (auto simp add: tbd dest: mem_V_imp_not_mem_U)
qed

lemma (in bipartite_graph) no_loop:
  shows "{v, v} \<notin> G"
proof (standard, goal_cases)
  case 1
  show ?case
  proof (cases "v \<in> U")
    case True
    thus ?thesis
      using 1 U_independent
      by blast
  next
    case False
    hence "v \<in> V"
      using 1
      by (auto intro: not_mem_U_imp_mem_V)
    thus ?thesis
      using 1 V_independent
      by blast
  qed
qed

(* TODO Move. *)
(* TODO Rename. *)
lemma lolol:
  assumes "path G p"
  assumes "Suc i < length p"
  shows "{p ! i, p ! (Suc i)} \<in> G"
  using assms
proof (induct p arbitrary: i rule: path_induct)
  case 3
  thus ?case
    by (auto simp add: less_Suc_eq_0_disj)
qed simp_all

(* TODO Rename. *)
lemma (in bipartite_graph) xaxa:
  assumes "path G p"
  assumes "Suc i < length p"
  shows "p ! i \<in> U \<longleftrightarrow> p ! (Suc i) \<in> V"
  using assms
  by (auto simp add: tbd dest: lolol)

(* TODO Rename. *)
lemma (in bipartite_graph) xoxo:
  assumes "path G p"
  assumes "Suc i < length p"
  shows "p ! i \<in> U \<longleftrightarrow> p ! (Suc i) \<notin> U"
proof -
  have "p ! i \<in> U \<longleftrightarrow> p ! (Suc i) \<in> V"
    using assms
    by (intro xaxa)
  also have "... \<longleftrightarrow> p ! (Suc i) \<notin> U"
  proof (standard, goal_cases)
    case 1
    thus ?case
      by (intro mem_V_imp_not_mem_U)
  next
    case 2
    thus ?case
      using assms
      by (fastforce intro: mem_path_Vs intro: not_mem_U_imp_mem_V)
  qed
  finally show ?thesis
    .
qed

(* TODO Rename. *)
lemma (in bipartite_graph) xexe:
  assumes "path G p"
  assumes "hd p \<in> U"
  assumes "i < length p"
  shows "p ! i \<in> U \<longleftrightarrow> even i"
  using assms
proof (induct i)
  case 0
  thus ?case
    by (simp add: hd_conv_nth)
next
  case (Suc i)
  hence "p ! Suc i \<in> U \<longleftrightarrow> p ! i \<notin> U"
    by (auto simp add: xoxo)
  also have "... \<longleftrightarrow> odd i"
    using Suc.prems
    by (simp add: Suc.hyps)
  also have "... \<longleftrightarrow> even (Suc i)"
    by simp
  finally show ?case
    .
qed

(* TODO Rename. *)
lemma (in bipartite_graph) xuxu:
  assumes "path G p"
  assumes "hd p \<in> V"
  assumes "i < length p"
  shows "p ! i \<in> V \<longleftrightarrow> even i"
  using assms
proof (induct i)
  case 0
  thus ?case
    by (simp add: hd_conv_nth)
next
  case (Suc i)
  hence "p ! Suc i \<in> V \<longleftrightarrow> p ! i \<in> U"
    by (simp add: xaxa)
  also have "... \<longleftrightarrow> p ! i \<notin> V"
  proof (standard, goal_cases)
    case 1
    thus ?case
      using U_subset_Vs
      by (auto dest: mem_U_imp_not_mem_V)
  next
    case 2
    have "p ! i \<in> Vs G"
      using Suc.prems(1, 3)
      by (fastforce intro: mem_path_Vs)
    thus ?case
      using 2
      by (intro not_mem_V_imp_mem_U)
  qed
  also have "... \<longleftrightarrow> odd i"
    using Suc.prems
    by (simp add: Suc.hyps)
  also have "... \<longleftrightarrow> even (Suc i)"
    by simp
  finally show ?case
    .
qed

theorem (in bipartite_graph) no_odd_cycle:
  shows "\<nexists>c. path G c \<and> odd_cycle c"
proof (standard, elim exE)
  fix c
  assume assm: "path G c \<and> odd_cycle c"
  hence c_non_empty: "c \<noteq> []"
    by (auto simp add: odd_cycle_def)
  show False
  proof (cases "hd c \<in> U")
    case True
    { fix i
      assume "i < length c"
      hence "c ! i \<in> U \<longleftrightarrow> even i"
        using assm True
        by (intro xexe) simp }
    moreover have "c ! (length c - 1) \<in> U"
    proof -
      have "last c \<in> U"
        using assm True
        by (simp add: odd_cycleD(2))
      thus ?thesis
        using c_non_empty
        by (simp add: last_conv_nth)
    qed
    ultimately have "even (path_length c)"
      using c_non_empty
      by (simp add: edges_of_path_length)
    thus False
      using assm
      by (auto dest: odd_cycleD(1))
  next
    case False
    { fix i
      assume "i < length c"
      hence "c ! i \<in> U \<longleftrightarrow> odd i"
      proof (induct i)
        case 0
        thus ?case
          using False
          by (simp add: hd_conv_nth)
      next
        case (Suc i)
        hence "c ! Suc i \<in> U \<longleftrightarrow> c ! i \<notin> U"
          using assm
          by (auto simp add: xoxo)
        also have "... \<longleftrightarrow> even i"
          using Suc.prems
          by (simp add: Suc.hyps)
        also have "... \<longleftrightarrow> odd (Suc i)"
          by simp
        finally show ?case
          .
      qed }
    moreover have "c ! (length c - 1) \<notin> U"
    proof -
      have "last c \<notin> U"
        using assm False
        by (simp add: odd_cycleD(2))
      thus ?thesis
        using c_non_empty
        by (simp add: last_conv_nth)
    qed
    ultimately have "even (path_length c)"
      using c_non_empty
      by (simp add: edges_of_path_length)
    thus False
      using assm
      by (auto dest: odd_cycleD(1))
  qed
qed

end