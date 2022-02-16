theory Undirected_Adjacency
  imports
    "../Adjacency"
    AGF.Berge
    Graph_Tbd
begin

definition (in adjacency) E :: "'m \<Rightarrow> 'a set set" where
  "E G \<equiv> {{u, v} |u v. v \<in> set (adjacency G u)}"

abbreviation (in adjacency) V :: "'m \<Rightarrow> 'a set" where
  "V G \<equiv> Vs (E G)"

subsection \<open>Edges\<close>

lemma (in adjacency) finite_E:
  assumes "invar G"
  shows "finite (E G)"
proof (rule finite_subset)
  { fix u v
    assume "{u, v} \<in> E G"
    then consider (u_v) "v \<in> set (adjacency G u)" | (v_u) "u \<in> set (adjacency G v)"
      by (auto simp add: E_def doubleton_eq_iff)
    hence "{u, v} \<subseteq> M.dom G \<union> \<Union> (S.set ` M.ran G)"
    proof (cases)
      case u_v
      then obtain s where
        "Map_lookup G u = Some s"
        "v \<in> S.set s"
        by (elim mem_adjacencyE)
      hence
        "u \<in> M.dom G"
        "v \<in> \<Union> (S.set ` M.ran G)"
        by (auto simp add: M.mem_dom_iff M.ran_def)
      thus ?thesis
        by fast
    next
      case v_u
      then obtain s where
        "Map_lookup G v = Some s"
        "u \<in> S.set s"
        by (elim mem_adjacencyE)
      hence
        "v \<in> M.dom G"
        "u \<in> \<Union> (S.set ` M.ran G)"
        by (auto simp add: M.mem_dom_iff M.ran_def)
      thus ?thesis
        by fast
    qed }
  thus "E G \<subseteq> Pow (M.dom G \<union> \<Union> (S.set ` M.ran G))"
    by (auto simp add: E_def)
  show "finite ..."
    using assms
    by (auto simp add: S.set_def dest: invarD(1) intro: M.finite_dom M.finite_ran)
qed

lemma (in symmetric_adjacency) mem_adjacency_iff_edge:
  shows "v \<in> set (adjacency G u) \<longleftrightarrow> {u, v} \<in> E G"
proof (standard, goal_cases)
  case 1
  thus ?case
    by (auto simp add: E_def)
next
  case 2
  hence "v \<in> set (adjacency G u) \<or> u \<in> set (adjacency G v)"
    by (auto simp add: E_def doubleton_eq_iff)
  thus ?case
    by (simp add: symmetric)
qed

lemma (in symmetric_adjacency) mem_adjacency_iff_edge_2:
  shows "u \<in> set (adjacency G v) \<longleftrightarrow> {u, v} \<in> E G"
  by (simp add: symmetric mem_adjacency_iff_edge[symmetric])

subsection \<open>Vertices\<close>

lemma (in adjacency) finite_V:
  assumes "invar G"
  shows "finite (V G)"
  using assms
  by (fastforce simp add: Vs_def E_def dest: finite_E)

subsection \<open>Union\<close>

lemma (in adjacency) E_union_cong:
  assumes "invar m1"
  assumes "invar m2"
  shows "E (union m1 m2) = E m1 \<union> E m2"
  using assms
  by (auto simp add: E_def adjacency_union_cong)

lemma (in adjacency) V_union_cong:
  assumes "invar m1"
  assumes "invar m2"
  shows "V (union m1 m2) = V m1 \<union> V m2"
  using assms
  by (simp add: Vs_def E_union_cong)

lemma (in adjacency) finite_V_union:
  assumes "invar m1"
  assumes "invar m2"
  shows "finite (V (union m1 m2))"
  using assms
  by (intro invar_union finite_V)

lemma (in adjacency) symmetric_adjacency_union:
  assumes "symmetric_adjacency' m1"
  assumes "symmetric_adjacency' m2"
  shows "symmetric_adjacency' (union m1 m2)"
proof (standard, goal_cases)
  case 1
  show ?case
    using assms
    by (intro symmetric_adjacency.invar invar_union)
next
  case (2 v u)
  have "v \<in> set (local.adjacency (union m1 m2) u) \<longleftrightarrow> v \<in> set (adjacency m1 u) \<union> set (adjacency m2 u)"
    using assms
    by (fastforce simp add: adjacency_union_cong dest: symmetric_adjacency.invar)
  also have "... \<longleftrightarrow> u \<in> set (adjacency m1 v) \<union> set (adjacency m2 v)"
    using assms
    by (simp add: symmetric_adjacency.symmetric)
  also have "... \<longleftrightarrow> u \<in> set (adjacency (union m1 m2) v)"
    using assms
    by (fastforce simp add: adjacency_union_cong dest: symmetric_adjacency.invar)
  finally show ?case
    .
qed

subsection \<open>Difference\<close>

lemma (in adjacency) symmetric_adjacency_difference:
  assumes "symmetric_adjacency' m1"
  assumes "symmetric_adjacency' m2"
  shows "symmetric_adjacency' (difference m1 m2)"
proof (standard, goal_cases)
  case 1
  show ?case
    using assms
    by (intro symmetric_adjacency.invar invar_difference)
next
  case (2 v u)
  have "v \<in> set (adjacency (difference m1 m2) u) \<longleftrightarrow> v \<in> set (adjacency m1 u) - set (adjacency m2 u)"
    using assms
    by (fastforce simp add: adjacency_difference_cong dest: symmetric_adjacency.invar)
  also have "... \<longleftrightarrow> u \<in> set (adjacency m1 v) - set (adjacency m2 v)"
    using assms
    by (simp add: symmetric_adjacency.symmetric)
  also have "... \<longleftrightarrow> u \<in> set (adjacency (difference m1 m2) v)"
    using assms
    by (fastforce simp add: adjacency_difference_cong dest: symmetric_adjacency.invar)
  finally show ?case
    .
qed

lemma (in adjacency) E_difference_cong:
  assumes "symmetric_adjacency' m1"
  assumes "symmetric_adjacency' m2"
  shows "E (difference m1 m2) = E m1 - E m2"
proof -
  { fix u v
    have "{u, v} \<in> E (difference m1 m2) \<longleftrightarrow> v \<in> set (adjacency (difference m1 m2) u)"
      using assms
      by (intro symmetric_adjacency.mem_adjacency_iff_edge[symmetric]) (auto intro: dunno)
    also have "... \<longleftrightarrow> v \<in> set (adjacency m1 u) - set (adjacency m2 u)"
      using assms
      by (fastforce simp add: adjacency_difference_cong dest: symmetric_adjacency.invar)
    also have "... \<longleftrightarrow> {u, v} \<in> E m1 - E m2"
      using assms
      by (simp add: symmetric_adjacency.mem_adjacency_iff_edge)
    finally have "{u, v} \<in> E (difference m1 m2) \<longleftrightarrow> {u, v} \<in> E m1 - E m2"
      . }
  thus ?thesis
    by (intro eqI) (auto simp add: E_def graph_def)
qed

lemma (in adjacency) finite_V_difference:
  assumes "invar m1"
  assumes "invar m2"
  shows "finite (V (difference m1 m2))"
  using assms
  by (intro invar_difference finite_V)

subsection \<open>\<close>

context adjacency'
begin
sublocale finite_graph "E G"
proof (standard, goal_cases)
  case 1
  show ?case
    by (auto simp add: E_def)
next
  case 2
  show ?case
    using invar
    by (intro finite_E)
qed
end

end