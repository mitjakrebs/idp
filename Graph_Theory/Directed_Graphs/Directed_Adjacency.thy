theory Directed_Adjacency
  imports
    "../Adjacency"
    Dgraph
    Dpath
begin

text \<open>
This theory interprets the graph represented as a map from vertices to their adjacencies as a
directed graph.
\<close>

section \<open>\<close>

definition (in adjacency) dE :: "'m \<Rightarrow> ('a \<times> 'a) set" where
  "dE G \<equiv> {(u, v). v \<in> set (adjacency G u)}"

abbreviation (in adjacency) dV :: "'m \<Rightarrow> 'a set" where
  "dV G \<equiv> dVs (dE G)"

subsection \<open>Edges\<close>

lemma (in adjacency) mem_adjacency_iff_edge:
  shows "v \<in> set (adjacency G u) \<longleftrightarrow> (u, v) \<in> dE G"
  by (simp add: dE_def)

lemma (in adjacency) edgeD:
  assumes "(u, v) \<in> dE G"
  shows
    "u \<in> dV G"
    "v \<in> dV G"
  using assms
  by (auto intro: dVsI)

lemma (in adjacency) finite_dE:
  assumes "invar G"
  shows "finite (dE G)"
proof (rule finite_subset)
  { fix u v
    assume "(u, v) \<in> dE G"
    then obtain s where
      "Map_lookup G u = Some s"
      "v \<in> S.set s"
      by (auto simp add: mem_adjacency_iff_edge[symmetric] elim: mem_adjacencyE)
    hence
      "u \<in> M.dom G"
      "v \<in> \<Union> (S.set ` M.ran G)"
      by (auto simp add: M.mem_dom_iff M.ran_def)
    hence "(u, v) \<in> M.dom G \<times> \<Union> (S.set ` M.ran G)"
      by blast }
  thus "dE G \<subseteq> M.dom G \<times> \<Union> (S.set ` M.ran G)"
    by auto
  show "finite ..."
    using assms
    by (auto simp add: S.set_def dest: invarD(1) intro: M.finite_dom M.finite_ran)
qed

subsection \<open>Vertices\<close>

lemma (in adjacency) adjacency_subset_dV:
  shows "set (adjacency G v) \<subseteq> dV G"
  by (auto simp add: mem_adjacency_iff_edge intro: edgeD(2))

lemma (in adjacency) finite_dV:
  assumes "invar G"
  shows "finite (dV G)"
  using assms
  by (auto simp add: finite_vertices_iff intro: finite_dE)

section \<open>Binary operations\<close>

subsection \<open>Union\<close>

lemma (in adjacency) dE_union_cong:
  assumes "invar m1"
  assumes "invar m2"
  shows "dE (union m1 m2) = dE m1 \<union> dE m2"
  using assms
  by (auto simp add: dE_def adjacency_union_cong)

lemma (in adjacency) dV_union_cong:
  assumes "invar m1"
  assumes "invar m2"
  shows "dV (union m1 m2) = dV m1 \<union> dV m2"
proof -
  have "dV (union m1 m2) = fst ` dE (union m1 m2) \<union> snd ` dE (union m1 m2)"
    by (simp add: dVs_eq)
  also have "... = fst ` (dE m1 \<union> dE m2) \<union> snd ` (dE m1 \<union> dE m2)"
    using assms
    by (simp add: dE_union_cong)
  also have "... = (fst ` dE m1 \<union> snd ` dE m1) \<union> (fst ` dE m2 \<union> snd ` dE m2)"
    by blast
  also have "... = dV m1 \<union> dV m2"
    by (simp add: dVs_eq)
  finally show ?thesis
    .
qed

lemma (in adjacency) finite_dE_union:
  assumes "invar m1"
  assumes "invar m2"
  shows "finite (dE (union m1 m2))"
  using assms
  by (auto simp add: dE_union_cong intro: finite_dE)

lemma (in adjacency) finite_dV_union:
  assumes "invar m1"
  assumes "invar m2"
  shows "finite (dV (union m1 m2))"
  using assms
  by (intro invar_union finite_dV)

subsection \<open>Difference\<close>

lemma (in adjacency) dE_difference_cong:
  assumes "invar m1"
  assumes "invar m2"
  shows "dE (difference m1 m2) = dE m1 - dE m2"
  using assms
  by (auto simp add: dE_def adjacency_difference_cong)

lemma (in adjacency) finite_dE_difference:
  assumes "invar m1"
  assumes "invar m2"
  shows "finite (dE (difference m1 m2))"
  using assms
  by (auto simp add: dE_difference_cong intro: finite_dE)

lemma (in adjacency) finite_dV_difference:
  assumes "invar m1"
  assumes "invar m2"
  shows "finite (dV (difference m1 m2))"
  using assms
  by (intro invar_difference finite_dV)

end