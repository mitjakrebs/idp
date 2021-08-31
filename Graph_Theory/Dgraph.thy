theory Dgraph
  imports
    AGF.DDFS
    "HOL-Data_Structures.Set_Specs"
begin

section \<open>Graphs\<close>

type_synonym 'a dgraph = "('a \<times> 'a) set"

locale dgraph =
  fixes G :: "'a dgraph"

locale finite_dgraph = dgraph G for G +
  assumes edges_finite: "finite G"

lemma (in finite_dgraph) vertices_finite:
  shows "finite (dVs G)"
  unfolding dVs_def
proof -
  have "{{v1, v2} |v1 v2. (v1, v2) \<in> G} = {(\<lambda>e. {fst e, snd e}) e |e. e \<in> G}" (is "?E = _")
    by simp
  also have "... = (\<lambda>e. {fst e, snd e}) ` G"
    by blast
  finally have "?E = (\<lambda>e. {fst e, snd e}) ` G"
    .
  moreover have "finite ..."
    using edges_finite
    by simp
  ultimately have "finite ?E"
    by simp
  thus "finite (\<Union> ?E)"
    by blast
qed

subsection \<open>Neighborhood\<close>

definition out_neighborhood :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "out_neighborhood G u \<equiv> {v \<in> dVs G. (u, v) \<in> G}"

lemma (in dgraph) mem_out_neighborhood_iff_edge:
  shows "v \<in> out_neighborhood G u \<longleftrightarrow> (u, v) \<in> G"
  using dVsI(2)
  by (auto simp add: out_neighborhood_def)

lemma (in dgraph) out_neighborhood_subset_vertices:
  shows "out_neighborhood G u \<subseteq> dVs G"
  by (simp add: out_neighborhood_def)

lemma (in finite_dgraph) out_neighborhood_finite:
  shows "finite (out_neighborhood G u)"
  using out_neighborhood_subset_vertices vertices_finite
  by (rule finite_subset)

section \<open>\<close>

locale finite_dgraph_tbd =
  finite_dgraph G +
  Set_by_Ordered where insert = insert
  for
    G :: "'a::linorder dgraph" and
    insert :: "'a \<Rightarrow> 's \<Rightarrow> 's" +
  fixes out_neighborhood :: "'a \<Rightarrow> 's"
  assumes invar_out_neighborhood: "v \<in> dVs G \<Longrightarrow> invar (out_neighborhood v)"
  assumes isin_out_neighborhood_iff_edge: "invar (out_neighborhood u) \<Longrightarrow> isin (out_neighborhood u) v \<longleftrightarrow> (u, v) \<in> G"

lemma (in finite_dgraph_tbd) mem_out_neighborhood_iff_edge:
  assumes "invar (out_neighborhood u)"
  shows "v \<in> set (out_neighborhood u) \<longleftrightarrow> (u, v) \<in> G"
  using assms isin_out_neighborhood_iff_edge
  by (simp add: invar_def isin set_def)

lemma (in finite_dgraph_tbd) mem_out_neighborhood_if_edge:
  assumes "(u, v) \<in> G"
  shows "v \<in> set (out_neighborhood u)"
proof -
  have "u \<in> dVs G"
    using assms
    by (intro dVsI(1))
  hence "invar (out_neighborhood u)"
    by (intro invar_out_neighborhood)
  thus ?thesis
    using assms
    by (simp add: mem_out_neighborhood_iff_edge)
qed

lemma (in finite_dgraph_tbd) out_neighborhood_subset_vertices:
  assumes "invar (out_neighborhood u)"
  shows "set (out_neighborhood u) \<subseteq> dVs G"
  using assms
  by (auto simp add: mem_out_neighborhood_iff_edge intro: dVsI(2))

lemma (in finite_dgraph_tbd) out_neighborhood_finite:
  shows "finite (set (out_neighborhood u))"
  by (simp add: set_def)

end