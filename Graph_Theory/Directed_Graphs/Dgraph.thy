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
  assumes finite_edges: "finite G"

locale simple_dgraph = dgraph G for G +
  assumes no_loop: "(u, v) \<in> G \<Longrightarrow> u \<noteq> v"

locale symmetric_dgraph = dgraph G for G +
  assumes symmetric: "(u, v) \<in> G \<longleftrightarrow> (v, u) \<in> G"

subsection \<open>Vertices\<close>

lemma (in finite_dgraph) finite_vertices:
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
    using finite_edges
    by simp
  ultimately have "finite ?E"
    by simp
  thus "finite (\<Union> ?E)"
    by blast
qed

subsection \<open>Neighborhood\<close>

definition out_neighborhood :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "out_neighborhood G u \<equiv> {v \<in> dVs G. (u, v) \<in> G}"

lemma mem_out_neighborhood_iff_edge:
  shows "v \<in> out_neighborhood G u \<longleftrightarrow> (u, v) \<in> G"
  using dVsI(2)
  by (auto simp add: out_neighborhood_def)

lemma out_neighborhood_subset_vertices:
  shows "out_neighborhood G u \<subseteq> dVs G"
  by (simp add: out_neighborhood_def)

lemma (in finite_dgraph) finite_out_neighborhood:
  shows "finite (out_neighborhood G u)"
  using out_neighborhood_subset_vertices finite_edges finite_subset
  by (fastforce intro: finite_vertices)

end