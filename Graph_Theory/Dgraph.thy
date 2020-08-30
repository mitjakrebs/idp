theory Dgraph
  imports AGF.DDFS
begin

section \<open>Graphs\<close>

type_synonym 'v dgraph = "('v \<times> 'v) set"

locale dgraph =
  fixes G :: "'v dgraph"

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

section \<open>Neighborhood\<close>

definition out_neighborhood :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v set" where
  "out_neighborhood G u \<equiv> {v \<in> dVs G. (u, v) \<in> G}"

lemma (in finite_dgraph) out_neighborhood_finite:
  shows "finite (out_neighborhood G u)"
  using vertices_finite
  by (simp add: out_neighborhood_def)

end