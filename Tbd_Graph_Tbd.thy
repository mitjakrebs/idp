theory Tbd_Graph_Tbd
  imports
    "Graph_Theory/Graph_Theory"
    "HOL-Data_Structures.Set_Specs"
begin

locale digraph = Set_by_Ordered where insert = insert
  for insert :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 's" +
  fixes vertices :: "'a set"
  fixes edges :: "('a \<times> 'a) set"
  fixes out_neighborhood :: "'a \<Rightarrow> 's"
  assumes digraph: "\<forall>e\<in>edges. \<exists>u v. u \<in> vertices \<and> v \<in> vertices \<and> u \<noteq> v \<and> e = (u, v)"
  assumes invar_out_neighborhood: "v \<in> vertices \<Longrightarrow> invar (out_neighborhood v)"
  assumes isin_out_neighborhood_iff_edge: "invar (out_neighborhood u) \<Longrightarrow> isin (out_neighborhood u) v \<longleftrightarrow> (u, v) \<in> edges"

subsection \<open>@{term edges}\<close>

lemma (in digraph) edgeI:
  assumes "(u, v) \<in> edges"
  shows
    "u \<in> vertices"
    "v \<in> vertices"
    "u \<noteq> v"
  using assms digraph
  by fastforce+

lemma (in digraph) edges_subset:
  shows "edges \<subseteq> vertices \<times> vertices"
  by (auto intro: edgeI(1, 2))

subsection \<open>@{term out_neighborhood}\<close>

lemma (in digraph) mem_out_neighborhood_iff_edge:
  assumes "invar (out_neighborhood u)"
  shows "v \<in> set (out_neighborhood u) \<longleftrightarrow> (u, v) \<in> edges"
  using assms isin_out_neighborhood_iff_edge
  by (simp add: invar_def isin set_def)

lemma (in digraph) mem_out_neighborhood_if_edge:
  assumes "(u, v) \<in> edges"
  shows "v \<in> set (out_neighborhood u)"
proof -
  have "u \<in> vertices"
    using assms
    by (intro edgeI(1))
  hence "invar (out_neighborhood u)"
    by (intro invar_out_neighborhood)
  thus ?thesis
    using assms
    by (simp add: mem_out_neighborhood_iff_edge)
qed

lemma (in digraph) out_neighborhood_subset_vertices:
  assumes "invar (out_neighborhood u)"
  shows "set (out_neighborhood u) \<subseteq> vertices"
  using assms
  by (auto simp add: mem_out_neighborhood_iff_edge intro: edgeI(2))

locale finite_digraph = digraph +
  assumes vertices_finite: "finite vertices"

section \<open>\<close>

lemma (in finite_digraph) edges_finite:
  shows "finite edges"
  using edges_subset vertices_finite
  by (auto intro: finite_subset)

context finite_digraph
begin
  sublocale finite_dgraph edges
    using edges_finite
    by unfold_locales
end

lemma (in finite_digraph) out_neighborhood_finite:
  shows "finite (set (out_neighborhood u))"
  by (simp add: set_def)

end