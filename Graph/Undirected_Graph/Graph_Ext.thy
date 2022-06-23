theory Graph_Ext
  imports
    AGF.Berge
begin

type_synonym 'a vertex = 'a

text \<open>An edge in an undirected graph is a set of vertices.\<close>

type_synonym 'a edge = "'a vertex set"

type_synonym 'a graph = "'a edge set"

text \<open>
Since this definition allows for hyperedges, we define a graph, as opposed to a hypergraph, as
follows.
\<close>

locale graph =
  fixes G :: "'a graph"
  assumes graph: "\<forall>e\<in>G. \<exists>u v. e = {u, v}"

lemma \<^marker>\<open>tag invisible\<close> (in graph) mem_VsE:
  assumes "u \<in> Vs G"
  obtains v where
    "{u, v} \<in> G"
  using assms graph
  by (fastforce simp add: insert_commute elim: vs_member_elim)

lemma (in graph) graph_subset:
  assumes "G' \<subseteq> G"
  shows "graph G'"
  using graph assms
  by (force intro: graph.intro)

lemma graphs_eqI:
  assumes "graph G1"
  assumes "graph G2"
  assumes "\<And>u v. {u, v} \<in> G1 \<longleftrightarrow> {u, v} \<in> G2"
  shows "G1 = G2"
  using assms
  by (auto simp add: graph_def)

locale finite_graph = graph G for G +
  assumes finite_edges: "finite G"

lemma (in finite_graph) finite_vertices:
  shows "finite (Vs G)"
  using graph finite_edges
  by (auto simp add: Vs_def)

end