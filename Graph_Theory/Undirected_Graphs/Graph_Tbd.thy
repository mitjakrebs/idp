theory Graph_Tbd
  imports
    AGF.Berge
begin

section \<open>Graphs\<close>

type_synonym 'a graph = "'a set set"

locale graph =
  fixes G :: "'a graph"
  assumes graph: "\<forall>e\<in>G. \<exists>u v. e = {u, v}"

locale finite_graph = graph G for G +
  assumes finite_edges: "finite G"

(**)
lemma eqI:
  assumes "graph G1"
  assumes "graph G2"
  assumes "\<And>u v. {u, v} \<in> G1 \<longleftrightarrow> {u, v} \<in> G2"
  shows "G1 = G2"
  using assms
  by (auto simp add: graph_def)

subsection \<open>Vertices\<close>

lemma (in finite_graph) finite_vertices:
  shows "finite (Vs G)"
  using graph finite_edges
  by (auto simp add: Vs_def)

end