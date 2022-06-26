subsubsection \<open>Adaptors\<close>

theory Graph_Adaptor
  imports
    "../Directed_Graph/Dgraph"
    "../Undirected_Graph/Graph_Ext"
begin

text \<open>
An undirected graph can be viewed as a symmetric directed graph. Session @{session AGF} shows how to
transform a @{type graph} into a symmetric @{type dgraph}. We extend, or rather, redo (parts of)
their theory. Our issue with their theory is that the lemmas are inside a locale that assumes that
the graph does not have loops. Most--if not all--of the lemmas hold even if the graph contains
loops, though.
\<close>

definition (in graph) dEs :: "'a dgraph" where
  "dEs \<equiv> {(u, v). {u, v} \<in> G}"

lemma (in graph) dEs_symmetric:
  shows "(u, v) \<in> dEs \<longleftrightarrow> (v, u) \<in> dEs"
  by (simp add: dEs_def insert_commute)

lemma \<^marker>\<open>tag invisible\<close> (in graph) edge_iff_edge_1:
  shows "{u, v} \<in> G \<longleftrightarrow> (u, v) \<in> dEs"
  by (simp add: dEs_def)

lemma \<^marker>\<open>tag invisible\<close> (in graph) edge_iff_edge_2:
  shows "{u, v} \<in> G \<longleftrightarrow> (v, u) \<in> dEs"
  by (simp add: edge_iff_edge_1 dEs_symmetric)

lemma \<^marker>\<open>tag invisible\<close> (in graph) edge_iff_edges:
  shows "{u, v} \<in> G \<longleftrightarrow> (u, v) \<in> dEs \<and> (v, u) \<in> dEs"
  using edge_iff_edge_1 edge_iff_edge_2
  by simp

context finite_graph
begin
sublocale F: finite_dgraph dEs
proof (standard, goal_cases)
  case 1
  have "dEs \<subseteq> Vs G \<times> Vs G"
    using edge_iff_edge_1
    by auto
  moreover have "finite (Vs G \<times> Vs G)"
    using finite_vertices
    by fast
  ultimately show ?case
    by (rule finite_subset)
qed
end

end