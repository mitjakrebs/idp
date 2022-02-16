theory Graph_Adaptor
  imports
    "../Directed_Graphs/Dgraph"
    "../Undirected_Graphs/Graph_Tbd"
begin

definition (in graph) dEs :: "'a dgraph" where
  "dEs \<equiv> {(u, v). {u, v} \<in> G}"

lemma (in graph) dEs_symmetric:
  shows "(u, v) \<in> dEs \<longleftrightarrow> (v, u) \<in> dEs"
  by (simp add: dEs_def insert_commute)

lemma (in graph) edge_iff_edge_1:
  shows "{u, v} \<in> G \<longleftrightarrow> (u, v) \<in> dEs"
  by (simp add: dEs_def)

lemma (in graph) edge_iff_edge_2:
  shows "{u, v} \<in> G \<longleftrightarrow> (v, u) \<in> dEs"
  by (simp add: edge_iff_edge_1 dEs_symmetric)

lemma (in graph) edge_iff_edges:
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