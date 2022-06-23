theory Adjacency_Adaptor
  imports
    Directed_Adjacency
    "../Adaptors/Graph_Adaptor"
    Undirected_Adjacency
begin

subsection \<open>Edges\<close>

subsection \<open>Vertices\<close>

lemma (in adjacency) V_eq_dV:
  shows "V G = dV G"
proof -
  have "E G = {{u, v} |u v. (u, v) \<in> dE G}"
    by (simp add: E_def mem_adjacency_iff_edge)
  thus ?thesis
    by (simp add: V_def Vs_def dV_def dVs_def)
qed

lemma (in adjacency) adjacency_subset_V:
  shows "set (adjacency_list G v) \<subseteq> V G"
  using adjacency_subset_dV
  by (simp add: V_eq_dV)

subsection \<open>\<close>

lemma (in symmetric_adjacency) dE_eq_dEs:
  shows "dE G = dEs"
  unfolding dE_def dEs_def
  by (simp add: mem_adjacency_iff_edge)

end