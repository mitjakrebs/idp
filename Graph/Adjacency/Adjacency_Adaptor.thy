theory \<^marker>\<open>tag invisible\<close> Adjacency_Adaptor
  imports
    Directed_Adjacency
    "../Adaptors/Graph_Adaptor"
    Undirected_Adjacency
begin

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) V_eq_dV:
  shows "V G = dV G"
proof -
  have "E G = {{u, v} |u v. (u, v) \<in> dE G}"
    by (simp add: E_def mem_adjacency_iff_edge)
  thus ?thesis
    by (simp add: V_def Vs_def dV_def dVs_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) adjacency_subset_V:
  shows "set (adjacency_list G v) \<subseteq> V G"
  using adjacency_subset_dV
  by (simp add: V_eq_dV)

lemma \<^marker>\<open>tag invisible\<close> (in symmetric_adjacency) dE_eq_dEs:
  shows "dE G = dEs"
  unfolding dE_def dEs_def
  by (simp add: mem_adjacency_iff_edge)

end \<^marker>\<open>tag invisible\<close> 