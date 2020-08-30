theory Shortest_Dpath
  imports
    Dgraph
    Dpath
    Ports.Noschinski_to_DDFS
begin

definition dist :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> bool" where
  "dist G u d v \<equiv> \<exists>p. dpath_bet G p u v \<and> dpath_length p = d"

definition min_dist :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat" where
  "min_dist G u v = (LEAST d. dist G u d v)"

lemma min_dist_singleton:
  assumes "v \<in> dVs G"
  shows "min_dist G v v = 0"
proof (rule antisym)
  have "dpath_bet G [v] v v"
    using assms
    by (intro dpath_bet_reflexive)
  hence "dist G v 0 v"
    by (auto simp add: dist_def)
  thus "min_dist G v v \<le> 0"
    by (simp add: min_dist_def)
qed simp

definition shortest_dpath_length :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat option" where
  "shortest_dpath_length G u v \<equiv>
    if reachable G u v then Some (min_dist G u v)
    else None"

lemma shortest_dpath_length_singleton:
  assumes "v \<in> dVs G"
  shows "shortest_dpath_length G v v = Some 0"
  using assms
  by (simp add: shortest_dpath_length_def min_dist_singleton)

end