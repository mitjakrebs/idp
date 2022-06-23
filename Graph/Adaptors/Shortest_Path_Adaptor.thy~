theory Shortest_Path_Adaptor
  imports
    Path_Adaptor
    "../Directed_Graph/Shortest_Dpath"
    "../Undirected_Graph/Shortest_Path"
begin

abbreviation is_shortest_dpath :: "'a dgraph \<Rightarrow> 'a dpath \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_shortest_dpath G p u v \<equiv> dpath_bet G p u v \<and> dpath_length p = Shortest_Dpath.dist G u v"

lemma (in graph) dist_eq_dist:
  shows "dist G u v = Shortest_Dpath.dist dEs u v"
  unfolding dist_def Shortest_Dpath.dist_def
  by (simp add: walk_betw_iff_dpath_bet path_length_eq_dpath_length)

lemma (in graph) is_shortest_path_iff_is_shortest_dpath:
  shows "is_shortest_path G p u v = is_shortest_dpath dEs p u v"
  by (simp add: walk_betw_iff_dpath_bet path_length_eq_dpath_length dist_eq_dist)

end