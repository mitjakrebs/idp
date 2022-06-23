theory Shortest_Path
  imports
    Path
begin

definition dist :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "dist G u v \<equiv> INF p\<in>{p. walk_betw G u p v}. enat (path_length p)"

abbreviation is_shortest_path :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_shortest_path G p u v \<equiv> walk_betw G u p v \<and> path_length p = dist G u v"

end