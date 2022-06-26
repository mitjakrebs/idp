theory Undirected_BFS_Partial
  imports
    BFS_Partial
    Undirected_BFS
begin

lemma (in undirected_bfs_valid_input) undirected_bfs_partial_correct:
  shows "is_shortest_path_Map G src (bfs_partial G src)"
proof -
  have "is_shortest_dpath_Map G src (bfs_partial G src)"
    using bfs_partial_correct
    .
  thus ?thesis
    by (simp add: is_shortest_path_iff_is_shortest_dpath reachable_iff_reachable)
qed

lemma (in bfs) undirected_bfs_partial_correct:
  assumes "undirected_bfs_valid_input' G src"
  shows "is_shortest_path_Map G src (bfs_partial G src)"
  using assms
  by (intro undirected_bfs_valid_input.undirected_bfs_partial_correct)

end