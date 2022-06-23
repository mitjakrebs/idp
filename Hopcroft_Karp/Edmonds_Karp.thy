section \<open>Edmonds-Karp algorithm\<close>

text \<open>
This section specifies an algorithm that solves the maximum cardinality matching problem in
bipartite graphs, and verifies its correctness.

The algorithm is based on Berge's theorem, which states that a matching $M$ is maximum if and only
if there is no augmenting path w.r.t.\ $M$. This immediately suggests the following algorithm for
finding a maximum matching: repeatedly find an augmenting path and augment the matching until there
are no augmenting paths. We claim that the algorithm specified below, in each iteration, finds not
just any augmenting path but a shortest one. We do not verify this claim, however, as the
distinction is not relevant for the correctness of the algorithm.

The algorithm is an adaptation of the Edmonds-Karp algorithm, which solves the
maximum flow problem, to the maximum cardinality matching problem in bipartite graphs, which reduces
to the maximum flow problem.
\<close>

theory Edmonds_Karp
  imports
    "../Alternating_BFS/Alternating_BFS"
    "../Graph/Undirected_Graph/Augmenting_Path"
    "../Graph/Undirected_Graph/Bipartite_Graph"
begin

subsection \<open>Specification of the algorithm\<close>

locale edmonds_karp =
  alt_bfs where
  Map_update = Map_update and
  P_update = P_update +
  M: Map_by_Ordered where
  empty = M_empty and
  update = M_update and
  delete = M_delete and
  lookup = M_lookup and
  inorder = M_inorder and
  inv = M_inv for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_empty and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_delete and
  M_lookup and
  M_inorder and
  M_inv
begin

definition is_free_vertex :: "'m \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_free_vertex M v \<equiv> M_lookup M v = None"

definition free_vertices :: "'s \<Rightarrow> 'm \<Rightarrow> 'a list" where
  "free_vertices V M \<equiv> filter (is_free_vertex M) (Set_inorder V)"

text \<open>
To find an augmenting path, we use a modified BFS @{term alt_bfs}, which takes two graphs
@{term G1}, @{term G2} as well as a source vertex @{term src} as input and outputs a parent
relation such that any path from @{term src} induced by the parent relation is a shortest
alternating path, that is, it alternates between edges in @{term G2} and @{term G1} and is shortest
among all such paths.

Let $(@{term L},@{term R},@{term G})$ be a bipartite graph and @{term M} be a matching in @{term G}.
Recall that an augmenting path in @{term G} w.r.t.\ @{term M} is a path between two free vertices
that alternates between edges not in @{term M} and edges in @{term M}. Since @{term G} is bipartite,
any such path is between a free vertex in @{term L} and a free vertex in @{term R} (every augmenting
path in a bipartite graph has odd length, and every path of odd length starting at a vertex in
@{term L} ends at a vertex in @{term R}). This suggests to let @{term src} be a free vertex
@{term v} in @{term L}, @{term G1} be the graph comprising all edges contained in @{term M},
and @{term G2} be the graph comprising all other edges.

As there may not be an augmenting path starting at @{term v} but one starting at another free vertex
in @{term L} and @{term alt_bfs} takes only a single source vertex as input, we augment our input
for @{term alt_bfs} as follows. Let @{term G'} be the graph comprising all edges contained in
@{term M} and @{term G''} be the graph comprising all other edges. We add a new vertex @{term s} to
@{term G'} and connect it to all free vertices in @{term L}. Let @{term p} be a path in graph
@{term G}, that is, not containing @{term s}. We then have that @{term p} is an augmenting path from
a free vertex in @{term L} if and only if @{term "s # p"} is a path alternating between edges in
@{term G'} and @{term G''}, ending at a free vertex in @{term R}.

Moreover, we add another new vertex @{term t} to graph @{term G'} and connect all free vertices in
@{term R} to it. Again, let @{term p} be a path in graph @{term G}, that is, containing neither
@{term s} nor @{term t}. We then have that @{term p} is an augmenting path from a free vertex in
@{term L} if and only if @{term "s # p @ [t]"} is a path alternating between edges in @{term G'} and
@{term G''}.

We now choose the input for @{term alt_bfs} as follows. We set @{term G1} to be @{term G''}, that
is, the graph comprising all edges in graph @{term G} not in matching @{term M}, @{term G2} to be
@{term G'}, that is, the graph comprising all edges in @{term M} as well as two new vertices
@{term s}, @{term t} such that @{term s} is connected to all free vertices in @{term L} and all free
vertices in @{term R} are connected to @{term t}, and @{term src} to be @{term s}.
\<close>

definition G2_1 :: "'m \<Rightarrow> 'n" where
  "G2_1 M \<equiv> List.fold G.insert (M_inorder M) Map_empty"

text \<open>Graph @{term G2_1} is the graph induced by the current matching @{term M}.\<close>

definition G2_2 :: "'s \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'n" where
  "G2_2 L s M \<equiv> List.fold (G.insert_edge s) (free_vertices L M) (G2_1 M)"

text \<open>
Graph @{term G2_2} connects vertex @{term s} in graph @{term G2_1} to every free vertex in
@{term L}.
\<close>

definition G2_3 :: "'s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'n" where
  "G2_3 L R s t M \<equiv> List.fold (G.insert_edge t) (free_vertices R M) (G2_2 L s M)"

text \<open>
Graph @{term G2_3} connects every free vertex in @{term R} to vertex @{term t} in graph
@{term G2_2}.
\<close>

definition G2 :: "'s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'n" where
  "G2 \<equiv> G2_3"

definition G1 :: "'n \<Rightarrow> 'n \<Rightarrow> 'n" where
  "G1 \<equiv> G.difference"

text \<open>
As described above, the algorithm repeatedly finds an augmenting path and augments the matching
until there are no augmenting paths. And there are no augmenting paths if
  \<^enum> either side of the bipartite graph contains no free vertex, or
  \<^enum> @{term alt_bfs} does not find an alternating path between vertices @{term s} and @{term t}.
\<close>

definition done_1 :: "'s \<Rightarrow> 's \<Rightarrow> 'm \<Rightarrow> bool" where
  "done_1 L R M \<equiv> free_vertices L M = [] \<or> free_vertices R M = []"

definition done_2 :: "'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "done_2 t m \<equiv> P_lookup m t = None"

(*
TODO This function is an atrocity. Since augmenting a matching by a path corresponds to taking the
symmetric difference, maybe representing a matching as a set instead of a map would be better?
*)
fun augment :: "'m \<Rightarrow> 'a path \<Rightarrow> 'm" where
  "augment M [] = M" |
  "augment M [u, v] = (M_update v u (M_update u v M))" |
  "augment M (u # v # w # ws) = augment (M_update v u (M_update u v (M_delete w M))) (w # ws)"

function (domintros) loop' where
  "loop' G L R s t M =
   (if done_1 L R M then M
    else if done_2 t (alt_bfs (G1 G (G2 L R s t M)) (G2 L R s t M) s) then M
         else loop' G L R s t (augment M (butlast (tl (rev_follow (alt_bfs (G1 G (G2 L R s t M)) (G2 L R s t M) s) t)))))"
  by pat_completeness simp

(*
TODO Vertices @{term s} and @{term t} should not be part of the input. Instead, in locale
@{locale edmonds_karp} we should assume a function that given a graph @{term G} returns a new
vertex, that is, a vertex not in @{term G}.
*)
definition edmonds_karp :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm" where
  "edmonds_karp G L R s t \<equiv> loop' G L R s t M_empty"

(* TODO Rename. *)
abbreviation m_tbd :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" where
  "m_tbd G L R s t M \<equiv> let G2 = G2 L R s t M in alt_bfs (G1 G G2) G2 s"

(* TODO Rename. *)
abbreviation p_tbd :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'a path" where
  "p_tbd G L R s t M \<equiv> butlast (tl (rev_follow (m_tbd G L R s t M) t))"

(* TODO Rename. *)
abbreviation M_tbd :: "'m \<Rightarrow> 'a graph" where
  "M_tbd M \<equiv> {{u, v} |u v. M_lookup M u = Some v}"

(* TODO Rename. *)
abbreviation P_tbd :: "'a path \<Rightarrow> 'a graph" where
  "P_tbd p \<equiv> set (edges_of_path p)"

abbreviation is_symmetric_Map :: "'m \<Rightarrow> bool" where
  "is_symmetric_Map M \<equiv> \<forall>u v. M_lookup M u = Some v \<longleftrightarrow> M_lookup M v = Some u"

end

subsection \<open>Verification of the correctness of the algorithm\<close>

subsubsection \<open>Assumptions on the input\<close>

text \<open>
Algorithm @{term edmonds_karp.edmonds_karp} expects an input @{term G}, @{term L}, @{term R},
@{term s}, @{term t} such that
  \<^item> $(@{term L},@{term R},@{term G})$ is a bipartite graph, and
  \<^item> @{term s} and @{term t} are two new vertices, that is, vertices not in @{term G},


and the correctness theorem will assume such an input. Let us formally specify these assumptions.
\<close>

locale edmonds_karp_valid_input = edmonds_karp where
  Map_update = Map_update and
  P_update = P_update and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes G :: 'n
  fixes L R :: 's
  fixes s t :: 'a
  assumes symmetric_adjacency_G: "G.symmetric_adjacency' G"
  assumes bipartite_graph: "bipartite_graph (G.E G) (G.S.set L) (G.S.set R)"
  assumes s_not_mem_V: "s \<notin> G.V G"
  assumes t_not_mem_V: "t \<notin> G.V G"
  assumes s_neq_t: "s \<noteq> t"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_valid_input' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "edmonds_karp_valid_input' G L R s t \<equiv>
   edmonds_karp_valid_input
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list Q_snoc
    M_empty M_delete M_lookup M_inorder M_inv
    Map_update P_update M_update
    G L R s t"

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) invar_G:
  shows "G.invar G"
  using symmetric_adjacency_G
  by (intro symmetric_adjacency.invar)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) symmetric_G:
  shows "v \<in> set (G.adjacency_list G u) \<longleftrightarrow> u \<in> set (G.adjacency_list G v)"
  using symmetric_adjacency_G
  by (intro symmetric_adjacency.symmetric)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) finite_E:
  shows "finite (G.E G)"
  using invar_G
  by (intro G.finite_E)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) finite_V:
  shows "finite (G.V G)"
  using invar_G
  by (intro G.finite_V)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) L_union_R_eq_V:
  shows "G.S.set L \<union> G.S.set R = G.V G"
  unfolding G.V_def
  using bipartite_graph
  by (intro bipartite_graph.L_union_R_eq_Vs)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) L_R_disjoint:
  shows "G.S.set L \<inter> G.S.set R = {}"
  using bipartite_graph
  by (intro bipartite_graph.L_R_disjoint)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) L_subset_V:
  shows "G.S.set L \<subseteq> G.V G"
  unfolding G.V_def
  using bipartite_graph
  by (intro bipartite_graph.L_subset_Vs)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) R_subset_V:
  shows "G.S.set R \<subseteq> G.V G"
  unfolding G.V_def
  using bipartite_graph
  by (intro bipartite_graph.R_subset_Vs)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) s_not_mem_L:
  shows "s \<notin> G.S.set L"
  using L_subset_V s_not_mem_V
  by blast

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) s_not_mem_R:
  shows "s \<notin> G.S.set R"
  using R_subset_V s_not_mem_V
  by blast

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) t_not_mem_L:
  shows "t \<notin> G.S.set L"
  using L_subset_V t_not_mem_V
  by blast

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) t_not_mem_R:
  shows "t \<notin> G.S.set R"
  using R_subset_V t_not_mem_V
  by blast

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) graph_G:
  shows "\<forall>e\<in>G.E G. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
proof -
  have "\<forall>e\<in>G.E G. \<exists>u v. e = {u, v}"
    using bipartite_graph
    by (intro bipartite_graph.axioms(1) graph.graph)
  thus ?thesis
    using bipartite_graph
    by (fastforce dest: bipartite_graph.no_loop)
qed

text \<open>
As was the case for locale @{locale alt_bfs}, graph @{term G} is represented as an
@{locale adjacency}, that is, as a @{locale Map_by_Ordered} mapping a vertex to its adjacency, which
is represented as a @{locale Set_by_Ordered}. And sets @{term L} and @{term R} are represented as
@{locale Set_by_Ordered}s.
\<close>

subsubsection \<open>Loop invariants\<close>

text \<open>
Unfolding the definition of algorithm @{term edmonds_karp.edmonds_karp}, we see that recursive
function @{term edmonds_karp.loop'} lies at the heart of the algorithm. It expects an input
@{term G}, @{term L}, @{term R}, @{term s}, @{term t}, @{term M} such that
  \<^item> @{term G}, @{term L}, @{term R}, @{term s}, @{term t} satisfy the assumptions specified above, and
  \<^item> @{term M} is a matching in @{term G}.


Let us now formally specify the assumptions on @{term M}. As @{term M} is the only data structure
that is subject to change from one iteration to the next, these assumptions constitute the loop
invariants of @{term edmonds_karp.loop'}.
\<close>

locale edmonds_karp_invar = edmonds_karp_valid_input where
  Map_update = Map_update and
  P_update = P_update and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes M :: 'm
  assumes invar_M: "M.invar M"
  assumes is_symmetric_Map_M: "is_symmetric_Map M"
  assumes match_imp_edge: "M_lookup M u = Some v \<Longrightarrow> {u, v} \<in> G.E G"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "edmonds_karp_invar' G L R s t \<equiv>
   edmonds_karp_invar
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list Q_snoc
    M_empty M_delete M_lookup M_inorder M_inv
    G L R s t
    Map_update P_update M_update"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) edmonds_karp_invar'' :: "'m \<Rightarrow> bool" where
  "edmonds_karp_invar'' \<equiv> edmonds_karp_invar' G L R s t"

context \<^marker>\<open>tag invisible\<close> edmonds_karp
begin
sublocale \<^marker>\<open>tag invisible\<close> M: graph "M_tbd M"
proof (standard, goal_cases)
  case 1
  then show ?case
    by auto
qed
end \<^marker>\<open>tag invisible\<close>

lemma (in edmonds_karp_invar) M_tbd_subset_E:
  shows "M_tbd M \<subseteq> G.E G"
proof -
  { fix u v
    assume "{u, v} \<in> M_tbd M"
    hence "M_lookup M u = Some v"
      using is_symmetric_Map_M
      by (auto simp add: doubleton_eq_iff)
    hence "{u, v} \<in> G.E G"
      by (intro match_imp_edge) }
  thus ?thesis
    using M.graph
    by blast
qed

text \<open>
Matching @{term M} is represented as a @{locale Map_by_Ordered} mapping a vertex to another
vertex--its match.
\<close>

lemma (in edmonds_karp_invar) matching_M_tbd:
  shows "matching (M_tbd M)"
proof -
  { fix u v x y
    assume assm:
      "{u, v} \<in> M_tbd M"
      "{x, y} \<in> M_tbd M"
      "{u, v} \<noteq> {x, y}"
      "{u, v} \<inter> {x, y} \<noteq> {}"
    hence
      "M_lookup M u = Some v"
      "M_lookup M x = Some y"
      using assm(1, 2) is_symmetric_Map_M
      by (auto simp add: doubleton_eq_iff)
    moreover hence "u = x"
      using assm(3, 4) is_symmetric_Map_M
      by force
    moreover hence "v \<noteq> y"
      using assm(3)
      by fast
    ultimately have False
      by simp }
  thus ?thesis
    unfolding matching_def
    using M.graph
    by blast
qed

lemma (in edmonds_karp_invar) graph_matching_M_tbd:
  shows "graph_matching (G.E G) (M_tbd M)"
  using matching_M_tbd M_tbd_subset_E
  by fastforce

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar) finite_M_tbd:
  shows "finite (M_tbd M)"
  using M_tbd_subset_E finite_E
  by (rule finite_subset)

text \<open>
To verify the correctness of loop @{term edmonds_karp.loop'}, we need to show that
  \<^enum> the loop invariants are satisfied prior to the first iteration of the loop, and that
  \<^enum> the loop invariants are maintained.


Let us start with the former, that is, let us prove that the empty matching satisfies the loop
invariants.
\<close>

lemma (in edmonds_karp_valid_input) edmonds_karp_invar_empty:
  shows "edmonds_karp_invar'' M_empty"
proof (standard, goal_cases)
  case 1
  show ?case
    using M.invar_empty
    .
next
  case 2
  show ?case
    by (simp add: M.map_empty)
next
  case (3 u v)
  thus ?case
    by (simp add: M.map_empty)
qed

text \<open>
Let us now verify that the loop invariants are maintained, that is, if they hold at the start of an
iteration of loop @{term edmonds_karp.loop'}, then they will also hold at the end. For this, we
verify the correctness of the body of the loop, that is,
  \<^enum> if there is an augmenting path, then the algorithm will find one, and
  \<^enum> given an augmenting path, the algorithm correctly augments the current matching.


Let us start with the former.
\<close>

locale edmonds_karp_invar_not_done_1 = edmonds_karp_invar where
  Map_update = Map_update and
  P_update = P_update and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes not_done_1: "\<not> done_1 L R M"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_not_done_1' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "edmonds_karp_invar_not_done_1' G L R s t M \<equiv>
   edmonds_karp_invar_not_done_1
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list Q_snoc
    M_empty M_delete M_lookup M_inorder M_inv
    G L R s t M
    Map_update P_update M_update"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) edmonds_karp_invar_not_done_1'' :: "'m \<Rightarrow> bool" where
  "edmonds_karp_invar_not_done_1'' \<equiv> edmonds_karp_invar_not_done_1' G L R s t"

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_not_done_1I:
  assumes "edmonds_karp_invar' G L R s t M"
  assumes "\<not> done_1 L R M"
  shows "edmonds_karp_invar_not_done_1' G L R s t M"
  using assms
  by (simp add: edmonds_karp_invar_not_done_1_def edmonds_karp_invar_not_done_1_axioms_def)

locale edmonds_karp_invar_not_done_2 = edmonds_karp_invar_not_done_1 where
  Map_update = Map_update and
  P_update = P_update and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes not_done_2: "\<not> done_2 t (m_tbd G L R s t M)"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_not_done_2' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "edmonds_karp_invar_not_done_2' G L R s t M \<equiv>
   edmonds_karp_invar_not_done_2
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list Q_snoc
    M_empty M_delete M_lookup M_inorder M_inv
    G L R s t M
    Map_update P_update M_update"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) edmonds_karp_invar_not_done_2'' :: "'m \<Rightarrow> bool" where
  "edmonds_karp_invar_not_done_2'' \<equiv> edmonds_karp_invar_not_done_2' G L R s t"

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_not_done_2I:
  assumes "edmonds_karp_invar_not_done_1' G L R s t M"
  assumes "\<not> done_2 t (m_tbd G L R s t M)"
  shows "edmonds_karp_invar_not_done_2' G L R s t M"
  using assms
  by (simp add: edmonds_karp_invar_not_done_2_def edmonds_karp_invar_not_done_2_axioms_def)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_not_done_2I_2:
  assumes "edmonds_karp_invar' G L R s t M"
  assumes "\<not> done_1 L R M"
  assumes "\<not> done_2 t (m_tbd G L R s t M)"
  shows "edmonds_karp_invar_not_done_2' G L R s t M"
  using assms
  by
    (simp add:
     edmonds_karp_invar_not_done_1_def edmonds_karp_invar_not_done_1_axioms_def
     edmonds_karp_invar_not_done_2_def edmonds_karp_invar_not_done_2_axioms_def)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) mem_set_free_verticesI:
  assumes "v \<in> G.S.set V"
  assumes "is_free_vertex M v"
  shows "v \<in> set (free_vertices V M)"
  using assms
  by (simp add: free_vertices_def G.S.set_def)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) set_free_vertices_subset:
  shows "set (free_vertices V M) \<subseteq> G.S.set V"
  by (simp add: free_vertices_def G.S.set_def)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) invar_G2_1:
  shows "G.invar (G2_1 M)"
  using G.invar_empty
  by (auto simp add: G2_1_def intro: G.invar_fold_insert)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_G2_1_cong:
  assumes "M.invar M"
  shows "set (G.adjacency_list (G2_1 M) u) = (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {v})"
proof -
  { fix v
    have
      "v \<in> set (G.adjacency_list (G2_1 M) u) \<longleftrightarrow>
       v \<in> set (G.adjacency_list Map_empty u) \<union> (\<Union>p\<in>set (M_inorder M). if u = fst p then {snd p} else {})"
      using G.invar_empty
      by (simp add: G2_1_def G.adjacency_fold_insert_cong)
    also have "... \<longleftrightarrow> v \<in> (\<Union>p\<in>set (M_inorder M). if u = fst p then {snd p} else {})"
      by (simp add: G.adjacency_list_def G.M.map_empty)
    also have "... \<longleftrightarrow> (\<exists>p\<in>set (M_inorder M). u = fst p \<and> v = snd p)"
      by auto
    also have "... \<longleftrightarrow> (u, v) \<in> set (M_inorder M)"
      by (metis prod.collapse fst_conv snd_conv)
    also have "... \<longleftrightarrow> M_lookup M u = Some v"
      using assms
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    finally have "v \<in> set (G.adjacency_list (G2_1 M) u) \<longleftrightarrow> M_lookup M u = Some v"
      . }
  thus ?thesis
    by (force split: option.splits(2))
qed

text \<open>
Assuming appropriate input for algorithm @{term alt_bfs.alt_bfs}, the statement follows from the
correctness of @{term alt_bfs.alt_bfs}. Hence, we mainly have to show that our construction of
@{term edmonds_karp.G1}, @{term edmonds_karp.G2} is correct and that it satisfies the input
assumptions of @{term alt_bfs.alt_bfs}.

We first prove that graph @{term edmonds_karp.G2} comprises all edges in the current matching
@{term M} as well as vertices @{term s}, @{term t} that are connected to all free vertices in
@{term L}, @{term R}, respectively.
\<close>

lemma (in edmonds_karp) E2_1_cong:
  assumes "M.invar M"
  shows "G.E (G2_1 M) = M_tbd M"
proof -
  { fix u v
    have
      "{u, v} \<in> G.E (G2_1 M) \<longleftrightarrow>
       u \<in> set (G.adjacency_list (G2_1 M) v) \<or> v \<in> set (G.adjacency_list (G2_1 M) u)"
      by (auto simp add: G.E_def doubleton_eq_iff)
    also have "... \<longleftrightarrow> M_lookup M v = Some u \<or> M_lookup M u = Some v"
      using assms
      by (auto simp add: adjacency_G2_1_cong split: option.split)
    also have "... \<longleftrightarrow> {u, v} \<in> M_tbd M"
      by (auto simp add: doubleton_eq_iff)
    finally have "{u, v} \<in> G.E (G2_1 M) \<longleftrightarrow> {u, v} \<in> M_tbd M"
      . }
  thus ?thesis
    by (intro graphs_eqI) (auto simp add: G.E_def graph_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) symmetric_adjacency_G2_1:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  shows "G.symmetric_adjacency' (G2_1 M)"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G2_1
    .
next
  case 2
  show ?case
    using assms
    by (fastforce simp add: adjacency_G2_1_cong split: option.splits(2))
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) invar_G2_2:
  shows "G.invar (G2_2 L s M)"
  using invar_G2_1
  by (auto simp add: G2_2_def intro: G.invar_fold_insert_edge)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_G2_2_cong:
  shows
    "set (G.adjacency_list (G2_2 L s M) u) =
     set (G.adjacency_list (G2_1 M) u) \<union>
     (\<Union>v\<in>set (free_vertices L M). if u = s then {v} else if u = v then {s} else {})"
  using invar_G2_1
  by (simp add: G2_2_def G.adjacency_fold_insert_edge_cong)

lemma (in edmonds_karp) E2_2_cong:
  shows "G.E (G2_2 L s M) = G.E (G2_1 M) \<union> {{s, v} |v. v \<in> set (free_vertices L M)}"
  using invar_G2_1
  by (simp add: G2_2_def G.E_fold_insert_edge_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) symmetric_adjacency_G2_2:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  shows "G.symmetric_adjacency' (G2_2 L s M)"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G2_2
    .
next
  case (2 v u)
  have
    "v \<in> set (G.adjacency_list (G2_2 L s M) u) \<longleftrightarrow>
     v \<in> set (G.adjacency_list (G2_1 M) u) \<or>
     (v \<in> set (free_vertices L M) \<and> u = s) \<or>
     (u \<in> set (free_vertices L M) \<and> v = s)"
    by (auto simp add: adjacency_G2_2_cong)
  also have
    "... \<longleftrightarrow>
     u \<in> set (G.adjacency_list (G2_1 M) v) \<or>
     (v \<in> set (free_vertices L M) \<and> u = s) \<or>
     (u \<in> set (free_vertices L M) \<and> v = s)"
    using assms
    by (simp add: symmetric_adjacency.symmetric[OF symmetric_adjacency_G2_1])
  also have "... \<longleftrightarrow> u \<in> set (G.adjacency_list (G2_2 L s M) v)"
    by (auto simp add: adjacency_G2_2_cong)
  finally show ?case
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) invar_G2_3:
  shows "G.invar (G2_3 L R s t M)"
  using invar_G2_2
  by (auto simp add: G2_3_def intro: G.invar_fold_insert_edge)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_G2_3_cong:
  shows
    "set (G.adjacency_list (G2_3 L R s t M) u) =
     set (G.adjacency_list (G2_2 L s M) u) \<union>
     (\<Union>v\<in>set (free_vertices R M). if u = t then {v} else if u = v then {t} else {})"
  using invar_G2_2
  by (simp add: G2_3_def G.adjacency_fold_insert_edge_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_G2_3_G2_1_cong:
  shows
    "set (G.adjacency_list (G2_3 L R s t M) u) =
     set (G.adjacency_list (G2_1 M) u) \<union>
     (\<Union>v\<in>set (free_vertices L M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices R M). if u = t then {v} else if u = v then {t} else {})"
  by (simp add: adjacency_G2_3_cong adjacency_G2_2_cong)

lemma (in edmonds_karp) E2_3_cong:
  shows "G.E (G2_3 L R s t M) = G.E (G2_2 L s M) \<union> {{t, v} |v. v \<in> set (free_vertices R M)}"
  using invar_G2_2
  by (simp add: G2_3_def G.E_fold_insert_edge_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) E2_3_E2_1_cong:
  shows
    "G.E (G2_3 L R s t M) =
     G.E (G2_1 M) \<union>
     {{s, v} |v. v \<in> set (free_vertices L M)} \<union>
     {{t, v} |v. v \<in> set (free_vertices R M)}"
  by (simp add: E2_3_cong E2_2_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) E2_3_M_tbd_cong:
  assumes "M.invar M"
  shows
    "G.E (G2_3 L R s t M) =
     M_tbd M \<union>
     {{s, v} |v. v \<in> set (free_vertices L M)} \<union>
     {{t, v} |v. v \<in> set (free_vertices R M)}"
  using assms
  by (simp add: E2_3_E2_1_cong E2_1_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) symmetric_adjacency_G2_3:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  shows "G.symmetric_adjacency' (G2_3 L R s t M)"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G2_3
    .
next
  case (2 v u)
  have
    "v \<in> set (G.adjacency_list (G2_3 L R s t M) u) \<longleftrightarrow>
     v \<in> set (G.adjacency_list (G2_2 L s M) u) \<or>
     (v \<in> set (free_vertices R M) \<and> u = t) \<or>
     (u \<in> set (free_vertices R M) \<and> v = t)"
    by (auto simp add: adjacency_G2_3_cong)
  also have
    "... \<longleftrightarrow>
     u \<in> set (G.adjacency_list (G2_2 L s M) v) \<or>
     (v \<in> set (free_vertices R M) \<and> u = t) \<or>
     (u \<in> set (free_vertices R M) \<and> v = t)"
    using assms
    by (simp add: symmetric_adjacency.symmetric[OF symmetric_adjacency_G2_2])
  also have "... \<longleftrightarrow> u \<in> set (G.adjacency_list (G2_3 L R s t M) v)"
    by (auto simp add: adjacency_G2_3_cong)
  finally show ?case
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) invar_G2:
  shows "G.invar (G2 L R s t M)"
  unfolding G2_def
  using invar_G2_3
  .

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_G2_cong:
  assumes "M.invar M"
  shows
    "set (G.adjacency_list (G2 L R s t M) u) =
     (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {v}) \<union>
     (\<Union>v\<in>set (free_vertices L M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices R M). if u = t then {v} else if u = v then {t} else {})"
  using assms
  by (simp add: G2_def adjacency_G2_3_G2_1_cong adjacency_G2_1_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_G2_s_cong:
  assumes "s \<notin> G.S.set R"
  assumes "s \<noteq> t"
  assumes "M.invar M"
  assumes "M_lookup M s = None"
  shows "set (G.adjacency_list (G2 L R s t M) s) = set (free_vertices L M)"
  using assms set_free_vertices_subset
  by (auto simp add: adjacency_G2_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_G2_t_cong:
  assumes "t \<notin> G.S.set L"
  assumes "s \<noteq> t"
  assumes "M.invar M"
  assumes "M_lookup M t = None"
  shows "set (G.adjacency_list (G2 L R s t M) t) = set (free_vertices R M)"
  using assms set_free_vertices_subset
  by (auto simp add: adjacency_G2_cong)

lemma (in edmonds_karp) E2_cong:
  assumes "M.invar M"
  shows
    "G.E (G2 L R s t M) =
     M_tbd M \<union>
     {{s, v} |v. v \<in> set (free_vertices L M)} \<union>
     {{t, v} |v. v \<in> set (free_vertices R M)}"
  unfolding G2_def
  using assms
  by (intro E2_3_M_tbd_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) symmetric_adjacency_G2:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  shows "G.symmetric_adjacency' (G2 L R s t M)"
  unfolding G2_def
  using assms
  by (intro symmetric_adjacency_G2_3)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) invar_G1:
  assumes "G.invar G"
  assumes "G.invar G'"
  shows "G.invar (G1 G G')"
  unfolding G1_def
  using assms
  by (intro G.invar_difference)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_G1_cong:
  assumes "G.invar G"
  assumes "G.invar G'"
  shows
    "set (G.adjacency_list (G1 G G') v) =
     set (G.adjacency_list G v) - set (G.adjacency_list G' v)"
  unfolding G1_def
  using assms
  by (intro G.adjacency_difference_cong)

text \<open>
We now show that graph @{term edmonds_karp.G1} comprises all edges not in the current matching.
\<close>

lemma (in edmonds_karp) E1_cong:
  assumes "G.symmetric_adjacency' G"
  assumes "G.symmetric_adjacency' G'"
  shows "G.E (G1 G G') = G.E G - G.E G'"
  unfolding G1_def
  using assms
  by (intro G.E_difference_cong)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) symmetric_adjacency_G1:
  assumes "G.symmetric_adjacency' G"
  assumes "G.symmetric_adjacency' G'"
  shows "G.symmetric_adjacency' (G1 G G')"
  unfolding G1_def
  using assms
  by (intro G.symmetric_adjacency_difference)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) adjacency_union_G1_G2_cong:
  assumes "G.symmetric_adjacency' G"
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "M_tbd M \<subseteq> G.E G"
  shows
    "set (G.adjacency_list (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) u) =
     set (G.adjacency_list G u) \<union>
     (\<Union>v\<in>set (free_vertices L M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices R M). if u = t then {v} else if u = v then {t} else {})"
proof -
  have
    "set (G.adjacency_list (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) u) =
     set (G.adjacency_list (G1 G (G2 L R s t M)) u) \<union> set (G.adjacency_list (G2 L R s t M) u)"
    using assms(1) invar_G2
    by (intro invar_G1 G.adjacency_union_cong) (rule symmetric_adjacency.invar)
  also have "... = set (G.adjacency_list G u) \<union> set (G.adjacency_list (G2 L R s t M) u)"
    using assms(1) invar_G2
    by (auto simp add: adjacency_G1_cong dest: symmetric_adjacency.invar)
  also have
    "... =
     set (G.adjacency_list G u) \<union>
     (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {v}) \<union>
     (\<Union>v\<in>set (free_vertices L M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices R M). if u = t then {v} else if u = v then {t} else {})"
    unfolding adjacency_G2_cong[OF assms(2)]
    by blast
  also have
    "... =
     set (G.adjacency_list G u) \<union>
     (\<Union>v\<in>set (free_vertices L M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices R M). if u = t then {v} else if u = v then {t} else {})"
    using assms(1, 4)
    by (fastforce simp add: symmetric_adjacency.mem_adjacency_iff_edge split: option.splits(2))
  finally show ?thesis
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) E_union_G1_G2_cong:
  assumes "G.symmetric_adjacency' G"
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "M_tbd M \<subseteq> G.E G"
  shows
    "G.E (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) =
     G.E G \<union> {{s, v} |v. v \<in> set (free_vertices L M)} \<union> {{t, v} |v. v \<in> set (free_vertices R M)}"
proof -
  let ?G2 = "G2 L R s t M"
  let ?G1 = "G1 G ?G2"
  have "G.E (G.union ?G1 ?G2) = G.E ?G1 \<union> G.E ?G2"
    using assms(1) invar_G2
    by (intro invar_G1 G.E_union_cong) (rule symmetric_adjacency.invar)
  also have "... = G.E G \<union> G.E ?G2"
    using assms symmetric_adjacency_G2
    by (simp add: E1_cong)
  also have
    "... =
     G.E G \<union>
     M_tbd M \<union>
     {{s, v} |v. v \<in> set (free_vertices L M)} \<union>
     {{t, v} |v. v \<in> set (free_vertices R M)}"
    using assms(2)
    by (auto simp add: E2_cong)
  also have
    "... =
     G.E G \<union>
     {{s, v} |v. v \<in> set (free_vertices L M)} \<union>
     {{t, v} |v. v \<in> set (free_vertices R M)}"
    using assms(4)
    by auto
  finally show ?thesis
    .
qed

text \<open>
One point to note is that, given graphs @{term edmonds_karp.G1}, @{term edmonds_karp.G2}, algorithm
@{term alt_bfs.alt_bfs} finds alternating paths in the union of @{term edmonds_karp.G1} and
@{term edmonds_karp.G2}. We, on the other hand, are interested in paths in the input graph
@{term G}, which, due to our augmentation by vertices @{term s} and @{term t}, is not equal to the
union of @{term edmonds_karp.G1} and @{term edmonds_karp.G2}. So let us relate the union to the
input graph.
\<close>

lemma (in edmonds_karp_invar) E_union_G1_G2_cong:
  shows
    "G.E (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) =
     G.E G \<union> {{s, v} |v. v \<in> set (free_vertices L M)} \<union> {{t, v} |v. v \<in> set (free_vertices R M)}"
  using symmetric_adjacency_G invar_M is_symmetric_Map_M M_tbd_subset_E
  by (intro E_union_G1_G2_cong)

lemma (in edmonds_karp_invar_not_done_1) V_union_G1_G2_cong:
  shows "G.V (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) = G.V G \<union> {s} \<union> {t}"
proof -
  let ?G2 = "G2 L R s t M"
  let ?G1 = "G1 G (G2 L R s t M)"
  have
    "G.V (G.union ?G1 ?G2) =
     G.V G \<union> {s} \<union> set (free_vertices L M) \<union> {t} \<union> set (free_vertices R M)"
  proof -
    have
      "G.E (G.union ?G1 ?G2) =
       G.E G \<union> {{s, v} |v. v \<in> set (free_vertices L M)} \<union> {{t, v} |v. v \<in> set (free_vertices R M)}"
      using E_union_G1_G2_cong
      .
    moreover have "Vs {{s, v} |v. v \<in> set (free_vertices L M)} = {s} \<union> set (free_vertices L M)"
    proof -
      have "set (free_vertices L M) \<noteq> {}"
        using not_done_1
        by (simp add: done_1_def)
      thus ?thesis
        unfolding ex_in_conv[symmetric] Vs_def
        by auto
    qed
    moreover have "Vs {{t, v} |v. v \<in> set (free_vertices R M)} = {t} \<union> set (free_vertices R M)"
    proof -
      have "set (free_vertices R M) \<noteq> {}"
        using not_done_1
        by (simp add: done_1_def)
      thus ?thesis
        unfolding ex_in_conv[symmetric] Vs_def
        by auto
    qed
    ultimately show ?thesis
      by (simp add: Vs_def G.V_def)
  qed
  moreover have "set (free_vertices L M) \<subseteq> G.V G"
    using set_free_vertices_subset L_subset_V
    by (rule subset_trans)
  moreover have "set (free_vertices R M) \<subseteq> G.V G"
    using set_free_vertices_subset R_subset_V
    by (rule subset_trans)
  ultimately show ?thesis
    by auto
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) symmetric_adjacency_union_G1_G2:
  assumes "G.symmetric_adjacency' G"
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  shows "G.symmetric_adjacency' (G.union (G1 G (G2 L R s t M)) (G2 L R s t M))"
  using assms
  by (intro symmetric_adjacency_G2 symmetric_adjacency_G1 G.symmetric_adjacency_union)

text \<open>
We are now able to show that @{term edmonds_karp.G1}, @{term edmonds_karp.G2}, @{term s} constitutes
a valid input for algorithm @{term alt_bfs.alt_bfs}.
\<close>

lemma (in edmonds_karp_invar_not_done_1) alt_bfs_valid_input:
  shows "alt_bfs_valid_input' (G1 G (G2 L R s t M)) (G2 L R s t M) s"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G invar_G2
    by (intro invar_G1)
next
  case 2
  show ?case
    using invar_G2
    .
next
  case (3 v u)
  show ?case
    using symmetric_adjacency_G invar_M is_symmetric_Map_M
    by (auto intro: symmetric_adjacency_G2 dest: symmetric_adjacency_G1 symmetric_adjacency.symmetric)
next
  case (4 v u)
  show ?case
    using invar_M is_symmetric_Map_M
    by (auto dest: symmetric_adjacency_G2 symmetric_adjacency.symmetric)
next
  case 5
  show ?case
    using symmetric_adjacency_G invar_M is_symmetric_Map_M symmetric_adjacency_G2
    by (auto simp add: E1_cong)
next
  case 6
  have
    "bipartite_graph
      (G.E (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)))
      (G.S.set L \<union> {t})
      (G.S.set R \<union> {s})"
  proof (standard, goal_cases)
    case 1
    show ?case
      by (auto simp add: G.E_def)
  next
    case 2
    have "G.V (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) = G.V G \<union> {s} \<union> {t}"
      by (intro L_subset_V R_subset_V V_union_G1_G2_cong)
    thus ?case
      by (auto simp add: L_union_R_eq_V G.V_def)
  next
    case 3
    show ?case
      using s_not_mem_L t_not_mem_R s_neq_t
      by (simp add: L_R_disjoint)
  next
    case (4 u v)
    then consider
      (1) "{u, v} \<in> G.E G" |
      (2) "{u, v} \<in> {{s, v} |v. v \<in> set (free_vertices L M)}" |
      (3) "{u, v} \<in> {{t, v} |v. v \<in> set (free_vertices R M)}"
      by (auto simp add: E_union_G1_G2_cong)
    thus ?case
    proof (cases)
      case 1
      hence "u \<in> G.S.set L \<union> {t} \<longleftrightarrow> u \<in> G.S.set L"
        using t_not_mem_V
        by (auto simp add: G.V_def)
      also have "... \<longleftrightarrow> v \<in> G.S.set R"
        using bipartite_graph 1
        by (intro bipartite_graph.endpoints)
      also have "... \<longleftrightarrow> v \<in> G.S.set R \<union> {s}"
        using 1 s_not_mem_V
        by (auto simp add: G.V_def)
      finally show ?thesis
        .
    next
      case 2
      hence "u \<in> G.S.set L \<union> {t} \<longleftrightarrow> u \<in> set (free_vertices L M) \<and> v = s"
        using s_not_mem_L s_neq_t set_free_vertices_subset
        by (auto simp add: doubleton_eq_iff)
      also have "... \<longleftrightarrow> v \<in> G.S.set R \<union> {s}"
        using 2 set_free_vertices_subset L_R_disjoint
        by (auto simp add: doubleton_eq_iff)
      finally show ?thesis
        .
    next
      case 3
      hence "u \<in> G.S.set L \<union> {t} \<longleftrightarrow> u = t \<and> v \<in> set (free_vertices R M)"
        using set_free_vertices_subset L_R_disjoint
        by (auto simp add: doubleton_eq_iff)
      also have "... \<longleftrightarrow> v \<in> G.S.set R \<union> {s}"
        using 3 t_not_mem_R s_neq_t set_free_vertices_subset
        by (auto simp add: doubleton_eq_iff)
      finally show ?thesis
        .
    qed
  qed
  thus ?case
    by (intro bipartite_graph.no_odd_cycle)
next
  case 7
  obtain v where
    "v \<in> set (free_vertices L M)"
    using not_done_1
    by (fastforce simp add: done_1_def)
  thus ?case
    unfolding G.V_def
    using invar_M
    by (intro edges_are_Vs) (auto simp add: E2_cong)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_1) parent:
  shows "Parent_Relation.parent (P_lookup (m_tbd G L R s t M))"
proof -
  have
    "alt_bfs_invar'
      (G1 G (G2 L R s t M))
      (G2 L R s t M)
      s
      (alt_loop (G1 G (G2 L R s t M)) (G2 L R s t M) s (init s))"
    using alt_bfs_valid_input
    by (intro alt_bfs_invar_alt_loop_init)
  thus ?thesis
    unfolding alt_bfs_def
    by (metis alt_bfs_invar.axioms(2))
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_1) hd_rev_follow_eq_s:
  assumes "P_lookup (m_tbd G L R s t M) v \<noteq> None"
  shows "hd (rev_follow (m_tbd G L R s t M) v) = s"
proof -
  have
    "alt_bfs_invar'
      (G1 G (G2 L R s t M))
      (G2 L R s t M)
      s
      (alt_loop (G1 G (G2 L R s t M)) (G2 L R s t M) s (init s))"
    using alt_bfs_valid_input
    by (intro alt_bfs_invar_alt_loop_init)
  thus ?thesis
    using assms
    unfolding alt_bfs_def
    by (meson is_discovered_def alt_bfs_invar.hd_rev_follow_eq_src)
qed

text \<open>
Hence, by the soundness of algorithm @{term alt_bfs.alt_bfs}, any path from vertex @{term s} induced
by the parent relation output by @{term alt_bfs.alt_bfs} is a shortest alternating path in the union
of graphs @{term edmonds_karp.G1} and @{term edmonds_karp.G2}.
\<close>

lemma (in edmonds_karp_invar_not_done_1) is_shortest_alt_path_rev_follow:
  assumes "P_lookup (m_tbd G L R s t M) v \<noteq> None"
  shows
    "is_shortest_alt_path
      (\<lambda>e. e \<in> G.E (G2 L R s t M))
      (Not \<circ> (\<lambda>e. e \<in> G.E (G2 L R s t M)))
      (G.E (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)))
      (rev_follow (m_tbd G L R s t M) v) s v"
  using alt_bfs_valid_input assms
  unfolding alt_bfs_def
  by (metis alt_bfs_valid_input.alt_bfs_invar_init is_discovered_def alt_bfs_valid_input.soundness)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar) lookup_s_eq_None:
  shows "M_lookup M s = None"
proof -
  { fix v
    assume "M_lookup M s = Some v"
    hence "{s, v} \<in> G.E G"
      by (intro match_imp_edge)
    hence "s \<in> G.V G"
      unfolding G.V_def
      by (intro edges_are_Vs)
    hence False
      using s_not_mem_V
      by auto }
  thus ?thesis
    by fastforce
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar) adjacency_union_G1_G2_s_cong:
  shows
    "set (G.adjacency_list (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) s) =
     set (free_vertices L M)"
proof -
  have
    "set (G.adjacency_list (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) s) =
     set (G.adjacency_list (G1 G (G2 L R s t M)) s) \<union> set (G.adjacency_list (G2 L R s t M) s)"
    using invar_G invar_G2
    by (intro invar_G1 G.adjacency_union_cong)
  also have "... = set (G.adjacency_list G s) \<union> set (G.adjacency_list (G2 L R s t M) s)"
    using invar_G invar_G2
    by (simp add: adjacency_G1_cong)
  also have "... = set (G.adjacency_list (G2 L R s t M) s)"
  proof -
    { fix v
      assume "v \<in> set (G.adjacency_list G s)"
      hence "{s, v} \<in> G.E G"
        using symmetric_adjacency_G
        by (simp add: symmetric_adjacency.mem_adjacency_iff_edge)
      hence "s \<in> G.V G"
        unfolding G.V_def
        by (intro edges_are_Vs)
      hence False
        using s_not_mem_V
        by auto }
    thus ?thesis
      by blast
  qed
  also have "... = set (free_vertices L M)"
    using s_not_mem_R s_neq_t invar_M lookup_s_eq_None
    by (intro adjacency_G2_s_cong)
  finally show ?thesis
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar) lookup_t_eq_None:
  shows "M_lookup M t = None"
proof -
  { fix v
    assume "M_lookup M t = Some v"
    hence "{t, v} \<in> G.E G"
      by (intro match_imp_edge)
    hence "t \<in> G.V G"
      unfolding G.V_def
      by (intro edges_are_Vs)
    hence False
      using t_not_mem_V
      by auto }
  thus ?thesis
    by fastforce
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar) adjacency_union_G1_G2_t_cong:
  shows
    "set (G.adjacency_list (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) t) =
     set (free_vertices R M)"
proof -
  have
    "set (G.adjacency_list (G.union (G1 G (G2 L R s t M)) (G2 L R s t M)) t) =
     set (G.adjacency_list (G1 G (G2 L R s t M)) t) \<union> set (G.adjacency_list (G2 L R s t M) t)"
    using invar_G invar_G2
    by (intro invar_G1 G.adjacency_union_cong)
  also have "... = set (G.adjacency_list G t) \<union> set (G.adjacency_list (G2 L R s t M) t)"
    using invar_G invar_G2
    by (simp add: adjacency_G1_cong)
  also have "... = set (G.adjacency_list (G2 L R s t M) t)"
  proof -
    { fix v
      assume "v \<in> set (G.adjacency_list G t)"
      hence "{t, v} \<in> G.E G"
        using symmetric_adjacency_G
        by (simp add: symmetric_adjacency.mem_adjacency_iff_edge)
      hence "t \<in> G.V G"
        unfolding G.V_def
        by (intro edges_are_Vs)
      hence False
        using t_not_mem_V
        by auto }
    thus ?thesis
      by blast
  qed
  also have "... = set (free_vertices R M)"
    using t_not_mem_L s_neq_t invar_M lookup_t_eq_None
    by (intro adjacency_G2_t_cong)
  finally show ?thesis
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) rev_followE:
  obtains p u v where
    "rev_follow (m_tbd G L R s t M) t = s # u # p @ [v, t]"
proof (cases "rev_follow (m_tbd G L R s t M) t")
  case Nil
  thus ?thesis
    using parent
    by (auto dest: rev_follow_non_empty)
next
  case p: (Cons x xs)
  let ?G = "G.union (G1 G (G2 L R s t M)) (G2 L R s t M)"
  let ?p = "rev_follow (m_tbd G L R s t M) t"
  have path_p: "path (G.E ?G) ?p"
    using not_done_2
    unfolding done_2_def
    by
      (intro is_shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(1))
      (rule is_shortest_alt_path_rev_follow)
  have hd_p_eq_s: "hd ?p = s"
    using not_done_2
    by (auto simp add: done_2_def intro: hd_rev_follow_eq_s)
  have last_p_eq_t: "last ?p = t"
    using parent
    by (intro last_rev_follow)
  show ?thesis
  proof (cases xs)
    case Nil
    hence "?p = [x]"
      by (simp add: p)
    hence
      "x = s"
      "x = t"
      using hd_p_eq_s last_p_eq_t
      by simp+
    thus ?thesis
      using s_neq_t
      by force
  next
    case xs: (Cons y ys)
    show ?thesis
    proof (cases "rev ys")
      case Nil
      hence "?p = [x, y]"
        by (simp add: p xs)
      moreover hence
        "x = s"
        "y = t"
        using hd_p_eq_s last_p_eq_t
        by simp+
      ultimately have "{s, t} \<in> (G.E ?G)"
        using path_p
        by simp
      then consider
        (1) "{s, t} \<in> G.E G" |
        (2) "{s, t} \<in> {{s, v} |v. v \<in> set (free_vertices L M)}" |
        (3) "{s, t} \<in> {{t, v} |v. v \<in> set (free_vertices R M)}"
        by (auto simp add: E_union_G1_G2_cong)
      thus ?thesis
      proof (cases)
        case 1
        thus ?thesis
          using s_not_mem_V
          by (auto simp add: G.V_def intro: edges_are_Vs)
      next
        case 2
        thus ?thesis
          using t_not_mem_L set_free_vertices_subset
          by (force simp add: doubleton_eq_iff)
      next
        case 3
        thus ?thesis
          using s_not_mem_R set_free_vertices_subset
          by (force simp add: doubleton_eq_iff)
      qed
    next
      case (Cons z zs)
      hence ys: "ys = rev zs @ [z]"
        by simp
      show ?thesis
      proof (cases zs)
        case Nil
        hence "?p = x # y # [z]"
          by (simp add: p xs ys)
        moreover hence
          "x = s"
          "z = t"
          using hd_p_eq_s last_p_eq_t
          by simp+
        ultimately have
          "{s, y} \<in> (G.E ?G)"
          "{y, t} \<in> (G.E ?G)"
          using path_p
          by simp+
        hence
          "{s, y} \<in> (G.E ?G)"
          "{t, y} \<in> (G.E ?G)"
          by (metis doubleton_eq_iff)+
        hence
          "y \<in> set (G.adjacency_list ?G s)"
          "y \<in> set (G.adjacency_list ?G t)"
          unfolding symmetric_adjacency.mem_adjacency_iff_edge[OF symmetric_adjacency_union_G1_G2[OF symmetric_adjacency_G invar_M is_symmetric_Map_M]]
          .
        hence
          "y \<in> set (free_vertices L M)"
          "y \<in> set (free_vertices R M)"
          by (simp_all add: adjacency_union_G1_G2_s_cong adjacency_union_G1_G2_t_cong)
        hence
          "y \<in> G.S.set L"
          "y \<in> G.S.set R"
          using set_free_vertices_subset
          by blast+
        thus ?thesis
          using L_R_disjoint
          by blast
      next
        case (Cons z' zs')
        hence "ys = rev zs' @ [z', z]"
          by (simp add: ys)
        hence "?p = x # y # rev zs' @ [z', z]"
          by (simp add: p xs)
        moreover hence
          "x = s"
          "z = t"
          using hd_p_eq_s last_p_eq_t
          by simp+
        ultimately show ?thesis
          by (blast intro: that)
      qed
    qed
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) length_rev_follow_geq_4:
  shows "4 \<le> length (rev_follow (m_tbd G L R s t M) t)"
  using rev_followE
  by fastforce

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) length_p_tbd_geq_2:
  shows "2 \<le> length (p_tbd G L R s t M)"
proof -
  have "4 \<le> length (rev_follow (m_tbd G L R s t M) t)"
    using length_rev_follow_geq_4
    .
  moreover hence "length (p_tbd G L R s t M) = length (rev_follow (m_tbd G L R s t M) t) - 2"
    by (intro length_butlast_tl) simp
  ultimately show ?thesis
    by linarith
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) not_mem_Vs_M_tbd_if_free:
  assumes "is_symmetric_Map M"
  assumes "is_free_vertex M v"
  shows "v \<notin> Vs (M_tbd M)"
proof
  assume "v \<in> Vs (M_tbd M)"
  then obtain u where
    "{u, v} \<in> M_tbd M"
    by (auto simp add: Vs_def)
  hence "M_lookup M u = Some v"
    using assms(2)
    by (auto simp add: doubleton_eq_iff is_free_vertex_def)
  hence "M_lookup M v = Some u"
    by (simp add: assms(1))
  thus False
    using assms(2)
    by (simp add: is_free_vertex_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) not_mem_Vs_M_tbd_imp_free:
  assumes "v \<notin> Vs (M_tbd M)"
  shows "is_free_vertex M v"
proof (rule ccontr, goal_cases)
  case 1
  then obtain u where
    "M_lookup M v = Some u"
    by (auto simp add: is_free_vertex_def)
  thus False
    using assms
    by auto
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) mem_M_tbd_iff_mem_E2:
  assumes "M.invar M"
  assumes "s \<notin> set p"
  assumes "t \<notin> set p"
  shows "\<forall>e\<in>P_tbd p. e \<in> G.E (G2 L R s t M) \<longleftrightarrow> e \<in> M_tbd M"
proof
  fix e
  assume "e \<in> P_tbd p"
  hence
    "s \<notin> e"
    "t \<notin> e"
    using assms(2, 3)
    by (auto dest: v_in_edge_in_path_gen)
  thus "e \<in> G.E (G2 L R s t M) \<longleftrightarrow> e \<in> M_tbd M"
    using assms(1)
    by (auto simp add: E2_cong)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) s_not_mem_p_tbd:
  shows "s \<notin> set (p_tbd G L R s t M)"
proof -
  have "hd (rev_follow (m_tbd G L R s t M) t) \<notin> set (tl (rev_follow (m_tbd G L R s t M) t))"
    using parent
    by (intro rev_follow_non_empty distinct_rev_follow distinct_imp_hd_not_mem_set_tl)
  hence "s \<notin> set (tl (rev_follow (m_tbd G L R s t M) t))"
    using not_done_2
    by (simp add: done_2_def hd_rev_follow_eq_s)
  thus ?thesis
    by (auto dest: in_set_butlastD)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) t_not_mem_p_tbd:
  shows "t \<notin> set (p_tbd G L R s t M)"
proof -
  have tl_non_empty: "tl (rev_follow (m_tbd G L R s t M) t) \<noteq> []"
  proof -
    have "4 \<le> length (rev_follow (m_tbd G L R s t M) t)"
      using length_rev_follow_geq_4
      .
    hence "3 \<le> length (tl (rev_follow (m_tbd G L R s t M) t))"
      by force
    thus ?thesis
      by force
  qed
  have "last (tl (rev_follow (m_tbd G L R s t M) t)) \<notin> set (p_tbd G L R s t M)"
    using tl_non_empty parent
    by (intro distinct_rev_follow distinct_tl distinct_imp_last_not_mem_set_butlast) force+
  moreover have "last (tl (rev_follow (m_tbd G L R s t M) t)) = t"
  proof -
    have "last (rev_follow (m_tbd G L R s t M) t) = t"
      using parent
      by (intro last_rev_follow)
    thus ?thesis
      using tl_non_empty
      by (subst last_tl) force+
  qed
  ultimately show ?thesis
    by force
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) mem_M_tbd_iff_mem_E2:
  shows "\<forall>e\<in>P_tbd (p_tbd G L R s t M). e \<in> G.E (G2 L R s t M) \<longleftrightarrow> e \<in> M_tbd M"
  using invar_M s_not_mem_p_tbd t_not_mem_p_tbd
  by (intro mem_M_tbd_iff_mem_E2)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2)
  shows
    hd_p_tbd_mem_adjacency_G2_s: "hd (p_tbd G L R s t M) \<in> set (G.adjacency_list (G2 L R s t M) s)" and
    last_p_tbd_mem_adjacency_G2_t: "last (p_tbd G L R s t M) \<in> set (G.adjacency_list (G2 L R s t M) t)"
proof -
  let ?G = "G.union (G1 G (G2 L R s t M)) (G2 L R s t M)"
  let ?p = "rev_follow (m_tbd G L R s t M) t"
  have path_p: "path (G.E ?G) ?p"
    using not_done_2
    unfolding done_2_def
    by
      (intro is_shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(1))
      (rule is_shortest_alt_path_rev_follow)
  obtain p u v where
    p: "?p = s # u # p @ [v, t]"
    using rev_followE
    .
  hence
    "{s, u} \<in> (G.E ?G)"
    "{v, t} \<in> (G.E ?G)"
    using path_p
    by (auto intro: path_snocD[where ?p = "s # u # p"])
  hence
    "{s, u} \<in> (G.E ?G)"
    "{t, v} \<in> (G.E ?G)"
    by (metis doubleton_eq_iff)+
  hence
    "u \<in> set (G.adjacency_list ?G s)"
    "v \<in> set (G.adjacency_list ?G t)"
    unfolding symmetric_adjacency.mem_adjacency_iff_edge[OF symmetric_adjacency_union_G1_G2[OF symmetric_adjacency_G invar_M is_symmetric_Map_M]]
    .
  hence
    "u \<in> set (free_vertices L M)"
    "v \<in> set (free_vertices R M)"
    by (simp_all add: adjacency_union_G1_G2_s_cong adjacency_union_G1_G2_t_cong)
  hence
    "u \<in> set (G.adjacency_list (G2 L R s t M) s)"
    "v \<in> set (G.adjacency_list (G2 L R s t M) t)"
  proof -
    assume "u \<in> set (free_vertices L M)"
    thus "u \<in> set (G.adjacency_list (G2 L R s t M) s)"
      using lookup_s_eq_None s_not_mem_R s_neq_t invar_M
      by (subst adjacency_G2_s_cong) blast+
    assume "v \<in> set (free_vertices R M)"
    thus "v \<in> set (G.adjacency_list (G2 L R s t M) t)"
      using lookup_t_eq_None t_not_mem_L s_neq_t invar_M
      by (subst adjacency_G2_t_cong) blast+
  qed
  thus
    "hd (p_tbd G L R s t M) \<in> set (G.adjacency_list (G2 L R s t M) s)"
    "last (p_tbd G L R s t M) \<in> set (G.adjacency_list (G2 L R s t M) t)"
    by (simp_all add: p butlast_append)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) hd_p_tbd_not_mem_Vs_M_tbd:
  shows "hd (p_tbd G L R s t M) \<notin> Vs (M_tbd M)"
proof -
  have "hd (p_tbd G L R s t M) \<in> set (G.adjacency_list (G2 L R s t M) s)"
    using hd_p_tbd_mem_adjacency_G2_s
    .
  hence "hd (p_tbd G L R s t M) \<in> set (free_vertices L M)"
    using s_not_mem_R s_neq_t invar_M lookup_s_eq_None
    by (simp add: adjacency_G2_s_cong)
  hence "is_free_vertex M (hd (p_tbd G L R s t M))"
    by (simp add: free_vertices_def)
  thus ?thesis
    using is_symmetric_Map_M
    by (intro not_mem_Vs_M_tbd_if_free)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) last_p_tbd_not_mem_Vs_M_tbd:
  shows "last (p_tbd G L R s t M) \<notin> Vs (M_tbd M)"
proof -
  have "last (p_tbd G L R s t M) \<in> set (G.adjacency_list (G2 L R s t M) t)"
    using last_p_tbd_mem_adjacency_G2_t
    .
  hence "last (p_tbd G L R s t M) \<in> set (free_vertices R M)"
    using t_not_mem_L s_neq_t invar_M lookup_t_eq_None
    by (simp add: adjacency_G2_t_cong)
  hence "is_free_vertex M (last (p_tbd G L R s t M))"
    by (simp add: free_vertices_def)
  thus ?thesis
    using is_symmetric_Map_M
    by (intro not_mem_Vs_M_tbd_if_free)
qed

text \<open>
By our construction of graphs @{term edmonds_karp.G1} and @{term edmonds_karp.G2}, we can use
this--as described above--to obtain an augmenting path in graph @{term G} w.r.t.\ the current
matching @{term M}.
\<close>

lemma (in edmonds_karp_invar_not_done_2) augmenting_path_p_tbd:
  shows "augmenting_path (M_tbd M) (p_tbd G L R s t M)"
proof (rule augmenting_pathI, goal_cases)
  case 1
  show ?case
    using length_p_tbd_geq_2
    .
next
  case 2
  let ?p = "rev_follow (m_tbd G L R s t M) t"
  have non_empty:
    "edges_of_path (p_tbd G L R s t M) \<noteq> []"
    "edges_of_path (tl ?p) \<noteq> []"
    "edges_of_path ?p \<noteq> []"
  proof -
    have "2 \<le> length (p_tbd G L R s t M)"
      using length_p_tbd_geq_2
      .
    hence
      "2 \<le> length (p_tbd G L R s t M)"
      "3 \<le> length (tl ?p)"
      "4 \<le> length ?p"
      by simp+
    hence
      "1 \<le> length (edges_of_path (p_tbd G L R s t M))"
      "2 \<le> length (edges_of_path (tl ?p))"
      "3 \<le> length (edges_of_path ?p)"
      by (simp_all add: edges_of_path_length)
    thus
      "edges_of_path (p_tbd G L R s t M) \<noteq> []"
      "edges_of_path (tl ?p) \<noteq> []"
      "edges_of_path ?p \<noteq> []"
      by fastforce+
  qed
  
  have
    "alt_list
      (\<lambda>e. e \<in> (G.E (G2 L R s t M)))
      (Not \<circ> (\<lambda>e. e \<in> (G.E (G2 L R s t M))))
      (edges_of_path ?p)"
    using not_done_2
    unfolding done_2_def
    by (intro is_shortest_alt_pathD(2) alt_pathD(1)) (rule is_shortest_alt_path_rev_follow)
  hence
    "alt_list
      (Not \<circ> (\<lambda>e. e \<in> (G.E (G2 L R s t M))))
      (\<lambda>e. e \<in> (G.E (G2 L R s t M)))
      (edges_of_path (tl ?p))"
    using non_empty(2)
    by (auto simp add: edges_of_path_tl intro: alt_list_tl)
  hence
    "alt_list
      (Not \<circ> (\<lambda>e. e \<in> (G.E (G2 L R s t M))))
      (\<lambda>e. e \<in> (G.E (G2 L R s t M)))
      (edges_of_path (butlast (tl ?p)))"
    using non_empty(1)
    by (auto simp add: edges_of_path_butlast intro: alt_list_butlast)
  thus ?case
    using mem_M_tbd_iff_mem_E2
    by (auto intro: alt_list_cong)
next
  case 3
  show ?case
    using hd_p_tbd_not_mem_Vs_M_tbd
    .
next
  case 4
  show ?case
    using last_p_tbd_not_mem_Vs_M_tbd
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) P_tbd_subset_E:
  shows "P_tbd (p_tbd G L R s t M) \<subseteq> G.E G"
proof
  let ?G = "G.union (G1 G (G2 L R s t M)) (G2 L R s t M)"
  let ?p = "rev_follow (m_tbd G L R s t M) t"
  fix e
  assume assm: "e \<in> P_tbd (p_tbd G L R s t M)"
  have "path (G.E ?G) ?p"
    using not_done_2
    unfolding done_2_def
    by
      (intro is_shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(1))
      (rule is_shortest_alt_path_rev_follow)
  hence "path (G.E ?G) (tl ?p)"
    by (intro tl_path_is_path)
  hence "path (G.E ?G) (p_tbd G L R s t M)"
    by (intro path_butlastI)
  hence "P_tbd (p_tbd G L R s t M) \<subseteq> G.E ?G"
    by (intro path_edges_subset)
  hence "e \<in> G.E ?G"
    using assm
    by (rule set_mp)
  then consider
    (1) "e \<in> G.E G" |
    (2) "e \<in> {{s, v} |v. v \<in> set (free_vertices L M)}" |
    (3) "e \<in> {{t, v} |v. v \<in> set (free_vertices R M)}"
    by (auto simp add: E_union_G1_G2_cong)
  thus "e \<in> G.E G"
  proof (cases)
    case 1
    thus ?thesis
      .
  next
    case 2
    thus ?thesis
      using assm s_not_mem_p_tbd
      by (auto dest: v_in_edge_in_path_gen)
  next
    case 3
    thus ?thesis
      using assm t_not_mem_p_tbd
      by (auto dest: v_in_edge_in_path_gen)
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) set_p_tbd_subset_V:
  shows "set (p_tbd G L R s t M) \<subseteq> G.V G"
proof
  let ?G = "G.union (G1 G (G2 L R s t M)) (G2 L R s t M)"
  let ?p = "rev_follow (m_tbd G L R s t M) t"
  fix v
  assume assm: "v \<in> set (p_tbd G L R s t M)"
  have "path (G.E ?G) ?p"
    using not_done_2
    unfolding done_2_def
    by
      (intro is_shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(1))
      (rule is_shortest_alt_path_rev_follow)
  hence "path (G.E ?G) (tl ?p)"
    by (intro tl_path_is_path)
  hence "path (G.E ?G) (p_tbd G L R s t M)"
    by (intro path_butlastI)
  hence "set (p_tbd G L R s t M) \<subseteq> G.V ?G"
    unfolding G.V_def
    by (intro mem_path_Vs subsetI)
  hence "v \<in> G.V ?G"
    using assm
    by (rule set_mp)
  then consider
    (1) "v \<in> G.V G" |
    (2) "v \<in> {s}" |
    (3) "v \<in> {t}"
    by (auto simp add: V_union_G1_G2_cong)
  thus "v \<in> G.V G"
  proof (cases)
    case 1
    thus ?thesis
      .
  next
    case 2
    thus ?thesis
      using assm s_not_mem_p_tbd
      by force
  next
    case 3
    thus ?thesis
      using assm t_not_mem_p_tbd
      by force
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) distinct_p_tbd:
  shows "distinct (p_tbd G L R s t M)"
  using parent
  by (intro distinct_rev_follow distinct_tl distinct_butlast)

lemma (in edmonds_karp_invar_not_done_2) augpath_p_tbd:
  shows "augpath (G.E G) (M_tbd M) (p_tbd G L R s t M)"
proof (rule augpathI, goal_cases)
  case 1
  thus ?case
    using P_tbd_subset_E set_p_tbd_subset_V
    unfolding G.V_def
    by (intro pathI)
next
  case 2
  show ?case
    using distinct_p_tbd
    .
next
  case 3
  show ?case
    using augmenting_path_p_tbd
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) M_tbd_set_inorder_cong:
  assumes "M.invar M"
  shows "M_tbd M = {{u, v} |u v. (u, v) \<in> set (M_inorder M)}"
  using assms
  by (simp add: M.mem_inorder_iff_lookup_eq_Some)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) M_tbd_delete_cong:
  assumes "M.invar M"
  shows
    "M_tbd (M_delete u M) =
     M_tbd M -
     (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> if v \<noteq> u \<and> M_lookup M v = Some u then {} else {{u, v}})"
proof -
  { fix x y
    have
      "{x, y} \<in> M_tbd (M_delete u M) \<longleftrightarrow>
       M_lookup (M_delete u M) x = Some y \<or> M_lookup (M_delete u M) y = Some x"
      by (auto simp add: doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       (x, y) \<in> set (M_inorder (M_delete u M)) \<or>
       (y, x) \<in> set (M_inorder (M_delete u M))"
      using assms M.invar_delete
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have
      "... \<longleftrightarrow>
       (x, y) \<in> set (M_inorder M) - (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {(u, v)}) \<or>
       (y, x) \<in> set (M_inorder M) - (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {(u, v)})"
      using assms
      by (simp add: M.set_inorder_delete_cong)
    also have
      "... \<longleftrightarrow>
       {x, y} \<in> M_tbd M -
       (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> if v \<noteq> u \<and> M_lookup M v = Some u then {} else {{u, v}})"
    proof (cases "M_lookup M u")
      case None
      thus ?thesis
        using assms
        by (auto simp add: M.mem_inorder_iff_lookup_eq_Some doubleton_eq_iff)
    next
      case (Some v)
      show ?thesis
        using assms
        by (auto simp add: Some M.mem_inorder_iff_lookup_eq_Some doubleton_eq_iff)
    qed
    finally have
      "{x, y} \<in> M_tbd (M_delete u M) \<longleftrightarrow>
       {x, y} \<in> M_tbd M -
       (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> if v \<noteq> u \<and> M_lookup M v = Some u then {} else {{u, v}})"
      . }
  thus ?thesis
    by (intro graphs_eqI) (auto simp add: graph_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) M_tbd_update_cong:
  assumes "M.invar M"
  shows
    "M_tbd (M_update u v M) =
     M_tbd M -
     (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> if w \<noteq> u \<and> M_lookup M w = Some u then {} else {{u, w}}) \<union>
     {{u, v}}"
proof -
  { fix x y
    have
      "{x, y} \<in> M_tbd (M_update u v M) \<longleftrightarrow>
       M_lookup (M_update u v M) x = Some y \<or> M_lookup (M_update u v M) y = Some x"
      by (auto simp add: doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       (x, y) \<in> set (M_inorder (M_update u v M)) \<or>
       (y, x) \<in> set (M_inorder (M_update u v M))"
      using assms M.invar_update
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have
      "... \<longleftrightarrow>
       (x, y) \<in> set (M_inorder M) - (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> {(u, w)}) \<union> {(u, v)} \<or>
       (y, x) \<in> set (M_inorder M) - (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> {(u, w)}) \<union> {(u, v)}"
      using assms
      by (simp add: M.set_inorder_update_cong)
    also have
      "... \<longleftrightarrow>
       {x, y} \<in> M_tbd M - (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> if w \<noteq> u \<and> M_lookup M w = Some u then {} else {{u, w}}) \<union> {{u, v}}"
    proof (cases "M_lookup M u")
      case None
      thus ?thesis
        using assms
        by (auto simp add: M.mem_inorder_iff_lookup_eq_Some doubleton_eq_iff)
    next
      case (Some v)
      show ?thesis
        using assms
        by (auto simp add: Some M.mem_inorder_iff_lookup_eq_Some doubleton_eq_iff)
    qed
    finally have
      "{x, y} \<in> M_tbd (M_update u v M) \<longleftrightarrow>
       {x, y} \<in> M_tbd M - (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> if w \<noteq> u \<and> M_lookup M w = Some u then {} else {{u, w}}) \<union> {{u, v}}"
      . }
  thus ?thesis
    by (intro graphs_eqI) (auto simp add: graph_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) mem_Vs_M_tbd_iff_lookup_eq_Some:
  assumes "is_symmetric_Map M"
  shows "v \<notin> Vs (M_tbd M) \<longleftrightarrow> M_lookup M v = None"
proof -
  { have "v \<in> Vs (M_tbd M) \<longleftrightarrow> (\<exists>u. {v, u} \<in> M_tbd M)"
      using M.graph
      by (auto simp add: Vs_def)
    also have "... \<longleftrightarrow> (\<exists>u. M_lookup M v = Some u)"
      using assms
      by (auto simp add: doubleton_eq_iff)
    finally have "v \<in> Vs (M_tbd M) \<longleftrightarrow> (\<exists>u. M_lookup M v = Some u)"
      . }
  thus ?thesis
    by simp
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) invar_augment:
  assumes "M.invar M"
  assumes "even (length p)"
  shows "M.invar (augment M p)"
  using assms
proof (induct M p rule: augment.induct)
  case (2 M u v)
  thus ?case
    by (auto intro: M.invar_update)
next
  case (3 M u v w ws)
  hence "M.invar (M_update v u (M_update u v (M_delete w M)))"
    by (intro M.invar_delete M.invar_update)
  thus ?case
    using "3.prems"(2)
    by (auto intro: "3.hyps")
qed simp+

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) augment_induct_case_2D:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "augmenting_path (M_tbd M) [u, v]"
  assumes "distinct [u, v]"
  assumes "even (length [u, v])"
  shows
    "u \<noteq> v"
    "{u, v} \<notin> M_tbd M"
    "M.invar (M_update u v M)"
    "M.invar (M_update v u (M_update u v M))"
    "M_lookup M u = None"
    "M_lookup M v = None"
    "M_lookup (M_update u v M) u = Some v"
    "M_lookup (M_update u v M) v = None"
proof -
  show neq: "u \<noteq> v"
    using assms(4)
    by simp
  show "{u, v} \<notin> M_tbd M"
    using assms(3)
    by (auto simp add: alt_list_step dest: augmenting_pathD(2))
  show
    "M.invar (M_update u v M)"
    "M.invar (M_update v u (M_update u v M))"
    using assms(1)
    by (auto intro: M.invar_update)
  show
    "M_lookup M u = None"
    "M_lookup M v = None"
    using assms(2, 3)
    by (auto simp add: mem_Vs_M_tbd_iff_lookup_eq_Some dest: augmenting_pathD(3, 4))
  thus
    "M_lookup (M_update u v M) u = Some v"
    "M_lookup (M_update u v M) v = None"
    using assms(1) neq
    by (simp_all add: M.map_update)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) augment_induct_case_3D:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "augmenting_path (M_tbd M) (u # v # w # ws)"
  assumes "distinct (u # v # w # ws)"
  assumes "even (length (u # v # w # ws))"
  shows
    "u \<noteq> v"
    "v \<noteq> w"
    "u \<noteq> w"
    "{u, v} \<notin> M_tbd M"
    "{v, w} \<in> M_tbd M"
    "{u, v} \<notin> P_tbd (v # w # ws)"
    "{u, v} \<notin> P_tbd (w # ws)"
    "{v, w} \<notin> P_tbd (w # ws)"
    "M.invar (M_delete w M)"
    "M.invar (M_update u v (M_delete w M))"
    "M.invar (M_update v u (M_update u v (M_delete w M)))"
    "M_lookup M u = None"
    "M_lookup M v = Some w"
    "M_lookup M w = Some v"
    "M_lookup (M_delete w M) u = None"
    "M_lookup (M_delete w M) v = Some w"
    "M_lookup (M_delete w M) w = None"
    "M_lookup (M_update u v (M_delete w M)) v = Some w"
    "M_lookup (M_update u v (M_delete w M)) w = None"
    "M_lookup (M_update v u (M_update u v (M_delete w M))) w = None"
proof -
  show neq:
    "u \<noteq> v"
    "v \<noteq> w"
    "u \<noteq> w"
    using assms(4)
    by simp+
  show mem_M_tbd:
    "{u, v} \<notin> M_tbd M"
    "{v, w} \<in> M_tbd M"
    using assms(3)
    by (auto simp add: alt_list_step dest: augmenting_pathD(2))
  show
    "{u, v} \<notin> P_tbd (v # w # ws)"
    "{u, v} \<notin> P_tbd (w # ws)"
    "{v, w} \<notin> P_tbd (w # ws)"
    using assms(4)
    by (auto dest: v_in_edge_in_path)
  show invar:
    "M.invar (M_delete w M)"
    "M.invar (M_update u v (M_delete w M))"
    "M.invar (M_update v u (M_update u v (M_delete w M)))"
    using assms(1)
    by (auto intro: M.invar_delete M.invar_update)
  show
    "M_lookup M u = None"
    "M_lookup M v = Some w"
    "M_lookup M w = Some v"
    using assms(2, 3) mem_M_tbd(2)
    by (auto simp add: mem_Vs_M_tbd_iff_lookup_eq_Some doubleton_eq_iff dest: augmenting_pathD(3))
  thus
    "M_lookup (M_delete w M) u = None"
    "M_lookup (M_delete w M) v = Some w"
    "M_lookup (M_delete w M) w = None"
    using assms(1) neq(2-3)
    by (simp_all add: M.map_delete)
  thus
    "M_lookup (M_update u v (M_delete w M)) v = Some w"
    "M_lookup (M_update u v (M_delete w M)) w = None"
    using invar(1) neq(1, 3)
    by (simp_all add: M.map_update)
  thus
    "M_lookup (M_update v u (M_update u v (M_delete w M))) w = None"
    using invar(2) neq(2)
    by (simp add: M.map_update)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) M_tbd_update_update_delete_cong:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "augmenting_path (M_tbd M) (u # v # w # ws)"
  assumes "distinct (u # v # w # ws)"
  assumes "even (length (u # v # w # ws))"
  shows "M_tbd (M_update v u (M_update u v (M_delete w M))) = M_tbd M - {{v, w}} \<union> {{u, v}}"
proof -
  have
    "M_tbd (M_update v u (M_update u v (M_delete w M))) =
     M_tbd (M_update u v (M_delete w M)) - {{v, w}} \<union> {{u, v}}"
    using assms augment_induct_case_3D(10, 18, 19)
    by (simp add: M_tbd_update_cong insert_commute)
  also have "... = M_tbd (M_delete w M) \<union> {{u, v}} - {{v, w}} \<union> {{u, v}}"
    using augment_induct_case_3D(9, 15)[OF assms]
    by (simp add: M_tbd_update_cong)
  also have "... = M_tbd (M_delete w M) - {{v, w}} \<union> {{u, v}}"
    by (simp add: insert_Diff_if)
  also have "... = M_tbd M - {{v, w}} \<union> {{u, v}}"
    using assms(1) augment_induct_case_3D(13, 14)[OF assms]
    by (simp add: M_tbd_delete_cong)
  finally show ?thesis
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) is_symmetric_Map_update_update_delete:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "augmenting_path (M_tbd M) (u # v # w # ws)"
  assumes "distinct (u # v # w # ws)"
  assumes "even (length (u # v # w # ws))"
  shows "is_symmetric_Map (M_update v u (M_update u v (M_delete w M)))"
proof (standard, standard)
  fix x y
  have
    "M_lookup (M_update v u (M_update u v (M_delete w M))) x = Some y \<longleftrightarrow>
     (x, y) \<in> set (M_inorder (M_update v u (M_update u v (M_delete w M))))"
    using assms augment_induct_case_3D(11)
    by (intro M.mem_inorder_iff_lookup_eq_Some)
  also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder (M_update u v (M_delete w M))) - {(v, w)} \<union> {(v, u)}"
    using assms augment_induct_case_3D(10, 18)
    by (simp add: M.set_inorder_update_cong)
  also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder (M_delete w M)) \<union> {(u, v)} - {(v, w)} \<union> {(v, u)}"
    using assms augment_induct_case_3D(9, 15)
    by (simp add: M.set_inorder_update_cong)
  also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder M) - {(w, v)} \<union> {(u, v)} - {(v, w)} \<union> {(v, u)}"
    using assms(1) augment_induct_case_3D(14)[OF assms]
    by (simp add: M.set_inorder_delete_cong)
  also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder M) - {(w, v)} \<union> {(u, v)} - {(v, w)} \<union> {(v, u)}"
    using assms(1, 2)
    by (auto simp add: M.mem_inorder_iff_lookup_eq_Some)
  also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_delete w M)) \<union> {(u, v)} - {(v, w)} \<union> {(v, u)}"
    using assms(1) augment_induct_case_3D(14)[OF assms]
    by (simp add: M.set_inorder_delete_cong)
  also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_update u v (M_delete w M))) - {(v, w)} \<union> {(v, u)}"
    using assms augment_induct_case_3D(9, 15)
    by (simp add: M.set_inorder_update_cong)
  also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_update v u (M_update u v (M_delete w M))))"
    using assms augment_induct_case_3D(10, 18)
    by (simp add: M.set_inorder_update_cong)
  also have "... \<longleftrightarrow> M_lookup (M_update v u (M_update u v (M_delete w M))) y = Some x"
    using assms
    by (intro augment_induct_case_3D(11) M.mem_inorder_iff_lookup_eq_Some[symmetric])
  finally show
    "M_lookup (M_update v u (M_update u v (M_delete w M))) x = Some y \<longleftrightarrow>
     M_lookup (M_update v u (M_update u v (M_delete w M))) y = Some x"
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) is_symmetric_Map_augment_aux:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "augmenting_path (M_tbd M) (u # v # w # ws)"
  assumes "distinct (u # v # w # ws)"
  assumes "even (length (u # v # w # ws))"
  shows "augmenting_path (M_tbd (M_update v u (M_update u v (M_delete w M)))) (w # ws)"
proof (rule augmenting_pathI, goal_cases)
  case 1
  show ?case
    using assms(5)
    by (auto simp add: Suc_le_eq)
next
  case 2
  have "Berge.alt_path (M_tbd M) (w # ws)"
    using assms(3)
    by
      (fastforce
        dest: augmenting_pathD(2)
        intro: alt_list_split_1[where ?l1.0 = "edges_of_path ([u, v] @ [hd (w # ws)])"])
  thus ?case
    using assms augment_induct_case_3D(7, 8)[OF assms]
    by (auto simp add: M_tbd_update_update_delete_cong intro: alt_list_cong)
next
  case 3
  show ?case
    using assms is_symmetric_Map_update_update_delete augment_induct_case_3D(20)
    by (simp add: mem_Vs_M_tbd_iff_lookup_eq_Some)
next
  case 4
  let ?x = "last (w # ws)"
  have neq:
    "?x \<noteq> u"
    "?x \<noteq> v"
    using assms(4)
    by auto
  have "M_lookup M ?x = None"
    using assms(2, 3)
    by (auto simp add: mem_Vs_M_tbd_iff_lookup_eq_Some dest: augmenting_pathD(4))
  hence "M_lookup (M_delete w M) ?x = None"
    using assms(1)
    by (simp add: M.map_delete)
  hence "M_lookup (M_update u v (M_delete w M)) ?x = None"
    using assms(1) M.invar_delete neq(1)
    by (simp add: M.map_update)
  hence "M_lookup (M_update v u (M_update u v (M_delete w M))) ?x = None"
    using assms(1) M.invar_delete M.invar_update neq(2)
    by (simp add: M.map_update)
  thus ?case
    using assms is_symmetric_Map_update_update_delete
    by (simp add: mem_Vs_M_tbd_iff_lookup_eq_Some)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) is_symmetric_Map_augment:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "augmenting_path (M_tbd M) p"
  assumes "distinct p"
  assumes "even (length p)"
  shows "is_symmetric_Map (augment M p)"
  using assms
proof (induct M p rule: augment.induct)
  case (2 M u v)
  { fix x y
    have "M_lookup (augment M [u, v]) x = Some y \<longleftrightarrow> M_lookup (M_update v u (M_update u v M)) x = Some y"
      by simp
    also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder (M_update v u (M_update u v M)))"
      using "2.prems" augment_induct_case_2D(4)
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder (M_update u v M)) \<union> {(v, u)}"
      using "2.prems" augment_induct_case_2D(3, 8)
      by (simp add: M.set_inorder_update_cong)
    also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder M) \<union> {(u, v)} \<union> {(v, u)}"
      using "2.prems"(1) augment_induct_case_2D(5)[OF "2.prems"]
      by (simp add: M.set_inorder_update_cong)
    also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder M) \<union> {(u, v)} \<union> {(v, u)}"
      using "2.prems"(1, 2)
      by (auto simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_update u v M)) \<union> {(v, u)}"
      using "2.prems"(1) augment_induct_case_2D(5)[OF "2.prems"]
      by (simp add: M.set_inorder_update_cong)
    also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_update v u (M_update u v M)))"
      using "2.prems" augment_induct_case_2D(3, 8)
      by (simp add: M.set_inorder_update_cong)
    also have "... \<longleftrightarrow> M_lookup (M_update v u (M_update u v M)) y = Some x"
      using "2.prems" augment_induct_case_2D(4)
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> M_lookup (augment M [u, v]) y = Some x"
      by simp
    finally have "M_lookup (augment M [u, v]) x = Some y \<longleftrightarrow> M_lookup (augment M [u, v]) y = Some x"
      . }
  thus ?case
    by fast
next
  case (3 M u v w ws)
  { fix x y
    have
      "M_lookup (augment (M_update v u (M_update u v (M_delete w M))) (w # ws)) x = Some y \<longleftrightarrow>
       M_lookup (augment (M_update v u (M_update u v (M_delete w M))) (w # ws)) y = Some x"
      using "3.prems" augment_induct_case_3D(11) is_symmetric_Map_update_update_delete is_symmetric_Map_augment_aux
      by (simp add: "3.hyps") }
  thus ?case
    by simp
qed (simp_all add: augmenting_path_def)

text \<open>
Having found an augmenting path @{term P} in graph @{term G} w.r.t.\ the current matching @{term M},
we now verify that the algorithm correctly augments @{term M} by @{term P}, that is, we show that
function @{term edmonds_karp.augment} implements the symmetric difference @{term "M \<oplus> P"}.
\<close>

lemma (in edmonds_karp) M_tbd_augment_cong:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "augmenting_path (M_tbd M) p"
  assumes "distinct p"
  assumes "even (length p)"
  shows "M_tbd (augment M p) = M_tbd M \<oplus> P_tbd p"
  using assms
proof (induct rule: augment.induct)
  case (2 M u v)
  have "M_tbd (augment M [u, v]) = M_tbd (M_update v u (M_update u v M))"
    by simp
  also have "... = M_tbd (M_update u v M) \<union> {{u, v}}"
    using "2.prems" augment_induct_case_2D(3, 8)
    by (auto simp add: M_tbd_update_cong)
  also have "... = M_tbd M \<union> {{u, v}}"
    using "2.prems"(1) augment_induct_case_2D(1, 5)[OF "2.prems"]
    by (simp add: M_tbd_update_cong)
  also have "... = M_tbd M \<oplus> {{u, v}}"
    using augment_induct_case_2D(2)[OF "2.prems"]
    by (simp add: symmetric_diff_def)
  also have "... = M_tbd M \<oplus> P_tbd [u, v]"
    by simp
  finally show ?case
    .
next
  case (3 M u v w ws)
  have
    "M_tbd (augment M (u # v # w # ws)) =
     M_tbd (augment (M_update v u (M_update u v (M_delete w M))) (w # ws))"
    by simp
  also have "... = M_tbd (M_update v u (M_update u v (M_delete w M))) \<oplus> P_tbd (w # ws)"
  proof (rule "3.hyps", goal_cases)
    case 1
    show ?case
      using "3.prems"
      by (intro augment_induct_case_3D(11))
  next
    case 2
    show ?case
      using "3.prems"
      by (intro is_symmetric_Map_update_update_delete)
  next
    case 3
    show ?case
      using "3.prems"
      by (intro is_symmetric_Map_augment_aux)
  next
    case 4
    show ?case
      using "3.prems"(4)
      by force
  next
    case 5
    show ?case
      using "3.prems"(5)
      by force
  qed
  also have "... = M_tbd M - {{v, w}} \<union> {{u, v}} \<oplus> P_tbd (w # ws)"
    using "3.prems"
    by (simp add: M_tbd_update_update_delete_cong)
  also have "... = M_tbd M - {{v, w}} \<union> {{u, v}} \<union> {{v, w}} \<oplus> (P_tbd (w # ws) \<union> {{v, w}})"
    using augment_induct_case_3D(4, 5, 8)[OF "3.prems"]
    unfolding symmetric_diff_def
    by fastforce
  also have "... = M_tbd M \<union> {{u, v}} \<oplus> P_tbd (v # w # ws)"
    using "3.prems" augment_induct_case_3D(5)
    by (simp add: insert_commute insert_absorb)
  also have "... = M_tbd M \<oplus> (P_tbd (v # w # ws) \<union> {{u, v}})"
    using augment_induct_case_3D(4, 6)[OF "3.prems"]
    unfolding symmetric_diff_def
    by blast
  also have "... = M_tbd M \<oplus> P_tbd (u # v # w # ws)"
    by simp
  finally show ?case
    .
qed (simp_all add: augmenting_path_def)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) p_tbd_non_empty:
  shows "p_tbd G L R s t M \<noteq> []"
  using length_p_tbd_geq_2
  by force

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) even_length_p_tbd:
  shows "even (length (p_tbd G L R s t M))"
proof -
  let ?p = "p_tbd G L R s t M"
  have "path (G.E G) ?p"
    using P_tbd_subset_E set_p_tbd_subset_V
    unfolding G.V_def
    by (intro pathI)
  moreover have "hd ?p \<in> G.S.set L"
  proof -
    have "hd ?p \<in> set (G.adjacency_list (G2 L R s t M) s)"
      using hd_p_tbd_mem_adjacency_G2_s
      .
    hence "hd ?p \<in> set (free_vertices L M)"
      using s_not_mem_R s_neq_t invar_M lookup_s_eq_None
      by (simp add: adjacency_G2_s_cong)
    thus ?thesis
      using set_free_vertices_subset
      by (rule set_rev_mp)
  qed
  moreover have "length ?p - 1 < length ?p"
    using p_tbd_non_empty
    by (fastforce intro: diff_less)
  moreover have "?p ! (length ?p - 1) \<notin> G.S.set L"
  proof -
    have "last ?p \<in> set (G.adjacency_list (G2 L R s t M) t)"
      using last_p_tbd_mem_adjacency_G2_t
      .
    hence "last ?p \<in> set (free_vertices R M)"
      using t_not_mem_L s_neq_t invar_M lookup_t_eq_None
      by (simp add: adjacency_G2_t_cong)
    hence "last ?p \<in> G.S.set R"
      using set_free_vertices_subset
      by (rule set_rev_mp)
    hence "last ?p \<notin> G.S.set L"
      using bipartite_graph
      by (intro bipartite_graph.mem_R_imp_not_mem_L)
    thus ?thesis
      using p_tbd_non_empty
      by (simp add: last_conv_nth)
  qed
  ultimately show ?thesis
    using bipartite_graph
    by (simp add: bipartite_graph.nth_mem_L_iff_even)
qed

text \<open>
Having verified the correctness of the body of loop @{term edmonds_karp.loop'}, we are now finally
able to show that the loop invariants are maintained.
\<close>

lemma (in edmonds_karp_invar_not_done_2) edmonds_karp_invar_augment:
  shows "edmonds_karp_invar'' (augment M (p_tbd G L R s t M))"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_M even_length_p_tbd
    by (intro invar_augment)
next
  case 2
  show ?case
    using invar_M is_symmetric_Map_M augmenting_path_p_tbd distinct_p_tbd even_length_p_tbd
    by (intro is_symmetric_Map_augment)
next
  case (3 u v)
  let ?p = "p_tbd G L R s t M"
  have "{u, v} \<in> M_tbd (augment M ?p)"
    using 3
    by blast
  hence "{u, v} \<in> M_tbd M \<oplus> P_tbd ?p"
    using invar_M is_symmetric_Map_M augmenting_path_p_tbd distinct_p_tbd even_length_p_tbd
    by (simp add: M_tbd_augment_cong[symmetric])
  hence "{u, v} \<in> M_tbd M \<union> P_tbd ?p"
    using sym_diff_subset
    by fast
  thus ?case
    using M_tbd_subset_E P_tbd_subset_E
    by blast
qed

(* TODO Prove with weaker assumptions via induction? *)
lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) M_tbd_augment_subset_E:
  assumes "M.invar M"
  assumes "is_symmetric_Map M"
  assumes "M_tbd M \<subseteq> G.E G"
  assumes "augpath (G.E G) (M_tbd M) p"
  assumes "distinct p"
  assumes "even (length p)"
  shows "M_tbd (augment M p) \<subseteq> G.E G"
proof (rule subset_trans[where ?B = "M_tbd M \<union> P_tbd p"], goal_cases)
  case 1
  show ?case
    using assms
    by (simp add: M_tbd_augment_cong sym_diff_subset)
next
  case 2
  show ?case
    using assms(3, 4)
    by (simp add: path_edges_subset)
qed

subsubsection \<open>Termination\<close>

text \<open>
Before we can prove the correctness of loop @{term edmonds_karp.loop'}, we need to prove that it
terminates on appropriate inputs. For this, we show that the size of matching @{term M} increases
from one iteration to the next.
\<close>

lemma (in edmonds_karp_valid_input) loop'_dom:
  assumes "edmonds_karp_invar'' M"
  shows "loop'_dom (G, L, R, s, t, M)"
  using assms
proof \<^marker>\<open>tag visible\<close> (induct "card (G.E G) - card (M_tbd M)" arbitrary: M rule: less_induct)
  case less
  let ?G2 = "G2 L R s t M"
  let ?G1 = "G1 G ?G2"
  let ?m = "alt_bfs ?G1 ?G2 s"
  have m: "?m = m_tbd G L R s t M"
    by metis
  show ?case
  proof (cases "done_1 L R M")
    case True
    thus ?thesis
      by (blast intro: loop'.domintros)
  next
    case not_done_1: False
    show ?thesis
    proof (cases "done_2 t ?m")
      case True
      thus ?thesis
        by (blast intro: loop'.domintros)
    next
      case False
      let ?p = "butlast (tl (rev_follow ?m t))"
      have p: "?p = p_tbd G L R s t M"
        by metis
      let ?M = "augment M ?p"
      have edmonds_karp_invar_not_done_2: "edmonds_karp_invar_not_done_2'' M"
        using less.prems not_done_1 False
        unfolding m
        by (intro edmonds_karp_invar_not_done_2I_2)
      hence augpath_p: "augpath (G.E G) (M_tbd M) ?p"
        unfolding m
        by (intro edmonds_karp_invar_not_done_2.augpath_p_tbd)
      show ?thesis
      proof (rule loop'.domintros, rule less.hyps, goal_cases)
        case 1
        have "card (M_tbd M) < card (M_tbd ?M)"
        proof \<^marker>\<open>tag invisible\<close> -
          have "card (M_tbd M) < card (M_tbd M \<oplus> P_tbd ?p)"
            using finite_E less.prems augpath_p
            by
              (auto
               dest: augpathD(2, 3) edmonds_karp_invar.M_tbd_subset_E finite_subset
               intro: new_matching_bigger)
          also have "... = card (M_tbd ?M)"
          proof \<^marker>\<open>tag invisible\<close> -
            have
              "M.invar M"
              "is_symmetric_Map M"
              using less.prems
              by (auto dest: edmonds_karp_invar.invar_M edmonds_karp_invar.is_symmetric_Map_M)
            moreover have
              "augmenting_path (M_tbd M) ?p"
              "distinct ?p"
              using augpath_p
              by (auto dest: augpathD(2, 3))
            moreover have "even (length ?p)"
              unfolding p
              using edmonds_karp_invar_not_done_2
              by (intro edmonds_karp_invar_not_done_2.even_length_p_tbd)
            ultimately show ?thesis
              by (simp add: M_tbd_augment_cong)
          qed
          finally show ?thesis
            .
        qed
        moreover have "card (M_tbd ?M) \<le> card (G.E G)"
        proof \<^marker>\<open>tag invisible\<close> (intro M_tbd_augment_subset_E card_mono, goal_cases)
          case 1
          show ?case
            using finite_E
            .
        next
          case 2
          show ?case
            using less.prems
            by (intro edmonds_karp_invar.invar_M)
        next
          case 3
          show ?case
            using less.prems
            by (intro edmonds_karp_invar.is_symmetric_Map_M)
        next
          case 4
          show ?case
            using less.prems
            by (intro edmonds_karp_invar.M_tbd_subset_E)
        next
          case 5
          show ?case
            using augpath_p
            .
        next
          case 6
          show ?case
            using augpath_p
            by (intro augpathD(2))
        next
          case 7
          show ?case
            unfolding p
            using edmonds_karp_invar_not_done_2
            by (intro edmonds_karp_invar_not_done_2.even_length_p_tbd)
        qed
        ultimately show ?case
          by linarith
      next
        case 2
        thus ?case
          unfolding p
          using edmonds_karp_invar_not_done_2
          by (intro edmonds_karp_invar_not_done_2.edmonds_karp_invar_augment)
      qed
    qed
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar) loop'_dom:
  shows "loop'_dom (G, L, R, s, t, M)"
  using edmonds_karp_invar_axioms
  by (intro loop'_dom)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar) loop'_psimps:
  shows
    "loop' G L R s t M =
     (if done_1 L R M then M
      else if done_2 t (m_tbd G L R s t M) then M
           else loop' G L R s t (augment M (p_tbd G L R s t M)))"
proof -
  let ?G2 = "G2 L R s t M"
  let ?G1 = "G1 G ?G2"
  let ?m = "alt_bfs ?G1 ?G2 s"
  have m: "?m = m_tbd G L R s t M"
    by metis
  show ?thesis
    unfolding m[symmetric]
    using loop'_dom
    by (intro loop'.psimps)
qed

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_not_done_2) loop'_psimps:
  shows "loop' G L R s t M = loop' G L R s t (augment M (p_tbd G L R s t M))"
  using not_done_1 not_done_2
  by (simp add: loop'_psimps)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_induct:
  assumes "edmonds_karp_invar' G L R s t M"
  assumes
    "\<And>G L R s t M.
      (\<not> done_1 L R M \<Longrightarrow>
       \<not> done_2 t (m_tbd G L R s t M) \<Longrightarrow>
       Q G L R s t (augment M (p_tbd G L R s t M))) \<Longrightarrow>
      Q G L R s t M"
  shows "Q G L R s t M"
proof (rule loop'.pinduct, goal_cases)
  case 1
  show ?case
    using assms(1)
    by (intro edmonds_karp_invar.loop'_dom)
next
  case (2 G L R s t M)
  let ?G2 = "G2 L R s t M"
  let ?G1 = "G1 G ?G2"
  let ?m = "alt_bfs ?G1 ?G2 s"
  have m: "?m = m_tbd G L R s t M"
    by metis
  show ?case
    using 2
    unfolding m
    by (auto intro: assms(2))
qed

subsubsection \<open>Correctness\<close>

text \<open>
We are now finally ready to prove the correctness of algorithm @{term edmonds_karp.edmonds_karp}. We
still need to show that if the algorithm doesn't find an augmenting path, then the current matching
@{term M} is already maximum.
\<close>

abbreviation is_maximum_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "is_maximum_matching G M \<equiv> graph_matching G M \<and> (\<forall>M'. graph_matching G M' \<longrightarrow> card M' \<le> card M)"

locale edmonds_karp_invar_done_1 = edmonds_karp_invar where
  Map_update = Map_update and
  P_update = P_update and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes done_1: "done_1 L R M"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_done_1' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "edmonds_karp_invar_done_1' G L R s t M \<equiv>
   edmonds_karp_invar_done_1
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list Q_snoc
    M_empty M_delete M_lookup M_inorder M_inv
    G L R s t M
    Map_update P_update M_update"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) edmonds_karp_invar_done_1'' :: "'m \<Rightarrow> bool" where
  "edmonds_karp_invar_done_1'' \<equiv> edmonds_karp_invar_done_1' G L R s t"

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_done_1I:
  assumes "edmonds_karp_invar' G L R s t M"
  assumes "done_1 L R M"
  shows "edmonds_karp_invar_done_1' G L R s t M"
  using assms
  by (simp add: edmonds_karp_invar_done_1_def edmonds_karp_invar_done_1_axioms_def)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_done_1) loop'_psimps:
  shows "loop' G L R s t M = M"
  using done_1
  by (simp add: loop'_psimps)

lemma (in edmonds_karp_invar_done_1) is_maximum_matching_M_tbd:
  shows "is_maximum_matching (G.E G) (M_tbd M)"
proof -
  { fix M'
    assume assm: "graph_matching (G.E G) M' \<and> card (M_tbd M) < card M'"
    obtain p where
      augpath_p: "augpath (G.E G) (M_tbd M) p"
    proof -
      have "\<exists>M'\<subseteq>(G.E G). matching M' \<and> card (M_tbd M) < card M'"
        using assm
        by blast
      hence "\<exists>p. augmenting_path (M_tbd M) p \<and> path (G.E G) p \<and> distinct p"
        using finite_M_tbd graph_matching_M_tbd graph_G finite_V
        by (simp add: G.V_def Berge)
      thus ?thesis
        by (auto intro: that)
    qed
    have p_non_empty: "p \<noteq> []"
      using augpath_p
      by (auto dest: augmenting_pathD(1))
    have free:
      "is_free_vertex M (hd p)"
      "is_free_vertex M (last p)"
      using augpath_p
      by (auto dest: augmenting_pathD(3, 4) intro: not_mem_Vs_M_tbd_imp_free)
    have mem_V:
      "hd p \<in> G.V G"
      "last p \<in> G.V G"
      using augpath_p p_non_empty
      by (fastforce simp add: G.V_def intro: mem_path_Vs)+
    have even_length: "even (length p)"
      using augpath_p
      by (auto simp add: edges_of_path_length dest: augmenting_path_odd_length)
    hence False
    proof (cases "hd p \<in> G.S.set L")
      case True
      have "last p \<in> G.S.set R"
      proof -
        have "length p - 1 < length p"
          using p_non_empty
          by (fastforce intro: diff_less)
        moreover have "odd (length p - 1)"
          using p_non_empty even_length
          by simp
        ultimately have "p ! (length p - 1) \<notin> G.S.set L"
          using bipartite_graph augpath_p True
          by (simp add: bipartite_graph.nth_mem_L_iff_even)
        hence "last p \<notin> G.S.set L"
          using p_non_empty
          by (simp add: last_conv_nth)
        with bipartite_graph mem_V(2)
        show ?thesis
          unfolding G.V_def
          by (rule bipartite_graph.not_mem_L_imp_mem_R)
      qed
      hence
        "hd p \<in> set (free_vertices L M)"
        "last p \<in> set (free_vertices R M)"
        using True free
        by (simp_all add: G.S.set_def free_vertices_def)
      thus ?thesis
        using done_1
        by (auto simp add: done_1_def)
    next
      case False
      with bipartite_graph mem_V(1)
      have hd_mem_R: "hd p \<in> G.S.set R"
        unfolding G.V_def
        by (rule bipartite_graph.not_mem_L_imp_mem_R)
      have "last p \<in> G.S.set L"
      proof -
        have "length p - 1 < length p"
          using p_non_empty
          by (fastforce intro: diff_less)
        moreover have "odd (length p - 1)"
          using p_non_empty even_length
          by simp
        ultimately have "p ! (length p - 1) \<notin> G.S.set R"
          using bipartite_graph augpath_p hd_mem_R
          by (simp add: bipartite_graph.nth_mem_R_iff_even)
        hence "last p \<notin> G.S.set R"
          using p_non_empty
          by (simp add: last_conv_nth)
        with bipartite_graph mem_V(2)
        show ?thesis
          unfolding G.V_def
          by (rule bipartite_graph.not_mem_R_imp_mem_L)
      qed
      hence
        "hd p \<in> set (free_vertices R M)"
        "last p \<in> set (free_vertices L M)"
        using hd_mem_R free
        by (simp_all add: G.S.set_def free_vertices_def)
      thus ?thesis
        using done_1
        by (auto simp add: done_1_def)
    qed }
  thus ?thesis
    using graph_matching_M_tbd
    by force
qed

locale edmonds_karp_invar_done_2 = edmonds_karp_invar_not_done_1 where
  Map_update = Map_update and
  P_update = P_update and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes done_2: "done_2 t (m_tbd G L R s t M)"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_done_2' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "edmonds_karp_invar_done_2' G L R s t M \<equiv>
   edmonds_karp_invar_done_2
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list Q_snoc
    M_empty M_delete M_lookup M_inorder M_inv
    G L R s t M
    Map_update P_update M_update"

abbreviation \<^marker>\<open>tag invisible\<close> (in edmonds_karp_valid_input) edmonds_karp_invar_done_2'' :: "'m \<Rightarrow> bool" where
  "edmonds_karp_invar_done_2'' \<equiv> edmonds_karp_invar_done_2' G L R s t"

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_done_2I:
  assumes "edmonds_karp_invar_not_done_1' G L R s t M"
  assumes "done_2 t (m_tbd G L R s t M)"
  shows "edmonds_karp_invar_done_2' G L R s t M"
  using assms
  by (simp add: edmonds_karp_invar_done_2_def edmonds_karp_invar_done_2_axioms_def)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp) edmonds_karp_invar_done_2I_2:
  assumes "edmonds_karp_invar' G L R s t M"
  assumes "\<not> done_1 L R M"
  assumes "done_2 t (m_tbd G L R s t M)"
  shows "edmonds_karp_invar_done_2' G L R s t M"
  using assms
  by
    (simp add:
     edmonds_karp_invar_not_done_1_def edmonds_karp_invar_not_done_1_axioms_def
     edmonds_karp_invar_done_2_def edmonds_karp_invar_done_2_axioms_def)

lemma \<^marker>\<open>tag invisible\<close> (in edmonds_karp_invar_done_2) loop'_psimps:
  shows "loop' G L R s t M = M"
  using not_done_1 done_2
  by (simp add: loop'_psimps)

lemma (in edmonds_karp_invar_done_2) is_maximum_matching_M_tbd:
  shows "is_maximum_matching (G.E G) (M_tbd M)"
proof -
  { fix M'
    let ?G2 = "G2 L R s t M"
    let ?G1 = "G1 G ?G2"
    let ?G = "G.union ?G1 ?G2"
    assume assm: "graph_matching (G.E G) M' \<and> card (M_tbd M) < card M'"
    obtain p where
      augpath_p: "augpath (G.E G) (M_tbd M) p"
    proof -
      have "\<exists>M'\<subseteq>(G.E G). matching M' \<and> card (M_tbd M) < card M'"
        using assm
        by blast
      hence "\<exists>p. augmenting_path (M_tbd M) p \<and> path (G.E G) p \<and> distinct p"
        using finite_M_tbd graph_matching_M_tbd graph_G finite_V
        by (simp add: G.V_def Berge)
      thus ?thesis
        by (auto intro: that)
    qed
    have p_non_empty: "p \<noteq> []"
      using augpath_p
      by (auto dest: augmenting_pathD(1))
    have free:
      "is_free_vertex M (hd p)"
      "is_free_vertex M (last p)"
      using augpath_p
      by (auto dest: augmenting_pathD(3, 4) intro: not_mem_Vs_M_tbd_imp_free)
    have mem_V:
      "hd p \<in> G.V G"
      "last p \<in> G.V G"
      using augpath_p p_non_empty
      by (fastforce simp add: G.V_def intro: mem_path_Vs)+
    have even_length: "even (length p)"
      using augpath_p
      by (auto simp add: edges_of_path_length dest: augmenting_path_odd_length)
    obtain p' where
      augpath_p': "augpath (G.E G) (M_tbd M) p'" and
      hd_p': "hd p' \<in> set (free_vertices L M)" and
      last_p': "last p' \<in> set (free_vertices R M)"
    proof (cases "hd p \<in> G.S.set L")
      case True
      have "last p \<in> G.S.set R"
      proof -
        have "length p - 1 < length p"
          using p_non_empty
          by (fastforce intro: diff_less)
        moreover have "odd (length p - 1)"
          using p_non_empty even_length
          by simp
        ultimately have "p ! (length p - 1) \<notin> G.S.set L"
          using bipartite_graph augpath_p True
          by (simp add: bipartite_graph.nth_mem_L_iff_even)
        hence "last p \<notin> G.S.set L"
          using p_non_empty
          by (simp add: last_conv_nth)
        with bipartite_graph mem_V(2)
        show ?thesis
          unfolding G.V_def
          by (rule bipartite_graph.not_mem_L_imp_mem_R)
      qed
      hence
        "hd p \<in> set (free_vertices L M)"
        "last p \<in> set (free_vertices R M)"
        using True free
        by (simp_all add: G.S.set_def free_vertices_def)
      thus ?thesis
        using augpath_p
        by (intro that)
    next
      case False
      with bipartite_graph mem_V(1)
      have hd_mem_R: "hd p \<in> G.S.set R"
        unfolding G.V_def
        by (rule bipartite_graph.not_mem_L_imp_mem_R)
      have "last p \<in> G.S.set L"
      proof -
        have "length p - 1 < length p"
          using p_non_empty
          by (fastforce intro: diff_less)
        moreover have "odd (length p - 1)"
          using p_non_empty even_length
          by simp
        ultimately have "p ! (length p - 1) \<notin> G.S.set R"
          using bipartite_graph augpath_p hd_mem_R
          by (simp add: bipartite_graph.nth_mem_R_iff_even)
        hence "last p \<notin> G.S.set R"
          using p_non_empty
          by (simp add: last_conv_nth)
        with bipartite_graph mem_V(2)
        show ?thesis
          unfolding G.V_def
          by (rule bipartite_graph.not_mem_R_imp_mem_L)
      qed
      hence
        "hd p \<in> set (free_vertices R M)"
        "last p \<in> set (free_vertices L M)"
        using hd_mem_R free
        by (simp_all add: G.S.set_def free_vertices_def)
      hence
        "hd (rev p) \<in> set (free_vertices L M)"
        "last (rev p) \<in> set (free_vertices R M)"
        using p_non_empty
        by (simp_all add: hd_rev last_rev)
      thus ?thesis
        using augpath_p
        by (intro that) (rule augpath_revI)
    qed
    have "alt_path (\<lambda>e. e \<in> G.E ?G2) (Not \<circ> (\<lambda>e. e \<in> G.E ?G2)) (G.E ?G) (s # p' @ [t]) s t"
    proof -
      have "alt_path (Not \<circ> (\<lambda>e. e \<in> G.E ?G2)) (\<lambda>e. e \<in> G.E ?G2) (G.E ?G) p' (hd p') (last p')"
      proof (intro alt_pathI, goal_cases)
        case 1
        have
          "s \<notin> set p'"
          "t \<notin> set p'"
          using augpath_p' s_not_mem_V t_not_mem_V
          by (auto simp add: G.V_def intro: mem_path_Vs)
        hence "\<forall>e\<in>P_tbd p'. e \<in> G.E ?G2 \<longleftrightarrow> e \<in> M_tbd M"
          using invar_M
          by (intro mem_M_tbd_iff_mem_E2)
        thus ?case
          using augpath_p'
          by (force dest: augmenting_pathD(2) intro: alt_list_cong)
      next
        case 2
        show ?case
        proof (rule nonempty_path_walk_between, goal_cases)
          case 1
          have "path (G.E G) p'"
            using augpath_p'
            ..
          thus ?case
            by (auto simp add: E_union_G1_G2_cong intro: path_subset)
        next
          case 2
          show ?case
            using augpath_p'
            by (auto dest: augmenting_pathD(1))
        qed simp+
      qed
      hence "alt_path (Not \<circ> (\<lambda>e. e \<in> G.E ?G2)) (\<lambda>e. e \<in> G.E ?G2) (G.E ?G) (p' @ [t]) (hd p') t"
      proof (rule alt_path_snoc_oddI, goal_cases)
        case 1
        show ?case
          using augpath_p'
          by (intro augmenting_path_odd_length) force
      next
        case 2
        show ?case
          using last_p'
          by (auto simp add: E_union_G1_G2_cong)
      next
        case 3
        show ?case
          using invar_M last_p'
          by (auto simp add: E2_cong)
      qed
      thus ?thesis
      proof (rule alt_path_ConsI, goal_cases)
        case 1
        show ?case
          using hd_p'
          by (auto simp add: E_union_G1_G2_cong)
      next
        case 2
        show ?case
          using invar_M hd_p'
          by (auto simp add: E2_cong)
      qed
    qed
    hence "alt_reachable (\<lambda>e. e \<in> G.E ?G2) (Not \<circ> (\<lambda>e. e \<in> G.E ?G2)) (G.E ?G) s t"
      by (auto simp add: alt_reachable_def)
    hence False
      using alt_bfs_valid_input s_neq_t done_2
      unfolding done_2_def
      unfolding alt_bfs_def
      by (metis alt_bfs_valid_input.alt_bfs_invar_init is_discovered_def alt_bfs_valid_input.completeness) }
  thus ?thesis
    using graph_matching_M_tbd
    by force
qed

text \<open>
Otherwise, we augment matching @{term M} by the augmenting path found as verified above, and it
follows by induction (via the induction rule given by function @{term edmonds_karp.loop'}) that the
algorithm outputs a maximum matching.
\<close>

lemma (in edmonds_karp_valid_input) is_maximum_matching_M_tbd_loop':
  assumes "edmonds_karp_invar'' M"
  shows "is_maximum_matching (G.E G) (M_tbd (loop' G L R s t M))"
  using assms
proof \<^marker>\<open>tag visible\<close> (induct rule: edmonds_karp_induct[OF assms])
  case (1 G L R s t M)
  show ?case
  proof (cases "done_1 L R M")
    case True
    with "1.prems"
    have "edmonds_karp_invar_done_1' G L R s t M"
      by (intro edmonds_karp_invar_done_1I)
    thus ?thesis
      by
        (intro edmonds_karp_invar_done_1.is_maximum_matching_M_tbd)
        (simp add: edmonds_karp_invar_done_1.loop'_psimps)
  next
    case not_done_1: False
    show ?thesis
    proof (cases "done_2 t (m_tbd G L R s t M)")
      case True
      with "1.prems" not_done_1
      have "edmonds_karp_invar_done_2' G L R s t M"
        by (intro edmonds_karp_invar_done_2I_2)
      thus ?thesis
        by
          (intro edmonds_karp_invar_done_2.is_maximum_matching_M_tbd)
          (simp add: edmonds_karp_invar_done_2.loop'_psimps)
    next
      case False
      with "1.prems" not_done_1
      have "edmonds_karp_invar_not_done_2' G L R s t M"
        by (intro edmonds_karp_invar_not_done_2I_2)
      thus ?thesis
        using not_done_1 False
        by
          (auto
            simp add: edmonds_karp_invar_not_done_2.loop'_psimps
            dest: "1.hyps"
            intro: edmonds_karp_invar_not_done_2.edmonds_karp_invar_augment)
    qed
  qed
qed

text \<open>
We finally have everything to state and prove the correctness theorem for algorithm
@{term edmonds_karp.edmonds_karp}.
\<close>

lemma (in edmonds_karp_valid_input) edmonds_karp_correct:
  shows "is_maximum_matching (G.E G) (M_tbd (edmonds_karp G L R s t))"
  unfolding edmonds_karp_def
  using edmonds_karp_invar_empty
  by (intro is_maximum_matching_M_tbd_loop')

theorem (in edmonds_karp) edmonds_karp_correct:
  assumes "edmonds_karp_valid_input' G L R s t"
  shows "is_maximum_matching (G.E G) (M_tbd (edmonds_karp G L R s t))"
  using assms
  by (intro edmonds_karp_valid_input.edmonds_karp_correct)

end