section \<open>Alternating BFS\<close>

text \<open>
This section specifies and verifies a modified BFS that alternates between edges in two given graphs.
\<close>

theory Alternating_BFS
  imports
    "../Graph/Undirected_Graph/Shortest_Alternating_Path"
    "../BFS/Undirected_BFS"
begin

subsection \<open>Specification of the algorithm\<close>

locale alt_bfs = bfs where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q"
begin

text \<open>Apart from enforcing alternation, the algorithm works identically to BFS.\<close>

thm init_def

thm DONE_def

thm is_discovered_def

thm discover_def

thm traverse_edge_def

text \<open>
And we enforce alternation by checking, when determining the vertices adjacent to a vertex
@{term u}, how @{term u} was reached from its parent. If it was reached via an edge in @{term G1},
then we consider only vertices adjacent to @{term u} in @{term G2} and vice versa.
\<close>

definition P :: "'n \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "P G u v \<equiv> case Map_lookup G u of None \<Rightarrow> False | Some s \<Rightarrow> Set_isin s v"

definition P' :: "'n \<Rightarrow> 'a option \<Rightarrow> 'a \<Rightarrow> bool" where
  "P' G uo v \<equiv> case uo of None \<Rightarrow> False | Some u \<Rightarrow> P G u v"

definition adjacency :: "'n \<Rightarrow> 'n \<Rightarrow> ('q, 'm) state \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "adjacency G1 G2 s v \<equiv>
   if P' G2 (P_lookup (parent s) v) v then G.adjacency_list G1 v
   else G.adjacency_list G2 v"

function (domintros) alt_loop :: "'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "alt_loop G1 G2 src s =
   (if \<not> DONE s
    then let
          u = Q_head (queue s);
          q = Q_tail (queue s)
         in alt_loop G1 G2 src (List.fold (traverse_edge src u) (adjacency G1 G2 s u) (s\<lparr>queue := q\<rparr>))
    else s)"
  by pat_completeness simp

definition alt_bfs :: "'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> 'm" where
  "alt_bfs G1 G2 src \<equiv> parent (alt_loop G1 G2 src (init src))"

abbreviation alt_fold :: "'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "alt_fold G1 G2 src s \<equiv>
   List.fold
    (traverse_edge src (Q_head (queue s)))
    (adjacency G1 G2 s (Q_head (queue s)))
    (s\<lparr>queue := Q_tail (queue s)\<rparr>)"

end

subsection \<open>Verification of the correctness of the algorithm\<close>

subsubsection \<open>Assumptions on the input\<close>

text \<open>
Algorithm @{term alt_bfs.alt_bfs} expects two undirected graphs @{term G1} and @{term G2} such that
@{term G1}'s and @{term G2}'s edges are disjoint and the union of @{term G1} and @{term G2} does not
contain any odd-length cycles, as well a source vertex @{term src} in @{term G2} as input, and the
correctness theorem will assume such an input. We remark that the assumption that @{term G1}'s and
@{term G2}'s edges are disjoint is for the purpose of convenience. More specifically, when
determining the vertices adjacent to a vertex @{term u}, with this assumption it is sufficient to
check whether the edge from @{term u}'s parent to @{term u} is in @{term G1} or @{term G2}.


Let us now formally specify our assumptions on the input.
\<close>

locale alt_bfs_valid_input = alt_bfs where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  fixes G1 G2 :: 'n
  fixes src :: 'a
  assumes invar_G1: "G.invar G1"
  assumes invar_G2: "G.invar G2"
  assumes G1_symmetric: "v \<in> set (G.adjacency_list G1 u) \<longleftrightarrow> u \<in> set (G.adjacency_list G1 v)"
  assumes G2_symmetric: "v \<in> set (G.adjacency_list G2 u) \<longleftrightarrow> u \<in> set (G.adjacency_list G2 v)"
  assumes E1_E2_disjoint: "G.E G1 \<inter> G.E G2 = {}"
  assumes no_odd_cycle: "\<not> (\<exists>c. path (G.E (G.union G1 G2)) c \<and> odd_cycle c)"
  assumes src_mem_V2: "src \<in> G.V G2"

abbreviation \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_bfs_valid_input' :: "'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "alt_bfs_valid_input' G1 G2 src \<equiv>
   alt_bfs_valid_input
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update P_update Q_snoc G1 G2 src"

context alt_bfs_valid_input
begin

sublocale G1: symmetric_adjacency where G = G1
proof (standard, goal_cases)
  case 1
  show ?case using invar_G1 .
next
  case 2
  show ?case using G1_symmetric .
qed

sublocale G2: symmetric_adjacency where G = G2
proof (standard, goal_cases)
  case 1
  show ?case using invar_G2 .
next
  case 2
  show ?case using G2_symmetric .
qed

end

abbreviation (in alt_bfs_valid_input) G :: 'n where
  "G \<equiv> G.union G1 G2"

lemma (in alt_bfs_valid_input) invar_G:
  shows "G.invar G"
  using invar_G1 invar_G2
  by (intro G.invar_union)

context alt_bfs_valid_input
begin
sublocale G: symmetric_adjacency where G = G
proof (standard, goal_cases)
  case 1
  show ?case using invar_G .
next
  case (2 u v)
  have "u \<in> set (G.adjacency_list G v) \<longleftrightarrow> u \<in> set (G.adjacency_list G1 v) \<or> u \<in> set (G.adjacency_list G2 v)"
    using invar_G1 invar_G2
    by (simp add: G.adjacency_union_cong)
  also have "... \<longleftrightarrow> v \<in> set (G.adjacency_list G1 u) \<or> v \<in> set (G.adjacency_list G2 u)"
    by (simp add: G1_symmetric G2_symmetric)
  also have "... \<longleftrightarrow> v \<in> set (G.adjacency_list G u)"
    using invar_G1 invar_G2
    by (simp add: G.adjacency_union_cong)
  finally show ?case
    .
qed
end

subsubsection \<open>Loop invariants\<close>

text \<open>
The loop invariants of @{term alt_bfs.alt_loop} are very similar to those of @{term bfs.loop}.
\<close>

abbreviation (in alt_bfs_valid_input) d :: "'m \<Rightarrow> 'a \<Rightarrow> nat" where
  "d m v \<equiv> path_length (rev_follow m v)"

abbreviation (in alt_bfs_valid_input) P'' :: "'a set \<Rightarrow> bool" where
  "P'' e \<equiv> e \<in> G.E G2"

abbreviation (in alt_bfs_valid_input) alt :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "alt s u v \<equiv> P' G2 (P_lookup (parent s) u) u \<longleftrightarrow> \<not> P G2 u v"

abbreviation (in alt_bfs_valid_input) Q :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "Q s v \<equiv> if P' G2 (P_lookup (parent s) v) v then (Not \<circ> P'') else P''"

abbreviation (in alt_bfs_valid_input) white :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "white s v \<equiv> \<not> is_discovered src (parent s) v"

abbreviation (in alt_bfs_valid_input) gray :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "gray s v \<equiv> is_discovered src (parent s) v \<and> v \<in> set (Q_list (queue s))"

abbreviation (in alt_bfs_valid_input) black :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "black s v \<equiv> is_discovered src (parent s) v \<and> v \<notin> set (Q_list (queue s))"

locale alt_bfs_invar =
  alt_bfs_valid_input where P_update = P_update and Q_snoc = Q_snoc +
  parent "P_lookup (parent s)" for
  P_update :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  s :: "('q, 'm) state" +
  assumes invar_queue: "Q_invar (queue s)"
  assumes invar_parent: "P_invar (parent s)"
  assumes parent_src: "P_lookup (parent s) src = None"
  assumes parent_imp_alt: "P_lookup (parent s) v = Some u \<Longrightarrow> alt s u v"
  assumes parent_imp_edge: "P_lookup (parent s) v = Some u \<Longrightarrow> {u, v} \<in> G.E G"
  assumes not_white_if_mem_queue: "v \<in> set (Q_list (queue s)) \<Longrightarrow> \<not> white s v"
  assumes not_white_if_parent: "P_lookup (parent s) v = Some u \<Longrightarrow> \<not> white s u"
  assumes black_imp_adjacency_not_white: "\<lbrakk> alt s u v; {u, v} \<in> G.E G; black s u \<rbrakk> \<Longrightarrow> \<not> white s v"
  assumes queue_sorted_wrt_d: "sorted_wrt (\<lambda>u v. d (parent s) u \<le> d (parent s) v) (Q_list (queue s))"
  assumes d_last_queue_le:
    "\<not> Q_is_empty (queue s) \<Longrightarrow>
     d (parent s) (last (Q_list (queue s))) \<le> d (parent s) (Q_head (queue s)) + 1"
  assumes d_triangle_inequality:
    "\<lbrakk> alt_path (Q s u) (Not \<circ> Q s u) (G.E G) p u v; \<not> white s u; \<not> white s v \<rbrakk> \<Longrightarrow>
     d (parent s) v \<le> d (parent s) u + path_length p"

abbreviation \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_bfs_invar' :: "'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> bool" where
  "alt_bfs_invar' G1 G2 src s \<equiv>
   alt_bfs_invar
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update G1 G2 src P_update Q_snoc s"

abbreviation \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) alt_bfs_invar'' :: "('q, 'm) state \<Rightarrow> bool" where
  "alt_bfs_invar'' \<equiv> alt_bfs_invar' G1 G2 src"

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) follow_invar_parent_init:
  shows "follow_invar (P_lookup (parent (init src)))"
  using wf_empty
  by (simp add: init_def P.map_empty follow_invar_def)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) invar_queue_init:
  shows "Q_invar (queue (init src))"
  using Q.invar_empty
  by (auto simp add: init_def intro: Q.invar_snoc)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) invar_parent_init:
  shows "P_invar (parent (init src))"
  using P.invar_empty
  by (simp add: init_def)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) parent_src_init:
  shows "P_lookup (parent (init src)) src = None"
  by (simp add: init_def P.map_empty)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) parent_imp_alt_init:
  assumes "P_lookup (parent (init src)) v = Some u"
  shows "alt (init src) u v"
  using assms
  by (simp add: init_def P.map_empty)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) parent_imp_edge_init:
  assumes "P_lookup (parent (init src)) v = Some u"
  shows "{u, v} \<in> G.E G"
  using assms
  by (simp add: init_def P.map_empty)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) not_white_if_mem_queue_init:
  assumes "v \<in> set (Q_list (queue (init src)))"
  shows "\<not> white (init src) v"
  using assms Q.invar_empty
  by (simp add: init_def Q.list_snoc Q.list_empty is_discovered_def)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) not_white_if_parent_init:
  assumes "P_lookup (parent (init src)) v = Some u"
  shows "\<not> white (init src) u"
  using assms
  by (simp add: init_def P.map_empty)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) black_imp_adjacency_not_white_init:
  assumes "alt (init src) u v"
  assumes "{u, v} \<in> G.E G"
  assumes "black (init src) u"
  shows "\<not> white s v"
proof -
  have "u = src"
    using assms(3)
    by (simp add: is_discovered_def init_def P.map_empty)
  thus ?thesis
    using assms(3) Q.invar_empty
    by (simp add: init_def Q.list_snoc)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) queue_sorted_wrt_d_init:
  shows "sorted_wrt (\<lambda>u v. d (parent (init src)) u \<le> d (parent (init src)) v) (Q_list (queue (init src)))"
  using Q.invar_empty
  by (simp add: init_def Q.list_snoc Q.list_empty)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) d_last_queue_le_init:
  assumes "\<not> Q_is_empty (queue (init src))"
  shows "d (parent (init src)) (last (Q_list (queue (init src)))) \<le> d (parent (init src)) (Q_head (queue (init src))) + 1"
  using Q.invar_empty invar_queue_init
  by (simp add: init_def Q.list_snoc Q.list_empty Q.list_head)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) d_triangle_inequality_init:
  assumes "alt_path (Q (init src) u) (Not \<circ> Q (init src) u) (G.E G) p u v"
  assumes "\<not> white (init src) u"
  assumes "\<not> white (init src) v"
  shows "d (parent (init src)) v \<le> d (parent (init src)) u + path_length p"
  using assms
  by (simp add: is_discovered_def init_def P.map_empty)

text \<open>
Compared to @{term bfs.loop}, we need one additional invariant,
@{thm [source] alt_bfs_invar.parent_imp_alt}, which captures alternation.
\<close>

text \<open>
Let us verify that the loop invariants of @{term alt_bfs.alt_loop} are satisfied prior to the first
iteration of the loop.
\<close>

lemma (in alt_bfs_valid_input) alt_bfs_invar_init:
  shows "alt_bfs_invar'' (init src)"
proof (standard, goal_cases)
case 1
  show ?case using follow_invar_parent_init .
next
  case 2
  show ?case using invar_queue_init .
next
  case 3
  show ?case using invar_parent_init .
next
  case 4
  show ?case using parent_src_init .
next
  case (5 v u)
  thus ?case by (intro parent_imp_alt_init)
next
  case (6 v u)
  thus ?case by (intro parent_imp_edge_init)
next
  case (7 v)
  thus ?case by (intro not_white_if_mem_queue_init)
next
  case (8 v u)
  thus ?case by (intro not_white_if_parent_init)
next
  case (9 u v)
  thus ?case by (intro black_imp_adjacency_not_white_init)
next
  case 10
  show ?case using queue_sorted_wrt_d_init .
next
  case 11
  thus ?case by (intro d_last_queue_le_init)
next
  case (12 u p v)
  thus ?case by (intro d_triangle_inequality_init)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) distinct_adjacency:
  assumes "G.invar G1"
  assumes "G.invar G2"
  shows "distinct (adjacency G1 G2 s v)"
  using assms
  by (auto simp add: adjacency_def intro: G.distinct_adjacency_list)

text \<open>
Let us now verify that the loop invariants are maintained. For this, let us first look at how the
different subroutines change the queue and parent map.
\<close>

lemma (in alt_bfs) list_queue_alt_fold_cong:
  assumes "G.invar G1"
  assumes "G.invar G2"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "\<not> DONE s"
  shows
    "Q_list (queue (alt_fold G1 G2 src s)) =
     Q_list (Q_tail (queue s)) @
     filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s)))"
proof -
  have
    "Q_list (queue (alt_fold G1 G2 src s)) =
     Q_list (queue (s\<lparr>queue := Q_tail (queue s)\<rparr>)) @
     filter
      (Not \<circ> is_discovered src (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)))
      (adjacency G1 G2 s (Q_head (queue s)))"
    using assms
    by (intro invar_tail distinct_adjacency list_queue_fold_cong) simp+
  thus ?thesis
    unfolding comp_apply
    by (simp add: is_discovered_def)
qed

lemma (in alt_bfs) lookup_parent_alt_fold_cong:
  assumes "G.invar G1"
  assumes "G.invar G2"
  assumes "P_invar (parent s)"
  shows
    "P_lookup (parent (alt_fold G1 G2 src s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s)))))"
proof -
  have
    "P_lookup (parent (alt_fold G1 G2 src s)) =
     override_on
      (P_lookup (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> is_discovered src (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>))) (adjacency G1 G2 s (Q_head (queue s)))))"
    using assms
    by (intro distinct_adjacency lookup_parent_fold_cong) simp
  thus ?thesis
    by (simp add: is_discovered_def)
qed

lemma (in alt_bfs_invar) lookup_parent_alt_fold_cong:
  shows
    "P_lookup (parent (alt_fold G1 G2 src s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s)))))"
  using invar_G1 invar_G2 invar_parent
  by (intro lookup_parent_alt_fold_cong)

lemma (in alt_bfs) T_alt_fold_cong:
  assumes "G.invar G1"
  assumes "G.invar G2"
  assumes "P_invar (parent s)"
  shows
    "T (parent (alt_fold G1 G2 src s)) =
     T (parent s) \<union>
     {(Q_head (queue s), v) |v. v \<in> set (adjacency G1 G2 s (Q_head (queue s))) \<and> \<not> is_discovered src (parent s) v}"
proof -
  have
    "T (parent (alt_fold G1 G2 src s)) =
     T (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)) \<union>
     {(Q_head (queue s), v) |v.
      v \<in> set (adjacency G1 G2 s (Q_head (queue s))) \<and>
      \<not> is_discovered src (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)) v}"
    using assms
    by (intro distinct_adjacency T_fold_cong) simp
  thus ?thesis
    by (simp add: is_discovered_def)
qed

lemma (in alt_bfs_invar) T_fold_cong:
  shows
    "T (parent (alt_fold G1 G2 src s)) =
     T (parent s) \<union>
     {(Q_head (queue s), v) |v. v \<in> set (adjacency G1 G2 s (Q_head (queue s))) \<and> \<not> is_discovered src (parent s) v}"
  using invar_G1 invar_G2 invar_parent
  by (intro T_alt_fold_cong)

text \<open>Next, we verify the maintenance of the loop invariants one by one.\<close>

locale alt_bfs_invar_not_DONE = alt_bfs_invar where P_update = P_update and Q_snoc = Q_snoc for
  P_update :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
assumes not_DONE: "\<not> DONE s"

abbreviation \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_bfs_invar_not_DONE' :: "'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> bool" where
  "alt_bfs_invar_not_DONE' G1 G2 src s \<equiv>
   alt_bfs_invar_not_DONE
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update G1 G2 src s P_update Q_snoc"

abbreviation \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) alt_bfs_invar_not_DONE'' :: "('q, 'm) state \<Rightarrow> bool" where
  "alt_bfs_invar_not_DONE'' \<equiv> alt_bfs_invar_not_DONE' G1 G2 src"

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) list_queue_non_empty:
  shows "Q_list (queue s) \<noteq> []"
  using invar_queue not_DONE
  by (intro list_queue_non_empty)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) head_queue_mem_queue:
  shows "Q_head (queue s) \<in> set (Q_list (queue s))"
  using invar_queue list_queue_non_empty
  by (simp add: Q.list_head)

lemma (in alt_bfs_invar_not_DONE) follow_invar_parent_alt_fold:
  shows "follow_invar (P_lookup (parent (alt_fold G1 G2 src s)))"
  unfolding follow_invar_def T_fold_cong
proof (rule wf_Un)
  let ?r =
    "{(Q_head (queue s), v) |v.
      v \<in> set (adjacency G1 G2 s (Q_head (queue s))) \<and> \<not> is_discovered src (parent s) v}"
  show "wf (T (parent s))"
    using follow_invar
    by (simp add: follow_invar_def)
  have "\<not> white s (Q_head (queue s))"
    by (intro head_queue_mem_queue not_white_if_mem_queue)
  thus "wf ?r"
    by (simp add: wf_def)
  show "Domain (T (parent s)) \<inter> Range ?r = {}"
    using not_white_if_parent
    by auto
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) invar_queue_alt_fold:
  assumes "G.invar G1"
  assumes "G.invar G2"
  assumes "Q_invar (queue s)"
  assumes "\<not> DONE s"
  shows "Q_invar (queue (alt_fold G1 G2 src s))"
  using assms
  by (auto simp add: adjacency_def intro: G.distinct_adjacency_list invar_tail invar_queue_fold)

lemma (in alt_bfs_invar_not_DONE) invar_queue_alt_fold:
  shows "Q_invar (queue (alt_fold G1 G2 src s))"
  using invar_G1 invar_G2 invar_queue not_DONE
  by (intro invar_queue_alt_fold)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) invar_parent_alt_fold:
  assumes "G.invar G1"
  assumes "G.invar G2"
  assumes "P_invar (parent s)"
  shows "P_invar (parent (alt_fold G1 G2 src s))"
  using assms
  by (intro distinct_adjacency invar_parent_fold) simp

lemma (in alt_bfs_invar) invar_parent_alt_fold:
  shows "P_invar (parent (alt_fold G1 G2 src s))"
  using invar_G1 invar_G2 invar_parent
  by (intro invar_parent_alt_fold)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) src_not_white:
  shows "\<not> white s src"
  by (simp add: is_discovered_def)

lemma (in alt_bfs_invar) parent_src_alt_fold:
  shows "P_lookup (parent (alt_fold G1 G2 src s)) src = None"
  using src_not_white
  by (simp add: lookup_parent_alt_fold_cong parent_src)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) not_white_imp_lookup_parent_alt_fold_eq_lookup_parent:
  assumes "\<not> white s v"
  shows "P_lookup (parent (alt_fold G1 G2 src s)) v = P_lookup (parent s) v"
  using assms
  by (simp add: lookup_parent_alt_fold_cong)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) whiteI:
  assumes "P_lookup (parent s) v \<noteq> Some u"
  assumes "P_lookup (parent (alt_fold G1 G2 src s)) v = Some u"
  shows "white s v"
proof -
  have "P_lookup (parent s) v = None"
    using assms
    by (auto simp add: lookup_parent_alt_fold_cong override_on_def is_discovered_def split: if_splits(2))
  thus ?thesis
    using assms(2) parent_src_alt_fold
    by (auto simp add: is_discovered_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) white_not_white_alt_foldD:
  assumes "white s v"
  assumes "\<not> white (alt_fold G1 G2 src s) v"
  shows
    "v \<in> set (adjacency G1 G2 s (Q_head (queue s)))"
    "P_lookup (parent (alt_fold G1 G2 src s)) v = Some (Q_head (queue s))"
proof -
  show "v \<in> set (adjacency G1 G2 s (Q_head (queue s)))"
    using assms
    by (fastforce simp add: is_discovered_def lookup_parent_alt_fold_cong)
  thus "P_lookup (parent (alt_fold G1 G2 src s)) v = Some (Q_head (queue s))"
    using assms
    by (auto simp add: lookup_parent_alt_fold_cong)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) mem_E1_iff_not_mem_E2:
  assumes "e \<in> G.E G"
  shows "e \<notin> G.E G1 = P'' e"
proof (standard, goal_cases)
  case 1
  thus ?case
    using assms invar_G1 invar_G2
    by (simp add: G.E_union_cong)
next
  case 2
  then show ?case
    using E1_E2_disjoint
    by blast
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) mem_E_if_mem_E1:
  assumes "e \<in> G.E G1"
  shows "e \<in> G.E G"
  using invar_G1 invar_G2 assms
  by (simp add: G.E_union_cong)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) P_iff_mem_adjacency:
  assumes "G.invar G"
  shows "P G u v \<longleftrightarrow> v \<in> set (G.adjacency_list G u)"
proof -
  have "v \<in> set (G.adjacency_list G u) \<longleftrightarrow> (\<exists>s. Map_lookup G u = Some s \<and> v \<in> G.S.set s)"
    using G.mem_adjacency_iff_lookup_eq_Some
    .
  also have "... \<longleftrightarrow> (\<exists>s. Map_lookup G u = Some s \<and> Set_isin s v)"
    using assms
    by (auto simp add: G.invar_def G.M.ran_def G.S.set_isin)
  also have "... \<longleftrightarrow> P G u v"
    by (simp add: P_def split: option.split)
  finally show ?thesis
    ..
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) P_P''_cong:
  shows "P G2 u v \<longleftrightarrow> P'' {u, v}"
  using invar_G2
  by (subst P_iff_mem_adjacency) (simp add: G2.mem_adjacency_iff_edge)+

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) mem_adjacency_imp_alt:
  assumes "v \<in> set (adjacency G1 G2 s u)"
  shows "alt s u v"
proof (standard, goal_cases)
  case 1
  hence "v \<in> set (G.adjacency_list G1 u)"
    using assms
    by (simp add: adjacency_def)
  hence "{u, v} \<in> G.E G1"
    by (simp add: G1.mem_adjacency_iff_edge)
  hence "\<not> P'' {u, v}"
    using mem_E1_iff_not_mem_E2
    by (auto intro: mem_E_if_mem_E1)
  thus ?case
    by (simp add: P_P''_cong)
next
  case 2
  thus ?case
  proof (rule contrapos_pp)
    assume "\<not> P' G2 (P_lookup (parent s) u) u"
    hence "v \<in> set (G.adjacency_list G2 u)"
      using assms
      by (simp add: adjacency_def)
    hence "P'' {u, v}"
      by (simp add: G2.mem_adjacency_iff_edge)
    thus "\<not> \<not> P G2 u v"
      by (simp add: P_P''_cong)
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) head_queueI:
  assumes "P_lookup (parent s) v \<noteq> Some u"
  assumes "P_lookup (parent (alt_fold G1 G2 src s)) v = Some u"
  shows "u = Q_head (queue s)"
  using assms
  by (simp add: lookup_parent_alt_fold_cong override_on_def split: if_splits(2))

lemma (in alt_bfs_invar_not_DONE) parent_imp_alt_alt_fold:
  assumes "P_lookup (parent (alt_fold G1 G2 src s)) v = Some u"
  shows "alt (alt_fold G1 G2 src s) u v"
proof (cases "P_lookup (parent s) v = Some u")
  case True
  thus ?thesis
    using parent_imp_alt not_white_if_parent
    by (simp add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent)
next
  case False
  hence "white s v"
    using assms
    by (intro whiteI)
  hence "v \<in> set (adjacency G1 G2 s (Q_head (queue s)))"
    using assms
    by (auto simp add: is_discovered_def intro: white_not_white_alt_foldD(1))
  hence "alt s (Q_head (queue s)) v"
    by (intro mem_adjacency_imp_alt)
  hence "alt (alt_fold G1 G2 src s) (Q_head (queue s)) v"
    using head_queue_mem_queue
    by (auto simp add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent dest: not_white_if_mem_queue)
  thus ?thesis
    using False assms
    by (blast dest: head_queueI)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) mem_E_if_mem_E2:
  assumes "e \<in> G.E G2"
  shows "e \<in> G.E G"
  using invar_G1 invar_G2 assms
  by (simp add: G.E_union_cong)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) mem_adjacency_imp_edge:
  assumes "v \<in> set (adjacency G1 G2 s u)"
  shows "{u, v} \<in> G.E G"
  using assms
  by
    (cases "P' G2 (P_lookup (parent s) u) u")
    (auto
      simp add: adjacency_def G1.mem_adjacency_iff_edge G2.mem_adjacency_iff_edge
      intro: mem_E_if_mem_E1 mem_E_if_mem_E2)

lemma (in alt_bfs_invar_not_DONE) parent_imp_edge_alt_fold:
  assumes "P_lookup (parent (alt_fold G1 G2 src s)) v = Some u"
  shows "{u, v} \<in> G.E G"
proof (cases "P_lookup (parent s) v = Some u")
  case True
  thus ?thesis
    by (intro parent_imp_edge)
next
  case False
  hence "u = Q_head (queue s)"
    using assms
    by (intro head_queueI)
  hence "v \<in> set (adjacency G1 G2 s u)"
    using False assms
    by (auto simp add: is_discovered_def dest: whiteI intro: white_not_white_alt_foldD(1))
  thus ?thesis
    by (intro mem_adjacency_imp_edge)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) not_white_imp_not_white_alt_fold:
  assumes "\<not> white s v"
  shows "\<not> white (alt_fold G1 G2 src s) v"
  using assms
  by (auto simp add: is_discovered_def lookup_parent_alt_fold_cong)

lemma (in alt_bfs_invar_not_DONE) list_queue_alt_fold_cong:
  shows
    "Q_list (queue (alt_fold G1 G2 src s)) =
     Q_list (Q_tail (queue s)) @
     filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s)))"
  using invar_G1 invar_G2 invar_queue invar_parent not_DONE
  by (intro list_queue_alt_fold_cong)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) not_white_if_mem_queue_alt_fold:
  assumes "v \<in> set (Q_list (queue (alt_fold G1 G2 src s)))"
  shows "\<not> white (alt_fold G1 G2 src s) v"
proof (cases "v \<in> set (Q_list (queue s))")
  case True
  thus ?thesis
    by (intro not_white_if_mem_queue not_white_imp_not_white_alt_fold)
next
  case False
  hence "v \<notin> set (Q_list (Q_tail (queue s)))"
    using invar_queue list_queue_non_empty
    by (auto simp add: Q.list_tail intro: list.set_sel(2))
  hence "v \<in> set (adjacency G1 G2 s (Q_head (queue s))) \<and> \<not> is_discovered src (parent s) v"
    using assms
    by (simp add: list_queue_alt_fold_cong)
  thus ?thesis
    using assms
    by (fastforce simp add: is_discovered_def lookup_parent_alt_fold_cong)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) not_white_head_queue:
  shows "\<not> white s (Q_head (queue s))"
  using head_queue_mem_queue
  by (intro not_white_if_mem_queue)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) not_white_if_parent_alt_fold:
  assumes "P_lookup (parent (alt_fold G1 G2 src s)) v = Some u"
  shows "\<not> white (alt_fold G1 G2 src s) u"
proof (cases "P_lookup (parent s) v = Some u")
  case True
  thus ?thesis
    by (intro not_white_if_parent not_white_imp_not_white_alt_fold)
next
  case False
  hence "u = Q_head (queue s)"
    using assms
    by (intro head_queueI)
  thus ?thesis
    using not_white_head_queue
    by (intro not_white_imp_not_white_alt_fold) simp
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) vertex_color_induct [case_names white gray black]:
  assumes "white s v \<Longrightarrow> Q' s v"
  assumes "gray s v \<Longrightarrow> Q' s v"
  assumes "black s v \<Longrightarrow> Q' s v"
  shows "Q' s v"
  using assms
  by blast

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) whiteD:
  assumes "white s v"
  shows "\<not> black (alt_fold G1 G2 src s) v"
  using assms
  by (auto simp add: is_discovered_def lookup_parent_alt_fold_cong list_queue_alt_fold_cong)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) mem_adjacency_if_edge:
  assumes "alt s u v"
  assumes "{u, v} \<in> G.E G"
  assumes "\<not> white s u"
  shows "v \<in> set (adjacency G1 G2 s u)"
proof (cases "P' G2 (P_lookup (parent s) u) u")
  case True
  hence "{u, v} \<in> G.E G1"
    using assms(2)
    by (simp add: assms(1) P_P''_cong mem_E1_iff_not_mem_E2[symmetric])
  thus ?thesis
    using True
    by (simp add: G1.mem_adjacency_iff_edge adjacency_def)
next
  case False
  hence "{u, v} \<in> G.E G2"
    using assms(2)
    by (simp add: assms(1) P_P''_cong mem_E1_iff_not_mem_E2)
  thus ?thesis
    using False
    by (simp add: G2.mem_adjacency_iff_edge adjacency_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) head_queueI_2:
  assumes "v \<in> set (Q_list (queue s))"
  assumes "v \<notin> set (Q_list (queue (alt_fold G1 G2 src s)))"
  shows "v = Q_head (queue s)"
proof -
  have "Q_list (queue s) = Q_head (queue s) # Q_list (Q_tail (queue s))"
    using invar_queue list_queue_non_empty
    by (intro Q.list_queue)
  thus ?thesis
    using assms
    by (simp add: list_queue_alt_fold_cong)
qed

lemma (in alt_bfs_invar_not_DONE) black_imp_adjacency_not_white_alt_fold:
  assumes "alt (alt_fold G1 G2 src s) u v"
  assumes "{u, v} \<in> G.E G"
  assumes "black (alt_fold G1 G2 src s) u"
  shows "\<not> white (alt_fold G1 G2 src s) v"
proof (induct s u rule: vertex_color_induct)
  case white
  thus ?case
    using assms(3) whiteD
    by blast
next
  case gray
  hence "alt s u v"
    using assms(1)
    by (simp add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent)
  hence "v \<in> set (adjacency G1 G2 s u)"
    using assms(2) gray
    by (intro mem_adjacency_if_edge) simp+
  hence "v \<in> set (adjacency G1 G2 s (Q_head (queue s)))"
    using gray assms(3)
    by (auto dest: head_queueI_2)
  thus ?case
    by (simp add: is_discovered_def lookup_parent_alt_fold_cong override_on_def)
next
  case black
  hence "alt s u v"
    using assms(1)
    by (simp add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent)
  thus ?case
    using assms(2) black
    by (intro black_imp_adjacency_not_white not_white_imp_not_white_alt_fold)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) parent_alt_fold:
  shows "Parent_Relation.parent (P_lookup (parent (alt_fold G1 G2 src s)))"
proof (standard, goal_cases)
  case 1
  show ?case
    by (intro follow_invar_parent_alt_fold)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) not_white_imp_rev_follow_alt_fold_eq_rev_follow:
  assumes "\<not> white s v"
  shows "rev_follow (parent (alt_fold G1 G2 src s)) v = rev_follow (parent s) v"
    using assms
proof (induct v rule: follow_pinduct)
  case (1 v)
  show ?case
  proof (cases "v = src")
    case True
    hence
      "P_lookup (parent s) v = None"
      "P_lookup (parent (alt_fold G1 G2 src s)) v = None"
      using parent_src parent_src_alt_fold
      by simp+
    hence
      "rev_follow (parent s) v = [v]"
      "rev_follow (parent (alt_fold G1 G2 src s)) v = [v]"
      using "1.prems"(1) parent_alt_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      by fastforce
  next
    case False
    then obtain u where u:
      "P_lookup (parent s) v = Some u"
      "\<not> white s u"
      using "1.prems"(1) not_white_if_parent
      by (auto simp add: is_discovered_def)
    moreover hence "P_lookup (parent (alt_fold G1 G2 src s)) v = Some u"
      using "1.prems"
      by (simp add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent)
    ultimately have
      "rev_follow (parent s) v = rev_follow (parent s) u @ [v]"
      "rev_follow (parent (alt_fold G1 G2 src s)) v = rev_follow (parent (alt_fold G1 G2 src s)) u @ [v]"
      using "1.prems"(1) parent_alt_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      using u
      by (simp add: "1.hyps")
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) mem_queue_imp_d_le:
  assumes "v \<in> set (Q_list (queue s))"
  shows "d (parent s) v \<le> d (parent s) (last (Q_list (queue s)))"
proof (cases "v = last (Q_list (queue s))")
  case True
  thus ?thesis
    by simp
next
  case False
  have "\<not> Q_is_empty (queue s)"
    using invar_queue assms
    by (auto simp add: Q.is_empty)
  thus ?thesis
    using queue_sorted_wrt_d assms False sorted_wrt_imp_last
    by fastforce
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) mem_filterD:
  assumes "v \<in> set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))))"
  shows
    "d (parent (alt_fold G1 G2 src s)) v = d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
    "d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue s))) \<le> d (parent (alt_fold G1 G2 src s)) v"
proof -
  let ?u = "Q_head (queue s)"
  have "P_lookup (parent (alt_fold G1 G2 src s)) v = Some ?u"
    using assms
    by (simp add: lookup_parent_alt_fold_cong)
  hence "rev_follow (parent (alt_fold G1 G2 src s)) v = rev_follow (parent (alt_fold G1 G2 src s)) ?u @ [v]"
    using assms(1) parent_alt_fold
    by (simp add: parent.follow_psimps)
  thus d_eq: "d (parent (alt_fold G1 G2 src s)) v = d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
    using assms(1) parent_alt_fold parent.follow_non_empty
    by (fastforce simp add: G.path_length_snoc)

  have "d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue s))) = d (parent s) (last (Q_list (queue s)))"
    using assms list_queue_non_empty not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  also have "... \<le> d (parent s) ?u + 1"
    using not_DONE d_last_queue_le
    by (simp add: DONE_def)
  also have "... = d (parent (alt_fold G1 G2 src s)) ?u + 1"
    using assms not_white_head_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  also have "... = d (parent (alt_fold G1 G2 src s)) v"
    unfolding d_eq
    ..
  finally show "d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue s))) \<le> d (parent (alt_fold G1 G2 src s)) v"
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) queue_sorted_wrt_d_alt_fold_aux:
  assumes u_mem_tail_queue: "u \<in> set (Q_list (Q_tail (queue s)))"
  assumes v_mem_filter: "v \<in> set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))))"
  shows "d (parent (alt_fold G1 G2 src s)) u \<le> d (parent (alt_fold G1 G2 src s)) v"
proof -
  have u_mem_queue: "u \<in> set (Q_list (queue s))"
    using u_mem_tail_queue invar_queue list_queue_non_empty
    by (auto simp add: Q.list_tail intro: list.set_sel(2))
  have "d (parent (alt_fold G1 G2 src s)) u = d (parent s) u"
    using u_mem_queue not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  also have "... \<le> d (parent s) (last (Q_list (queue s)))"
    using u_mem_queue
    by (intro mem_queue_imp_d_le)
  also have "... = d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue s)))"
    using list_queue_non_empty not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  also have "... \<le> d (parent (alt_fold G1 G2 src s)) v"
    using v_mem_filter
    by (intro mem_filterD(2))
  finally show ?thesis
    .
qed

lemma (in alt_bfs_invar_not_DONE) queue_sorted_wrt_d_alt_fold:
  shows "sorted_wrt (\<lambda>u v. d (parent (alt_fold G1 G2 src s)) u \<le> d (parent (alt_fold G1 G2 src s)) v) (Q_list (queue (alt_fold G1 G2 src s)))"
proof -
  let ?P = "\<lambda>u v. d (parent (alt_fold G1 G2 src s)) u \<le> d (parent (alt_fold G1 G2 src s)) v"
  have "sorted_wrt ?P (Q_list (queue s))"
    using queue_sorted_wrt_d not_white_if_mem_queue sorted_wrt_mono_rel[of "(Q_list (queue s))"]
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  hence "sorted_wrt ?P (Q_list (Q_tail (queue s)))"
    by (simp add: Q.list_queue[OF invar_queue list_queue_non_empty])
  moreover have "sorted_wrt ?P (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))))"
    by (auto simp add: mem_filterD(1) intro: sorted_wrt_if)
  moreover have
    "\<forall>u\<in>set (Q_list (Q_tail (queue s))).
      \<forall>v\<in>set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s)))).
       d (parent (alt_fold G1 G2 src s)) u \<le> d (parent (alt_fold G1 G2 src s)) v"
    by (blast intro: queue_sorted_wrt_d_alt_fold_aux)
  ultimately show ?thesis 
    by (simp add: list_queue_alt_fold_cong sorted_wrt_append)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) d_last_queue_le_alt_fold_aux:
  assumes "\<not> Q_is_empty (queue (alt_fold G1 G2 src s))"
  shows "d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue (alt_fold G1 G2 src s)))) \<le> d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
proof (cases "filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))) = []")
  case True
  hence list_tail_non_empty: "Q_list (Q_tail (queue s)) \<noteq> []"
    using invar_queue_alt_fold assms
    by (simp add: list_queue_alt_fold_cong Q.is_empty)

  hence "last (Q_list (queue (alt_fold G1 G2 src s))) = last (Q_list (Q_tail (queue s)))"
    unfolding list_queue_alt_fold_cong last_appendL[OF True]
    by blast
  hence "last (Q_list (queue (alt_fold G1 G2 src s))) = last (Q_list (queue s))"
    using list_tail_non_empty
    by (simp add: Q.list_queue[OF invar_queue list_queue_non_empty])
  hence "d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue (alt_fold G1 G2 src s)))) = d (parent s) (last (Q_list (queue s)))"
    using list_queue_non_empty not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  also have "... \<le> d (parent s) (Q_head (queue s)) + 1"
    using invar_queue list_queue_non_empty d_last_queue_le
    by (simp add: Q.is_empty)
  also have "... = d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
    using not_white_head_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  finally show ?thesis
    .
next
  case False
  hence
    "last (Q_list (queue (alt_fold G1 G2 src s))) \<in>
     set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))))"
    unfolding list_queue_alt_fold_cong last_appendR[OF False]
    by (intro last_in_set)
  thus ?thesis
    by (simp add: mem_filterD(1))
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) mem_queue_imp_d_ge:
  assumes "v \<in> set (Q_list (queue s))"
  shows "d (parent s) (Q_head (queue s)) \<le> d (parent s) v"
proof (cases "v = Q_head (queue s)")
  case True
  thus ?thesis
    by simp
next
  case False
  have "\<not> Q_is_empty (queue s)"
    using invar_queue assms
    by (auto simp add: Q.is_empty)
  moreover hence "Q_head (queue s) = hd (Q_list (queue s))"
    using invar_queue Q.list_head
    by (simp add: Q.is_empty)
  ultimately show ?thesis
    using queue_sorted_wrt_d assms False sorted_wrt_imp_hd
    by fastforce
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) d_last_queue_le_alt_fold_aux_2:
  assumes "\<not> Q_is_empty (queue (alt_fold G1 G2 src s))"
  shows "d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) \<le> d (parent (alt_fold G1 G2 src s)) (Q_head (queue (alt_fold G1 G2 src s)))"
proof (cases "Q_list (Q_tail (queue s)) = []")
  case True
  have "Q_head (queue (alt_fold G1 G2 src s)) = hd (Q_list (queue (alt_fold G1 G2 src s)))"
    using invar_queue_alt_fold assms
    by (simp add: Q.is_empty Q.list_head)
  hence
    "Q_head (queue (alt_fold G1 G2 src s)) =
     hd (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))))"
    by (simp add: True list_queue_alt_fold_cong)
  moreover have "filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))) \<noteq> []"
    using invar_queue_alt_fold assms
    by (simp add: True Q.is_empty list_queue_alt_fold_cong)
  ultimately have head_queue_alt_fold_mem_filter:
    "Q_head (queue (alt_fold G1 G2 src s)) \<in>
     set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))))"
    using list.set_sel(1)
    by metis

  have "d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) = d (parent s) (Q_head (queue s))"
    using not_white_head_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  also have "... \<le> d (parent s) (last (Q_list (queue s)))"
    by (intro head_queue_mem_queue mem_queue_imp_d_le)
  also have "... = d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue s)))"
    using list_queue_non_empty not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  also have "... \<le> d (parent (alt_fold G1 G2 src s)) (Q_head (queue (alt_fold G1 G2 src s)))"
    using head_queue_alt_fold_mem_filter
    by (intro mem_filterD(2))
  finally show ?thesis
    .
next
  case False
  have "Q_head (queue (alt_fold G1 G2 src s)) = hd (Q_list (queue (alt_fold G1 G2 src s)))"
    using invar_queue_alt_fold assms
    by (simp add: Q.is_empty Q.list_head)
  hence "Q_head (queue (alt_fold G1 G2 src s)) = hd (Q_list (Q_tail (queue s)))"
    using False
    by (simp add: list_queue_alt_fold_cong)
  hence head_queue_alt_fold_mem_queue: "Q_head (queue (alt_fold G1 G2 src s)) \<in> set (Q_list (queue s))"
    using False invar_queue list_queue_non_empty
    by (auto simp add: Q.list_tail intro: list.set_sel(2))

  have "d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) = d (parent s) (Q_head (queue s))"
    using not_white_head_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  also have "... \<le> d (parent s) (Q_head (queue (alt_fold G1 G2 src s)))"
    using head_queue_alt_fold_mem_queue
    by (intro mem_queue_imp_d_ge)
  also have "... = d (parent (alt_fold G1 G2 src s)) (Q_head (queue (alt_fold G1 G2 src s)))"
    using head_queue_alt_fold_mem_queue not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
  finally show ?thesis
    .
qed

lemma (in alt_bfs_invar_not_DONE) d_last_queue_le_alt_fold:
  assumes "\<not> Q_is_empty (queue (alt_fold G1 G2 src s))"
  shows
    "d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue (alt_fold G1 G2 src s)))) \<le>
     d (parent (alt_fold G1 G2 src s)) (Q_head (queue (alt_fold G1 G2 src s))) + 1"
proof -
  have "d (parent (alt_fold G1 G2 src s)) (last (Q_list (queue (alt_fold G1 G2 src s)))) \<le> d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
    using assms
    by (intro d_last_queue_le_alt_fold_aux)
  also have "... \<le> d (parent (alt_fold G1 G2 src s)) (Q_head (queue (alt_fold G1 G2 src s))) + 1"
    using assms
    by (auto intro: d_last_queue_le_alt_fold_aux_2)
  finally show ?thesis
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) parent_imp_rev_follow:
  assumes "P_lookup (parent s) v = Some u"
  shows "rev_follow (parent s) v = rev_follow (parent s) u @ [v]"
proof -
  obtain p where
    "follow v = v # u # p"
    using assms
    by (elim parent_eq_SomeE)
  moreover hence "follow u = u # p"
    by (rule follow_Cons_ConsD(1))
  ultimately show ?thesis
    by simp
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) src_mem_V:
  shows "src \<in> G.V G"
  using src_mem_V2 invar_G1 invar_G2
  by (simp add: G.V_union_cong)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) alt_path_rev_follow_src:
  shows "alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) src) src src"
proof (rule alt_pathI, goal_cases)
  case 1
  then show ?case
    using parent_src alt_list_empty
    by (auto simp add: follow_psimps)
next
  case 2
  show ?case
    using parent_src src_mem_V
    by (auto simp add: G.V_def follow_psimps intro: walk_reflexive)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) P'E:
  assumes "P' G2 (P_lookup (parent s) v) v"
  obtains u where
    "P_lookup (parent s) v = Some u"
    "P'' {u, v}"
  using assms
  by (simp add: P'_def P_P''_cong split: option.splits(2))

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) parent_rev_followE:
  assumes "P_lookup (parent s) v = Some u"
  obtains p where "rev_follow (parent s) v = p @ [u, v]"
  using assms
  by (auto elim: parent_eq_SomeE)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) not_P'E:
  assumes "\<not> P' G2 (P_lookup (parent s) v) v"
  assumes "v \<noteq> src"
  assumes "\<not> white s v"
  obtains u where
    "P_lookup (parent s) v = Some u"
    "\<not> P'' {u, v}"
  using assms parent_src
  by (simp add: P'_def is_discovered_def P_P''_cong split: option.splits(2))

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) not_P'D:
  assumes "\<not> P' G2 (P_lookup (parent s) v) v"
  assumes "v \<noteq> src"
  assumes "\<not> white s v"
  shows
    "edges_of_path (rev_follow (parent s) v) \<noteq> []"
    "\<not> P'' (last (edges_of_path (rev_follow (parent s) v)))"
proof -
  obtain u where
    "P_lookup (parent s) v = Some u"
    "\<not> P'' {u, v}"
    using assms
    by (elim not_P'E)
  thus
    "edges_of_path (rev_follow (parent s) v) \<noteq> []"
    "\<not> P'' (last (edges_of_path (rev_follow (parent s) v)))"
    by (auto simp add: P_P''_cong[symmetric] edges_of_path_append_2[of "[u, v]"] elim: parent_rev_followE)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) P'_P''_cong:
  shows "P' G2 (P_lookup (parent s) v) v \<longleftrightarrow> edges_of_path (rev_follow (parent s) v) \<noteq> [] \<and> P'' (last (edges_of_path (rev_follow (parent s) v)))"
proof (standard, goal_cases)
  case 1
  then obtain u where
    "P_lookup (parent s) v = Some u"
    "P'' {u, v}"
    by (elim P'E)
  thus ?case
    by (auto simp add: edges_of_path_append_2[of "[u, v]"] elim: parent_rev_followE)
next
  case 2
  show ?case
  proof (rule ccontr)
    assume assm: "\<not> P' G2 (P_lookup (state.parent s) v) v"
    have
      "v \<noteq> src"
      "\<not> white s v"
      using 2 parent_src
      by (auto simp add: follow_psimps is_discovered_def)
    with assm
    have "\<not> P'' (last (edges_of_path (rev_follow (parent s) v)))"
      by (intro not_P'D(2))
    thus False
      using 2
      by fast
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) rev_follow:
  shows
    "rev_follow (parent s) v \<noteq> []"
    "last (rev_follow (parent s) v) = v"
proof (goal_cases)
  case 1
  show ?case
    using follow_non_empty
    by simp
next
  case 2
  have "follow v = hd (follow v) # tl (follow v)"
    using follow_non_empty
    by simp
  thus ?case
    using follow_non_empty
    by (auto simp add: last_rev[symmetric] dest: follow_ConsD)
qed

lemma (in alt_bfs_invar) alt_path_rev_follow_snocI:
  assumes "alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) u) src u"
  assumes "{u, v} \<in> G.E G"
  assumes "alt s u v"
  assumes "\<not> white s u"
  shows "alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) u @ [v]) src v"
proof (rule alt_pathI, goal_cases)
  case 1
  show ?case
  proof (cases "P' G2 (P_lookup (parent s) u) u")
    case True
    hence
      "edges_of_path (rev_follow (parent s) u) \<noteq> []"
      "P'' (last (edges_of_path (rev_follow (parent s) u)))"
      by (simp_all add: P'_P''_cong)
    moreover have "alt_list (Not \<circ> P'') P'' (edges_of_path [u, v])"
      using True alt_list_step alt_list_empty
      by (fastforce simp add: assms(3) P_P''_cong[symmetric])
    ultimately have "alt_list P'' (Not \<circ> P'') (edges_of_path (rev_follow (parent s) u) @ edges_of_path [u, v])"
      using assms(1)
      by (auto dest: alt_pathD(1) intro: alt_list_append_2')
    thus ?thesis
      by (simp add: rev_follow(2) edges_of_path_append_3[OF rev_follow(1)])
  next
    case not_P': False
    show ?thesis
    proof (cases "u = src")
      case True
      hence "rev_follow (parent s) u @ [v] = [u, v]"
        by (simp add: follow_psimps parent_src)
      moreover have "alt_list P'' (Not \<circ> P'') (edges_of_path [u, v])"
        using not_P' alt_list_step alt_list_empty
        by (fastforce simp add: assms(3) P_P''_cong[symmetric])
      ultimately show ?thesis
        by simp
    next
      case False
      hence
        "edges_of_path (rev_follow (parent s) u) \<noteq> []"
        "\<not> P'' (last (edges_of_path (rev_follow (parent s) u)))"
        using not_P' assms(4)
        by (auto dest: not_P'D)
      moreover have "alt_list P'' (Not \<circ> P'') (edges_of_path [u, v])"
        using not_P' alt_list_step alt_list_empty
        by (fastforce simp add: assms(3) P_P''_cong[symmetric])
      ultimately have "alt_list P'' (Not \<circ> P'') (edges_of_path (rev_follow (parent s) u) @ edges_of_path [u, v])"
        using assms(1)
        by (auto dest: alt_pathD(1) intro: alt_list_append_3')
      thus ?thesis
        by (simp add: rev_follow(2) edges_of_path_append_3[OF rev_follow(1)])
    qed
  qed
next
  case 2
  show ?case
    using assms(1, 2)
    by (fastforce dest: alt_pathD(2) edges_are_walks walk_transitive)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) not_white_imp_alt_path_rev_follow:
  assumes "\<not> white s v"
  shows "alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) v) src v"
  using assms
proof (induct v rule: follow_pinduct)
  case (1 v)
  show ?case
  proof (cases "v = src")
    case True
    thus ?thesis
      by (fastforce intro: alt_path_rev_follow_src)
  next
    case False
    then obtain u where
      u: "P_lookup (parent s) v = Some u"
      using "1.prems"
      by (auto simp add: is_discovered_def)
    hence
      "{u, v} \<in> G.E G"
      "alt s u v"
      "\<not> white s u"
      using parent_imp_edge parent_imp_alt not_white_if_parent
      by blast+
    moreover hence "alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) u) src u"
      using u
      by (intro "1.hyps")
    ultimately show ?thesis
      using u
      by (subst parent_imp_rev_follow) (auto intro: alt_path_rev_follow_snocI)
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) Q_P''_cong:
  assumes "P' G2 (P_lookup (parent s) v) v"
  shows
    "Q s v = (Not \<circ> P'')"
    "(Not \<circ> Q s v) = P''"
  using assms
  by auto

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) Q_P''_cong_2:
  assumes "\<not> P' G2 (P_lookup (parent s) v) v"
  shows
    "Q s v = P''"
    "(Not \<circ> Q s v) = (Not \<circ> P'')"
  using assms
  by auto

lemma (in alt_bfs_invar) alt_path_rev_follow_appendI:
  assumes alt_path: "alt_path (Q s u) (Not \<circ> Q s u) (G.E G) (p @ [v, w]) u w"
  assumes not_white: "\<not> white s u"
  shows "alt_path P'' (Not \<circ> P'') (G.E G) (butlast (rev_follow (parent s) u) @ p @ [v, w]) src w"
proof (rule alt_pathI, goal_cases)
  case 1
  have "alt_list P'' (Not \<circ> P'') (edges_of_path (rev_follow (parent s) u) @ edges_of_path (p @ [v, w]))"
  proof (cases "P' G2 (P_lookup (parent s) u) u")
    case True
    show ?thesis
    proof (rule alt_list_append_2', goal_cases)
      case 1
      show ?case
        using not_white
        by (auto intro: not_white_imp_alt_path_rev_follow alt_pathD(1))
    next
      case 2
      show ?case
        using alt_path
        unfolding Q_P''_cong(2)[OF True]
        unfolding Q_P''_cong(1)[OF True]
        by (intro alt_pathD(1))
    next
      case 3
      show ?case
        using True
        by (simp add: P'_P''_cong)
    next
      case 4
      show ?case
        using True
        by (simp add: P'_P''_cong)
    qed simp
  next
    case not_P': False
    have alt_list: "alt_list P'' (Not \<circ> P'') (edges_of_path (p @ [v, w]))"
      using assms(1)
      unfolding Q_P''_cong_2(2)[OF not_P']
      unfolding Q_P''_cong_2(1)[OF not_P']
      by (intro alt_pathD(1))
    show ?thesis
    proof (cases "u = src")
      case True
      hence "edges_of_path (rev_follow (parent s) u) = []"
        by (simp add: follow_psimps parent_src)
      thus ?thesis
        using alt_list
        by simp
    next
      case False
      show ?thesis
      proof (rule alt_list_append_3', goal_cases)
        case 1
        show ?case
          using not_white
          by (auto intro: not_white_imp_alt_path_rev_follow alt_pathD(1))
      next
        case 2
        show ?case
          using alt_list
          .
      next
        case 3
        show ?case
          using not_P' False not_white
          by (intro not_P'D(1))
      next
        case 4
        show ?case
          using not_P' False not_white
          by (auto dest: not_P'D(2))
      qed simp
    qed
  qed
  moreover have
    "edges_of_path (rev_follow (parent s) u) @ edges_of_path (p @ [v, w]) =
     edges_of_path (butlast (rev_follow (parent s) u) @ p @ [v, w])"
  proof -
    have "rev_follow (parent s) u = butlast (rev_follow (parent s) u) @ [last (rev_follow (parent s) u)]"
      using rev_follow(1)
      by (intro append_butlast_last_id[symmetric])
    also have "... = butlast (rev_follow (parent s) u) @ [hd (p @ [v, w])]"
      using alt_path
      by (auto simp add: rev_follow(2) walk_between_nonempty_path(3) dest: alt_pathD(2))
    finally show ?thesis
      by (subst edges_of_path_append_2[of "p @ [v, w]" "butlast (rev_follow (parent s) u)"]) simp+
  qed
  ultimately show ?case
    by fastforce
next
  case 2
  show ?case
    using assms
    by (fastforce intro: alt_pathD(2) not_white_imp_alt_path_rev_follow walk_betw_transitive_2)
qed

lemma (in alt_bfs_invar) alt_path_snoc_snocD:
  assumes alt_path: "alt_path P'' (Not \<circ> P'') (G.E G) (p @ [u, v]) src v"
  assumes not_white: "\<not> white s u"
  shows
    "{u, v} \<in> G.E G"
    "alt s u v"
proof (goal_cases)
  case 1
  show ?case
    using alt_path
    by (intro alt_pathD(2) walk_between_nonempty_path(1) path_snocD)
next
  case 2
  { let ?c = "p @ [u] @ tl (follow u)"
    assume assm: "P' G2 (P_lookup (parent s) u) u = P G2 u v"
    have rev_follow_alt_path: "alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) u) src u"
      using not_white
      by (intro not_white_imp_alt_path_rev_follow)
    hence follow_u_path: "walk_betw (G.E G) u (follow u) src"
      by (fastforce dest: alt_pathD(2) walk_symmetric)
    hence c_path: "walk_betw (G.E G) src ?c src"
      using alt_path alt_path_pref
      by (fastforce dest: alt_pathD(2) walk_transitive[where ?p = "p @ [u]"])
    hence "path (G.E G) ?c"
      by (intro walk_between_nonempty_path)
    moreover have "odd_cycle ?c"
    proof (rule odd_cycleI, goal_cases)
      case 1
      show ?case
      proof (cases "P'' {u, v}")
        case True
        have "even (path_length (p @ [u]))"
        proof -
          have "odd (path_length (p @ [u, v]))"
            using alt_path True
            by (fastforce simp add: edges_of_path_append_2[of "[u, v]"] dest: alt_pathD(1) odd_if_last)
          thus ?thesis
            by (simp add: edges_of_path_length)
        qed
        moreover have "odd (path_length (follow u))"
        proof -
          have "P G2 u v"
            using True
            by (simp add: P_P''_cong[symmetric])
          hence "P' G2 (P_lookup (parent s) u) u"
            by (simp add: assm)
          hence
            "edges_of_path (rev_follow (parent s) u) \<noteq> []"
            "P'' (last (edges_of_path (rev_follow (parent s) u)))"
            by (simp_all add: P'_P''_cong)
          hence "odd (path_length (rev_follow (parent s) u))"
            using rev_follow_alt_path
            by (fastforce dest: alt_pathD(1) odd_if_last)
          thus ?thesis
            by (simp add: edges_of_path_length)
        qed
        ultimately show ?thesis
          using follow_u_path edges_of_path_append_4[of "p @ [u]" "follow u"]
          by (auto dest: walk_between_nonempty_path(3))
      next
        case not_P'': False
        have "odd (path_length (p @ [u]))"
        proof -
          have "even (path_length (p @ [u, v]))"
            using alt_path not_P''
            by (fastforce simp add: edges_of_path_append_2[of "[u, v]"] dest: alt_pathD(1) even_if_last)
          thus ?thesis
            by (simp add: edges_of_path_length)
        qed
        moreover have "even (path_length (follow u))"
        proof (cases "u = src")
          case True
          thus ?thesis
            using parent_src
            by (simp add: follow_psimps edges_of_path_length)
        next
          case False
          have "\<not> P G2 u v"
            using not_P''
            by (simp add: P_P''_cong[symmetric])
          hence "\<not> P' G2 (P_lookup (parent s) u) u"
            by (simp add: assm)
          hence
            "edges_of_path (rev_follow (parent s) u) \<noteq> []"
            "\<not> P'' (last (edges_of_path (rev_follow (parent s) u)))"
            using False not_white
            by (auto dest: not_P'D)
          hence "even (path_length (rev_follow (parent s) u))"
            using rev_follow_alt_path
            by (fastforce dest: alt_pathD(1) even_if_last)
          thus ?thesis
            by (simp add: edges_of_path_length)
        qed
        ultimately show ?thesis
          using follow_u_path edges_of_path_append_4[of "p @ [u]" "follow u"]
          by (auto dest: walk_between_nonempty_path(3))
      qed
    next
      case 2
      show ?case
        using c_path
        by (simp add: walk_between_nonempty_path(3, 4))
    qed
    ultimately have False
      using no_odd_cycle
      by blast }
  thus ?case
    by force
qed

lemma (in alt_bfs_invar) white_imp_gray_ancestor:
  assumes "alt_path (Q s u) (Not \<circ> Q s u) (G.E G) p u w"
  assumes "\<not> white s u"
  assumes "white s w"
  obtains v where
    "v \<in> set p"
    "gray s v"
  using assms
proof (induct p arbitrary: w rule: path_rev_induct)
  case 1
  thus ?case
    by (auto dest: alt_pathD(2) walk_between_nonempty_path(2))
next
  case (2 v)
  hence "walk_betw (G.E G) u [v] w"
    by (intro alt_pathD(2))
  hence "[v] = [u] \<and> u = w"
    by (intro list_length_1) (auto dest: walk_between_nonempty_path(2-4))
  thus ?case
    using "2.prems"(3, 4)
    by fastforce
next
  case (3 v v' l)
  show ?case
  proof (induct s v rule: vertex_color_induct)
    case white
    have "alt_path (Q s u) (Not \<circ> Q s u) (G.E G) (l @ [v]) u v"
      using "3.prems"(2)
      by (intro alt_path_pref)
    with "3.prems"(1)
    show ?case
      using "3.prems"(3) white
      by (force intro: "3.hyps")
  next
    case gray
    thus ?case
      by (auto intro: "3.prems"(1))
  next
    case black
    have "alt_path P'' (Not \<circ> P'') (G.E G) (butlast (rev_follow (parent s) u) @ l @ [v, w]) src w"
      using "3.prems"(2, 3)
      by (intro alt_path_snoc_snoc alt_path_rev_follow_appendI)
    hence
      "{v, w} \<in> G.E G"
      "alt s v w"
      using black alt_path_snoc_snocD[where ?p = "butlast (rev_follow (parent s) u) @ l"]
      by simp+
    thus ?case
      using black black_imp_adjacency_not_white "3.prems"(4)
      by blast
  qed
qed

lemma (in alt_bfs_valid_input) parent_imp_d:
  assumes "Parent_Relation.parent (P_lookup (parent s))"
  assumes "P_lookup (parent s) v = Some u"
  shows "d (parent s) v = d (parent s) u + 1"
proof -
  have "rev_follow (parent s) v = rev_follow (parent s) u @ [v]"
    using assms
    by (simp add: parent.follow_psimps)
  thus ?thesis
    using parent.follow_non_empty[OF assms(1)]
    by (simp add: G.path_length_snoc)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) white_not_white_alt_foldD_2:
  assumes "white s v"
  assumes "\<not> white (alt_fold G1 G2 src s) v"
  shows "d (parent (alt_fold G1 G2 src s)) v = d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
  using parent_alt_fold assms
  by (fastforce intro: white_not_white_alt_foldD(2) parent_imp_d)

lemma (in alt_bfs_invar_not_DONE) d_triangle_inequality_alt_fold:
  assumes alt_path_p: "alt_path (Q (alt_fold G1 G2 src s) u) (Not \<circ> Q (alt_fold G1 G2 src s) u) (G.E G) p u v"
  assumes not_white_alt_fold_u: "\<not> white (alt_fold G1 G2 src s) u"
  assumes not_white_alt_fold_v: "\<not> white (alt_fold G1 G2 src s) v"
  shows "d (parent (alt_fold G1 G2 src s)) v \<le> d (parent (alt_fold G1 G2 src s)) u + path_length p"
proof -
  consider
    (white_white) "white s u \<and> white s v" |
    (white_not_white) "white s u \<and> \<not> white s v" |
    (gray_white) "gray s u \<and> white s v" |
    (black_white) "black s u \<and> white s v" |
    (not_white_not_white) "\<not> white s u \<and> \<not> white s v"
    by fast
  thus ?thesis
  proof (cases)
    case white_white
    hence "d (parent (alt_fold G1 G2 src s)) v = d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
      using not_white_alt_fold_v
      by (intro white_not_white_alt_foldD_2) simp
    also have "... = d (parent (alt_fold G1 G2 src s)) u"
      using white_white not_white_alt_fold_u
      by (intro white_not_white_alt_foldD_2[symmetric]) simp
    finally show ?thesis
      by simp
  next
    case white_not_white
    have alt_path_Cons: "alt_path (Q s (Q_head (queue s))) (Not \<circ> Q s (Q_head (queue s))) (G.E G) (Q_head (queue s) # p) (Q_head (queue s)) v"
    proof -
      have parent: "P_lookup (parent (alt_fold G1 G2 src s)) u = Some (Q_head (queue s))"
        using white_not_white not_white_alt_fold_u
        by (intro white_not_white_alt_foldD(2)) simp

      have "alt_path (Not \<circ> Q (alt_fold G1 G2 src s) u) (Q (alt_fold G1 G2 src s) u) (G.E G) (Q_head (queue s) # p) (Q_head (queue s)) v"
      proof (rule alt_path_ConsI[where ?v = u], goal_cases)
        case 1
        show ?case
          using alt_path_p
          .
      next
        case 2
        show ?case
          using parent
          by (intro parent_imp_edge_alt_fold)
      next
        case 3
        show ?case
          using parent
          by (simp add: P'_def P_P''_cong[symmetric])
      qed
      moreover have "Not \<circ> Q (alt_fold G1 G2 src s) u = Q (alt_fold G1 G2 src s) (Q_head (queue s))"
        using parent
        by
          (cases "P' G2 (P_lookup (parent (alt_fold G1 G2 src s)) u) u")
          (auto simp add: P'_def dest: parent_imp_alt_alt_fold)
      moreover hence "Q (alt_fold G1 G2 src s) u = Not \<circ> Q (alt_fold G1 G2 src s) (Q_head (queue s))"
        by fastforce
      ultimately have "alt_path (Q (alt_fold G1 G2 src s) (Q_head (queue s))) (Not \<circ> Q (alt_fold G1 G2 src s) (Q_head (queue s))) (G.E G) (Q_head (queue s) # p) (Q_head (queue s)) v"
        by auto
      thus ?thesis
        using not_white_head_queue
        by (simp add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent)
    qed
    
    have "d (parent (alt_fold G1 G2 src s)) v = d (parent s) v"
      using white_not_white
      by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
    also have "... \<le> d (parent s) (Q_head (queue s)) + path_length (Q_head (queue s) # p)"
      using not_white_head_queue white_not_white alt_path_Cons
      by (auto intro: d_triangle_inequality)
    also have "... = d (parent s) (Q_head (queue s)) + 1 + path_length p"
      using alt_path_p
      by (auto simp add: G.path_length_Cons dest: alt_pathD(2))
    also have "... = d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1 + path_length p"
      using not_white_head_queue
      by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
    also have "... = d (parent (alt_fold G1 G2 src s)) u + path_length p"
      using white_not_white not_white_alt_fold_u
      by (simp add: white_not_white_alt_foldD_2)
    finally show ?thesis
      .
  next
    case gray_white
    hence "d (parent (alt_fold G1 G2 src s)) v = d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
      using not_white_alt_fold_v
      by (intro white_not_white_alt_foldD_2) simp
    also have "... = d (parent s) (Q_head (queue s)) + 1"
      using not_white_head_queue
      by (auto simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
    also have "... \<le> d (parent s) u + 1"
      using gray_white
      by (intro mem_queue_imp_d_ge add_right_mono) simp
    also have "... = d (parent (alt_fold G1 G2 src s)) u + 1"
      using gray_white
      by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
    also have "... \<le> d (parent (alt_fold G1 G2 src s)) u + path_length p"
      using alt_path_p gray_white
      by (fastforce dest: alt_pathD(2) intro: G.path_length_geq_1I add_left_mono)
    finally show ?thesis
      .
  next
    case black_white
    hence "alt_path (Q s u) (Not \<circ> Q s u) (G.E G) p u v"
      using alt_path_p
      by (simp add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent)
    then obtain w where
      "w \<in> set p" and
      gray_w: "gray s w"
      using black_white
      by (elim white_imp_gray_ancestor) simp+
    then obtain q r where
      p: "p = q @ tl r" and
      path_q: "walk_betw (G.E G) u q w" and
      path_r: "walk_betw (G.E G) w r v"
      using alt_path_p
      by (auto simp add: in_set_conv_decomp dest: alt_pathD(2) elim: G.path_vertex_decompE)
    hence "alt_path (Q (alt_fold G1 G2 src s) u) (Not \<circ> Q (alt_fold G1 G2 src s) u) (G.E G) q u w"
      using alt_path_p
      by (fastforce dest: walk_between_nonempty_path(2, 4) alt_path_pref_2)
    hence alt_path_q: "alt_path (Q s u) (Not \<circ> Q s u) (G.E G) q u w"
      using black_white
      by (simp add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent)
    have path_length_p: "path_length p = path_length q + path_length r"
      using path_q path_r
      by (auto simp add: p dest: walk_between_nonempty_path(2-4) intro: G.path_length_append_2)

    have "d (parent (alt_fold G1 G2 src s)) v = d (parent (alt_fold G1 G2 src s)) (Q_head (queue s)) + 1"
      using black_white not_white_alt_fold_v
      by (intro white_not_white_alt_foldD_2) simp
    also have "... = d (parent s) (Q_head (queue s)) + 1"
      using not_white_head_queue
      by (auto simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
    also have "... \<le> d (parent s) w + 1"
      using gray_w
      by (intro mem_queue_imp_d_ge add_right_mono) simp
    also have "... \<le> d (parent s) u + path_length q + 1"
      using alt_path_q black_white gray_w
      by (auto intro: d_triangle_inequality add_right_mono)
    also have "... \<le> d (parent s) u + path_length p"
      using path_r gray_w black_white G.path_length_geq_1I
      by (fastforce simp add: path_length_p)
    also have "... = d (parent (alt_fold G1 G2 src s)) u + path_length p"
      using black_white
      by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
    finally show ?thesis
      .
  next
    case not_white_not_white
    hence "d (parent (alt_fold G1 G2 src s)) v = d (parent s) v"
      by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
    also have "... \<le> d (parent s) u + path_length p"
      using alt_path_p not_white_not_white
      by (intro d_triangle_inequality) (simp_all add: not_white_imp_lookup_parent_alt_fold_eq_lookup_parent)
    also have "... = d (parent (alt_fold G1 G2 src s)) u + path_length p"
      using not_white_not_white
      by (simp add: not_white_imp_rev_follow_alt_fold_eq_rev_follow)
    finally show ?thesis
      .
  qed
qed

lemma (in alt_bfs_invar_not_DONE) alt_bfs_invar_alt_fold:
  shows "alt_bfs_invar'' (alt_fold G1 G2 src s)"
proof (standard, goal_cases)
  case 1
  show ?case using follow_invar_parent_alt_fold .
next
  case 2
  show ?case using invar_queue_alt_fold .
next
  case 3
  show ?case using invar_parent_alt_fold .
next
  case 4
  show ?case using parent_src_alt_fold .
next
  case (5 v u)
  thus ?case by (intro parent_imp_alt_alt_fold)
next
  case (6 v u)
  thus ?case by (intro parent_imp_edge_alt_fold)
next
  case (7 v)
  thus ?case by (intro not_white_if_mem_queue_alt_fold)
next
  case (8 v u)
  thus ?case by (intro not_white_if_parent_alt_fold)
next
  case (9 u v)
  thus ?case by (intro black_imp_adjacency_not_white_alt_fold)
next
  case 10
  show ?case using queue_sorted_wrt_d_alt_fold .
next
  case 11
  thus ?case by (intro d_last_queue_le_alt_fold)
next
  case (12 u p v)
  thus ?case by (intro d_triangle_inequality_alt_fold)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) adjacency_subset_V_union:
  assumes "G.invar G1"
  assumes "G.invar G2"
  shows "set (adjacency G1 G2 s v) \<subseteq> G.V (G.union G1 G2)"
  using assms G.adjacency_subset_V
  by (auto simp add: adjacency_def G.V_union_cong)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) queue_alt_fold_subset_V_union:
  assumes "G.invar G1"
  assumes "G.invar G2"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.V (G.union G1 G2)"
  assumes "\<not> DONE s"
  shows "set (Q_list (queue (alt_fold G1 G2 src s))) \<subseteq> G.V (G.union G1 G2)"
proof
  fix v
  assume assm: "v \<in> set (Q_list (queue (alt_fold G1 G2 src s)))"
  show "v \<in> G.V (G.union G1 G2)"
  proof (cases "v \<in> set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))))")
    case True
    have "set (adjacency G1 G2 s (Q_head (queue s))) \<subseteq> G.V (G.union G1 G2)"
      using assms(1, 2)
      by (intro adjacency_subset_V_union)
    thus ?thesis
      using True
      by auto
  next
    case False
    hence "v \<in> set (Q_list (Q_tail (queue s)))"
      using assms assm
      by (auto simp add: list_queue_alt_fold_cong)
    hence "v \<in> set (Q_list (queue s))"
      using assms(3, 6) list_queue_non_empty
      by (auto simp add: Q.list_tail intro: list.set_sel(2))
    thus ?thesis
      using assms(5)
      by blast
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) dom_parent_fold_subset_V:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  assumes "P.dom (parent s) \<subseteq> G.V G"
  assumes "set l \<subseteq> G.V G"
  shows "P.dom (parent (List.fold (traverse_edge src u) l s)) \<subseteq> G.V G"
  using assms
  unfolding G.V_eq_dV
  by (intro dom_parent_fold_subset_dV)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) dom_parent_alt_fold_subset_V_union:
  assumes "G.invar G1"
  assumes "G.invar G2"
  assumes "P_invar (parent s)"
  assumes "P.dom (parent s) \<subseteq> G.V (G.union G1 G2)"
  shows "P.dom (parent (alt_fold G1 G2 src s)) \<subseteq> G.V (G.union G1 G2)"
  using assms
  by (intro distinct_adjacency adjacency_subset_V_union dom_parent_fold_subset_V) simp+


subsubsection \<open>Termination\<close>

text \<open>
Before we can prove the correctness of loop @{term alt_bfs.alt_loop}, we need to prove that it
terminates on appropriate inputs.
\<close>

lemma (in alt_bfs) alt_loop_dom:
  assumes "G.invar G1"
  assumes "G.invar G2"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.V (G.union G1 G2)"
  assumes "P.dom (parent s) \<subseteq> G.V (G.union G1 G2)"
  shows "alt_loop_dom (G1, G2, src, s)"
  using assms
proof (induct "card (G.V (G.union G1 G2)) + length (Q_list (queue s)) - card (P.dom (parent s))"
       arbitrary: s
       rule: less_induct)
  case less
  show ?case
  proof (cases "DONE s")
    case True
    thus ?thesis
      by (blast intro: alt_loop.domintros)
  next
    case False
    let ?u = "Q_head (queue s)"
    let ?q = "Q_tail (queue s)"
    let ?S = "set (filter (Not \<circ> is_discovered src (parent s)) (adjacency G1 G2 s (Q_head (queue s))))"

    have "length (Q_list (queue (alt_fold G1 G2 src s))) = length (Q_list ?q) + card ?S"
      using less.prems(1-4) False distinct_adjacency
      by (simp add: list_queue_alt_fold_cong distinct_card[symmetric])
    moreover have "card (P.dom (parent (alt_fold G1 G2 src s))) = card (P.dom (parent s)) + card ?S"
    proof -
      have "P.dom (parent (alt_fold G1 G2 src s)) = P.dom (parent s) \<union> ?S"
        using less.prems(1, 2, 4)
        by (auto simp add: P.dom_def lookup_parent_alt_fold_cong override_on_def)
      moreover have "finite (P.dom (parent s))"
        using less.prems(1, 2, 6) finite_subset
        by (fastforce intro: G.finite_V_union)
      moreover have "finite ?S"
        by simp
      moreover have "P.dom (parent s) \<inter> ?S = {}"
        by (auto simp add: P.dom_def is_discovered_def)
      ultimately show ?thesis
        by (simp add: card_Un_disjoint)
    qed
    ultimately have
      "card (G.V (G.union G1 G2)) + length (Q_list (queue (alt_fold G1 G2 src s))) - card (P.dom (parent (alt_fold G1 G2 src s))) =
       card (G.V (G.union G1 G2)) + length (Q_list ?q) + card ?S - (card (P.dom (parent s)) + card ?S)"
      by force
    also have "... = card (G.V (G.union G1 G2)) + length (Q_list ?q) - card (P.dom (parent s))"
      by simp
    also have "... < card (G.V (G.union G1 G2)) + length (Q_list (queue s)) - card (P.dom (parent s))"
    proof -
      have "Q_list (queue s) \<noteq> []"
        using less.prems(3) False
        by (intro list_queue_non_empty)
      hence "length (Q_list (Q_tail (queue s))) < length (Q_list (queue s))"
        using less.prems(3)
        by (simp add: Q.list_tail)
      moreover have "card (P.dom (parent s)) \<le> card (G.V (G.union G1 G2))"
        using less.prems(1, 2, 6)
        by (intro G.finite_V_union card_mono)
      ultimately show ?thesis
        by simp
    qed
    finally have
      "card (G.V (G.union G1 G2)) + length (Q_list (queue (alt_fold G1 G2 src s))) - card (P.dom (parent (alt_fold G1 G2 src s))) <
       card (G.V (G.union G1 G2)) + length (Q_list (queue s)) - card (P.dom (parent s))"
      .
    thus ?thesis
      using less.prems
      by (intro invar_queue_alt_fold invar_parent_alt_fold queue_alt_fold_subset_V_union dom_parent_alt_fold_subset_V_union less.hyps[of "alt_fold G1 G2 src s"] alt_loop.domintros)
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) queue_subset_V:
  shows "set (Q_list (queue s)) \<subseteq> G.V G"
  using not_white_if_mem_queue not_white_imp_alt_path_rev_follow
  by (auto simp add: G.V_def dest: alt_pathD(2) intro: walk_endpoints(2))

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) dom_parent_subset_V:
  shows "P.dom (parent s) \<subseteq> G.V G"
proof
  fix v
  assume "v \<in> P.dom (parent s)"
  then obtain u where
    "P_lookup (parent s) v = Some u"
    by (auto simp add: P.dom_def)
  hence "{u, v} \<in> G.E G"
    by (intro parent_imp_edge)
  thus "v \<in> G.V G"
    unfolding G.V_def
    by (intro vs_member_intro[where ?e = "{u, v}"]) simp
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) alt_loop_dom:
  shows "alt_loop_dom (G1, G2, src, s)"
  using invar_G1 invar_G2 invar_queue invar_parent queue_subset_V dom_parent_subset_V
  by (intro alt_loop_dom)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_loop_psimps:
  assumes "alt_bfs_invar' G1 G2 src s"
  shows "alt_loop G1 G2 src s = (if \<not> DONE s then alt_loop G1 G2 src (alt_fold G1 G2 src s) else s)"
  using assms
  by (metis alt_bfs_invar.alt_loop_dom alt_loop.psimps)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_not_DONE) alt_loop_psimps:
  shows "alt_loop G1 G2 src s = alt_loop G1 G2 src (alt_fold G1 G2 src s)"
  using not_DONE alt_bfs_invar_axioms
  by (simp add: alt_loop_psimps)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_bfs_induct:
  assumes "alt_bfs_invar' G1 G2 src s"
  assumes "\<And>G1 G2 src s. (\<not> DONE s \<Longrightarrow> Q G1 G2 src (alt_fold G1 G2 src s)) \<Longrightarrow> Q G1 G2 src s"
  shows "Q G1 G2 src s"
  using assms
  by (blast intro: alt_bfs_invar.alt_loop_dom alt_loop.pinduct)

subsubsection \<open>Correctness\<close>

text \<open>We are now finally ready to prove the correctness of algorithm @{term alt_bfs.alt_bfs}.\<close>

locale alt_bfs_invar_DONE = alt_bfs_invar where P_update = P_update and Q_snoc = Q_snoc for
  P_update :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  assumes DONE: "DONE s"

abbreviation \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_bfs_invar_DONE' :: "'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> bool" where
  "alt_bfs_invar_DONE' G1 G2 src s \<equiv>
   alt_bfs_invar_DONE
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update G1 G2 src s P_update Q_snoc"

abbreviation \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) alt_bfs_invar_DONE'' :: "('q, 'm) state \<Rightarrow> bool" where
  "alt_bfs_invar_DONE'' \<equiv> alt_bfs_invar_DONE' G1 G2 src"

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_bfs_invar_not_DONE'I:
  assumes "alt_bfs_invar' G1 G2 src s"
  assumes "\<not> DONE s"
  shows "alt_bfs_invar_not_DONE' G1 G2 src s"
  using assms
  by (simp add: alt_bfs_invar_not_DONE_def alt_bfs_invar_not_DONE_axioms_def)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_bfs_invar_DONE'I:
  assumes "alt_bfs_invar' G1 G2 src s"
  assumes "DONE s"
  shows "alt_bfs_invar_DONE' G1 G2 src s"
  using assms
  by (simp add: alt_bfs_invar_DONE_def alt_bfs_invar_DONE_axioms_def)

lemma (in alt_bfs_invar_DONE) white_imp_not_alt_reachable:
  assumes "white s v"
  shows "\<not> alt_reachable P'' (Not \<circ> P'') (G.E G) src v"
proof
  assume "alt_reachable P'' (Not \<circ> P'') (G.E G) src v"
  then obtain p where
    "alt_path P'' (Not \<circ> P'') (G.E G) p src v"
    by (auto simp add: alt_reachable_def)
  thus False
    using assms
  proof (induct p arbitrary: v rule: path_rev_induct)
    case 1
    thus ?case
      by (auto dest: walk_between_nonempty_path(2) alt_pathD(2))
  next
    case 2
    thus ?case
      using src_not_white walk_between_nonempty_path(3, 4)
      by (fastforce dest: alt_pathD(2))
  next
    case (3 u u' l)
    show ?case
    proof (induct s u rule: vertex_color_induct)
      case white
      have "alt_path P'' (Not \<circ> P'') (G.E G) (l @ [u]) src u"
        using "3.prems"(1)
        by (intro alt_path_pref)
      thus ?case
        using white
        by (intro "3.hyps")
    next
      case gray
      thus ?case
        using invar_queue DONE
        by (simp add: Q.is_empty DONE_def)
    next
      case black
      have "u' = v"
        using "3.prems"(1)
        by (fastforce dest: alt_pathD(2) walk_between_nonempty_path(4))
      hence "alt_path P'' (Not \<circ> P'') (G.E G) (l @ [u, v]) src v"
        using "3.prems"(1)
        by force
      hence
        "alt s u v"
        "{u, v} \<in> G.E G"
        using black alt_path_snoc_snocD
        by blast+
      thus ?case
        using black black_imp_adjacency_not_white "3.prems"(2)
        by blast
    qed
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) d_triangle_inequality_edge:
  assumes "{u, v} \<in> G.E G"
  assumes "alt s u v"
  assumes "\<not> white s u"
  assumes "\<not> white s v"
  shows "d (parent s) v \<le> d (parent s) u + 1"
proof -
  have "alt_path (Q s u) (Not \<circ> Q s u) (G.E G) [u, v] u v"
  proof (rule alt_pathI, goal_cases)
    case 1
    have "Q s u {u, v}"
      using assms(2)
      by (simp add: P_P''_cong)
    thus ?case
      by (simp add: alt_list_step alt_list_empty)
  next
    case 2
    show ?case
      using assms(1)
      by (intro edges_are_walks)
  qed
  thus ?thesis
    using assms(3, 4) d_triangle_inequality[where ?p = "[u, v]"]
    by simp
qed

lemma (in alt_bfs_invar_DONE) not_white_imp_d_le_alt_dist:
  assumes "\<not> white s v"
  shows "d (parent s) v \<le> alt_dist P'' (Not \<circ> P'') (G.E G) src v"
proof -
  have "alt_reachable P'' (Not \<circ> P'') (G.E G) src v"
    using assms
    by (auto simp add: alt_reachable_def intro: not_white_imp_alt_path_rev_follow)
  then obtain p where
    "is_shortest_alt_path P'' (Not \<circ> P'') (G.E G) p src v"
    using no_odd_cycle
    by (elim G.is_shortest_alt_pathE) simp+
  thus ?thesis
    using assms
  proof (induct p arbitrary: v rule: path_rev_induct)
    case 1
    thus ?case
      by (auto dest: is_shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(2))
  next
    case (2 u)
    hence
      "u = src" and
      v: "v = src"
      using walk_between_nonempty_path(3, 4)
      by (fastforce dest: is_shortest_alt_pathD(2) alt_pathD(2))+
    hence "is_shortest_alt_path P'' (Not \<circ> P'') (G.E G) [src] src v"
      using "2.prems"(1)
      by blast
    hence "is_shortest_alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) v) src v"
      using parent_src
      by (simp add: follow_psimps v)
    thus ?case
      by (intro is_shortest_alt_pathD(1) eq_refl)
  next
    case (3 u u' l)
    show ?case
    proof (cases "white s u")
      case True
      hence "\<not> alt_reachable P'' (Not \<circ> P'') (G.E G) src u"
        by (intro white_imp_not_alt_reachable)
      moreover have "alt_reachable P'' (Not \<circ> P'') (G.E G) src u"
        unfolding alt_reachable_def
        using "3.prems"(1)
        apply (intro exI) by (rule alt_path_pref) (rule is_shortest_alt_pathD(2))
      ultimately show ?thesis
        by simp
    next
      case False
      have is_shortest_alt_path_l_snoc_snoc: "is_shortest_alt_path P'' (Not \<circ> P'') (G.E G) (l @ [u, v]) src v"
        using "3.prems"(1)
        by (intro is_shortest_alt_path_snoc_snoc)
      hence is_shortest_alt_path_l_snoc: "is_shortest_alt_path P'' (Not \<circ> P'') (G.E G) (l @ [u]) src u"
        using "3.prems"(1) no_odd_cycle
        by (intro G.is_shortest_alt_path_pref)
      hence
        "{u, v} \<in> G.E G"
        "alt s u v"
        using is_shortest_alt_path_l_snoc_snoc False
        by (fastforce dest: is_shortest_alt_pathD(2) dest: alt_path_snoc_snocD)+
      hence "d (parent s) v \<le> d (parent s) u + 1"
        using False "3.prems"(2)
        by (intro d_triangle_inequality_edge)
      also have "... \<le> alt_dist P'' (Not \<circ> P'') (G.E G) src u + 1"
        using "3.hyps"[OF is_shortest_alt_path_l_snoc False]
        unfolding plus_enat_simps(1)[symmetric] one_enat_def[symmetric]
        by (intro add_right_mono)
      also have "... = alt_dist P'' (Not \<circ> P'') (G.E G) src v"
        using is_shortest_alt_path_l_snoc_snoc no_odd_cycle
        by (intro G.is_shortest_alt_path_snoc_snocD[symmetric])
      finally show ?thesis
        by fastforce
    qed
  qed
qed

lemma (in alt_bfs_invar_DONE) not_white_imp_is_shortest_alt_path:
  assumes "\<not> white s v"
  shows "is_shortest_alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) v) src v"
  unfolding is_shortest_alt_path_def
proof (rule conjI)
  show "alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent s) v) src v"
    using assms
    by (intro not_white_imp_alt_path_rev_follow)
  thus "d (parent s) v = alt_dist P'' (Not \<circ> P'') (G.E G) src v"
    using assms
    by (intro not_white_imp_d_le_alt_dist alt_dist_le_alt_path_length antisym)
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar_DONE) alt_loop_psimps:
  shows "alt_loop G1 G2 src s = s"
  using DONE alt_bfs_invar_axioms
  by (simp add: alt_loop_psimps)

lemma (in alt_bfs_valid_input) alt_loop_sound:
  assumes "alt_bfs_invar'' s"
  assumes "is_discovered src (parent (alt_loop G1 G2 src s)) v"
  shows "is_shortest_alt_path P'' (Not \<circ> P'') (G.E G) (rev_follow (parent (alt_loop G1 G2 src s)) v) src v"
  using assms
proof (induct rule: alt_bfs_induct[OF assms(1)])
  case (1 G1 G2 src s)
  show ?case
  proof (cases "DONE s")
    case True
    with "1.prems"(1)
    have "alt_bfs_invar_DONE' G1 G2 src s"
      by (intro alt_bfs_invar_DONE'I)
    thus ?thesis
      using "1.prems"(2)
      by (intro alt_bfs_invar_DONE.not_white_imp_is_shortest_alt_path) (simp_all add: alt_bfs_invar_DONE.alt_loop_psimps)
  next
    case False
    with "1.prems"(1)
    have "alt_bfs_invar_not_DONE' G1 G2 src s"
      by (intro alt_bfs_invar_not_DONE'I)
    thus ?thesis
      using False "1.prems"(2)
      by (auto simp add: alt_bfs_invar_not_DONE.alt_loop_psimps dest: "1.hyps" intro: alt_bfs_invar_not_DONE.alt_bfs_invar_alt_fold)
  qed
qed

lemma (in alt_bfs_valid_input) alt_loop_complete:
  assumes "alt_bfs_invar'' s"
  assumes "\<not> is_discovered src (parent (alt_loop G1 G2 src s)) v"
  shows "\<not> alt_reachable P'' (Not \<circ> P'') (G.E G) src v"
  using assms
proof (induct rule: alt_bfs_induct[OF assms(1)])
  case (1 G1 G2 src s)
  show ?case
  proof (cases "DONE s")
    case True
    with "1.prems"(1)
    have "alt_bfs_invar_DONE' G1 G2 src s"
      by (intro alt_bfs_invar_DONE'I)
    thus ?thesis
      using "1.prems"(2)
      by (intro alt_bfs_invar_DONE.white_imp_not_alt_reachable) (simp_all add: alt_bfs_invar_DONE.alt_loop_psimps)
  next
    case False
    with "1.prems"(1)
    have "alt_bfs_invar_not_DONE' G1 G2 src s"
      by (intro alt_bfs_invar_not_DONE'I)
    thus ?thesis
      using False "1.prems"(2)
      by
        (intro alt_bfs_invar_not_DONE.alt_bfs_invar_alt_fold "1.hyps")
        (simp_all add: alt_bfs_invar_not_DONE.alt_loop_psimps)
  qed
qed

abbreviation (in alt_bfs) is_shortest_alt_path_Map :: "('a set \<Rightarrow> bool) \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "is_shortest_alt_path_Map Q G src m \<equiv>
   \<forall>v.
    is_discovered src m v \<longrightarrow> is_shortest_alt_path Q (Not \<circ> Q) (G.E G) (rev_follow m v) src v \<and>
    \<not> is_discovered src m v \<longrightarrow> \<not> alt_reachable Q (Not \<circ> Q) (G.E G) src v"

lemma (in alt_bfs_valid_input) correctness:
  assumes "alt_bfs_invar'' s"
  shows "is_shortest_alt_path_Map P'' G src (parent (alt_loop G1 G2 src s))"
  using assms alt_loop_sound alt_loop_complete
  by simp

lemma (in alt_bfs_valid_input) alt_bfs_correct:
  shows "is_shortest_alt_path_Map P'' G src (alt_bfs G1 G2 src)"
  unfolding alt_bfs_def
  using alt_bfs_invar_init
  by (intro correctness)

theorem (in alt_bfs) alt_bfs_correct:
  assumes "alt_bfs_valid_input' G1 G2 src"
  shows "is_shortest_alt_path_Map (\<lambda>e. e \<in> G.E G2) (G.union G1 G2) src (alt_bfs G1 G2 src)"
  using assms
  by (intro alt_bfs_valid_input.alt_bfs_correct)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_invar) alt_bfs_invar_alt_loop:
  shows "alt_bfs_invar'' (alt_loop G1 G2 src s)"
  using alt_bfs_invar_axioms
proof (induct rule: alt_bfs_induct[OF alt_bfs_invar_axioms])
  case (1 G1 G2 src s)
  show ?case
  proof (cases "DONE s")
    case True
    thus ?thesis
      using "1.prems"
      by (simp add: alt_loop_psimps)
  next
    case False
    with "1.prems"
    have "alt_bfs_invar_not_DONE' G1 G2 src s"
      by (intro alt_bfs_invar_not_DONE'I)
    thus ?thesis
      using False
      by
        (auto
         simp add: alt_bfs_invar_not_DONE.alt_loop_psimps
         intro: alt_bfs_invar_not_DONE.alt_bfs_invar_alt_fold "1.hyps")
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) alt_bfs_invar_alt_loop:
  assumes "alt_bfs_invar'' s"
  shows "alt_bfs_invar'' (alt_loop G1 G2 src s)"
  using assms
  by (intro alt_bfs_invar.alt_bfs_invar_alt_loop)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs_valid_input) alt_bfs_invar_alt_loop_init:
  shows "alt_bfs_invar'' (alt_loop G1 G2 src (init src))"
  using alt_bfs_invar_init
  by (intro alt_bfs_invar_alt_loop)

lemma \<^marker>\<open>tag invisible\<close> (in alt_bfs) alt_bfs_invar_alt_loop_init:
  assumes "alt_bfs_valid_input' G1 G2 src"
  shows "alt_bfs_invar' G1 G2 src (alt_loop G1 G2 src (init src))"
  using assms
  by (intro alt_bfs_valid_input.alt_bfs_invar_alt_loop_init)

lemma (in alt_bfs_invar) hd_rev_follow_eq_src:
  assumes "\<not> white s v"
  shows "hd (rev_follow (parent s) v) = src"
  using assms
  by (intro alt_pathD(2) walk_between_nonempty_path(3)) (rule not_white_imp_alt_path_rev_follow)

end