theory BFS
  imports
    "../Graph/Adjacency/Directed_Adjacency"
    "../Graph/Directed_Graph/Directed_Graph"
    "../Map/Map_Specs_Ext"
    "../Map/Parent_Relation"
    "../Queue/Queue_Specs"
begin

text \<open>
This theory specifies and verifies breadth-first search (BFS). More specifically, we verify that
given a directed graph G and a source vertex src, the output of the algorithm induces a
breadth-first tree T, that is, T consists of the vertices reachable from src in G, and for every
vertex v in T, T contains a unique simple path from src to v that is also a shortest path from src
to v in G.
\<close>

section \<open>BFS\<close>

subsection \<open>Specification of the algorithm\<close>

record ('q, 'm) state =
  queue :: 'q
  parent :: "'m"

locale bfs =
  G: adjacency where Map_update = Map_update +
  P: Map where
  empty = P_empty and
  update = P_update and
  delete = P_delete and
  lookup = P_lookup and
  invar = P_invar +
  Q: Queue where
  empty = Q_empty and
  is_empty = Q_is_empty and
  snoc = Q_snoc and
  head = Q_head and
  tail = Q_tail and
  invar = Q_invar and
  list = Q_list for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_empty and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  P_delete and
  P_lookup and
  P_invar and
  Q_empty and
  Q_is_empty and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  Q_head and
  Q_tail and
  Q_invar and
  Q_list
begin

text \<open>
Our implementation of BFS keeps two data structures, a first-in, first-out queue, initialized to
contain the source vertex src, and a parent map, initialized to the empty map. As long as the queue
is not empty, the algorithm pops the head u of the queue, and for every adjacent vertex v, discovers
v if it hasn't been discovered yet, where discovering v entails enqueuing v as well as setting v's
parent to u.
\<close>

definition init :: "'a \<Rightarrow> ('q, 'm) state" where
  "init src \<equiv>
   \<lparr>queue = Q_snoc Q_empty src,
    parent = P_empty\<rparr>"

definition DONE :: "('q, 'm) state \<Rightarrow> bool" where
  "DONE s \<longleftrightarrow> Q_is_empty (queue s)"

definition is_discovered :: "'a \<Rightarrow> 'm \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_discovered src m v \<longleftrightarrow> v = src \<or> P_lookup m v \<noteq> None"

definition discover :: "'a \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "discover u v s \<equiv>
   \<lparr>queue = Q_snoc (queue s) v,
    parent = P_update v u (parent s)\<rparr>"

definition traverse_edge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "traverse_edge src u v s \<equiv>
   if \<not> is_discovered src (parent s) v then discover u v s
   else s"

function (domintros) loop :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "loop G src s =
   (if \<not> DONE s
    then let
          u = Q_head (queue s);
          q = Q_tail (queue s)
         in loop G src (fold (traverse_edge src u) (G.adjacency_list G u) (s\<lparr>queue := q\<rparr>))
    else s)"
  by pat_completeness simp

abbreviation bfs :: "'n \<Rightarrow> 'a \<Rightarrow> 'm" where
  "bfs G src \<equiv> parent (loop G src (init src))"

abbreviation fold :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "fold G src s \<equiv>
   List.fold
    (traverse_edge src (Q_head (queue s)))
    (G.adjacency_list G (Q_head (queue s)))
    (s\<lparr>queue := Q_tail (queue s)\<rparr>)"

abbreviation T :: "'m \<Rightarrow> 'a dgraph" where
  "T m \<equiv> {(u, v). P_lookup m v = Some u}"

end

subsection \<open>Verification of the correctness of the algorithm\<close>

subsubsection \<open>Input\<close>

text \<open>
Algorithm @{term bfs.bfs} expects a directed graph G and a source vertex src in G as input, and the
correctness theorem will assume such an input. We remark that the assumption that src is indeed a
vertex in G is for the purpose of convenience. Let us formally specify these assumptions.
\<close>

locale bfs_valid_input = bfs where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  fixes G :: 'n
  fixes src :: 'a
  assumes invar_G: "G.invar G"
  assumes src_mem_dV: "src \<in> G.dV G"

abbreviation (in bfs) bfs_valid_input' :: "'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "bfs_valid_input' G src \<equiv>
   bfs_valid_input
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update P_update Q_snoc G src"

subsubsection \<open>Loop invariants\<close>

text \<open>
Unfolding the definition of @{term bfs.bfs}, we see that function @{term bfs.loop} lies at the heart
of the algorithm. It expects the undirected graph G, the source vertex src in G, as well as the
current state s, which comprises the queue and parent map, as input. Let us look at the assumptions
on the queue and parent map. As these are the only two data structures that may change from one
iteration to the next, these assumptions constitute the loop invariants of @{term bfs.loop}.
\<close>

text \<open>
To keep track of progress, the algorithm colors every vertex in G either white, gray, or black. All
vertices start out white and may later become gray and then black.
\<close>

abbreviation (in bfs_valid_input) white :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "white s v \<equiv> \<not> is_discovered src (parent s) v"

abbreviation (in bfs_valid_input) gray :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "gray s v \<equiv> is_discovered src (parent s) v \<and> v \<in> set (Q_list (queue s))"

abbreviation (in bfs_valid_input) black :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "black s v \<equiv> is_discovered src (parent s) v \<and> v \<notin> set (Q_list (queue s))"

abbreviation (in bfs) rev_follow :: "'m \<Rightarrow> 'a \<Rightarrow> 'a dpath" where
  "rev_follow m v \<equiv> rev (parent.follow (P_lookup m) v)"

abbreviation (in bfs_valid_input) d :: "'m \<Rightarrow> 'a \<Rightarrow> nat" where
  "d m v \<equiv> dpath_length (rev_follow m v)"

locale bfs_invar =
  bfs_valid_input where P_update = P_update and Q_snoc = Q_snoc +
  parent "P_lookup (parent s)" for
  P_update :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  s :: "('q, 'm) state" +
  assumes invar_queue: "Q_invar (queue s)"
  assumes invar_parent: "P_invar (parent s)"
  assumes parent_src: "P_lookup (parent s) src = None"
  assumes parent_imp_edge: "P_lookup (parent s) v = Some u \<Longrightarrow> (u, v) \<in> G.dE G"
  assumes not_white_if_mem_queue: "v \<in> set (Q_list (queue s)) \<Longrightarrow> \<not> white s v"
  assumes not_white_if_parent: "P_lookup (parent s) v = Some u \<Longrightarrow> \<not> white s u"
  assumes black_imp_adjacency_not_white: "\<lbrakk> (u, v) \<in> G.dE G; black s u \<rbrakk> \<Longrightarrow> \<not> white s v"
  assumes queue_sorted_wrt_d: "sorted_wrt (\<lambda>u v. d (parent s) u \<le> d (parent s) v) (Q_list (queue s))"
  assumes d_last_queue_le:
    "\<not> Q_is_empty (queue s) \<Longrightarrow>
     d (parent s) (last (Q_list (queue s))) \<le> d (parent s) (Q_head (queue s)) + 1"
  assumes d_triangle_inequality:
    "\<lbrakk> dpath_bet (G.dE G) p u v; \<not> white s u; \<not> white s v \<rbrakk> \<Longrightarrow>
     d (parent s) v \<le> d (parent s) u + dpath_length p"

text \<open>
Invariant @{thm bfs_invar.black_imp_adjacency_not_white} says that all vertices adjacent to black
vertices have been discovered.
\<close>

text \<open>
For a vertex $v$ in G, let d v denote the distance from the source src to v induced by the current
parent map. 
\<close>

text \<open>
Let $v_1,\dots,v_k$ be the content of the current queue, where $v_1$ is the head. Then invariant
@{thm bfs_invar.queue_sorted_wrt_d} says that $d v_i\leq d v_{i+1}$ for all $i<k$. And invariant
@{thm bfs_invar.d_last_queue_le} says that $d v_k\leq d v_1 + 1$. That is, the current queue holds at
most two distinct $d$ values.
\<close>

text \<open>
Finally, invariant @{thm bfs_invar.d_triangle_inequality} says that d satisfies a variant of the
triangle inequality. More specifically, if there is a path in G between two vertices u, v that
have been discovered by the algorithm, then their d values differ by at most the length of that
path.
\<close>

abbreviation (in bfs) bfs_invar' :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> bool" where
  "bfs_invar' G src s \<equiv>
   bfs_invar
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update G src P_update Q_snoc s"

abbreviation (in bfs_valid_input) bfs_invar'' :: "('q, 'm) state \<Rightarrow> bool" where
  "bfs_invar'' \<equiv> bfs_invar' G src"

text \<open>
Let us quickly show that the initial configuration of the queue--containing only the source vertex
src--and parent map--the empty map--satisfies the loop invariants.
\<close>

lemma (in bfs_valid_input) follow_invar_parent_init:
  shows "follow_invar (P_lookup (parent (init src)))"
  using wf_empty
  by (simp add: init_def P.map_empty follow_invar_def)

lemma (in bfs_valid_input) invar_queue_init:
  shows "Q_invar (queue (init src))"
  using Q.invar_empty
  by (auto simp add: init_def intro: Q.invar_snoc)

lemma (in bfs_valid_input) invar_parent_init:
  shows "P_invar (parent (init src))"
  using P.invar_empty
  by (simp add: init_def)

lemma (in bfs_valid_input) parent_src_init:
  shows "P_lookup (parent (init src)) src = None"
  by (simp add: init_def P.map_empty)

lemma (in bfs_valid_input) parent_imp_edge_init:
  assumes "P_lookup (parent (init src)) v = Some u"
  shows "(u, v) \<in> G.dE G"
  using assms
  by (simp add: init_def P.map_empty)

lemma (in bfs_valid_input) not_white_if_mem_queue_init:
  assumes "v \<in> set (Q_list (queue (init src)))"
  shows "\<not> white (init src) v"
  using assms Q.invar_empty
  by (simp add: init_def Q.list_snoc Q.list_empty is_discovered_def)

lemma (in bfs_valid_input) not_white_if_parent_init:
  assumes "P_lookup (parent (init src)) v = Some u"
  shows "\<not> white (init src) u"
  using assms
  by (simp add: init_def P.map_empty)

lemma (in bfs_valid_input) black_imp_adjacency_not_white_init:
  assumes "black (init src) u"
  assumes "(u, v) \<in> G.dE G"
  shows "\<not> white s v"
proof -
  have "u = src"
    using assms(1)
    by (simp add: is_discovered_def init_def P.map_empty)
  thus ?thesis
    using assms(1) Q.invar_empty
    by (simp add: init_def Q.list_snoc)
qed

lemma (in bfs_valid_input) queue_sorted_wrt_d_init:
  shows "sorted_wrt (\<lambda>u v. d (parent (init src)) u \<le> d (parent (init src)) v) (Q_list (queue (init src)))"
  using Q.invar_empty
  by (simp add: init_def Q.list_snoc Q.list_empty)

lemma (in bfs_valid_input) d_last_queue_le_init:
  assumes "\<not> Q_is_empty (queue (init src))"
  shows
    "d (parent (init src)) (last (Q_list (queue (init src)))) \<le>
     d (parent (init src)) (Q_head (queue (init src))) + 1"
  using Q.invar_empty invar_queue_init
  by (simp add: init_def Q.list_snoc Q.list_empty Q.list_head)

lemma (in bfs_valid_input) d_triangle_inequality_init:
  assumes "dpath_bet (G.dE G) p u v"
  assumes "\<not> white (init src) u"
  assumes "\<not> white (init src) v"
  shows "d (parent (init src)) v \<le> d (parent (init src)) u + dpath_length p"
  using assms
  by (simp add: is_discovered_def init_def P.map_empty)

lemma (in bfs_valid_input) bfs_invar_init:
  shows "bfs_invar'' (init src)"
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
  thus ?case by (intro parent_imp_edge_init)
next
  case (6 v)
  thus ?case by (intro not_white_if_mem_queue_init)
next
  case (7 v u)
  thus ?case by (intro not_white_if_parent_init)
next
  case (8 u v)
  thus ?case by (intro black_imp_adjacency_not_white_init)
next
  case 9
  show ?case using queue_sorted_wrt_d_init .
next
  case 10
  thus ?case by (intro d_last_queue_le_init)
next
  case (11 p u v)
  thus ?case by (intro d_triangle_inequality_init)
qed

text \<open>
Let us now show that the loop invariants are maintained, that is, if they are satisfied at the start
of an iteration, then they also will be satisfied at the end.
\<close>

text \<open>For this, let us first look at how the different subroutines change the queue and parent map.\<close>

text \<open>How does @{term bfs.discover} change the queue and parent map?\<close>

lemma (in bfs) queue_discover_cong [simp]:
  shows "queue (discover u v s) = Q_snoc (queue s) v"
  by (simp add: discover_def)

lemma (in bfs) parent_discover_cong [simp]:
  shows "parent (discover u v s) = P_update v u (parent s)"
  by (simp add: discover_def)

text \<open>How does @{term bfs.traverse_edge} change the queue and parent map?\<close>

lemma (in bfs) queue_traverse_edge_cong:
  shows "queue (traverse_edge src u v s) = (if \<not> is_discovered src (parent s) v then Q_snoc (queue s) v else queue s)"
  by (simp add: traverse_edge_def)

lemma (in bfs) invar_queue_traverse_edge:
  assumes "Q_invar (queue s)"
  shows "Q_invar (queue (traverse_edge src u v s))"
  using assms Q.invar_snoc
  by (simp add: queue_traverse_edge_cong)

lemma (in bfs) list_queue_traverse_edge_cong:
  assumes "Q_invar (queue s)"
  shows
    "Q_list (queue (traverse_edge src u v s)) =
     Q_list (queue s) @ (if \<not> is_discovered src (parent s) v then [v] else [])"
  using assms
  by (simp add: queue_traverse_edge_cong Q.list_snoc)

lemma (in bfs) invar_parent_traverse_edge:
  assumes "P_invar (parent s)"
  shows "P_invar (parent (traverse_edge src u v s))"
  using assms P.invar_update
  by (simp add: traverse_edge_def)

lemma (in bfs) lookup_parent_traverse_edge_cong:
  assumes "P_invar (parent s)"
  shows
    "P_lookup (parent (traverse_edge src u v s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some u)
      (if \<not> is_discovered src (parent s) v then {v} else {})"
  using assms
  by (simp add: traverse_edge_def P.map_update override_on_insert')

lemma (in bfs) T_traverse_edge_cong:
  assumes "P_invar (parent s)"
  shows "T (parent (traverse_edge src u v s)) = T (parent s) \<union> (if \<not> is_discovered src (parent s) v then {(u, v)} else {})"
  using assms
  by (auto simp add: lookup_parent_traverse_edge_cong override_on_def is_discovered_def)

text \<open>How does @{term bfs.fold} change the queue and parent map?\<close>

lemma (in bfs) list_queue_fold_cong_aux:
  assumes "P_invar (parent s)"
  assumes "distinct (v # vs)"
  shows "filter (Not \<circ> is_discovered src (parent (traverse_edge src u v s))) vs = filter (Not \<circ> is_discovered src (parent s)) vs"
proof (rule filter_cong)
  fix w
  assume "w \<in> set vs"
  hence "is_discovered src (parent (traverse_edge src u v s)) w = is_discovered src (parent s) w"
    using assms
    by (auto simp add: is_discovered_def lookup_parent_traverse_edge_cong override_on_insert')
  thus "(Not \<circ> is_discovered src (parent (traverse_edge src u v s))) w = (Not \<circ> is_discovered src (parent s)) w"
    by simp
qed simp

lemma (in bfs) list_queue_fold_cong:
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "distinct l"
  shows
    "Q_list (queue (List.fold (traverse_edge src u) l s)) =
     Q_list (queue s) @ filter (Not \<circ> is_discovered src (parent s)) l"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons v vs)
  have
    "Q_list (queue (List.fold (traverse_edge src u) (v # vs) s)) =
     Q_list (queue (List.fold (traverse_edge src u) vs (traverse_edge src u v s)))"
    by simp
  also have
    "... =
     Q_list (queue (traverse_edge src u v s)) @
     filter (Not \<circ> is_discovered src (parent (traverse_edge src u v s))) vs"
    using Cons.prems
    by (auto intro: invar_queue_traverse_edge invar_parent_traverse_edge Cons.hyps)
  also have
    "... =
     Q_list (queue s) @
     (if \<not> is_discovered src (parent s) v then [v] else []) @
     filter (Not \<circ> is_discovered src (parent (traverse_edge src u v s))) vs"
    using Cons.prems(1)
    by (simp add: list_queue_traverse_edge_cong)
  also have
    "... =
     Q_list (queue s) @
     (if \<not> is_discovered src (parent s) v then [v] else []) @
     filter (Not \<circ> is_discovered src (parent s)) vs"
    using Cons.prems(2, 3)
    by (simp add: list_queue_fold_cong_aux)
  also have "... = Q_list (queue s) @ filter (Not \<circ> is_discovered src (parent s)) (v # vs)"
    by simp
  finally show ?case
    .
qed

lemma (in bfs) invar_tail:
  assumes "Q_invar (queue s)"
  assumes "\<not> DONE s"
  shows "Q_invar (queue (s\<lparr>queue := Q_tail (queue s)\<rparr>))"
  using assms Q.invar_tail
  by (simp add: DONE_def Q.is_empty)

lemma (in bfs) list_queue_fold_cong_2:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "\<not> DONE s"
  shows
    "Q_list (queue (fold G src s)) =
     Q_list (Q_tail (queue s)) @
     filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s)))"
proof -
  have
    "Q_list (queue (fold G src s)) =
     Q_list (queue (s\<lparr>queue := Q_tail (queue s)\<rparr>)) @
     filter
      (Not \<circ> is_discovered src (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)))
      (G.adjacency_list G (Q_head (queue s)))"
    using assms
    by (intro invar_tail G.distinct_adjacency_list list_queue_fold_cong) simp+
  thus ?thesis
    unfolding comp_apply
    by (simp add: is_discovered_def)
qed

lemma (in bfs) lookup_parent_fold_cong:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  shows
    "P_lookup (parent (List.fold (traverse_edge src u) l s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> is_discovered src (parent s)) l))"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons v vs)
  have
    "P_lookup (parent (List.fold (traverse_edge src u) (v # vs) s)) =
     P_lookup (parent (List.fold (traverse_edge src u) vs (traverse_edge src u v s)))"
    by simp
  also have
    "... =
     override_on
      (P_lookup (parent (traverse_edge src u v s)))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> is_discovered src (parent (traverse_edge src u v s))) vs))"
    using Cons.prems
    by (fastforce intro: invar_parent_traverse_edge Cons.hyps)
  also have
    "... =
     override_on
      (override_on (P_lookup (parent s)) (\<lambda>_. Some u) (if \<not> is_discovered src (parent s) v then {v} else {}))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> is_discovered src (parent (traverse_edge src u v s))) vs))"
    using Cons.prems(1)
    by (simp add: lookup_parent_traverse_edge_cong)
  also have
    "... =
     override_on
      (override_on (P_lookup (parent s)) (\<lambda>_. Some u) (if \<not> is_discovered src (parent s) v then {v} else {}))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> is_discovered src (parent s)) vs))"
    using Cons.prems
    by (simp add: list_queue_fold_cong_aux)
  finally show ?case
    by (simp add: override_on_insert')
qed

lemma (in bfs) lookup_parent_fold_cong_2:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  shows
    "P_lookup (parent (fold G src s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s)))))"
proof -
  have
    "P_lookup (parent (fold G src s)) =
     override_on
      (P_lookup (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> is_discovered src (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>))) (G.adjacency_list G (Q_head (queue s)))))"
    using assms
    by (intro G.distinct_adjacency_list lookup_parent_fold_cong) simp+
  thus ?thesis
    by (simp add: is_discovered_def)
qed

lemma (in bfs_invar) lookup_parent_fold_cong:
  shows
    "P_lookup (parent (fold G src s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s)))))"
  using invar_G invar_parent
  by (intro lookup_parent_fold_cong_2)

lemma (in bfs) T_fold_cong_aux:
  assumes "P_invar (parent s)"
  assumes "distinct (v # vs)"
  shows "w \<in> set vs \<and> \<not> is_discovered src (parent (traverse_edge src u v s)) w \<longleftrightarrow> w \<in> set vs \<and> \<not> is_discovered src (parent s) w"
  using assms
  by (auto simp add: is_discovered_def lookup_parent_traverse_edge_cong override_on_def)

lemma (in bfs) T_fold_cong:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  shows "T (parent (List.fold (traverse_edge src u) l s)) = T (parent s) \<union> {(u, v) |v. v \<in> set l \<and> \<not> is_discovered src (parent s) v}"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by auto
next
  case (Cons v vs)
  have
    "T (parent (List.fold (traverse_edge src u) (v # vs) s)) =
     T (parent (List.fold (traverse_edge src u) vs (traverse_edge src u v s)))"
    by simp
  also have
    "... =
     T (parent (traverse_edge src u v s)) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> is_discovered src (parent (traverse_edge src u v s)) w}"
    using Cons.prems
    by (intro invar_parent_traverse_edge Cons.hyps) simp+
  also have
    "... =
     T (parent s) \<union>
     (if \<not> is_discovered src (parent s) v then {(u, v)} else {}) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> is_discovered src (parent (traverse_edge src u v s)) w}"
    unfolding T_traverse_edge_cong[OF Cons.prems(1)]
    by blast
  also have
    "... =
     T (parent s) \<union>
     (if \<not> is_discovered src (parent s) v then {(u, v)} else {}) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> is_discovered src (parent s) w}"
    using Cons.prems
    by (simp add: T_fold_cong_aux)
  also have "... = T (parent s) \<union> {(u, w) |w. w \<in> set (v # vs) \<and> \<not> is_discovered src (parent s) w}"
    by force
  finally show ?case
    .
qed

lemma (in bfs) T_fold_cong_2:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  shows
    "T (parent (fold G src s)) =
     T (parent s) \<union>
     {(Q_head (queue s), v) |v. v \<in> set (G.adjacency_list G (Q_head (queue s))) \<and> \<not> is_discovered src (parent s) v}"
proof -
  have
    "T (parent (fold G src s)) =
     T (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)) \<union>
     {(Q_head (queue s), v) |v.
      v \<in> set (G.adjacency_list G (Q_head (queue s))) \<and>
      \<not> is_discovered src (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)) v}"
    using assms
    by (intro G.distinct_adjacency_list T_fold_cong) simp+
  thus ?thesis
    by (simp add: is_discovered_def)
qed

lemma (in bfs_invar) T_fold_cong:
  shows
    "T (parent (fold G src s)) =
     T (parent s) \<union>
     {(Q_head (queue s), v) |v. v \<in> set (G.adjacency_list G (Q_head (queue s))) \<and> \<not> is_discovered src (parent s) v}"
  using invar_G invar_parent
  by (intro T_fold_cong_2)

text \<open>We are now ready to prove that the variants are maintained.\<close>

locale bfs_invar_not_DONE = bfs_invar where P_update = P_update and Q_snoc = Q_snoc for
  P_update :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
assumes not_DONE: "\<not> DONE s"

abbreviation (in bfs) bfs_invar_not_DONE' :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> bool" where
  "bfs_invar_not_DONE' G src s \<equiv>
   bfs_invar_not_DONE
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update G src s P_update Q_snoc"

abbreviation (in bfs_valid_input) bfs_invar_not_DONE'' :: "('q, 'm) state \<Rightarrow> bool" where
  "bfs_invar_not_DONE'' \<equiv> bfs_invar_not_DONE' G src"

text \<open>We start with the first invariant.\<close>

lemma (in bfs) list_queue_non_empty:
  assumes "Q_invar (queue s)"
  assumes "\<not> DONE s"
  shows "Q_list (queue s) \<noteq> []"
  using assms
  by (simp add: DONE_def Q.is_empty)

lemma (in bfs_invar_not_DONE) list_queue_non_empty:
  shows "Q_list (queue s) \<noteq> []"
  using invar_queue not_DONE
  by (intro list_queue_non_empty)

lemma (in bfs_invar_not_DONE) head_queue_mem_queue:
  shows "Q_head (queue s) \<in> set (Q_list (queue s))"
  using invar_queue list_queue_non_empty
  by (simp add: Q.list_head)

lemma (in bfs_invar_not_DONE) not_white_head_queue:
  shows "\<not> white s (Q_head (queue s))"
  using head_queue_mem_queue
  by (intro not_white_if_mem_queue)

lemma (in bfs_invar_not_DONE) follow_invar_parent_fold:
  shows "follow_invar (P_lookup (parent (fold G src s)))"
  unfolding follow_invar_def T_fold_cong
proof (rule wf_Un)
  let ?r =
    "{(Q_head (queue s), v) |v.
      v \<in> set (G.adjacency_list G (Q_head (queue s))) \<and> \<not> is_discovered src (parent s) v}"
  show "wf (T (parent s))"
    using follow_invar
    by (simp add: follow_invar_def)
  have "\<not> white s (Q_head (queue s))"
    using not_white_head_queue
    .
  thus "wf ?r"
    by (simp add: wf_def)
  show "Domain (T (parent s)) \<inter> Range ?r = {}"
    using not_white_if_parent
    by auto
qed

text \<open>Then the second invariant, @{thm bfs_invar.invar_queue}.\<close>

lemma (in bfs) invar_queue_fold:
  assumes "Q_invar (queue s)"
  assumes "distinct l"
  shows "Q_invar (queue (List.fold (traverse_edge src u) l s))"
  using assms
  by (induct l arbitrary: s) (simp_all add: invar_queue_traverse_edge)

lemma (in bfs) invar_queue_fold_2:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "\<not> DONE s"
  shows "Q_invar (queue (fold G src s))"
  using assms
  by (auto intro: G.distinct_adjacency_list invar_tail invar_queue_fold)

lemma (in bfs_invar_not_DONE) invar_queue_fold:
  shows "Q_invar (queue (fold G src s))"
  using invar_G invar_queue not_DONE
  by (intro invar_queue_fold_2)

text \<open>Then the third invariant, @{thm bfs_invar.invar_parent}.\<close>

lemma (in bfs) invar_parent_fold:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  shows "P_invar (parent (List.fold (traverse_edge src u) l s))"
  using assms
  by (induct l arbitrary: s) (simp_all add: invar_parent_traverse_edge)

lemma (in bfs) invar_parent_fold_2:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  shows "P_invar (parent (fold G src s))"
  using assms
  by (intro G.distinct_adjacency_list invar_parent_fold) simp+

lemma (in bfs_invar) invar_parent_fold:
  shows "P_invar (parent (fold G src s))"
  using invar_G invar_parent
  by (intro invar_parent_fold_2)

text \<open>Then the fourth invariant, @{thm bfs_invar.parent_src}.\<close>

lemma (in bfs_valid_input) src_not_white:
  shows "\<not> white s src"
  by (simp add: is_discovered_def)

lemma (in bfs_invar) parent_src_fold:
  shows "P_lookup (parent (fold G src s)) src = None"
  using invar_G invar_parent src_not_white
  by (simp add: lookup_parent_fold_cong_2 parent_src)

text \<open>Then the fifth invariant, @{thm bfs_invar.parent_imp_edge}.\<close>

lemma (in bfs_invar) head_queueI:
  assumes "P_lookup (parent s) v \<noteq> Some u"
  assumes "P_lookup (parent (fold G src s)) v = Some u"
  shows "u = Q_head (queue s)"
  using assms
  by (simp add: lookup_parent_fold_cong override_on_def split: if_splits(2))

lemma (in bfs_invar_not_DONE) parent_imp_edge_fold:
  assumes "P_lookup (parent (fold G src s)) v = Some u"
  shows "(u, v) \<in> G.dE G"
proof (cases "P_lookup (parent s) v = Some u")
  case True
  thus ?thesis
    by (intro parent_imp_edge)
next
  case False
  thus ?thesis
    using assms head_queueI G.mem_adjacency_iff_edge
    by (fastforce simp add: lookup_parent_fold_cong)
qed

text \<open>Then the sixth invariant, @{thm bfs_invar.not_white_if_mem_queue}.\<close>

lemma (in bfs_invar) not_white_imp_not_white_fold:
  assumes "\<not> white s v"
  shows "\<not> white (fold G src s) v"
  using assms
  by (auto simp add: is_discovered_def lookup_parent_fold_cong)

lemma (in bfs_invar_not_DONE) list_queue_fold_cong:
  shows
    "Q_list (queue (fold G src s)) =
     Q_list (Q_tail (queue s)) @
     filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s)))"
  using invar_G invar_queue invar_parent not_DONE
  by (intro list_queue_fold_cong_2)

lemma (in bfs_invar_not_DONE) not_white_if_mem_queue_fold:
  assumes "v \<in> set (Q_list (queue (fold G src s)))"
  shows "\<not> white (fold G src s) v"
proof (cases "v \<in> set (Q_list (queue s))")
  case True
  thus ?thesis
    by (intro not_white_if_mem_queue not_white_imp_not_white_fold)
next
  case False
  hence "v \<notin> set (Q_list (Q_tail (queue s)))"
    using invar_queue list_queue_non_empty
    by (auto simp add: Q.list_tail intro: list.set_sel(2))
  hence "v \<in> set (G.adjacency_list G (Q_head (queue s))) \<and> \<not> is_discovered src (parent s) v"
    using assms
    by (simp add: list_queue_fold_cong)
  thus ?thesis
    using assms
    by (fastforce simp add: is_discovered_def lookup_parent_fold_cong)
qed

text \<open>Then the seventh invariant, @{thm bfs_invar.not_white_if_parent}.\<close>

lemma (in bfs_invar_not_DONE) not_white_if_parent_fold:
  assumes "P_lookup (parent (fold G src s)) v = Some u"
  shows "\<not> white (fold G src s) u"
proof (cases "P_lookup (parent s) v = Some u")
  case True
  thus ?thesis
    by (intro not_white_if_parent not_white_imp_not_white_fold)
next
  case False
  hence "u = Q_head (queue s)"
    using assms
    by (intro head_queueI)
  thus ?thesis
    using not_white_head_queue
    by (intro not_white_imp_not_white_fold) simp
qed

text \<open>Then the eighth invariant, @{thm bfs_invar.black_imp_adjacency_not_white}.\<close>

lemma (in bfs_valid_input) vertex_color_induct [case_names white gray black]:
  assumes "white s v \<Longrightarrow> P s v"
  assumes "gray s v \<Longrightarrow> P s v"
  assumes "black s v \<Longrightarrow> P s v"
  shows "P s v"
  using assms
  by blast

lemma (in bfs_invar_not_DONE) whiteD:
  assumes "white s v"
  shows "\<not> black (fold G src s) v"
  using assms
  by (auto simp add: is_discovered_def lookup_parent_fold_cong list_queue_fold_cong)

lemma (in bfs_invar_not_DONE) head_queueI_2:
  assumes "v \<in> set (Q_list (queue s))"
  assumes "v \<notin> set (Q_list (queue (fold G src s)))"
  shows "v = Q_head (queue s)"
proof -
  have "Q_list (queue s) = Q_head (queue s) # Q_list (Q_tail (queue s))"
    using invar_queue list_queue_non_empty
    by (intro Q.list_queue)
  thus ?thesis
    using assms
    by (simp add: list_queue_fold_cong)
qed

lemma (in bfs_invar_not_DONE) black_imp_adjacency_not_white_fold:
  assumes "black (fold G src s) u"
  assumes "(u, v) \<in> G.dE G"
  shows "\<not> white (fold G src s) v"
proof (induct s u rule: vertex_color_induct)
  case white
  thus ?case
    using assms(1) whiteD
    by blast
next
  case gray
  hence "u = Q_head (queue s)"
    using assms(1)
    by (intro head_queueI_2) simp+
  thus ?case
    using assms(2)
    by (simp add: is_discovered_def lookup_parent_fold_cong override_on_def G.mem_adjacency_iff_edge)
next
  case black
  thus ?case
    using assms(2)
    by (intro black_imp_adjacency_not_white not_white_imp_not_white_fold)
qed

text \<open>Then the ninth invariant, @{thm bfs_invar.queue_sorted_wrt_d}.\<close>

lemma (in bfs_invar_not_DONE) parent_fold:
  shows "Parent_Relation.parent (P_lookup (parent (fold G src s)))"
proof (standard, goal_cases)
  case 1
  show ?case
    by (intro follow_invar_parent_fold)
qed

lemma (in bfs_invar) not_white_imp_lookup_parent_fold_eq_lookup_parent:
  assumes "\<not> white s v"
  shows "P_lookup (parent (fold G src s)) v = P_lookup (parent s) v"
  using assms
  by (simp add: lookup_parent_fold_cong)

lemma (in bfs_invar_not_DONE) not_white_imp_rev_follow_fold_eq_rev_follow:
  assumes "\<not> white s v"
  shows "rev_follow (parent (fold G src s)) v = rev_follow (parent s) v"
  using assms
proof (induct v rule: follow_pinduct)
  case (1 v)
  show ?case
  proof (cases "v = src")
    case True
    hence
      "P_lookup (parent s) v = None"
      "P_lookup (parent (fold G src s)) v = None"
      using parent_src parent_src_fold
      by simp+
    hence
      "rev_follow (parent s) v = [v]"
      "rev_follow (parent (fold G src s)) v = [v]"
      using "1.prems"(1) parent_fold
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
    moreover hence "P_lookup (parent (fold G src s)) v = Some u"
      using "1.prems"
      by (simp add: not_white_imp_lookup_parent_fold_eq_lookup_parent)
    ultimately have
      "rev_follow (parent s) v = rev_follow (parent s) u @ [v]"
      "rev_follow (parent (fold G src s)) v = rev_follow (parent (fold G src s)) u @ [v]"
      using "1.prems"(1) parent_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      using u
      by (simp add: "1.hyps")
  qed
qed

lemma (in bfs_invar) mem_queue_imp_d_le:
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

lemma (in bfs_invar_not_DONE) mem_filterD:
  assumes "v \<in> set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"
  shows
    "d (parent (fold G src s)) v = d (parent (fold G src s)) (Q_head (queue s)) + 1"
    "d (parent (fold G src s)) (last (Q_list (queue s))) \<le> d (parent (fold G src s)) v"
proof -
  let ?u = "Q_head (queue s)"
  have "P_lookup (parent (fold G src s)) v = Some ?u"
    using assms
    by (simp add: lookup_parent_fold_cong)
  hence "rev_follow (parent (fold G src s)) v = rev_follow (parent (fold G src s)) ?u @ [v]"
    using assms(1) parent_fold
    by (simp add: parent.follow_psimps)
  thus d_eq: "d (parent (fold G src s)) v = d (parent (fold G src s)) (Q_head (queue s)) + 1"
    using assms(1) parent_fold parent.follow_non_empty
    by (fastforce simp add: dpath_length_snoc)

  have "d (parent (fold G src s)) (last (Q_list (queue s))) = d (parent s) (last (Q_list (queue s)))"
    using assms list_queue_non_empty not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> d (parent s) ?u + 1"
    using not_DONE d_last_queue_le
    by (simp add: DONE_def)
  also have "... = d (parent (fold G src s)) ?u + 1"
    using assms not_white_head_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... = d (parent (fold G src s)) v"
    unfolding d_eq
    ..
  finally show "d (parent (fold G src s)) (last (Q_list (queue s))) \<le> d (parent (fold G src s)) v"
    .
qed

lemma (in bfs_invar_not_DONE) queue_sorted_wrt_d_fold_aux:
  assumes u_mem_tail_queue: "u \<in> set (Q_list (Q_tail (queue s)))"
  assumes v_mem_filter: "v \<in> set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"
  shows "d (parent (fold G src s)) u \<le> d (parent (fold G src s)) v"
proof -
  have u_mem_queue: "u \<in> set (Q_list (queue s))"
    using u_mem_tail_queue invar_queue list_queue_non_empty
    by (auto simp add: Q.list_tail intro: list.set_sel(2))
  have "d (parent (fold G src s)) u = d (parent s) u"
    using u_mem_queue not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> d (parent s) (last (Q_list (queue s)))"
    using u_mem_queue
    by (intro mem_queue_imp_d_le)
  also have "... = d (parent (fold G src s)) (last (Q_list (queue s)))"
    using list_queue_non_empty not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> d (parent (fold G src s)) v"
    using v_mem_filter
    by (intro mem_filterD(2))
  finally show ?thesis
    .
qed

lemma (in bfs_invar_not_DONE) queue_sorted_wrt_d_fold:
  shows "sorted_wrt (\<lambda>u v. d (parent (fold G src s)) u \<le> d (parent (fold G src s)) v) (Q_list (queue (fold G src s)))"
proof -
  let ?P = "\<lambda>u v. d (parent (fold G src s)) u \<le> d (parent (fold G src s)) v"
  have "sorted_wrt ?P (Q_list (queue s))"
    using queue_sorted_wrt_d not_white_if_mem_queue sorted_wrt_mono_rel[of "(Q_list (queue s))"]
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  hence "sorted_wrt ?P (Q_list (Q_tail (queue s)))"
    by (simp add: Q.list_queue[OF invar_queue list_queue_non_empty])
  moreover have "sorted_wrt ?P (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"
    by (auto simp add: mem_filterD(1) intro: sorted_wrt_if)
  moreover have
    "\<forall>u\<in>set (Q_list (Q_tail (queue s))).
      \<forall>v\<in>set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s)))).
       d (parent (fold G src s)) u \<le> d (parent (fold G src s)) v"
    by (blast intro: queue_sorted_wrt_d_fold_aux)
  ultimately show ?thesis 
    by (simp add: list_queue_fold_cong sorted_wrt_append)
qed

text \<open>Then the tenth invariant, @{thm bfs_invar.d_last_queue_le}.\<close>

lemma (in bfs_invar_not_DONE) d_last_queue_le_fold_aux:
  assumes "\<not> Q_is_empty (queue (fold G src s))"
  shows "d (parent (fold G src s)) (last (Q_list (queue (fold G src s)))) \<le> d (parent (fold G src s)) (Q_head (queue s)) + 1"
proof (cases "filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))) = []")
  case True
  hence list_tail_non_empty: "Q_list (Q_tail (queue s)) \<noteq> []"
    using invar_G invar_queue not_DONE invar_queue_fold_2 assms
    by (simp add: list_queue_fold_cong Q.is_empty)

  hence "last (Q_list (queue (fold G src s))) = last (Q_list (Q_tail (queue s)))"
    unfolding list_queue_fold_cong last_appendL[OF True]
    by blast
  hence "last (Q_list (queue (fold G src s))) = last (Q_list (queue s))"
    using list_tail_non_empty
    by (simp add: Q.list_queue[OF invar_queue list_queue_non_empty])
  hence "d (parent (fold G src s)) (last (Q_list (queue (fold G src s)))) = d (parent s) (last (Q_list (queue s)))"
    using list_queue_non_empty not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> d (parent s) (Q_head (queue s)) + 1"
    using invar_queue list_queue_non_empty d_last_queue_le
    by (simp add: Q.is_empty)
  also have "... = d (parent (fold G src s)) (Q_head (queue s)) + 1"
    using not_white_head_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  finally show ?thesis
    .
next
  case False
  hence
    "last (Q_list (queue (fold G src s))) \<in>
     set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"
    unfolding list_queue_fold_cong last_appendR[OF False]
    by (intro last_in_set)
  thus ?thesis
    by (simp add: mem_filterD(1))
qed

lemma (in bfs_invar) mem_queue_imp_d_ge:
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

lemma (in bfs_invar_not_DONE) d_last_queue_le_fold_aux_2:
  assumes "\<not> Q_is_empty (queue (fold G src s))"
  shows "d (parent (fold G src s)) (Q_head (queue s)) \<le> d (parent (fold G src s)) (Q_head (queue (fold G src s)))"
proof (cases "Q_list (Q_tail (queue s)) = []")
  case True
  have "Q_head (queue (fold G src s)) = hd (Q_list (queue (fold G src s)))"
    using invar_G invar_queue not_DONE invar_queue_fold_2 assms
    by (simp add: Q.is_empty Q.list_head)
  hence
    "Q_head (queue (fold G src s)) =
     hd (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"
    by (simp add: True list_queue_fold_cong)
  moreover have "filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))) \<noteq> []"
    using invar_G invar_queue not_DONE invar_queue_fold_2 assms
    by (simp add: True Q.is_empty list_queue_fold_cong)
  ultimately have head_queue_fold_mem_filter:
    "Q_head (queue (fold G src s)) \<in>
     set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"
    using list.set_sel(1)
    by metis

  have "d (parent (fold G src s)) (Q_head (queue s)) = d (parent s) (Q_head (queue s))"
    using not_white_head_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> d (parent s) (last (Q_list (queue s)))"
    by (intro head_queue_mem_queue mem_queue_imp_d_le)
  also have "... = d (parent (fold G src s)) (last (Q_list (queue s)))"
    using list_queue_non_empty not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> d (parent (fold G src s)) (Q_head (queue (fold G src s)))"
    using head_queue_fold_mem_filter
    by (intro mem_filterD(2))
  finally show ?thesis
    .
next
  case False
  have "Q_head (queue (fold G src s)) = hd (Q_list (queue (fold G src s)))"
    using invar_G invar_queue not_DONE invar_queue_fold_2 assms
    by (simp add: Q.is_empty Q.list_head)
  hence "Q_head (queue (fold G src s)) = hd (Q_list (Q_tail (queue s)))"
    using False
    by (simp add: list_queue_fold_cong)
  hence head_queue_fold_mem_queue: "Q_head (queue (fold G src s)) \<in> set (Q_list (queue s))"
    using False invar_queue list_queue_non_empty
    by (auto simp add: Q.list_tail intro: list.set_sel(2))

  have "d (parent (fold G src s)) (Q_head (queue s)) = d (parent s) (Q_head (queue s))"
    using not_white_head_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> d (parent s) (Q_head (queue (fold G src s)))"
    using head_queue_fold_mem_queue
    by (intro mem_queue_imp_d_ge)
  also have "... = d (parent (fold G src s)) (Q_head (queue (fold G src s)))"
    using head_queue_fold_mem_queue not_white_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  finally show ?thesis
    .
qed

lemma (in bfs_invar_not_DONE) d_last_queue_le_fold:
  assumes "\<not> Q_is_empty (queue (fold G src s))"
  shows "d (parent (fold G src s)) (last (Q_list (queue (fold G src s)))) \<le> d (parent (fold G src s)) (Q_head (queue (fold G src s))) + 1"
proof -
  have "d (parent (fold G src s)) (last (Q_list (queue (fold G src s)))) \<le> d (parent (fold G src s)) (Q_head (queue s)) + 1"
    using assms
    by (intro d_last_queue_le_fold_aux)
  also have "... \<le> d (parent (fold G src s)) (Q_head (queue (fold G src s))) + 1"
    using assms
    by (auto intro: d_last_queue_le_fold_aux_2)
  finally show ?thesis
    .
qed

text \<open>Finally, the eleventh invariant, @{thm bfs_invar.d_triangle_inequality}.\<close>

lemma (in bfs_invar) white_imp_gray_ancestor:
  assumes "dpath_bet (G.dE G) p u w"
  assumes "\<not> white s u"
  assumes "white s w"
  obtains v where
    "v \<in> set p"
    "gray s v"
  using assms
proof (induct p arbitrary: w rule: dpath_rev_induct)
  case 1
  thus ?case
    by simp
next
  case 2
  thus ?case
    using hd_of_dpath_bet' last_of_dpath_bet
    by (fastforce intro: list_length_1)
next
  case (3 v v' l)
  show ?case
  proof (induct s v rule: vertex_color_induct)
    case white
    have "dpath_bet (G.dE G) (l @ [v]) u v"
      using "3.prems"(2)
      by (intro dpath_bet_pref) simp
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
    have "(v, w) \<in> G.dE G"
      using "3.prems"(2)
      by (auto simp add: dpath_bet_def intro: dpath_snoc_edge_2)
    thus ?case
      using black black_imp_adjacency_not_white "3.prems"(4)
      by blast
  qed
qed

lemma (in bfs_invar) white_not_white_foldD:
  assumes "white s v"
  assumes "\<not> white (fold G src s) v"
  shows
    "v \<in> set (G.adjacency_list G (Q_head (queue s)))"
    "P_lookup (parent (fold G src s)) v = Some (Q_head (queue s))"
proof -
  show "v \<in> set (G.adjacency_list G (Q_head (queue s)))"
    using assms
    by (fastforce simp add: is_discovered_def lookup_parent_fold_cong)
  thus "P_lookup (parent (fold G src s)) v = Some (Q_head (queue s))"
    using assms
    by (auto simp add: lookup_parent_fold_cong)
qed

lemma (in bfs_valid_input) parent_imp_d:
  assumes "Parent_Relation.parent (P_lookup (parent s))"
  assumes "P_lookup (parent s) v = Some u"
  shows "d (parent s) v = d (parent s) u + 1"
proof -
  have "rev_follow (parent s) v = rev_follow (parent s) u @ [v]"
    using assms
    by (simp add: parent.follow_psimps)
  thus ?thesis
    using parent.follow_non_empty[OF assms(1)]
    by (simp add: dpath_length_snoc)
qed

lemma (in bfs_invar_not_DONE) white_not_white_foldD_2:
  assumes "white s v"
  assumes "\<not> white (fold G src s) v"
  shows "d (parent (fold G src s)) v = d (parent (fold G src s)) (Q_head (queue s)) + 1"
  using parent_fold assms
  by (fastforce intro: white_not_white_foldD(2) parent_imp_d)

lemmas (in bfs_invar_not_DONE) white_not_white_foldD =
  white_not_white_foldD
  white_not_white_foldD_2

lemma (in bfs_invar_not_DONE) d_triangle_inequality_fold:
  assumes dpath_p: "dpath_bet (G.dE G) p u v"
  assumes not_white_fold_u: "\<not> white (fold G src s) u"
  assumes not_white_fold_v: "\<not> white (fold G src s) v"
  shows "d (parent (fold G src s)) v \<le> d (parent (fold G src s)) u + dpath_length p"
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
    hence "d (parent (fold G src s)) v = d (parent (fold G src s)) (Q_head (queue s)) + 1"
      using not_white_fold_v
      by (intro white_not_white_foldD(3)) simp
    also have "... = d (parent (fold G src s)) u"
      using white_white not_white_fold_u
      by (intro white_not_white_foldD(3)[symmetric]) simp
    finally show ?thesis
      by simp
  next
    case white_not_white
    hence dpath_Cons: "dpath_bet (G.dE G) (Q_head (queue s) # p) (Q_head (queue s)) v"
      using not_white_fold_u white_not_white_foldD(1) dpath_p
      by (auto simp add: G.mem_adjacency_iff_edge intro: dpath_bet_ConsI)
    have "d (parent (fold G src s)) v = d (parent s) v"
      using white_not_white
      by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
    also have "... \<le> d (parent s) (Q_head (queue s)) + dpath_length (Q_head (queue s) # p)"
      using not_white_head_queue white_not_white dpath_Cons
      by (auto intro: d_triangle_inequality)
    also have "... = d (parent s) (Q_head (queue s)) + 1 + dpath_length p"
      using dpath_p
      by (simp add: dpath_length_Cons)
    also have "... = d (parent (fold G src s)) (Q_head (queue s)) + 1 + dpath_length p"
      using not_white_head_queue
      by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
    also have "... = d (parent (fold G src s)) u + dpath_length p"
      using white_not_white not_white_fold_u
      by (simp add: white_not_white_foldD(3))
    finally show ?thesis
      .
  next
    case gray_white
    hence "d (parent (fold G src s)) v = d (parent (fold G src s)) (Q_head (queue s)) + 1"
      using not_white_fold_v
      by (intro white_not_white_foldD(3)) simp
    also have "... = d (parent s) (Q_head (queue s)) + 1"
      using not_white_head_queue
      by (auto simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
    also have "... \<le> d (parent s) u + 1"
      using gray_white
      by (intro mem_queue_imp_d_ge add_right_mono) simp
    also have "... = d (parent (fold G src s)) u + 1"
      using gray_white
      by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
    also have "... \<le> d (parent (fold G src s)) u + dpath_length p"
      using dpath_p gray_white
      by (fastforce intro: dpath_length_geq_1I add_left_mono)
    finally show ?thesis
      .
  next
    case black_white
    then obtain w where
      "w \<in> set p" and
      gray_w: "gray s w"
      using dpath_p
      by (elim white_imp_gray_ancestor) simp+
    then obtain q r where
      "p = q @ tl r" and
      dpath_q: "dpath_bet (G.dE G) q u w" and
      dpath_r: "dpath_bet (G.dE G) r w v"
      using dpath_p
      by (auto simp add: in_set_conv_decomp elim: dpath_bet_vertex_decompE)
    hence dpath_length_p: "dpath_length p = dpath_length q + dpath_length r"
      by (auto dest: dpath_betD(2-4) intro: dpath_length_append_2)

    have "d (parent (fold G src s)) v = d (parent (fold G src s)) (Q_head (queue s)) + 1"
      using black_white not_white_fold_v
      by (intro white_not_white_foldD(3)) simp
    also have "... = d (parent s) (Q_head (queue s)) + 1"
      using not_white_head_queue
      by (auto simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
    also have "... \<le> d (parent s) w + 1"
      using gray_w
      by (intro mem_queue_imp_d_ge add_right_mono) simp
    also have "... \<le> d (parent s) u + dpath_length q + 1"
      using dpath_q black_white gray_w
      by (auto intro: d_triangle_inequality add_right_mono)
    also have "... \<le> d (parent s) u + dpath_length p"
      using dpath_r gray_w black_white dpath_length_geq_1I
      by (fastforce simp add: dpath_length_p)
    also have "... = d (parent (fold G src s)) u + dpath_length p"
      using black_white
      by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
    finally show ?thesis
      .
  next
    case not_white_not_white
    hence "d (parent (fold G src s)) v = d (parent s) v"
      by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
    also have "... \<le> d (parent s) u + dpath_length p"
      using dpath_p not_white_not_white
      by (intro d_triangle_inequality) simp+
    also have "... = d (parent (fold G src s)) u + dpath_length p"
      using not_white_not_white
      by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
    finally show ?thesis
      .
  qed
qed

lemma (in bfs_invar_not_DONE) bfs_invar_fold:
  shows "bfs_invar'' (fold G src s)"
proof (standard, goal_cases)
  case 1
  show ?case using follow_invar_parent_fold .
next
  case 2
  show ?case using invar_queue_fold .
next
  case 3
  show ?case using invar_parent_fold .
next
  case 4
  show ?case using parent_src_fold .
next
  case (5 v u)
  thus ?case by (intro parent_imp_edge_fold)
next
  case (6 v)
  thus ?case by (intro not_white_if_mem_queue_fold)
next
  case (7 v u)
  thus ?case by (intro not_white_if_parent_fold)
next
  case (8 u v)
  thus ?case by (intro black_imp_adjacency_not_white_fold)
next
  case 9
  show ?case using queue_sorted_wrt_d_fold .
next
  case 10
  thus ?case by (intro d_last_queue_le_fold)
next
  case (11 p u v)
  thus ?case by (intro d_triangle_inequality_fold)
qed

(* qq *)
(* Next: termination. Then: correctness. *)

subsection \<open>@{term "Q_list \<circ> queue"}\<close>



subsection \<open>@{term "Q_head \<circ> queue"}\<close>

lemma (in bfs) head_queue_mem_dV:
  assumes "Q_invar (queue s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.dV G"
  assumes "\<not> DONE s"
  shows "Q_head (queue s) \<in> G.dV G"
  using assms list_queue_non_empty
  by (auto simp add: Q.list_head)

section \<open>Basic Lemmas\<close>

subsection \<open>@{term discover}\<close>

subsubsection \<open>@{term queue}\<close>



subsubsection \<open>@{term parent}\<close>



subsection \<open>@{term traverse_edge}\<close>

subsubsection \<open>@{term queue}\<close>



subsubsection \<open>@{term "Q_list \<circ> queue"}\<close>



subsubsection \<open>@{term "P_lookup \<circ> parent"}\<close>



subsubsection \<open>@{term "P_invar \<circ> parent"}\<close>



subsubsection \<open>@{term T}\<close>



subsection \<open>@{term fold}\<close>

subsubsection \<open>@{term "Q_invar \<circ> queue"}\<close>



subsubsection \<open>@{term "Q_list \<circ> queue"}\<close>




subsubsection \<open>@{term "set \<circ> Q_list \<circ> queue"}\<close>

lemma (in bfs) queue_fold_subset_dV:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.dV G"
  assumes "\<not> DONE s"
  shows "set (Q_list (queue (fold G src s))) \<subseteq> G.dV G"
proof
  fix v
  assume assm: "v \<in> set (Q_list (queue (fold G src s)))"
  show "v \<in> G.dV G"
  proof (cases "v \<in> set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))")
    case True
    thus ?thesis
      using G.adjacency_subset_dV
      by auto
  next
    case False
    hence "v \<in> set (Q_list (Q_tail (queue s)))"
      using assms assm
      by (auto simp add: list_queue_fold_cong_2)
    hence "v \<in> set (Q_list (queue s))"
      using assms(2, 5) list_queue_non_empty
      by (auto simp add: Q.list_tail intro: list.set_sel(2))
    thus ?thesis
      using assms(4)
      by blast
  qed
qed

subsubsection \<open>@{term parent}\<close>



subsubsection \<open>@{term "P_invar \<circ> parent"}\<close>



lemma (in bfs) dom_parent_fold_subset_dV:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  assumes "P.dom (parent s) \<subseteq> G.dV G"
  assumes "set l \<subseteq> G.dV G"
  shows "P.dom (parent (List.fold (traverse_edge src u) l s)) \<subseteq> G.dV G"
proof
  fix v
  assume assm: "v \<in> P.dom (parent (List.fold (traverse_edge src u) l s))"
  show "v \<in> G.dV G"
  proof (cases "v \<in> set (filter (Not \<circ> is_discovered src (parent s)) l)")
    case True
    thus ?thesis
      using assms(4)
      by auto
  next
    case False
    have "P_lookup (parent (List.fold (traverse_edge src u) l s)) v \<noteq> None"
      using assm
      by (simp add: P.dom_def)
    hence "P_lookup (parent s) v \<noteq> None"
      using assms(1, 2) False
      by (simp add: lookup_parent_fold_cong)
    thus ?thesis
      using assms(3)
      by (auto simp add: P.dom_def)
  qed
qed

lemma (in bfs) dom_parent_fold_subset_dV_2:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  assumes "P.dom (parent s) \<subseteq> G.dV G"
  shows "P.dom (parent (fold G src s)) \<subseteq> G.dV G"
  using assms G.adjacency_subset_dV
  by (intro G.distinct_adjacency_list dom_parent_fold_subset_dV) simp+

lemma (in bfs) ran_parent_fold_cong:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  shows
    "P.ran (parent (fold G src s)) =
     P.ran (parent s) \<union>
     (if set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s)))) = {}
      then {}
      else {Q_head (queue s)})"
proof
  let ?S = "set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"
  show "P.ran (parent (fold G src s)) \<subseteq> P.ran (parent s) \<union> (if ?S = {} then {} else {Q_head (queue s)})"
    using assms
    by (auto simp add: P.ran_def lookup_parent_fold_cong_2 override_on_def)
  show "P.ran (parent s) \<union> (if ?S = {} then {} else {Q_head (queue s)}) \<subseteq> P.ran (parent (fold G src s))"
  proof
    fix u
    assume assm: "u \<in> P.ran (parent s) \<union> (if ?S = {} then {} else {Q_head (queue s)})"
    show "u \<in> P.ran (parent (fold G src s))"
    proof (cases "u \<in> P.ran (parent s)")
      case True
      then obtain v where
        "P_lookup (parent s) v = Some u"
        by (auto simp add: P.ran_def)
      moreover hence "is_discovered src (parent s) v"
        by (simp add: is_discovered_def)
      ultimately show ?thesis
        using assms
        by (auto simp add: P.ran_def lookup_parent_fold_cong_2 override_on_def)
    next
      case False
      then obtain v where
        "v \<in> ?S"
        using assm
        by (auto split: if_splits(2))
      moreover have "u = Q_head (queue s)"
        using assm False
        by (simp split: if_splits(2))
      ultimately show ?thesis
        using assms
        by (auto simp add: P.ran_def lookup_parent_fold_cong_2 override_on_def)
    qed
  qed
qed

subsubsection \<open>@{term T}\<close>





section \<open>Termination\<close>

lemma (in bfs) loop_dom_aux:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  assumes "P.dom (parent s) \<subseteq> G.dV G"
  shows
    "card (P.dom (parent (fold G src s))) =
     card (P.dom (parent s)) +
     card (set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s)))))"
proof -
  let ?S = "set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"
  have "P.dom (parent (fold G src s)) = P.dom (parent s) \<union> ?S"
    using assms(1, 2)
    by (auto simp add: P.dom_def lookup_parent_fold_cong_2 override_on_def)
  moreover have "finite (P.dom (parent s))"
    using assms(1, 3) finite_subset
    by (fastforce intro: G.finite_dV)
  moreover have "finite ?S"
    by simp
  moreover have "P.dom (parent s) \<inter> ?S = {}"
    by (auto simp add: P.dom_def is_discovered_def)
  ultimately show ?thesis
    by (simp add: card_Un_disjoint)
qed

lemma (in bfs) loop_dom_aux_2:
  assumes invar_G: "G.invar G"
  assumes invar_queue: "Q_invar (queue s)"
  assumes not_DONE: "\<not> DONE s"
  assumes dom_parent_subset_dV: "P.dom (parent s) \<subseteq> G.dV G"
  shows
    "card (G.dV G) +
     length (Q_list (Q_tail (queue s))) -
     card (P.dom (parent s)) <
     card (G.dV G) +
     length (Q_list (queue s)) -
     card (P.dom (parent s))"
proof -
  have "Q_list (queue s) \<noteq> []"
    using invar_queue not_DONE
    by (intro list_queue_non_empty)
  hence "length (Q_list (Q_tail (queue s))) < length (Q_list (queue s))"
    using invar_queue
    by (simp add: Q.list_tail)
  moreover have "card (P.dom (parent s)) \<le> card (G.dV G)"
    using invar_G dom_parent_subset_dV
    by (intro G.finite_dV card_mono)
  ultimately show ?thesis
    by simp
qed

lemma (in bfs) loop_dom:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.dV G"
  assumes "P.dom (parent s) \<subseteq> G.dV G"
  shows "loop_dom (G, src, s)"
  using assms
proof (induct "card (G.dV G) + length (Q_list (queue s)) - card (P.dom (parent s))"
       arbitrary: s
       rule: less_induct)
  case less
  show ?case
  proof (cases "DONE s")
    case True
    thus ?thesis
      by (blast intro: loop.domintros)
  next
    case False
    let ?u = "Q_head (queue s)"
    let ?q = "Q_tail (queue s)"
    let ?S = "set (filter (Not \<circ> is_discovered src (parent s)) (G.adjacency_list G (Q_head (queue s))))"

    have "length (Q_list (queue (fold G src s))) = length (Q_list ?q) + card ?S"
      using less.prems(1-3) False G.distinct_adjacency_list
      by (simp add: list_queue_fold_cong_2 distinct_card[symmetric])
    moreover have "card (P.dom (parent (fold G src s))) = card (P.dom (parent s)) + card ?S"
      using less.prems(1, 3, 5)
      by (intro loop_dom_aux)
    ultimately have
      "card (G.dV G) + length (Q_list (queue (fold G src s))) - card (P.dom (parent (fold G src s))) =
       card (G.dV G) + length (Q_list ?q) + card ?S - (card (P.dom (parent s)) + card ?S)"
      by presburger
    also have "... = card (G.dV G) + length (Q_list ?q) - card (P.dom (parent s))"
      by simp
    also have "... < card (G.dV G) + length (Q_list (queue s)) - card (P.dom (parent s))"
      using less.prems False
      by (intro loop_dom_aux_2)
    finally have
      "card (G.dV G) + length (Q_list (queue (fold G src s))) - card (P.dom (parent (fold G src s))) <
       card (G.dV G) + length (Q_list (queue s)) - card (P.dom (parent s))"
      .
    thus ?thesis
      using less.prems
      by (intro invar_queue_fold_2 invar_parent_fold_2 queue_fold_subset_dV dom_parent_fold_subset_dV_2 less.hyps loop.domintros)
  qed
qed

section \<open>Invariants\<close>

subsection \<open>Definitions\<close>

(* TODO Rename. *)



locale bfs_invar_DONE = bfs_invar where P_update = P_update and Q_snoc = Q_snoc for
  P_update :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  assumes DONE: "DONE s"







abbreviation (in bfs) bfs_invar_DONE' :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> bool" where
  "bfs_invar_DONE' G src s \<equiv>
   bfs_invar_DONE
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update G src s P_update Q_snoc"

abbreviation (in bfs_valid_input) bfs_invar_DONE'' :: "('q, 'm) state \<Rightarrow> bool" where
  "bfs_invar_DONE'' \<equiv> bfs_invar_DONE' G src"

subsection \<open>Convenience Lemmas\<close>

subsubsection \<open>@{term bfs}\<close>

lemma (in bfs) bfs_invar_not_DONE'I:
  assumes "bfs_invar' G src s"
  assumes "\<not> DONE s"
  shows "bfs_invar_not_DONE' G src s"
  using assms
  by (simp add: bfs_invar_not_DONE_def bfs_invar_not_DONE_axioms_def)

lemma (in bfs) bfs_invar_DONE'I:
  assumes "bfs_invar' G src s"
  assumes "DONE s"
  shows "bfs_invar_DONE' G src s"
  using assms
  by (simp add: bfs_invar_DONE_def bfs_invar_DONE_axioms_def)

lemma (in bfs) rev_follow_non_empty:
  assumes "Parent_Relation.parent (P_lookup m)"
  shows "rev_follow m v \<noteq> []"
  using assms
  by (auto dest: parent.follow_non_empty)

lemma (in bfs) distinct_rev_follow:
  assumes "Parent_Relation.parent (P_lookup m)"
  shows "distinct (rev_follow m v)"
  unfolding distinct_rev
  using assms
  by (intro parent.distinct_follow)

lemma (in bfs) last_rev_follow:
  assumes "Parent_Relation.parent (P_lookup m)"
  shows "last (rev_follow m v) = v"
proof -
  let ?l = "parent.follow (P_lookup m) v"
  have "?l = hd ?l # tl ?l"
    using assms
    by (intro parent.follow_non_empty hd_Cons_tl[symmetric])
  hence "hd ?l = v"
    using assms
    by (auto dest: parent.follow_ConsD)
  thus ?thesis
    using assms parent.follow_non_empty
    by (fastforce simp add: last_rev)
qed

subsubsection \<open>@{term bfs_valid_input}\<close>

context bfs_valid_input
begin
sublocale finite_dgraph "G.dE G"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G
    by (intro G.finite_dE)
qed
end





subsubsection \<open>@{term bfs_invar}\<close>

lemma (in bfs_invar) distinct_rev_follow:
  shows "distinct (rev_follow (parent s) v)"
  using distinct_follow
  by simp

subsection \<open>Basic Lemmas\<close>

subsubsection \<open>@{term bfs_valid_input}\<close>



subsubsection \<open>@{term bfs_invar}\<close>

lemma (in bfs_invar) not_white_imp_dpath_rev_follow:
  assumes "\<not> white s v"
  shows "dpath_bet (G.dE G) (rev_follow (parent s) v) src v"
  using assms
proof (induct v rule: follow_pinduct)
  case (1 v)
  show ?case
  proof (cases "v = src")
    case True
    thus ?thesis
      using parent_src src_mem_dV
      by (auto simp add: G.dE_def G.dV_def follow_psimps intro: dpath_bet_reflexive)
  next
    case False
    then obtain u where
      u: "P_lookup (parent s) v = Some u"
      using "1.prems"
      by (auto simp add: is_discovered_def)
    hence
      "follow v = v # follow u"
      "(u, v) \<in> G.dE G"
      "\<not> white s u"
      using not_white_if_parent
      by (auto simp add: follow_psimps intro: parent_imp_edge)
    moreover hence "dpath_bet (G.dE G) (rev_follow (parent s) u) src u"
      using u
      by (intro "1.hyps")
    ultimately show ?thesis
      by (auto intro: dpath_bet_snocI)
  qed
qed

lemma (in bfs_invar) hd_rev_follow_eq_src:
  assumes "\<not> white s v"
  shows "hd (rev_follow (parent s) v) = src"
  using assms
  by (intro hd_of_dpath_bet'[symmetric]) (rule not_white_imp_dpath_rev_follow)





lemma (in bfs_invar) d_triangle_inequality_edge:
  assumes "(u, v) \<in> G.dE G"
  assumes "\<not> white s u"
  assumes "\<not> white s v"
  shows "d (parent s) v \<le> d (parent s) u + 1"
proof -
  have "dpath_bet (G.dE G) [u, v] u v"
    using assms(1)
    by (intro edges_are_dpath_bet)
  thus ?thesis
    using assms(2, 3)
    using d_triangle_inequality
    by fastforce
qed

subsection \<open>@{term bfs.init}\<close>

subsubsection \<open>\<close>



subsubsection \<open>\<close>



subsection \<open>@{term bfs.fold}\<close>

subsubsection \<open>Convenience Lemmas\<close>













subsubsection \<open>\<close>





subsubsection \<open>@{thm bfs_invar.invar_queue}\<close>



subsubsection \<open>@{thm bfs_invar.invar_parent}\<close>



subsubsection \<open>@{thm bfs_invar.parent_src}\<close>



subsubsection \<open>Basic Lemmas\<close>













lemmas (in bfs_invar_not_DONE) not_whiteD =
  not_white_imp_not_white_fold
  not_white_imp_lookup_parent_fold_eq_lookup_parent
  not_white_imp_rev_follow_fold_eq_rev_follow





subsubsection \<open>@{thm bfs_invar.parent_imp_edge}\<close>



subsubsection \<open>@{thm bfs_invar.not_white_if_mem_queue}\<close>



subsubsection \<open>@{thm bfs_invar.not_white_if_parent}\<close>



subsubsection \<open>@{thm bfs_invar.black_imp_adjacency_not_white}\<close>



subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_d}\<close>



subsubsection \<open>@{thm bfs_invar.d_last_queue_le}\<close>



subsubsection \<open>@{thm bfs_invar.d_triangle_inequality}\<close>



subsubsection \<open>\<close>



section \<open>Correctness\<close>

subsection \<open>Definitions\<close>

abbreviation (in bfs) dist :: "'n \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "dist G \<equiv> Shortest_Dpath.dist (G.dE G)"

abbreviation (in bfs) is_shortest_dpath :: "'n \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_shortest_dpath G p u v \<equiv> dpath_bet (G.dE G) p u v \<and> dpath_length p = dist G u v"

subsection \<open>Basic Lemmas\<close>

lemma (in bfs_invar) queue_subset_dV:
  shows "set (Q_list (queue s)) \<subseteq> G.dV G"
  using not_white_if_mem_queue not_white_imp_dpath_rev_follow
  by (auto simp add: G.dV_def intro: dpath_bet_endpoints(2))

lemma (in bfs_invar) dom_parent_subset_dV:
  shows "P.dom (parent s) \<subseteq> G.dV G"
proof
  fix v
  assume "v \<in> P.dom (parent s)"
  then obtain u where
    "P_lookup (parent s) v = Some u"
    by (auto simp add: P.dom_def)
  hence "(u, v) \<in> G.dE G"
    by (intro parent_imp_edge)
  thus "v \<in> G.dV G"
    by (intro G.edgeD(2))
qed

subsection \<open>Convenience Lemmas\<close>

lemma (in bfs_invar) loop_dom:
  shows "loop_dom (G, src, s)"
  using invar_G invar_queue invar_parent queue_subset_dV dom_parent_subset_dV
  by (intro loop_dom)

lemma (in bfs) loop_psimps:
  assumes "bfs_invar' G src s"
  shows "loop G src s = (if \<not> DONE s then loop G src (fold G src s) else s)"
  using assms
  by (metis bfs_invar.loop_dom loop.psimps)

lemma (in bfs_invar_not_DONE) loop_psimps:
  shows "loop G src s = loop G src (fold G src s)"
  using not_DONE bfs_invar_axioms
  by (simp add: loop_psimps)

lemma (in bfs_invar_DONE) loop_psimps:
  shows "loop G src s = s"
  using DONE bfs_invar_axioms
  by (simp add: loop_psimps)

lemma (in bfs) bfs_induct:
  assumes "bfs_invar' G src s"
  assumes "\<And>G src s. (\<not> DONE s \<Longrightarrow> P G src (fold G src s)) \<Longrightarrow> P G src s"
  shows "P G src s"
  using assms
  by (blast intro: bfs_invar.loop_dom loop.pinduct)

subsection \<open>Completeness\<close>

lemma (in bfs_invar_DONE) white_imp_not_reachable:
  assumes "white s v"
  shows "\<not> reachable (G.dE G) src v"
proof
  assume "reachable (G.dE G) src v"
  then obtain p where
    "dpath_bet (G.dE G) p src v"
    unfolding reachable_iff_dpath_bet
    ..
  thus False
    using assms
  proof (induct p arbitrary: v rule: dpath_rev_induct)
    case 1
    thus ?case
      by simp
  next
    case 2
    thus ?case
      using src_not_white hd_of_dpath_bet' last_of_dpath_bet
      by fastforce
  next
    case (3 u u' l)
    show ?case
    proof (induct s u rule: vertex_color_induct)
      case white
      have "dpath_bet (G.dE G) (l @ [u]) src u"
        using "3.prems"(1)
        by (intro dpath_bet_pref) simp
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
      have "(u, v) \<in> G.dE G"
        using "3.prems"(1)
        by (auto simp add: dpath_bet_def intro: dpath_snoc_edge_2)
      thus ?case
        using black black_imp_adjacency_not_white "3.prems"(2)
        by blast
    qed
  qed
qed

lemma (in bfs_valid_input) completeness:
  assumes "bfs_invar'' s"
  assumes "\<not> is_discovered src (parent (loop G src s)) v"
  shows "\<not> reachable (G.dE G) src v"
  using assms
proof (induct rule: bfs_induct[OF assms(1)])
  case (1 G src s)
  show ?case
  proof (cases "DONE s")
    case True
    with "1.prems"(1)
    have "bfs_invar_DONE' G src s"
      by (intro bfs_invar_DONE'I)
    thus ?thesis
      using "1.prems"(2)
      by (intro bfs_invar_DONE.white_imp_not_reachable) (simp_all add: bfs_invar_DONE.loop_psimps)
  next
    case False
    with "1.prems"(1)
    have "bfs_invar_not_DONE' G src s"
      by (intro bfs_invar_not_DONE'I)
    thus ?thesis
      using False "1.prems"(2)
      by (intro bfs_invar_not_DONE.bfs_invar_fold "1.hyps") (simp_all add: bfs_invar_not_DONE.loop_psimps)
  qed
qed

subsection \<open>Soundness\<close>

lemma (in bfs_invar_DONE) not_white_imp_d_le_dist:
  assumes "\<not> white s v"
  shows "d (parent s) v \<le> dist G src v"
proof -
  have "reachable (G.dE G) src v"
    using assms
    by (auto simp add: reachable_iff_dpath_bet intro: not_white_imp_dpath_rev_follow)
  then obtain p where
    "is_shortest_dpath G p src v"
    by (elim is_shortest_dpath_if_reachable_2) simp+
  thus ?thesis
    using assms
  proof (induct p arbitrary: v rule: dpath_rev_induct)
    case 1
    thus ?case
      by simp
  next
    case 2
    thus ?case
      using parent_src hd_of_dpath_bet' last_of_dpath_bet
      by (fastforce simp add: follow_psimps intro: list_length_1)
  next
    case (3 u u' l)
    show ?case
    proof (cases "white s u")
      case True
      hence "dist G src u = \<infinity>"
        by (metis white_imp_not_reachable dist_eq_\<delta> \<delta>_reachable_conv)
      thus ?thesis
        using "3.prems"(1)
        by (auto intro: is_shortest_dpathE_2)
    next
      case False
      have is_shortest_dpath: "is_shortest_dpath G (l @ [u]) src u"
        using "3.prems"(1)
        by
          (auto
           simp add: dpath_length_eq_dpath_weight dist_eq_\<delta> is_shortest_dpath_def[symmetric]
           intro: is_shortest_dpath_prefI)
      have "(u, v) \<in> G.dE G"
        using "3.prems"(1) last_of_dpath_bet
        by (fastforce simp add: edge_iff_dpath_bet intro: split_dpath)
      hence "d (parent s) v \<le> d (parent s) u + 1"
        using False "3.prems"(2)
        by (intro d_triangle_inequality_edge)
      also have "... \<le> dist G src u + 1"
        using "3.hyps"[OF is_shortest_dpath False]
        unfolding plus_enat_simps(1)[symmetric] one_enat_def[symmetric]
        by (intro add_right_mono)
      also have "... = dist G src v"
        using "3.prems"(1)
        by (auto intro: is_shortest_dpathE_2)
      finally show ?thesis
        by simp
    qed
  qed
qed

lemma (in bfs_invar_DONE) not_white_imp_is_shortest_dpath:
  assumes "\<not> white s v"
  shows "is_shortest_dpath G (rev_follow (parent s) v) src v"
proof (rule conjI)
  show "dpath_bet (G.dE G) (rev_follow (parent s) v) src v"
    using assms
    by (intro not_white_imp_dpath_rev_follow)
  thus "d (parent s) v = dist G src v"
    using assms
    by (intro not_white_imp_d_le_dist dist_le_dpath_length antisym)
qed

lemma (in bfs_valid_input) soundness:
  assumes "bfs_invar'' s"
  assumes "is_discovered src (parent (loop G src s)) v"
  shows "is_shortest_dpath G (rev_follow (parent (loop G src s)) v) src v"
  using assms
proof (induct rule: bfs_induct[OF assms(1)])
  case (1 G src s)
  show ?case
  proof (cases "DONE s")
    case True
    with "1.prems"(1)
    have "bfs_invar_DONE' G src s"
      by (intro bfs_invar_DONE'I)
    thus ?thesis
      using "1.prems"(2)
      by (intro bfs_invar_DONE.not_white_imp_is_shortest_dpath) (simp_all add: bfs_invar_DONE.loop_psimps)
  next
    case False
    with "1.prems"(1)
    have "bfs_invar_not_DONE' G src s"
      by (intro bfs_invar_not_DONE'I)
    thus ?thesis
      using False "1.prems"(2)
      by (auto simp add: bfs_invar_not_DONE.loop_psimps dest: "1.hyps" intro: bfs_invar_not_DONE.bfs_invar_fold)
  qed
qed

subsection \<open>Correctness\<close>

abbreviation (in bfs) is_shortest_dpath_Map :: "'n \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "is_shortest_dpath_Map G src m \<equiv>
   \<forall>v. (is_discovered src m v \<longrightarrow> is_shortest_dpath G (rev_follow m v) src v) \<and>
       (\<not> is_discovered src m v \<longrightarrow> \<not> reachable (G.dE G) src v)"

lemma (in bfs_valid_input) correctness:
  assumes "bfs_invar'' s"
  shows "is_shortest_dpath_Map G src (parent (loop G src s))"
  using assms soundness completeness
  by simp

theorem (in bfs_valid_input) bfs_correct:
  shows "is_shortest_dpath_Map G src (bfs G src)"
  using bfs_invar_init
  by (intro correctness)

corollary (in bfs) bfs_correct:
  assumes "bfs_valid_input' G src"
  shows "is_shortest_dpath_Map G src (bfs G src)"
  using assms
  by (intro bfs_valid_input.bfs_correct)

end