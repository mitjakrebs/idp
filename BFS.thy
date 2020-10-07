theory BFS
  imports
    "Graph_Theory/Graph_Theory"
    Queue_Specs
    Tbd
begin

record ('q, 'a) state =
  queue :: 'q
  parent :: "'a \<rightharpoonup> 'a"

locale bfs =
  finite_dgraph G +
  Queue where snoc = snoc
  for
    G :: "'a::linorder dgraph" and
    snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  fixes src :: 'a
  assumes src_in_vertices: "src \<in> dVs G"

abbreviation (in bfs) dist :: "'a \<Rightarrow> enat" where
  "dist \<equiv> Shortest_Dpath.dist G src"

section \<open>BFS Algorithm\<close>

definition (in bfs) init :: "('q, 'a) state" where
  "init \<equiv>
   \<lparr>queue = snoc empty src,
    parent = Map.empty\<rparr>"

definition (in bfs) cond :: "('q, 'a) state \<Rightarrow> bool" where
  "cond s \<longleftrightarrow> \<not> is_empty (queue s)"

definition (in bfs) discovered :: "('q, 'a) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "discovered s v \<longleftrightarrow> v = src \<or> v \<in> dom (parent s)"

definition (in bfs) discover :: "'a \<Rightarrow> 'a \<Rightarrow> ('q, 'a) state \<Rightarrow> ('q, 'a) state" where
  "discover u v s \<equiv>
   \<lparr>queue = snoc (queue s) v,
    parent = parent s(v \<mapsto> u)\<rparr>"

definition (in bfs) traverse_edge :: "'a \<Rightarrow> 'a \<Rightarrow> ('q, 'a) state \<Rightarrow> ('q, 'a) state" where
  "traverse_edge u v s \<equiv>
   if \<not> discovered s v then discover u v s
   else s"

function (in bfs) (domintros) loop :: "('q, 'a) state \<Rightarrow> ('q, 'a) state" where
  "loop s =
   (if cond s
    then let
          u = head (queue s);
          q = tail (queue s)
         in loop (fold (traverse_edge u) (sorted_list_of_set (out_neighborhood G u)) (s\<lparr>queue := q\<rparr>))
    else s)"
  by pat_completeness simp

abbreviation (in bfs) bfs :: "('q, 'a) state" where
  "bfs \<equiv> loop init"

section \<open>\<close>

abbreviation (in bfs) fold :: "('q, 'a) state \<Rightarrow> ('q, 'a) state" where
  "fold s \<equiv>
   List.fold
    (traverse_edge (head (queue s)))
    (sorted_list_of_set (out_neighborhood G (head (queue s))))
    (s\<lparr>queue := tail (queue s)\<rparr>)"

abbreviation (in bfs) T :: "('q, 'a) state \<Rightarrow> 'a dgraph" where
  "T s \<equiv> {(u, v) |u v. parent s v = Some u}"

section \<open>Convenience Lemmas\<close>

subsection \<open>invar \<circ> queue\<close>

lemma (in bfs) invar_tail:
  assumes "invar (queue s)"
  assumes "cond s"
  shows "invar (queue (s\<lparr>queue := tail (queue s)\<rparr>))"
  using assms invar_tail
  by (simp add: cond_def is_empty)

subsection \<open>list \<circ> queue\<close>

lemma (in bfs) list_queue_non_empty:
  assumes "invar (queue s)"
  assumes "cond s"
  shows "list (queue s) \<noteq> []"
  using assms
  by (simp add: cond_def is_empty)

section \<open>Basic Lemmas\<close>

subsection \<open>@{term bfs.discover}\<close>

subsubsection \<open>queue\<close>

lemma (in bfs) queue_discover_cong [simp]:
  shows "queue (discover u v s) = snoc (queue s) v"
  by (simp add: discover_def)

subsubsection \<open>parent\<close>

lemma (in bfs) parent_discover_cong [simp]:
  shows "parent (discover u v s) = parent s ++ [v \<mapsto> u]"
  by (simp add: discover_def)

subsection \<open>@{term bfs.traverse_edge}\<close>

subsubsection \<open>queue\<close>

lemma (in bfs) queue_traverse_edge_cong:
  shows "queue (traverse_edge u v s) = (if \<not> discovered s v then snoc (queue s) v else queue s)"
  by (simp add: traverse_edge_def)

subsubsection \<open>invar \<circ> queue\<close>

lemma (in bfs) invar_queue_traverse_edge:
  assumes "invar (queue s)"
  shows "invar (queue (traverse_edge u v s))"
  using assms invar_snoc
  by (simp add: queue_traverse_edge_cong)

subsubsection \<open>list \<circ> queue\<close>

lemma (in bfs) list_queue_traverse_edge_cong:
  assumes "invar (queue s)"
  shows
    "list (queue (traverse_edge u v s)) =
     list (queue s) @ (if \<not> discovered s v then [v] else [])"
  using assms
  by (simp add: queue_traverse_edge_cong list_snoc)

subsubsection \<open>parent\<close>

lemma (in bfs) parent_traverse_edge_cong:
  shows
    "parent (traverse_edge u v s) =
     parent s ++ (if \<not> discovered s v then [v \<mapsto> u] else Map.empty)"
  by (simp add: traverse_edge_def)

subsubsection \<open>@{term bfs.T}\<close>

lemma (in bfs) T_traverse_edge_cong:
  shows "T (traverse_edge u v s) = T s \<union> (if \<not> discovered s v then {(u, v)} else {})"
  by (auto simp add: traverse_edge_def discovered_def discover_def)

subsection \<open>@{term bfs.fold}\<close>

subsubsection \<open>invar \<circ> queue\<close>

lemma (in bfs) invar_queue_fold:
  assumes "invar (queue s)"
  assumes "distinct l"
  shows "invar (queue (List.fold (traverse_edge u) l s))"
  using assms
  by (induct l arbitrary: s) (simp_all add: invar_queue_traverse_edge)

lemma (in bfs) invar_queue_fold_2:
  assumes "invar (queue s)"
  assumes "cond s"
  shows "invar (queue (fold s))"
  using assms
  by (auto intro: invar_tail invar_queue_fold)

subsubsection \<open>list \<circ> queue\<close>

lemma (in bfs) list_queue_fold_cong_aux:
  assumes "distinct (v # vs)"
  assumes "w \<in> set vs"
  shows "discovered (traverse_edge u v s) w = discovered s w"
  using assms
  by (auto simp add: discovered_def parent_traverse_edge_cong)

lemma (in bfs) list_queue_fold_cong:
  assumes "invar (queue s)"
  assumes "distinct l"
  shows
    "list (queue (List.fold (traverse_edge u) l s)) =
     list (queue s) @ filter (Not \<circ> discovered s) l"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons v vs)    
  have
    "list (queue (List.fold (traverse_edge u) (v # vs) s)) =
     list (queue (List.fold (traverse_edge u) vs (traverse_edge u v s)))"
    by simp
  also have
    "... =
     list (queue (traverse_edge u v s)) @
     filter (Not \<circ> discovered (traverse_edge u v s)) vs"
    using Cons.prems
    by (auto intro: invar_queue_traverse_edge Cons.hyps)
  also have
    "... =
     list (queue s) @
     (if \<not> discovered s v then [v] else []) @
     filter (Not \<circ> discovered (traverse_edge u v s)) vs"
    using Cons.prems(1)
    by (simp add: list_queue_traverse_edge_cong)
  also have
    "... =
     list (queue s) @
     (if \<not> discovered s v then [v] else []) @
     filter (Not \<circ> discovered s) vs"
    unfolding comp_apply
    using Cons.prems(2)
    by (auto simp add: list_queue_fold_cong_aux intro: filter_cong)
  also have "... = list (queue s) @ filter (Not \<circ> discovered s) (v # vs)"
    by simp
  finally show ?case
    .
qed

lemma (in bfs) list_queue_fold_cong_2:
  assumes "invar (queue s)"
  assumes "cond s"
  shows
    "list (queue (fold s)) =
     list (tail (queue s)) @
     filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))"
proof -
  have
    "list (queue (fold s)) =
     list (queue (s\<lparr>queue := tail (queue s)\<rparr>)) @
     filter
      (Not \<circ> discovered (s\<lparr>queue := tail (queue s)\<rparr>))
      (sorted_list_of_set (out_neighborhood G (head (queue s))))"
    using assms
    by (intro invar_tail list_queue_fold_cong) simp+
  also have
    "... =
     list (tail (queue s)) @
     filter
      (Not \<circ> discovered s)
      (sorted_list_of_set (out_neighborhood G (head (queue s))))"
    unfolding comp_apply
    by (simp add: discovered_def)
  finally show ?thesis
    .
qed

subsubsection \<open>parent\<close>

lemma (in bfs) parent_fold_cong_aux:
  assumes "distinct (v # vs)"
  shows "w \<in> set vs \<and> \<not> discovered (traverse_edge u v s) w \<longleftrightarrow> w \<in> set vs \<and> \<not> discovered s w"
  using assms
  by (auto simp add: discovered_def parent_traverse_edge_cong)

lemma (in bfs) parent_fold_cong:
  assumes "distinct l"
  shows
    "parent (List.fold (traverse_edge u) l s) =
     parent s ++ (\<lambda>v. if v \<in> set l \<and> \<not> discovered s v then Some u else None)"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons v vs)
  have
    "parent (List.fold (traverse_edge u) (v # vs) s) =
     parent (List.fold (traverse_edge u) vs (traverse_edge u v s))"
    by simp
  also have
    "... =
     parent (traverse_edge u v s) ++
     (\<lambda>w. if w \<in> set vs \<and> \<not> discovered (traverse_edge u v s) w then Some u else None)"
    using Cons.prems
    by (intro Cons.hyps) simp
  also have
    "... =
     parent s ++
     (if \<not> discovered s v then [v \<mapsto> u] else Map.empty) ++
     (\<lambda>w. if w \<in> set vs \<and> \<not> discovered (traverse_edge u v s) w then Some u else None)"
    by (simp add: parent_traverse_edge_cong)
  also have
    "... =
     parent s ++
     (if \<not> discovered s v then [v \<mapsto> u] else Map.empty) ++
     (\<lambda>w. if w \<in> set vs \<and> \<not> discovered s w then Some u else None)"
    using Cons.prems
    by (simp add: parent_fold_cong_aux)
  also have
    "... =
     parent s ++
     (\<lambda>w. if w \<in> set (v # vs) \<and> \<not> discovered s w then Some u else None)"
    using Cons.prems
    by (auto simp add: map_add_def)
  finally show ?case
    .
qed

lemma (in bfs) parent_fold_cong_2:
  shows
    "parent (fold s) =
     parent s ++
     (\<lambda>v. if v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> \<not> discovered s v
          then Some (head (queue s))
          else None)"
proof -
  have
    "parent (fold s) =
     parent (s\<lparr>queue := tail (queue s)\<rparr>) ++
     (\<lambda>v. if v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and>
             \<not> discovered (s\<lparr>queue := tail (queue s)\<rparr>) v
          then Some (head (queue s))
          else None)"
    by (simp add: parent_fold_cong)
  thus ?thesis
    by (simp add: discovered_def)
qed

(* TODO: remove? *)
lemma (in bfs) parent_le_parent_fold:
  shows "parent s \<subseteq>\<^sub>m parent (fold s)"
  unfolding map_le_def
proof
  fix v
  assume "v \<in> dom (parent s)"
  hence "discovered s v"
    by (simp add: discovered_def)
  thus "parent s v = parent (fold s) v"
    by (simp add: parent_fold_cong_2 map_add_def)
qed

subsubsection \<open>dom \<circ> parent\<close>

lemma (in bfs) dom_parent_fold_subset_vertices:
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes "distinct l"
  assumes "set l \<subseteq> dVs G"
  shows "dom (parent (List.fold (traverse_edge u) l s)) \<subseteq> dVs G"
  using assms
  by (auto simp add: parent_fold_cong split: if_splits(2))

lemma (in bfs) dom_parent_fold_subset_vertices_2:
  assumes "dom (parent s) \<subseteq> dVs G"
  shows "dom (parent (fold s)) \<subseteq> dVs G"
proof -
  have "set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<subseteq> dVs G"
    using out_neighborhood_finite out_neighborhood_subset_vertices
    by simp
  thus ?thesis
    using assms dom_parent_fold_subset_vertices
    by simp
qed

subsubsection \<open>@{term bfs.T}\<close>

lemma (in bfs) T_fold_cong:
  assumes "distinct l"
  shows "T (List.fold (traverse_edge u) l s) = T s \<union> {(u, v) |v. v \<in> set l \<and> \<not> discovered s v}"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by auto
next
  case (Cons v vs)
  have
    "T (List.fold (traverse_edge u) (v # vs) s) =
     T (List.fold (traverse_edge u) vs (traverse_edge u v s))"
    by simp
  also have
    "... =
     T (traverse_edge u v s) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> discovered (traverse_edge u v s) w}"
    using Cons.prems
    by (intro Cons.hyps) simp
  also have
    "... =
     T s \<union>
     (if \<not> discovered s v then {(u, v)} else {}) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> discovered (traverse_edge u v s) w}"
    unfolding T_traverse_edge_cong
    by blast
  also have
    "... =
     T s \<union>
     (if \<not> discovered s v then {(u, v)} else {}) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> discovered s w}"
    using Cons.prems
    by (simp add: parent_fold_cong_aux)
  also have "... = T s \<union> {(u, w) |w. w \<in> set (v # vs) \<and> \<not> discovered s w}"
    by force
  finally show ?case
    .
qed

lemma (in bfs) T_fold_cong_2:
  shows
    "T (fold s) =
     T s \<union>
     {(head (queue s), v) |v.
      v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> \<not> discovered s v}"
proof -
  have
    "T (fold s) =
     T (s\<lparr>queue := tail (queue s)\<rparr>) \<union>
     {(head (queue s), v) |v.
      v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and>
      \<not> discovered (s\<lparr>queue := tail (queue s)\<rparr>) v}"
    by (intro T_fold_cong) simp
  thus ?thesis
    by (simp add: discovered_def)
qed

section \<open>Termination\<close>

lemma (in bfs) loop_dom_aux:
  assumes "dom (parent s) \<subseteq> dVs G"
  shows
    "card (dom (parent (fold s))) =
     card (dom (parent s)) +
     card {v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))). \<not> discovered s v}"
proof -
  let ?S = "{v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))). \<not> discovered s v}"
  have "dom (parent (fold s)) = dom (parent s) \<union> ?S"
    by (auto simp add: parent_fold_cong_2 domIff)
  moreover have "finite (dom (parent s))"
    using assms vertices_finite
    by (rule finite_subset)
  moreover have "finite ?S"
    using out_neighborhood_finite
    by simp
  moreover have "dom (parent s) \<inter> ?S = {}"
    by (auto simp add: discovered_def)
  ultimately show ?thesis
    by (simp add: card_Un_disjoint)
qed

lemma (in bfs) loop_dom_aux_2:
  assumes invar_queue: "invar (queue s)"
  assumes cond: "cond s"
  assumes dom_parent_subset_vertices: "dom (parent s) \<subseteq> dVs G"
  shows
    "card (dVs G) +
     length (list (tail (queue s))) -
     card (dom (parent s)) <
     card (dVs G) +
     length (list (queue s)) -
     card (dom (parent s))"
proof -
  have "list (queue s) \<noteq> []"
    using invar_queue cond
    by (intro list_queue_non_empty)
  hence "length (list (tail (queue s))) < length (list (queue s))"
    using invar_queue
    by (simp add: list_tail)
  moreover have "card (dom (parent s)) \<le> card (dVs G)"
    using vertices_finite dom_parent_subset_vertices
    by (intro card_mono)
  ultimately show ?thesis
    by simp
qed

lemma (in bfs) loop_dom:
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  shows "loop_dom s"
  using assms
proof (induct "card (dVs G) + length (list (queue s)) - card (dom (parent s))"
       arbitrary: s
       rule: less_induct)
  case less
  show ?case
  proof (cases "cond s")
    case True
    let ?u = "head (queue s)"
    let ?q = "tail (queue s)"
    let ?S = "{v \<in> set (sorted_list_of_set (out_neighborhood G ?u)). \<not> discovered s v}"

    have "length (list (queue (fold s))) = length (list ?q) + card ?S"
      using less.prems(1) True
      by (simp add: list_queue_fold_cong_2 distinct_card[symmetric])
    moreover have "card (dom (parent (fold s))) = card (dom (parent s)) + card ?S"
      using less.prems(2)
      by (intro loop_dom_aux)
    ultimately have
      "card (dVs G) + length (list (queue (fold s))) - card (dom (parent (fold s))) =
       card (dVs G) + length (list ?q) + card ?S - (card (dom (parent s)) + card ?S)"
      by presburger
    also have "... = card (dVs G) + length (list ?q) - card (dom (parent s))"
      by simp
    also have "... < card (dVs G) + length (list (queue s)) - card (dom (parent s))"
      using less.prems True
      by (intro loop_dom_aux_2)
    finally have
      "card (dVs G) + length (list (queue (fold s))) - card (dom (parent (fold s))) <
       card (dVs G) + length (list (queue s)) - card (dom (parent s))"
      .
    thus ?thesis
      using less.prems
      by (intro invar_queue_fold_2 dom_parent_fold_subset_vertices_2 less.hyps loop.domintros)
  next
    case False
    thus ?thesis
      by (blast intro: loop.domintros)
  qed
qed

section \<open>Invariants\<close>

subsection \<open>\<close>

abbreviation (in bfs) white :: "('q, 'a) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "white s v \<equiv> \<not> discovered s v"

abbreviation (in bfs) gray :: "('q, 'a) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "gray s v \<equiv> discovered s v \<and> v \<in> set (list (queue s))"

lemma (in bfs) gray_imp_not_white:
  assumes "gray s v"
  shows "\<not> white s v"
  using assms
  by simp

abbreviation (in bfs) black :: "('q, 'a) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "black s v \<equiv> discovered s v \<and> v \<notin> set (list (queue s))"

lemma (in bfs) black_imp_not_white:
  assumes "black s v"
  shows "\<not> white s v"
  using assms
  by simp

lemma (in bfs) vertex_color_induct [case_names white gray black]:
  assumes "white s v \<Longrightarrow> P s v"
  assumes "gray s v \<Longrightarrow> P s v"
  assumes "black s v \<Longrightarrow> P s v"
  shows "P s v"
  using assms
  by blast

locale bfs_invar =
  bfs where G = G and snoc = snoc +
  parent "state.parent s"
  for
    G :: "'a::linorder dgraph" and
    snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
    s :: "('q, 'a) state" +
  assumes invar_queue: "invar (queue s)"
  assumes queue_distinct: "distinct (list (queue s))"
  assumes parent_src: "parent s src = None"
  assumes gray_if_mem_queue: "v \<in> set (list (queue s)) \<Longrightarrow> gray s v"
  assumes black_if_mem_ran: "v \<in> ran (parent s) \<Longrightarrow> black s v"
  assumes queue_sorted_wrt_dpath_length:
    "\<not> is_empty (queue s) \<Longrightarrow>
     sorted_wrt (\<lambda>u v. dpath_length (rev (follow u)) \<le> dpath_length (rev (follow v))) (list (queue s)) \<and>
     dpath_length (rev (follow (last (list (queue s))))) \<le> dpath_length (rev (follow (head (queue s)))) + 1"
  assumes not_white_imp_shortest_dpath:
    "\<not> white s v \<Longrightarrow> dpath_bet G (rev (follow v)) src v \<and> dpath_length (rev (follow v)) = dist v"
  assumes black_imp_out_neighborhood_not_white: "black s v \<Longrightarrow> \<forall>w\<in>out_neighborhood G v. \<not> white s w"

subsection \<open>Convenience Lemmas\<close>

lemma (in bfs_invar) src_not_white:
  shows "\<not> white s src"
  by (simp add: discovered_def)

(* TODO: move somewhere else *)
lemma sorted_wrt_imp_hd:
  assumes l_sorted_wrt: "sorted_wrt P l"
  assumes x_mem_l: "x \<in> set l"
  assumes x_not_hd: "x \<noteq> hd l"
  shows "P (hd l) x"
proof -
  have "l \<noteq> []"
    using x_mem_l
    by fastforce
  hence hd_eq_0th: "hd l = l ! 0"
    by (simp add: hd_conv_nth)
  obtain i where
    "i < length l" and
    x_eq_ith: "x = l ! i"
    using x_mem_l
    by (auto simp add: in_set_conv_nth)
  moreover have "0 < i"
    using x_not_hd
    by (auto simp add: hd_eq_0th x_eq_ith intro: gr0I)
  ultimately show ?thesis
    using l_sorted_wrt
    by (auto simp add: hd_eq_0th x_eq_ith intro: sorted_wrt_nth_less)
qed

lemma (in bfs_invar) mem_queue_imp_dpath_length_head_queue:
  assumes "v \<in> set (list (queue s))"
  shows "dpath_length (rev (follow (head (queue s)))) \<le> dpath_length (rev (follow v))"
proof (cases "v = head (queue s)")
  case True
  thus ?thesis
    by simp
next
  case False
  have "\<not> is_empty (queue s)"
    using invar_queue assms
    by (auto simp add: is_empty)
  moreover hence "head (queue s) = hd (list (queue s))"
    using invar_queue list_head
    by (simp add: is_empty)
  ultimately show ?thesis
    using queue_sorted_wrt_dpath_length assms False sorted_wrt_imp_hd
    by fastforce
qed

lemma (in bfs_invar) mem_queue_imp_dist_head_queue:
  assumes "v \<in> set (list (queue s))"
  shows "dist (head (queue s)) \<le> dist v"
proof -
  have "list (queue s) \<noteq> []"
    using assms
    by fastforce
  hence "head (queue s) \<in> set (list (queue s))"
    using invar_queue
    by (simp add: list_head)
  hence "dist (head (queue s)) = dpath_length (rev (follow (head (queue s))))"
    using gray_if_mem_queue
    by (simp add: not_white_imp_shortest_dpath)
  also have "... \<le> dpath_length (rev (follow v))"
    using assms
    by (auto intro: mem_queue_imp_dpath_length_head_queue)
  also have "... = dist v"
    using assms gray_if_mem_queue
    by (simp add: not_white_imp_shortest_dpath)
  finally show ?thesis
    .
qed

(* TODO: move somewhere else *)
lemma sorted_wrt_imp_last_aux:
  assumes x_mem_l: "x \<in> set l"
  assumes x_neq_last: "x \<noteq> last l"
  obtains i where
    "i < length l - 1"
    "x = l ! i"
proof -
  have l_non_empty: "l \<noteq> []"
    using x_mem_l
    by fastforce
  obtain i where
    "i < length l" and
    x_eq_ith: "x = l ! i"
    using x_mem_l
    by (auto simp add: in_set_conv_nth)
  hence "i < Suc (length l - 1)"
    by simp
  moreover have "i \<noteq> length l - 1"
    using x_neq_last l_non_empty
    by (auto simp add: x_eq_ith last_conv_nth)
  ultimately have "i < length l - 1"
    by (elim less_SucE) simp+
  thus ?thesis
    using x_eq_ith
    by (intro that)
qed

(* TODO: move somewhere else *)
lemma sorted_wrt_imp_last:
  assumes l_sorted_wrt: "sorted_wrt P l"
  assumes x_mem_l: "x \<in> set l"
  assumes x_neq_last: "x \<noteq> last l"
  shows "P x (last l)"
proof -
  have "l \<noteq> []"
    using x_mem_l
    by fastforce
  hence last_eq: "last l = l ! (length l - 1)"
    by (simp add: last_conv_nth)
  obtain i where
    "i < length l - 1" and
    x_eq_ith: "x = l ! i"
    using assms(2, 3)
    by (elim sorted_wrt_imp_last_aux)
  thus ?thesis
    using l_sorted_wrt
    by (auto simp add: x_eq_ith last_eq intro: sorted_wrt_nth_less)
qed

lemma (in bfs_invar) mem_queue_imp_dpath_length_last_queue:
  assumes "v \<in> set (list (queue s))"
  shows "dpath_length (rev (follow v)) \<le> dpath_length (rev (follow (last (list (queue s)))))"
proof (cases "v = last (list (queue s))")
  case True
  thus ?thesis
    by simp
next
  case False
  have "\<not> is_empty (queue s)"
    using invar_queue assms
    by (auto simp add: is_empty)
  thus ?thesis
    using queue_sorted_wrt_dpath_length assms False sorted_wrt_imp_last
    by fastforce
qed

lemma (in bfs_invar) mem_queue_imp_dist_last_queue:
  assumes "v \<in> set (list (queue s))"
  shows "dist v \<le> dist (last (list (queue s)))"
proof -
  have list_queue_non_empty: "list (queue s) \<noteq> []"
    using assms
    by fastforce
  have "dist v = dpath_length (rev (follow v))"
    using assms gray_if_mem_queue
    by (simp add: not_white_imp_shortest_dpath)
  also have "... \<le> dpath_length (rev (follow (last (list (queue s)))))"
    using assms
    by (auto intro: mem_queue_imp_dpath_length_last_queue)
  also have "... = dist (last (list (queue s)))"
    using list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_shortest_dpath)
  finally show ?thesis
    .
qed

lemma (in bfs_invar) mem_queue_dpath_lengthI:
  assumes "v \<in> set (list (queue s))"
  shows
    "dpath_length (rev (follow (head (queue s)))) \<le> dpath_length (rev (follow v))"
    "dpath_length (rev (follow v)) \<le> dpath_length (rev (follow (last (list (queue s)))))"
  using assms
  by (auto intro: mem_queue_imp_dpath_length_head_queue mem_queue_imp_dpath_length_last_queue)

lemma (in bfs_invar) mem_queue_distI:
  assumes "v \<in> set (list (queue s))"
  shows
    "dist (head (queue s)) \<le> dist v"
    "dist v \<le> dist (last (list (queue s)))"
  using assms
  by (auto intro: mem_queue_imp_dist_head_queue mem_queue_imp_dist_last_queue)

subsection \<open>Basic Lemmas\<close>

lemma (in bfs_invar) parent_imp_edge:
  assumes "parent s v = Some u"
  shows "(u, v) \<in> G"
proof -
  have "rev (follow v) = rev (follow u) @ [v]"
    using assms
    by (simp add: follow_psimps)
  moreover have "rev (follow u) = (rev (tl (follow u))) @ [u]"
    using follow_non_empty hd_Cons_tl follow_ConsD rev.simps(2)
    by metis
  ultimately have "rev (follow v) = rev (tl (follow u)) @ [u, v]"
    by simp
  moreover have "dpath_bet G (rev (follow v)) src v"
    using assms not_white_imp_shortest_dpath
    by (simp add: discovered_def domIff)
  ultimately have "dpath_bet G (rev (tl (follow u)) @ [u, v]) src v"
    by simp
  thus ?thesis
    by (auto simp add: edge_iff_dpath_bet intro: split_dpath)
qed

lemma (in bfs_invar) dom_parent_subset_vertices:
  shows "dom (parent s) \<subseteq> dVs G"
proof
  fix v
  assume "v \<in> dom (parent s)"
  then obtain u where
    "parent s v = Some u"
    by (auto simp add: domIff)
  hence "(u, v) \<in> G"
    by (intro parent_imp_edge)
  thus "v \<in> dVs G"
    by (intro dVsI(2))
qed

lemma (in bfs_invar) queue_sorted_wrt_dist:
  assumes "\<not> is_empty (queue s)"
  shows
    "sorted_wrt (\<lambda>u v. dist u \<le> dist v) (list (queue s))"
    "dist (last (list (queue s))) \<le> dist (head (queue s)) + 1"
proof -
  have dpath_length_follow_eq_dist: "\<forall>v\<in>set (list (queue s)). dpath_length (rev (follow v)) = dist v"
    using gray_if_mem_queue not_white_imp_shortest_dpath
    by blast
  hence
    "\<And>u v. u \<in> set (list (queue s)) \<Longrightarrow>
            v \<in> set (list (queue s)) \<Longrightarrow>
            dpath_length (rev (follow u)) \<le> dpath_length (rev (follow v)) \<Longrightarrow>
            (\<lambda>u v. dist u \<le> dist v) u v"
    using assms
    by (simp add: enat_ord_simps(1)[symmetric])
  thus "sorted_wrt (\<lambda>u v. dist u \<le> dist v) (list (queue s))"
    using assms queue_sorted_wrt_dpath_length sorted_wrt_mono_rel[of "(list (queue s))"]
    by presburger
  have
    "last (list (queue s)) \<in> set (list (queue s))"
    "head (queue s) \<in> set (list (queue s))"
    using invar_queue assms
    by (simp_all add: is_empty list_head)
  thus "dist (last (list (queue s))) \<le> dist (head (queue s)) + 1"
    using assms queue_sorted_wrt_dpath_length dpath_length_follow_eq_dist
    unfolding enat_ord_simps(1)[symmetric] plus_enat_simps(1)[symmetric] one_enat_def[symmetric]
    by simp
qed

lemma (in bfs_invar) white_imp_gray_ancestor:
  assumes "dpath_bet G p u v"
  assumes "\<not> white s u"
  assumes "white s v"
  shows "\<exists>v\<in>set p. gray s v"
  using assms
proof (induct p arbitrary: v rule: dpath_rev_induct)
  case 1
  thus ?case
    by simp
next
  case (2 w)
  hence "[w] = [u] \<and> u = v"
    by (intro hd_of_dpath_bet' last_of_dpath_bet list_length_1) simp
  thus ?case
    using "2.prems"(2, 3)
    by simp
next
  case (3 w w' l)
  show ?case
  proof (induct s w rule: vertex_color_induct)
    case white
    have "dpath_bet G (l @ [w]) u w"
      using "3.prems"(1)
      by (intro dpath_bet_pref) simp
    hence "\<exists>v\<in>set (l @ [w]). gray s v"
      using "3.prems"(2) white
      by (intro "3.hyps")
    thus ?thesis
      by auto
  next
    case gray
    thus ?thesis
      by simp
  next
    case black
    have "v \<in> out_neighborhood G w"
      using "3.prems"(1)
      by (auto simp add: dpath_bet_def in_out_neighborhood_iff_edge intro: dpath_snoc_edge_2)
    hence "\<not> white s v"
      using black black_imp_out_neighborhood_not_white
        by blast
    thus ?thesis
      using "3.prems"(3)
      by simp
  qed
qed

lemma (in bfs_invar) white_imp_dist_ge_case_1_subcase_3:
  assumes IH:
    "\<And>v. \<lbrakk> dpath_bet G (l @ [u]) src v \<and> dpath_length (l @ [u]) = dist v; white s v \<rbrakk> \<Longrightarrow>
          (if is_empty (queue s) then \<infinity> else dist (last (list (queue s)))) \<le> dist v"
  assumes shortest_dpath: "dpath_bet G (l @ [u, u']) src v \<and> dpath_length (l @ [u, u']) = dist v"
  assumes white: "white s v"
  shows "(if is_empty (queue s) then \<infinity> else dist (last (list (queue s)))) \<le> dist v"
proof (induct s u rule: vertex_color_induct)
  case white
  have l_snoc_u_shortest_dpath: "dpath_bet G (l @ [u]) src u \<and> dpath_length (l @ [u]) = dist u"
    using shortest_dpath
    by
      (auto
       simp add: dpath_length_eq_dpath_weight dist_eq_\<delta> is_shortest_dpath_def[symmetric]
       intro: shortest_dpath_prefix_is_shortest_dpath)
  hence "(if is_empty (queue s) then \<infinity> else dist (last (list (queue s)))) \<le> dist u"
    using white
    by (intro IH)
  also have "... = dpath_length (l @ [u])"
    by (simp add: l_snoc_u_shortest_dpath)
  also have "... \<le> dpath_length (l @ [u, u'])"
    using dpath_length_append[where ?p = "l @ [u]" and ?q = "[u']"]
    by simp
  also have "... = dist v"
    by (simp add: shortest_dpath)
  finally show ?case
    .
next
  case gray
  hence "\<exists>v\<in>set (l @ [u, u']). gray s v"
    using src_not_white shortest_dpath white
    by (blast intro: white_imp_gray_ancestor)
  hence queue_non_empty: "\<not> is_empty (queue s)"
    using invar_queue
    by (auto simp add: is_empty)
  hence "dist (last (list (queue s))) \<le> dist (head (queue s)) + 1"
    by (intro queue_sorted_wrt_dist(2))
  also have "... \<le> dist u + 1"
    using gray
    by (blast intro: mem_queue_imp_dist_head_queue add_right_mono)
  also have "... = dist v"
    using shortest_dpath
    by (auto intro: shortest_dpathE_2)
  finally show ?case
    using queue_non_empty
    by simp
next
  case black
  have "v \<in> out_neighborhood G u"
    using shortest_dpath last_of_dpath_bet
    by (fastforce simp add: edge_iff_dpath_bet in_out_neighborhood_iff_edge intro: split_dpath)
  hence "\<not> white s v"
    using black black_imp_out_neighborhood_not_white
    by blast
  thus ?case
    using white
    by simp
qed

lemma (in bfs_invar) white_imp_dist_ge_case_1:
  assumes "dpath_bet G p src v \<and> dpath_length p = dist v"
  assumes "white s v"
  shows "(if is_empty (queue s) then \<infinity> else dist (last (list (queue s)))) \<le> dist v"
  using assms
proof (induct p arbitrary: v rule: dpath_rev_induct)
  case 1
  thus ?case
    by simp
next
  case (2 u)
  hence "[u] = [src] \<and> src = v"
    by (intro hd_of_dpath_bet' last_of_dpath_bet list_length_1) auto
  thus ?case
    using src_not_white "2.prems"(2)
    by simp
next
  case (3 u u' l)
  thus ?case
    by (rule white_imp_dist_ge_case_1_subcase_3)
qed

lemma (in bfs_invar) white_imp_dist_ge:
  assumes "white s v"
  shows "(if is_empty (queue s) then \<infinity> else dist (last (list (queue s)))) \<le> dist v"
proof (cases "reachable G src v")
  case True
  then obtain p where
    "dpath_bet G p src v \<and> dpath_length p = dist v"
    by (elim dist_dpath_betE) simp
  thus ?thesis
    using assms
    by (intro white_imp_dist_ge_case_1)
next
  case False
  hence "dist v = \<infinity>"
    unfolding dist_eq_\<delta>
    by (meson \<delta>_reachable_conv)
  thus ?thesis
    by simp
qed

subsection \<open>@{term bfs.init}\<close>

subsubsection \<open>\<close>

lemma (in bfs) follow_invar'_parent_init:
  shows "follow_invar' (parent init)"
  using wf_empty
  by (simp add: follow_invar'_def init_def)

lemma (in bfs) parent_init:
  shows "Tbd.parent (parent init)"
  using follow_invar'_parent_init
  by unfold_locales

subsubsection \<open>@{thm bfs_invar.invar_queue}\<close>

lemma (in bfs) invar_queue_init:
  shows "invar (queue init)"
  using invar_empty
  by (auto simp add: init_def intro: invar_snoc)

subsubsection \<open>@{thm bfs_invar.queue_distinct}\<close>

lemma (in bfs) queue_distinct_init:
  shows "distinct (list (queue init))"
  using invar_empty
  by (simp add: init_def list_snoc list_empty)

subsubsection \<open>@{thm bfs_invar.parent_src}\<close>

lemma (in bfs) parent_src_init:
  shows "parent init src = None"
  by (simp add: init_def)

subsubsection \<open>@{thm bfs_invar.gray_if_mem_queue}\<close>

lemma (in bfs) gray_if_mem_queue_init:
  assumes "v \<in> set (list (queue init))"
  shows "gray init v"
  using assms invar_empty
  by (simp add: init_def list_snoc list_empty discovered_def)

subsubsection \<open>@{thm bfs_invar.black_if_mem_ran}\<close>

lemma (in bfs) black_if_mem_ran_init:
  assumes "v \<in> ran (parent init)"
  shows "black init v"
  using assms
  by (simp add: init_def)

subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_dpath_length}\<close>

lemma (in bfs) queue_sorted_wrt_dpath_length_init:
  assumes "\<not> is_empty (queue init)"
  shows
    "sorted_wrt
      (\<lambda>u v. dpath_length (rev (parent.follow (parent init) u)) \<le>
             dpath_length (rev (parent.follow (parent init) v)))
      (list (queue init)) \<and>
     dpath_length (rev (parent.follow (parent init) (last (list (queue init))))) \<le>
     dpath_length (rev (parent.follow (parent init) (head (queue init)))) + 1"
  using invar_empty invar_queue_init
  by (simp add: init_def list_snoc list_empty list_head)

subsubsection \<open>@{thm bfs_invar.not_white_imp_shortest_dpath}\<close>

lemma (in bfs) not_white_imp_shortest_dpath_init:
  assumes "\<not> white init v"
  shows
    "dpath_bet G (rev (parent.follow (parent init) v)) src v \<and>
     dpath_length (rev (parent.follow (parent init) v)) = dist v"
proof -
  have dpath_bet: "dpath_bet G [src] src src"
    using src_in_vertices
    by (intro dpath_bet_reflexive)
  have "dpath_length [src] = 0"
    by simp
  also have "... \<le> dist src"
    using zero_le
    by (subst zero_enat_def[symmetric])
  finally have "dpath_length [src] \<le> dist src"
    .
  hence "dpath_length [src] = dist src"
    using dpath_bet
    by (intro dist_le_dpath_length antisym)
  moreover have "v = src"
    using assms
    by (simp add: discovered_def init_def)
  moreover have "rev (parent.follow (parent init) src) = [src]"
    using parent_init
    by (simp add: parent_src_init parent.follow_psimps)
  ultimately show ?thesis
    using dpath_bet
    by simp
qed

subsubsection \<open>@{thm bfs_invar.black_imp_out_neighborhood_not_white}\<close>

lemma (in bfs) black_imp_out_neighborhood_not_white_init:
  assumes "black init v"
  shows "\<forall>w\<in>out_neighborhood G v. \<not> white init w"
proof -
  have "v = src"
    using assms
    by (simp add: discovered_def init_def)
  moreover have "src \<in> set (list (queue init))"
    using invar_empty
    by (simp add: init_def list_snoc)
  ultimately show ?thesis
    using assms
    by blast
qed

subsubsection \<open>\<close>

lemma (in bfs) bfs_invar_init:
  shows "bfs_invar empty is_empty head tail invar list src G snoc init"
  using bfs_axioms
  using follow_invar'_parent_init
  using invar_queue_init queue_distinct_init parent_src_init gray_if_mem_queue_init
  using black_if_mem_ran_init queue_sorted_wrt_dpath_length_init not_white_imp_shortest_dpath_init
  using black_imp_out_neighborhood_not_white_init
  by unfold_locales

subsection \<open>@{term bfs.fold}\<close>

subsubsection \<open>Convenience Lemmas\<close>

lemma (in bfs_invar) list_queue_non_empty:
  assumes "cond s"
  shows "list (queue s) \<noteq> []"
  using invar_queue assms
  by (intro list_queue_non_empty)

(* TODO: move somewhere else *)
lemma (in Queue) list_queue:
  assumes "invar q"
  assumes "list q \<noteq> []"
  shows "list q = head q # list (tail q)"
  using assms
  by (simp add: list_head list_tail)

lemma (in bfs_invar) head_imp:
  assumes cond: "cond s"
  assumes v_eq_head: "v = head (queue s)"
  shows
    "v \<in> set (list (queue s))"
    "v \<notin> set (list (queue (fold s)))"
proof -
  show "v \<in> set (list (queue s))"
    using invar_queue assms list_queue_non_empty
    by (simp add: list_head)
  hence "v \<notin> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    using gray_if_mem_queue
    by fastforce
  moreover have "v \<notin> set (list (tail (queue s)))"
    using queue_distinct v_eq_head
    by (simp add: list_queue[OF invar_queue list_queue_non_empty[OF cond]])
  ultimately show "v \<notin> set (list (queue (fold s)))"
    using invar_queue cond
    by (simp add: list_queue_fold_cong_2)
qed

lemma (in bfs_invar) head_if:
  assumes "cond s"
  assumes "v \<in> set (list (queue s))"
  assumes "v \<notin> set (list (queue (fold s)))"
  shows "v = head (queue s)"
proof -
  have "list (queue s) = head (queue s) # list (tail (queue s))"
    using invar_queue assms(1)
    by (intro list_queue_non_empty list_queue)
  thus ?thesis
    using invar_queue assms
    by (simp add: list_queue_fold_cong_2)
qed

lemma (in bfs_invar) head_iff:
  assumes "cond s"
  shows "v = head (queue s) \<longleftrightarrow> v \<in> set (list (queue s)) \<and> v \<notin> set (list (queue (fold s)))"
proof (standard, goal_cases)
  case 1
  thus ?case
    using assms
    by (intro head_imp conjI)
next
  case 2
  thus ?case
    using assms
    by (blast intro: head_if)
qed

lemma (in bfs_invar) not_white_imp_not_white_fold:
  assumes "\<not> white s v"
  shows "\<not> white (fold s) v"
  using assms
  by (auto simp add: discovered_def parent_fold_cong_2)

subsubsection \<open>\<close>

lemma (in bfs_invar) follow_invar'_parent_fold:
  assumes "cond s"
  shows "follow_invar' (parent (fold s))"
  unfolding follow_invar'_def T_fold_cong_2
proof (rule wf_Un[unfolded follow_invar'_def])
  let ?r =
    "{(head (queue s), v) |v.
      v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> \<not> discovered s v}"
  show "wf (T s)"
    using follow_invar'
    by (simp add: follow_invar'_def)
  have "gray s (head (queue s))"
    using assms
    by (intro head_imp(1) gray_if_mem_queue) simp+
  thus "wf ?r"
    by (simp add: wf_def)
  show "Domain (T s) \<inter> Range ?r = {}"
    using black_if_mem_ran
    by (auto simp add: ran_def)
qed

lemma (in bfs_invar) parent_fold:
  assumes "cond s"
  shows "Tbd.parent (parent (fold s))"
  using assms
  by unfold_locales (intro follow_invar'_parent_fold)

subsubsection \<open>@{thm bfs_invar.invar_queue}\<close>

lemma (in bfs_invar) invar_queue_fold:
  assumes "cond s"
  shows "invar (queue (fold s))"
  using invar_queue assms
  by (intro invar_queue_fold_2)

subsubsection \<open>@{thm bfs_invar.queue_distinct}\<close>

lemma (in bfs_invar) queue_distinct_fold:
  assumes "cond s"
  shows "distinct (list (queue (fold s)))"
proof -
  let ?l1 = "(list (tail (queue s)))"
  let ?l2 = "(filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
  have list_queue_non_empty: "list (queue s) \<noteq> []"
    using assms
    by (intro list_queue_non_empty)
  hence "\<And>v. v \<in> set ?l1 \<Longrightarrow> \<not> white s v"
    using gray_if_mem_queue invar_queue
    by (auto simp add: list_tail intro: list.set_sel(2))
  hence "set ?l1 \<inter> set ?l2 = {}"
    by fastforce
  moreover have "distinct ?l1"
    using queue_distinct invar_queue list_queue_non_empty
    by (auto simp add: list_tail intro: distinct_tl)
  moreover have "distinct ?l2"
    by fastforce
  ultimately show ?thesis
    using invar_queue assms
    by (simp add: list_queue_fold_cong_2)
qed

subsubsection \<open>@{thm bfs_invar.parent_src}\<close>

lemma (in bfs_invar) parent_src_fold:
  shows "parent (fold s) src = None"
  using src_not_white
  by (simp add: parent_fold_cong_2 parent_src)

subsubsection \<open>@{thm bfs_invar.gray_if_mem_queue}\<close>

lemma (in bfs_invar) gray_if_mem_queue_fold:
  assumes cond: "cond s"
  assumes mem_queue_fold: "v \<in> set (list (queue (fold s)))"
  shows "gray (fold s) v"
proof (cases "v \<in> set (list (queue s))")
  case True
  hence "gray s v"
    by (intro gray_if_mem_queue)
  thus ?thesis
    using cond not_white_imp_not_white_fold mem_queue_fold
    by blast
next
  case False
  have "list (queue s) \<noteq> []"
    using cond
    by (intro list_queue_non_empty)
  hence "v \<notin> set (list (tail (queue s)))"
    using False invar_queue
    by (auto simp add: list_tail intro: list.set_sel(2))
  hence "v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> \<not> discovered s v"
    using mem_queue_fold invar_queue cond
    by (simp add: list_queue_fold_cong_2)
  hence "\<not> white (fold s) v"
    by (fastforce simp add: discovered_def parent_fold_cong_2)
  thus ?thesis
    using mem_queue_fold
    by blast
qed

subsubsection \<open>@{thm bfs_invar.black_if_mem_ran}\<close>

lemma (in bfs_invar) black_if_mem_ran_fold_case_1:
  assumes cond: "cond s"
  assumes mem_ran: "v \<in> ran (parent s)"
  shows "black (fold s) v"
proof (rule ccontr)
  assume assm: "\<not> black (fold s) v"
  have black: "black s v"
    using mem_ran
    by (intro black_if_mem_ran)
  with cond
  have not_white_fold: "\<not> white (fold s) v"
    by (intro black_imp_not_white not_white_imp_not_white_fold)
  have "list (queue s) \<noteq> []"
    using cond
    by (intro list_queue_non_empty)
  hence "v \<notin> set (list (tail (queue s)))"
    using black invar_queue
    by (auto simp add: list_tail intro: list.set_sel(2))
  moreover have "v \<in> set (list (queue (fold s)))"
    using assm not_white_fold
    by blast
  ultimately have "white (fold s) v"
    using invar_queue cond black
    by (simp add: discovered_def list_queue_fold_cong_2)
  thus "False"
    using not_white_fold
    by blast
qed

lemma (in bfs_invar) black_if_mem_ran_fold_case_2_aux:
  assumes "v \<notin> ran (parent s)"
  assumes "v \<in> ran (parent (fold s))"
  shows "v = head (queue s)"
proof -
  have
    "dom (parent s) \<inter>
     dom (\<lambda>v. if v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> \<not> discovered s v
              then Some (head (queue s)) else None) = {}"
    by (auto simp add: domIff discovered_def)
  hence
    "ran (parent (fold s)) =
     ran (parent s) \<union>
     ran (\<lambda>v. if v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> \<not> discovered s v
              then Some (head (queue s)) else None)"
    by (simp add: parent_fold_cong_2 ran_map_add)
  thus ?thesis
    using assms
    by (auto simp add: ran_def split: if_splits(2))
qed

lemma (in bfs_invar) black_if_mem_ran_fold_case_2:
  assumes cond: "cond s"
  assumes mem_ran_fold: "v \<in> ran (parent (fold s))"
  assumes not_mem_ran: "v \<notin> ran (parent s)"
  shows "black (fold s) v"
proof -
  have v_eq_head_queue: "v = head (queue s)"
    using invar_queue not_mem_ran mem_ran_fold
    by (intro black_if_mem_ran_fold_case_2_aux)
  hence "v \<in> set (list (queue s))"
    using invar_queue cond
    by (simp add: cond_def is_empty list_head)
  hence "\<not> white s v"
    by (intro gray_if_mem_queue gray_imp_not_white)
  with cond
  have "\<not> white (fold s) v"
    by (intro not_white_imp_not_white_fold)
  moreover have "v \<notin> set (list (queue (fold s)))"
    using cond v_eq_head_queue
    by (intro head_imp(2))
  ultimately show ?thesis
    by blast
qed

lemma (in bfs_invar) black_if_mem_ran_fold:
  assumes "cond s"
  assumes "v \<in> ran (parent (fold s))"
  shows "black (fold s) v"
proof (cases "v \<in> ran (parent s)")
  case True
  with assms(1)
  show ?thesis
    by (intro black_if_mem_ran_fold_case_1)
next
  case False
  with assms
  show ?thesis
    by (intro black_if_mem_ran_fold_case_2)
qed

subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_dpath_length}\<close>
subsubsection \<open>@{thm bfs_invar.not_white_imp_shortest_dpath}\<close>
subsubsection \<open>@{thm bfs_invar.black_imp_out_neighborhood_not_white}\<close>

subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_dpath_length}\<close>

lemma (in bfs_invar) not_white_imp_follow_fold_eq_follow:
  assumes "cond s"
  assumes "\<not> white s v"
  shows "parent.follow (parent (fold s)) v = follow v"
  using assms
proof (induct v rule: follow.pinduct[OF follow_dom])
  case (1 v)
  show ?case
  proof (cases "v = src")
    case True
    hence
      "parent s v = None"
      "parent (fold s) v = None"
      using parent_src "1.prems"(1) parent_src_fold
      by simp+
    hence
      "follow v = [v]"
      "parent.follow (parent (fold s)) v = [v]"
      using "1.prems"(1) parent_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      by fastforce
  next
    case False
    then obtain u where u:
      "parent s v = Some u"
      "\<not> white s u"
      using False "1.prems"(2) black_if_mem_ran
      by (auto simp add: discovered_def ran_def)
    moreover hence "parent (fold s) v = Some u"
      using "1.prems"
      by (simp add: parent_fold_cong_2 map_add_Some_iff)
    ultimately have
      "follow v = v # follow u"
      "parent.follow (parent (fold s)) v = v # parent.follow (parent (fold s)) u"
      using "1.prems"(1) parent_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      using u "1.prems"(1)
      by (simp add: "1.hyps"(2))
  qed
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_aux:
  assumes "cond s"
  shows
    "\<forall>v\<in>set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))).
      parent.follow (parent (fold s)) v = v # parent.follow (parent (fold s)) (head (queue s))"
proof
  let ?u = "head (queue s)"
  fix v
  assume "v \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G ?u)))"
  hence "parent (fold s) v = Some ?u"
    by (simp add: parent_fold_cong_2)
  thus "parent.follow (parent (fold s)) v = v # parent.follow (parent (fold s)) ?u"
    using assms parent_fold
    by (simp add: parent.follow_psimps)
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_aux_2:
  assumes "cond s"
  shows
    "\<And>u v.
      u \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))) \<Longrightarrow>
      v \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))) \<Longrightarrow>
      dpath_length (parent.follow (parent (fold s)) u) = dpath_length (parent.follow (parent (fold s)) v)"
proof -
  let ?u = "head (queue s)"
  fix u v
  assume
    "u \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G ?u)))"
    "v \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G ?u)))"
  hence
    "parent.follow (parent (fold s)) u = u # parent.follow (parent (fold s)) ?u" and
    "parent.follow (parent (fold s)) v = v # parent.follow (parent (fold s)) ?u"
    using assms queue_sorted_wrt_dpath_length_fold_aux
    by blast+
  hence
    "dpath_length (parent.follow (parent (fold s)) u) = dpath_length (parent.follow (parent (fold s)) ?u) + 1"
    "dpath_length (parent.follow (parent (fold s)) v) = dpath_length (parent.follow (parent (fold s)) ?u) + 1"
    using assms parent_fold parent.follow_non_empty
    by (fastforce simp add: dpath_length_Cons)+
  thus "dpath_length (parent.follow (parent (fold s)) u) = dpath_length (parent.follow (parent (fold s)) v)"
    by presburger
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_aux_3:
  assumes "cond s"
  shows
    "\<forall>v\<in>set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))).
      dpath_length (parent.follow (parent (fold s)) (last (list (queue s)))) \<le>
      dpath_length (parent.follow (parent (fold s)) v)"
proof
  let ?u = "head (queue s)"
  fix v
  assume "v \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G ?u)))"
  hence follow_fold_eq: "parent.follow (parent (fold s)) v = v # parent.follow (parent (fold s)) ?u"
    using assms queue_sorted_wrt_dpath_length_fold_aux
    by blast
  have
    "dpath_length (parent.follow (parent (fold s)) (last (list (queue s)))) =
      dpath_length (follow (last (list (queue s))))"
    using assms list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  also have "... \<le> dpath_length (follow ?u) + 1"
    using assms queue_sorted_wrt_dpath_length
    by (simp add: cond_def)
  also have "... = dpath_length (parent.follow (parent (fold s)) ?u) + 1"
    using assms head_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  also have "... = dpath_length (parent.follow (parent (fold s)) v)"
    using assms parent_fold parent.follow_non_empty
    by (fastforce simp add: follow_fold_eq dpath_length_Cons)
  finally show
    "dpath_length (parent.follow (parent (fold s)) (last (list (queue s)))) \<le>
      dpath_length (parent.follow (parent (fold s)) v)"
    .
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_aux_4:
  assumes "cond s"
  shows
    "\<forall>u\<in>set (list (tail (queue s))).
      \<forall>v\<in>set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))).
      dpath_length (parent.follow (parent (fold s)) u) \<le> dpath_length (parent.follow (parent (fold s)) v)"
proof (standard, standard)
  let ?u = "head (queue s)"
  let ?q = "tail (queue s)"
  fix u v
  assume "u \<in> set (list ?q)"
  hence u_mem_list_queue: "u \<in> set (list (queue s))"
    using invar_queue assms list_queue_non_empty
    by (auto simp add: list_tail intro: list.set_sel(2))
  assume v_mem_filter: "v \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G ?u)))"
  have
    "dpath_length (parent.follow (parent (fold s)) u) =
      dpath_length (follow u)"
    using assms u_mem_list_queue gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  also have "... \<le> dpath_length (follow (last (list (queue s))))"
    using u_mem_list_queue
    by (intro mem_queue_imp_dpath_length_last_queue)
  also have "... = dpath_length (parent.follow (parent (fold s)) (last (list (queue s))))"
    using assms list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  also have "... \<le> dpath_length (parent.follow (parent (fold s)) v)"
    using assms v_mem_filter queue_sorted_wrt_dpath_length_fold_aux_3
    by blast
  finally show
    "dpath_length (parent.follow (parent (fold s)) u) \<le>
      dpath_length (parent.follow (parent (fold s)) v)"
    .
qed

lemma (in bfs_invar) aux_0:
  assumes cond: "cond s"
  assumes "\<not> is_empty (queue (fold s))"
  shows
    "dpath_length (parent.follow (parent (fold s)) (last (list (queue (fold s))))) \<le>
      dpath_length (parent.follow (parent (fold s)) (head (queue s))) + 1"
proof (cases "filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))) = []")
  case True
  hence list_tail_non_empty: "list (tail (queue s)) \<noteq> []"
    using invar_queue assms invar_queue_fold_2
    by (simp add: list_queue_fold_cong_2 is_empty)
  hence "last (list (queue (fold s))) = last (list (tail (queue s)))"
    unfolding list_queue_fold_cong_2[OF invar_queue assms(1)] last_appendL[OF True]
    by blast
  hence "last (list (queue (fold s))) = last (list (queue s))"
    using list_tail_non_empty
    by (simp add: list_queue[OF invar_queue list_queue_non_empty[OF assms(1)]])
  hence
    "dpath_length (parent.follow (parent (fold s)) (last (list (queue (fold s))))) =
      dpath_length (follow (last (list (queue s))))"
    using cond list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  also have "... \<le> dpath_length (follow (head (queue s))) + 1"
    using invar_queue cond list_queue_non_empty queue_sorted_wrt_dpath_length
    by (simp add: is_empty)
  also have "... = dpath_length (parent.follow (parent (fold s)) (head (queue s))) + 1"
    using cond head_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  finally show ?thesis
    .
next
  case False
  hence
    "last (list (queue (fold s))) \<in>
      set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    unfolding list_queue_fold_cong_2[OF invar_queue cond] last_appendR[OF False]
    by (intro last_in_set)
  hence
    "parent.follow (parent (fold s)) (last (list (queue (fold s)))) =
      (last (list (queue (fold s)))) # parent.follow (parent (fold s)) (head (queue s))"
    using cond queue_sorted_wrt_dpath_length_fold_aux
    by blast
  thus ?thesis
    using cond parent_fold parent.follow_non_empty
    by (fastforce simp add: dpath_length_Cons)
qed

lemma (in bfs_invar) aux_1:
  assumes "cond s"
  assumes "\<not> is_empty (queue (fold s))"
  assumes "list (tail (queue s)) = []"
  shows
    "head (queue (fold s)) \<in>
      set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
proof -
  have "head (queue (fold s)) = hd (list (queue (fold s)))"
    using assms(1, 2) invar_queue invar_queue_fold_2
    by (simp add: is_empty list_head)
  hence
    "head (queue (fold s)) =
    hd (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    using invar_queue assms(1, 3)
    by (simp add: list_queue_fold_cong_2)
  moreover have "filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<noteq> []"
    using invar_queue assms invar_queue_fold_2
    by (simp add: is_empty list_queue_fold_cong_2)
  ultimately show ?thesis
    using list.set_sel(1)
    by metis
qed

lemma (in bfs_invar) aux_2:
  assumes cond: "cond s"
  assumes "\<not> is_empty (queue (fold s))"
  shows
    "dpath_length (parent.follow (parent (fold s)) (head (queue s))) \<le>
      dpath_length (parent.follow (parent (fold s)) (head (queue (fold s))))"
proof (cases "list (tail (queue s)) = []")
  case True
  have
    "dpath_length (parent.follow (parent (fold s)) (head (queue s))) =
      dpath_length (follow (head (queue s)))"
    using cond head_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  also have "... \<le> dpath_length (follow (last (list (queue s))))"
    using cond
    by (intro head_imp(1) mem_queue_imp_dpath_length_last_queue) simp+
  also have "... = dpath_length (parent.follow (state.parent (local.fold s)) (last (list (queue s))))"
    using cond list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  also have "... \<le> dpath_length (parent.follow (parent (fold s)) (head (queue (fold s))))"
    using assms True aux_1 queue_sorted_wrt_dpath_length_fold_aux_3
    by blast
  finally show ?thesis
    .
next
  case False
  have "head (queue (fold s)) = hd (list (queue (fold s)))"
    using assms invar_queue invar_queue_fold_2
    by (simp add: is_empty list_head)
  hence "head (queue (fold s)) = hd (list (tail (queue s)))"
    using invar_queue cond False
    by (simp add: list_queue_fold_cong_2)
  hence head_queue_fold_mem_list_queue: "head (queue (fold s)) \<in> set (list (queue s))"
    using False invar_queue cond list_queue_non_empty
    by (auto simp add: list_tail intro: list.set_sel(2))

  have
    "dpath_length (parent.follow (parent (fold s)) (head (queue s))) =
      dpath_length (follow (head (queue s)))"
    using cond head_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  also have "... \<le> dpath_length (follow (head (queue (fold s))))"
    using head_queue_fold_mem_list_queue
    by (intro mem_queue_imp_dpath_length_head_queue)
  also have "... = dpath_length (parent.follow (parent (fold s)) (head (queue (fold s))))"
    using cond head_queue_fold_mem_list_queue gray_if_mem_queue
    by (simp add: not_white_imp_follow_fold_eq_follow)
  finally show ?thesis
    .
qed

(* TODO: move somewhere else *)
lemma sorted_wrt_if:
  assumes "\<And>x y. x \<in> set l \<Longrightarrow> y \<in> set l \<Longrightarrow> P x y"
  shows "sorted_wrt P l"
  using assms
  by (simp add: sorted_wrt_iff_nth_less)

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_aux_5:
  assumes "cond s"
  shows
    "sorted_wrt
      (\<lambda>u v. dpath_length (parent.follow (parent (fold s)) u) \<le>
             dpath_length (parent.follow (parent (fold s)) v))
      (list (tail (queue s)))"
proof -
  have list_queue_non_empty: "list (queue s) \<noteq> []"
    using assms
    by (intro list_queue_non_empty)
  hence "sorted_wrt (\<lambda>u v. dpath_length (follow u) \<le> dpath_length (follow v)) (list (queue s))"
    using invar_queue queue_sorted_wrt_dpath_length
    by (simp add: is_empty)
  hence
    "sorted_wrt
      (\<lambda>u v. dpath_length (parent.follow (parent (fold s)) u) \<le>
             dpath_length (parent.follow (parent (fold s)) v))
      (list (queue s))"
    using assms gray_if_mem_queue sorted_wrt_mono_rel[of "(list (queue s))"]
    by (simp add: not_white_imp_follow_fold_eq_follow)
  thus ?thesis
    by (simp add: list_queue[OF invar_queue list_queue_non_empty])
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold:
  assumes "cond s"
  assumes "\<not> is_empty (queue (fold s))"
  shows
    "sorted_wrt
      (\<lambda>u v. dpath_length (parent.follow (parent (fold s)) u) \<le>
             dpath_length (parent.follow (parent (fold s)) v))
      (list (queue (fold s))) \<and>
     dpath_length (parent.follow (parent (fold s)) (last (list (queue (fold s))))) \<le>
     dpath_length (parent.follow (parent (fold s)) (head (queue (fold s)))) + 1"
proof (rule conjI)
  have
    "\<And>u v.
      u \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))) \<Longrightarrow>
      v \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))) \<Longrightarrow>
      dpath_length (parent.follow (parent (fold s)) u) \<le> dpath_length (parent.follow (parent (fold s)) v)"
    using assms(1)
    by (blast intro: queue_sorted_wrt_dpath_length_fold_aux_2 eq_imp_le)
  hence
    "sorted_wrt
      (\<lambda>u v. dpath_length (parent.follow (parent (fold s)) u) \<le>
             dpath_length (parent.follow (parent (fold s)) v))
      (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    by (blast intro: sorted_wrt_if)
  thus
    "sorted_wrt
      (\<lambda>u v. dpath_length (parent.follow (parent (fold s)) u) \<le>
             dpath_length (parent.follow (parent (fold s)) v))
      (list (queue (fold s)))"
    using invar_queue assms(1) queue_sorted_wrt_dpath_length_fold_aux_5 queue_sorted_wrt_dpath_length_fold_aux_4
    by (simp add: list_queue_fold_cong_2 sorted_wrt_append)

  have
    "dpath_length (parent.follow (parent (fold s)) (last (list (queue (fold s))))) \<le>
      dpath_length (parent.follow (parent (fold s)) (head (queue s))) + 1"
    using assms
    by (intro aux_0)
  also have "... \<le> dpath_length (parent.follow (parent (fold s)) (head (queue (fold s)))) + 1"
    using assms
    by (auto intro: aux_2)
  finally show
    "dpath_length (parent.follow (parent (fold s)) (last (list (queue (fold s))))) \<le>
      dpath_length (parent.follow (parent (fold s)) (head (queue (fold s)))) + 1"
    .
qed

subsubsection \<open>@{thm bfs_invar.not_white_imp_shortest_dpath}\<close>

lemma (in bfs_invar) parent_fold_eq_head_queue_if:
  assumes "white s v"
  assumes "\<not> white (fold s) v"
  shows "parent (fold s) v = Some (head (queue s))"
proof -
  have
    "parent (fold s) v =
      (\<lambda>v. if v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> white s v then Some (head (queue s)) else None) v"
    using assms(1)
    by (simp add: discovered_def domIff parent_fold_cong_2)
  thus ?thesis
    using assms
    by (auto simp add: discovered_def)
qed

lemma (in bfs_invar) not_white_imp_shortest_dpath_2:
  shows "\<And>v. \<not> white s v \<Longrightarrow> dpath_bet G (rev (follow v)) src v \<and> dpath_length (rev (follow v)) = dist v"
  sorry

thm bfs_invar.not_white_imp_shortest_dpath
lemma (in bfs_invar) not_white_imp_shortest_dpath_fold:
  assumes cond: "cond s"
  assumes not_white_fold: "\<not> white (fold s) v"
  assumes not_white_imp_shortest_dpath:
    "\<And>v. \<not> white s v \<Longrightarrow> dpath_bet G (rev (follow v)) src v \<and> dpath_length (rev (follow v)) = dist v"
  shows
    "dpath_bet G (rev (parent.follow (parent (fold s)) v)) src v \<and>
      dpath_length (rev (parent.follow (parent (fold s)) v)) = dist v"
proof (cases "white s v")
  case True
  let ?u = "head (queue s)"
  have *: "parent (fold s) v = Some ?u"
    using True not_white_fold
    by (intro parent_fold_eq_head_queue_if)

  have **: "\<not> white s ?u"
    using cond
    by (intro head_imp(1) gray_if_mem_queue gray_imp_not_white) simp+
  hence ****: "dpath_bet G (rev (follow ?u)) src ?u \<and> dpath_length (rev (follow ?u)) = dist ?u"
    by (intro not_white_imp_shortest_dpath)

  have "parent.follow (parent (fold s)) v = v # parent.follow (parent (fold s)) ?u"
    using cond parent_fold
    by (simp add: parent.follow_psimps *)
  hence "parent.follow (parent (fold s)) v = v # follow ?u"
    using cond **
    by (simp add: not_white_imp_follow_fold_eq_follow)
  hence ***: "rev (parent.follow (parent (fold s)) v) = rev (follow ?u) @ [v]"
    by simp

  have *****: "dpath_bet G [?u, v] ?u v"
    sorry
  hence 6: "dpath_bet G (rev (parent.follow (parent (fold s)) v)) src v"
    using **** dpath_bet_transitive
    by (fastforce simp add: ***)
  have "dpath_length (rev (parent.follow (parent (fold s)) v)) = dpath_length (rev (follow ?u)) + 1"
    using follow_non_empty
    by (simp add: *** dpath_length_snoc)
  also have "... = dist ?u + 1"
    unfolding plus_enat_simps(1)[symmetric]
    by (simp add: ****)
  finally have 10: "dpath_length (rev (parent.follow (parent (fold s)) v)) = dist ?u + 1"
    .
  have 11: "dist ?u + 1 \<ge> dist v"
    using ***** rename_me
    by (simp add: edge_iff_dpath_bet)
  
  have "reachable G src v"
    using 6
    by (auto simp add: reachable_iff_dpath_bet)
  then obtain p where p:
    "dpath_bet G p src v"
    "dpath_length p = dist v"
    by (elim dist_dpath_betE)
  have "dist ?u + 1 = dist v"
  proof (rule ccontr)
    assume "dist ?u + 1 \<noteq> dist v"
    hence 7: "dist v < dist ?u + 1"
      using 11
      by auto
    thus "False"
      using True p
    proof (induct p arbitrary: v rule: dpath_rev_induct)
      case 1
      thus ?case
        by auto
    next
      case (2 u)
      hence "[u] = [src] \<and> src = v"
        by (intro hd_of_dpath_bet' last_of_dpath_bet list_length_1) simp
      hence "white s src"
        using "2.prems"(2)
        by simp
      thus ?case
        by (simp add: discovered_def)
    next
      case (3 u u' l)
      have "dist u + 1 = dist v"
        using "3.prems"(3, 4)
        by (auto intro: shortest_dpathE_2)
      also have "... < dist ?u + 1"
        using "3.prems"(1)
        .
      finally have "dist u + 1 < dist ?u + 1"
        .
      hence 9: "dist u < dist ?u"
        unfolding plus_1_eSuc(2) eSuc_mono
        .
      show ?case
      proof (induct s u rule: vertex_color_induct)
        case white
        have "dist ?u \<le> dist (last (list (queue s)))"
          using cond list_queue_non_empty
          by (intro mem_queue_imp_dist_head_queue) simp
        also have "... \<le> dist u"
          using white cond white_imp_dist_ge
          by (simp add: cond_def)
        finally show ?case
          using 9
          by simp
      next
        case gray
        hence "dist ?u \<le> dist u"
          by (intro mem_queue_imp_dist_head_queue) simp
        thus ?case
          using 9
          by simp
      next
        case black
        have "dpath_bet G [u, v] u v"
          using "3.prems"(3) split_dpath last_of_dpath_bet
          by fastforce
        hence "v \<in> out_neighborhood G u"
          by (simp add: edge_iff_dpath_bet in_out_neighborhood_iff_edge)
        hence "\<not> white s v"
          using black black_imp_out_neighborhood_not_white
          by blast
        thus ?case
          using "3.prems"(2)
          by simp
      qed
    qed
  qed
  thus ?thesis
    using 6
    by (simp add: 10)
next
  case False
  thus ?thesis
    using assms not_white_imp_shortest_dpath
    by (simp add: not_white_imp_follow_fold_eq_follow)
qed

subsubsection \<open>@{thm bfs_invar.black_imp_out_neighborhood_not_white}\<close>

(* TODO: remove? *)
lemma (in bfs)
  shows "\<forall>v\<in>out_neighborhood G (head (queue s)). \<not> white (fold s) v"
  using out_neighborhood_finite
  by (auto simp add: discovered_def parent_fold_cong_2)

lemma (in bfs_invar) black_imp_out_neighborhood_not_white_fold:
  assumes cond: "cond s"
  assumes black_fold: "black (fold s) v"
  shows "\<forall>w\<in>out_neighborhood G v. \<not> white (fold s) w"
proof (induct s v rule: vertex_color_induct)
  case white
  hence "v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s))))"
    using black_fold
    by (fastforce simp add: discovered_def parent_fold_cong_2)
  hence "v \<in> set (list (queue (fold s)))"
    using white invar_queue cond
    by (simp add: discovered_def list_queue_fold_cong_2)
  thus ?case
    using black_fold
    by blast
next
  case gray
  hence "v = head (queue s)"
    using assms invar_queue
    by (intro head_if) simp+
  thus ?case
    using out_neighborhood_finite
    by (auto simp add: discovered_def parent_fold_cong_2)
next
  case black
  hence "\<forall>w\<in>out_neighborhood G v. \<not> white s w"
    by (intro black_imp_out_neighborhood_not_white)
  thus ?case
    using cond not_white_imp_not_white_fold
    by blast
qed

lemma (in bfs_invar) bfs_invar_fold:
  shows "bfs_invar empty is_empty head tail invar list src G snoc (fold s)"
  sorry

subsection \<open>@{term bfs.loop}\<close>

subsubsection \<open>@{thm bfs_invar.invar_queue}\<close>
subsubsection \<open>@{thm bfs_invar.dom_parent_subset_vertices}\<close>
subsubsection \<open>@{thm bfs_invar.black_if_mem_ran}\<close>
subsubsection \<open>@{thm bfs_invar.gray_if_mem_queue}\<close>
subsubsection \<open>@{thm bfs_invar.queue_distinct}\<close>
subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_dpath_length}\<close>
subsubsection \<open>@{thm bfs_invar.not_white_imp_shortest_dpath}\<close>
subsubsection \<open>@{thm bfs_invar.black_imp_out_neighborhood_not_white}\<close>
subsubsection \<open>@{thm bfs_invar.parent_src}\<close>

lemma (in bfs_invar) bfs_invar_fold:
  shows "bfs_invar empty is_empty head tail invar list src G snoc (fold s)"
  sorry

lemma (in bfs_invar) bfs_invar_loop:
  shows "bfs_invar empty is_empty head tail invar list src G snoc (loop s)"
  sorry

(**)

lemma (in bfs) bfs_invar_init_2:
  shows "bfs_invar empty is_empty head tail invar list src G snoc init"
  sorry

lemma (in bfs) bfs_invar_bfs:
  shows "bfs_invar empty is_empty head tail invar list src G snoc bfs"
  using bfs_invar_init bfs_invar.bfs_invar_loop
  by fast

section \<open>Correctness\<close>

(**)

lemma (in bfs) loop_psimps:
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  shows "loop s = (if cond s then loop (fold s) else s)"
  using loop.psimps[OF loop_dom[OF assms]]
  by meson

lemma (in bfs) bfs_induct:
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes
    "\<And>s. loop_dom s \<Longrightarrow>
          (cond s \<Longrightarrow>
            P (fold s)) \<Longrightarrow>
          P s"
  shows "P s"
  using assms
  by (blast intro: loop_dom loop.pinduct)

lemma (in bfs) bfs_induct_2:
  assumes "bfs_invar empty is_empty head tail invar list src G snoc s"
  assumes
    "\<And>s. loop_dom s \<Longrightarrow>
          (cond s \<Longrightarrow>
            P (fold s)) \<Longrightarrow>
          P s"
  shows "P s"
  using assms
proof -
  have "invar (queue s)"
    using assms(1)
    by (intro bfs_invar.invar_queue)
  moreover have "dom (parent s) \<subseteq> dVs G"
    using assms(1)
    by (intro bfs_invar.dom_parent_subset_vertices)
  ultimately show ?thesis
    using assms(2)
    by (rule bfs_induct)
qed

lemma (in bfs) sound:
  assumes "bfs_invar empty is_empty head tail invar list src G snoc s"
  assumes "discovered (loop s) v"
  shows
    "dpath_bet G (rev (parent.follow (parent (loop s)) v)) src v \<and>
      dpath_length (rev (parent.follow (parent (loop s)) v)) = dist v"
  using assms bfs_invar.bfs_invar_loop bfs_invar.not_white_imp_shortest_dpath_2
  by fast

lemma (in bfs_invar) sound:
  assumes "discovered (loop s) v"
  shows
    "dpath_bet G (rev (parent.follow (parent (loop s)) v)) src v \<and>
      dpath_length (rev (parent.follow (parent (loop s)) v)) = dist v"
  using assms bfs_invar_loop bfs_invar.not_white_imp_shortest_dpath_2
  by fast

lemma (in bfs_invar) white_loop_imp_white:
  assumes "white (loop s) v"
  shows "white s v"
  using assms
  sledgehammer
  by (metis discovered_def hd_of_dpath_bet not_white_imp_shortest_dpath parent.follow_ConsD parent_axioms)

lemma (in bfs) bfs_complete:
  assumes "bfs_invar empty is_empty head tail invar list src G snoc s"
  assumes "\<not> discovered (loop s) v"
  shows "\<not> reachable G src v"
  using assms
proof (induct rule: bfs_induct_2[OF assms(1)])
  thm bfs_invar.not_white_imp_not_white_fold
  case (1 s)
  show ?case
  proof (cases "cond s")
    case True
    hence *: "loop s = loop (fold s)"
      using "1.hyps"(1)
      by (metis loop.psimps surjective update_convs(1))
    have "bfs_invar empty is_empty head tail invar list src G snoc (loop (fold s))"
      using "1.prems"(1)
      sledgehammer
      using "*" bfs_invar.bfs_invar_loop by force
    moreover have "white (loop (fold s)) v"
      using "1.prems"
      by (simp add: *)
    ultimately show ?thesis
      using True
      sledgehammer
      by (simp add: True \<open>bfs_invar empty is_empty head tail invar list src G snoc (loop (local.fold s))\<close> \<open>white (loop (local.fold s)) v\<close> "1.hyps"(2) "1.prems"(1) bfs_invar.bfs_invar_fold)
  next
    case False
    thus ?thesis
      by (metis "1.hyps"(1) "1.prems"(1) "1.prems"(2) bfs.loop.psimps bfs_axioms bfs_invar.invar_queue bfs_invar.src_not_white bfs_invar.tbd cond_def empty_iff is_empty list.set(1) reachable_iff_dpath_bet)
  qed
qed

lemma (in bfs_invar) sound:
  assumes "v \<noteq> src"
  assumes "bfs_invar empty is_empty head tail invar list src G snoc s"
  assumes "(parent.follow (parent (loop s)) v) \<noteq> [v]"
  shows "dpath_bet G (parent.follow (parent (loop s)) v) src v"
    "dpath_length (parent.follow (parent (loop s)) v) = dist v"

lemma (in bfs_invar) sound:
  assumes "v \<noteq> src"
  assumes "bfs_invar empty is_empty head tail invar list src G snoc s"
  assumes "dpath_bet G p src v"
  shows "dpath_length p \<ge> dist v"
  thm white_imp_dist_ge

lemma (in bfs) bfs_sound:
  assumes "discovered bsf v"
  shows "dpath_bet G (parent.follow (parent bfs) v) src v \<and> dpath_length (parent.follow (parent bfs) v) = dist v"
proof -
  have "\<not> white bfs v"
    using assms
    by (simp add: domIff discovered_def)
  with bfs_invar_bfs
  show ?thesis
    by (intro bfs_invar.not_white_imp_shortest_dpath)
qed

lemma (in bfs) bfs_complete:
  assumes "\<not> discovered bfs v"
  shows "\<not> reachable G src v"
  sorry

lemma (in bfs) bfs_correct:
  shows
    "if discovered bfs v
     then dpath_bet G (parent.follow (parent bfs) v) src v \<and>
          dpath_length (parent.follow (parent bfs) v) = dist v
     else \<not> reachable G src v"
  using bfs_complete bfs_sound
  by (simp split: option.split)

(**)

subsection \<open>init\<close>


subsection \<open>bfs\<close>

lemma (in bfs) discovered_imp_shortest_dpath_fold:
  assumes "cond s"
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes
    "discovered s v \<Longrightarrow>
      dpath_bet G (parent.follow (parent s) v) src v \<and>
      dpath_length (parent.follow (parent s) v) = dist G src v"
  shows
    "discovered v (fold s) \<Longrightarrow>
      dpath_bet G (parent.follow (parent (fold s)) v) src v \<and>
      dpath_length (parent.follow (parent (fold s)) v) = dist G src v"
  sorry

lemma (in bfs) discovered_imp_shortest_dpath_loop:
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes
    "discovered s v \<Longrightarrow>
      dpath_bet G (parent.follow (parent s) v) src v \<and>
      dpath_length (parent.follow (parent s) v) = dist G src v"
  shows
    "discovered v (loop s) \<Longrightarrow>
      dpath_bet G (parent.follow (parent (loop s)) v) src v \<and>
      dpath_length (parent.follow (parent (loop s)) v) = dist G src v"
  using assms
  proof (induct rule: bfs_induct[OF assms(1, 2)])
  case (1 s)
  thus ?case
  proof (cases "cond s")
    case True
    hence loop:
      "loop s =
        loop (Finite_Set.fold (traverse_edge (head (queue s))) (s\<lparr>queue := tail (queue s)\<rparr>) (out_neighborhood G (head (queue s))))"
      unfolding loop.psimps[OF "1.hyps"(1)]
      by metis
    thus ?thesis
      using True "1.prems"
      unfolding loop
      by (intro tbd discovered_imp_shortest_dpath_fold "1.hyps"(2))
  next
    case False
    thus ?thesis
      using "1.prems"(1, 4) "1.hyps"(1)
      by (simp add: loop.psimps)
  qed
qed

lemma (in bfs_invar) discovered_imp_shortest_dpath_loop:
  assumes "discovered v (loop s)"
  shows
    "dpath_bet G (parent.follow (parent (loop s)) v) src v \<and>
      dpath_length (parent.follow (parent (loop s)) v) = dist G src v"
  using invar_queue dom_parent_subset_vertices discovered_imp_shortest_dpath assms
  by (intro discovered_imp_shortest_dpath_loop)

lemma (in bfs) discovered_imp_shortest_dpath_bfs:
  assumes "discovered v bfs"
  shows
    "dpath_bet G (parent.follow (parent bfs) v) src v \<and>
      dpath_length (parent.follow (parent bfs) v) = dist G src v"
  using bfs_invar_init assms
  by (intro bfs_invar.discovered_imp_shortest_dpath_loop)

(**)

lemma (in bfs_invar)
  assumes "\<not> discovered s v"
  shows "(if is_empty (queue s) then \<infinity> else dist (last (list (queue s)))) \<le> dist v"
proof (cases "reachable G src v")
  case True
  then obtain p where
    "dpath_bet G p src v"
    "dpath_length p = dist v"
    sorry
  thus ?thesis
    using assms
  proof (induct p arbitrary: v rule: dpath_rev_induct)
    case 1
    then show ?case sorry
  next
    case (2 w)
    then show ?case sorry
  next
    case (3 w w' l)
    consider
    (white) "\<not> discovered w s" |
    (gray) "discovered w s \<and> w \<in># mset (list (queue s))" |
    (black) "discovered w s \<and> w \<notin># mset (list (queue s))"
    by blast
    thus ?case
    proof (cases)
      case white
      then show ?thesis sorry
    next
      case gray
      then show ?thesis sorry
next
  case black
  then show ?thesis sorry
qed
  qed
next
  case False
  then show ?thesis sorry
qed

lemma (in bfs_invar)
  assumes "\<not> discovered s v"
  assumes "distinct_dpath_bet G p src v"
  shows "\<exists>v\<in>set p. v \<in># mset (list (queue s))"
  using assms
proof (induct p arbitrary: src rule: dpath_induct)
  case 1
  thus ?case
    by (simp add: distinct_dpath_bet_def)
next
  case (2 u)
  hence "dpath_bet G [u] src v"
    by (simp add: distinct_dpath_bet_def)
  hence "[u] = [src] \<and> src = v"
    using "2.prems"(2)
    by (intro hd_of_dpath_bet' last_of_dpath_bet list_length_1) simp
  hence "\<not> discovered src s"
    using "2.prems"(1)
    by simp
  thus ?case
    using parent_src discovered_def
    sledgehammer
    by (simp add: discovered_def)
next
  case (3 u u' l)
  hence "v \<noteq> u'"
    thm dpath.induct
    thm last_of_dpath_bet
    apply (simp add: distinct_dpath_bet_def)
  then show ?case sorry
qed


lemma (in bfs)
  assumes "\<not> discovered v (fold s)"
  assumes "dpath_bet G p (head (queue s)) v"
  shows "\<exists>v\<in>set p. v \<in># mset (list (queue (fold s)))"
  using assms
proof (induct p arbitrary: v rule: dpath_induct)
  case 1
  thus ?case
    by simp
next
  case (2 v)
  thus ?case
    sledgehammer
next
  case (3 v v' l)
  then show ?case sorry
qed

lemma (in bfs) bsf_complete:
  assumes "reachable G src v"
  shows "discovered v bsf"
  sorry

locale bfs_invar = bfs where G = G and snoc = snoc
  for
    G :: "'a dgraph" and
    snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  fixes s :: "('q, 'a) state"
  assumes distance_src: "distance s src = Some 0"
  assumes parent_src: "parent s src = None"
  assumes invar_queue: "invar (queue s)"
  assumes queue_subset_vertices: "set (list (queue s)) \<subseteq> dVs G"
  assumes dom_parent_subset_vertices: "dom (parent s) \<subseteq> dVs G"
  assumes parent_edge: "\<lbrakk> v \<noteq> src; parent s v = Some u \<rbrakk> \<Longrightarrow> (u, v) \<in> G"
  assumes distance_parent:
    "\<lbrakk> v \<noteq> src; parent s v = Some u \<rbrakk> \<Longrightarrow> distance s v = Some m \<and> distance s u = Some n \<and> m = Suc n"
  assumes distance_min: "distance s v = Some n \<Longrightarrow> dist G src v = n"

  assumes in_queue_imp_discovered: "\<lbrakk> v \<noteq> src; v \<in> set (list (queue s)) \<rbrakk> \<Longrightarrow> discovered s v"

  assumes not_discovered_if_not_reachable: "\<not> reachable G src v \<Longrightarrow> \<not> discovered s v"

  assumes "parent (parent s)"
  assumes "discovered s v \<Longrightarrow> dpath_bet G (parent.follow (parent s) v) src v \<and> dpath_length (parent.follow (parent s) v) = dist G src v"

subsection \<open>init\<close>

lemma (in bfs) distance_src_init:
  shows "distance init src = Some 0"
  by (simp add: init_def)

lemma (in bfs) parent_src_init:
  shows "parent init src = None"
  by (simp add: init_def)

lemma (in bfs) invar_queue_init:
  shows "invar (queue init)"
  using invar_empty
  by (auto simp add: init_def intro: invar_snoc)

lemma (in bfs) queue_subset_vertices_init:
  shows "set (list (queue init)) \<subseteq> dVs G"
proof -
  have "set (list (queue init)) = {src}"
    using invar_empty
    by (simp add: init_def list_snoc list_empty)
  also have "... \<subseteq> dVs G"
    using src_in_vertices
    by (simp add: dVs_def)
  finally show ?thesis
    .
qed

lemma (in bfs) dom_parent_subset_vertices_init:
  shows "dom (parent init) \<subseteq> dVs G"
  using src_in_vertices
  by (simp add: init_def)

lemma (in bfs) parent_edge_init:
  assumes "v \<noteq> src"
  assumes "parent init v = Some u"
  shows "(u, v) \<in> G"
  using assms
  by (simp add: init_def)

lemma (in bfs) distance_parent_init:
  assumes "v \<noteq> src"
  assumes "parent init v = Some u"
  shows "distance init v = Some m \<and> distance init u = Some n \<and> m = Suc n"
  using assms
  by (simp add: init_def)

lemma (in bfs) distance_min_init:
  assumes "distance init v = Some n"
  shows "dist G src v = n"
  sorry

lemma (in bfs) in_queue_imp_discovered_init:
  assumes "v \<noteq> src"
  assumes "v \<in> set (list (queue init))"
  shows "discovered v init"
  using assms invar_empty
  by (simp add: init_def list_snoc list_empty)

lemma (in bfs) not_discovered_if_not_reachable_init:
  assumes "\<not> reachable G src v"
  shows "parent init v = None"
  using assms
  by (simp add: init_def)

lemma (in bfs) bfs_invar_init:
  shows "bfs_invar empty is_empty head tail invar list src G snoc init"
  using
    bfs_axioms
    distance_src_init parent_src_init invar_queue_init queue_subset_vertices_init
    dom_parent_subset_vertices_init parent_edge_init distance_parent_init distance_min_init
    in_queue_imp_discovered_init not_discovered_if_not_reachable_init
  by unfold_locales

subsection \<open>\<close>

subsubsection \<open>\<close>

lemma (in bfs) invar_queue_loop:
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  shows "invar (queue (loop s))"
  using assms
proof (induct rule: bfs_induct[OF assms])
  case (1 s)
  thus ?case
  proof (cases "cond s")
    case True
    hence loop:
      "loop s =
        loop (Finite_Set.fold (traverse_edge (head (queue s))) (s\<lparr>queue := tail (queue s)\<rparr>) (out_neighborhood G (head (queue s))))"
      unfolding loop.psimps[OF "1.hyps"(1)]
      by metis
    show ?thesis
      unfolding loop
      using True "1.prems"
      by (intro tbd "1.hyps"(2))
  next
    case False
    thus ?thesis
      using "1.hyps"(1) "1.prems"(1)
      by (simp add: loop.psimps)
  qed
qed

lemma (in bfs_invar) invar_queue_loop:
  shows "invar (queue (loop s))"
  using invar_queue dom_parent_subset_vertices
  by (intro invar_queue_loop)

lemma (in bfs) invar_queue_bfs:
  shows "invar (queue bfs)"
  using bfs_invar_init
  by (intro bfs_invar.invar_queue_loop)

subsubsection \<open>\<close>

lemma (in bfs)
  assumes cond: "cond s"
  assumes invar_queue: "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes "\<lbrakk> v \<noteq> src; v \<in> set (list (queue s)) \<rbrakk> \<Longrightarrow> discovered s v"
  shows "\<lbrakk> v \<noteq> src; v \<in> set (list (queue (fold s))) \<rbrakk> \<Longrightarrow> discovered v (fold s)"
proof -
  have *: "invar (queue (s\<lparr>queue := tail (queue s)\<rparr>))"
    using cond invar_queue invar_tail
  by (simp add: is_empty cond_def)
  assume
    "v \<noteq> src"
    "v \<in># mset (list (queue (local.fold s)))"
  hence
    "v \<in># mset (list (queue (s\<lparr>queue := tail (queue s)\<rparr>))) +
      {#v \<in># mset_set (out_neighborhood G (head (queue s))). \<not> discovered v (s\<lparr>queue := tail (queue s)\<rparr>)#}"
    unfolding mset_list_queue_fold_cong[OF * out_neighborhood_finite]
    by blast
  hence "v \<in> set (list (queue (s\<lparr>queue := tail (queue s)\<rparr>))) \<or>
      v \<in> (out_neighborhood G (head (queue s))) \<and> \<not> discovered v (s\<lparr>queue := tail (queue s)\<rparr>)"
    by (simp add: out_neighborhood_finite)
    thm in_multiset_in_set
    using * out_neighborhood_finite
    sledgehammer
    using mset_list_queue_fold_cong
    try0
    thm mset_list_queue_fold_cong[OF * out_neighborhood_finite]
    apply (auto simp add: mset_list_queue_fold_cong)
    sledgehammer
    thm tbd
    by simp
  show ?thesis
    thm parent_fold_cong
    thm mset_list_queue_fold_cong

lemma (in bfs) in_queue_imp_discovered_loop:
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes "\<lbrakk> v \<noteq> src; v \<in> set (list (queue s)) \<rbrakk> \<Longrightarrow> discovered s v"
  shows "\<lbrakk> v \<noteq> src; v \<in> set (list (queue (loop s))) \<rbrakk> \<Longrightarrow> discovered v (loop s)"
  using assms
proof (induct rule: bfs_induct[OF assms(1, 2)])
  case (1 s)
  thus ?case
  proof (cases "cond s")
    case True
    hence loop:
      "loop s =
        loop (Finite_Set.fold (traverse_edge (head (queue s))) (s\<lparr>queue := tail (queue s)\<rparr>) (out_neighborhood G (head (queue s))))"
      unfolding loop.psimps[OF "1.hyps"(1)]
      by metis

    have *: "v \<in> set (list (queue
                 (loop
                   (Finite_Set.fold (traverse_edge (head (queue s)))
                     (s\<lparr>queue := tail (queue s)\<rparr>)
                     (out_neighborhood G (head (queue s)))))))"
      using "1.prems"(2)
      by (simp add: loop)

    have **: "invar
 (queue
   (Finite_Set.fold (traverse_edge (head (queue s))) (s\<lparr>queue := tail (queue s)\<rparr>)
     (out_neighborhood G (head (queue s)))))"
      using True "1.prems"(3, 4)
      apply (intro tbd(1)) by (simp add: loop)+

    have ***: "dom (state.parent
      (Finite_Set.fold (traverse_edge (head (queue s))) (s\<lparr>queue := tail (queue s)\<rparr>)
        (out_neighborhood G (head (queue s)))))
\<subseteq> dVs G"
      using True "1.prems"(3, 4)
      apply (intro tbd(2)) by (simp add: loop)+

    have "(v \<noteq> src \<Longrightarrow>
 v \<in> set (list (queue
                  (Finite_Set.fold (traverse_edge (head (queue s)))
                    (s\<lparr>queue := tail (queue s)\<rparr>)
                    (out_neighborhood G (head (queue s)))))) \<Longrightarrow>
 discovered v
  (Finite_Set.fold (traverse_edge (head (queue s))) (s\<lparr>queue := tail (queue s)\<rparr>)
    (out_neighborhood G (head (queue s)))))"
      thm "1.prems"
      find_theorems name: fold_cong
      sledgehammer

    show ?thesis
      using "1.hyps"(2)[OF True "1.prems"(1)]
      unfolding loop
      using "1.prems"(3)
      using True "1.prems"
      apply (auto simp add: loop intro: tbd "1.hyps"(2))
      thm "1.prems"
      thm "1.hyps"(2)
      thm "1.hyps"(2)[OF True "1.prems"(1) * ** ***]
      unfolding loop
      using True "1.prems"(1, 2, 3)
      apply (intro tbd "1.hyps"(2))
      apply (auto simp add: loop)
      using True "1.prems"(1, 2, 3)
      apply (intro "1.hyps"(2))
           apply auto
      apply (simp add: loop)
        apply (simp add: cond_def invar_queue_fold invar_tail is_empty out_neighborhood_finite)
      sledgehammer
      sledgehammer
      thm "1.prems"
      thm "1.hyps"
      sorry
  next
    case False
    thus ?thesis
      using "1.hyps"(1) "1.prems"(1, 2, 5)
      by (simp add: loop.psimps)
  qed
qed

lemma (in bfs_invar) in_queue_imp_discovered_loop:
  assumes "v \<noteq> src"
  assumes "v \<in> set (list (queue (loop s)))"
  shows "discovered v (loop s)"
  using invar_queue dom_parent_subset_vertices in_queue_imp_discovered assms
  by (intro in_queue_imp_discovered_loop)

lemma (in bfs) in_queue_imp_discovered_bfs:
  assumes "v \<noteq> src"
  assumes "v \<in> set (list (queue bfs))"
  shows "discovered v bfs"
  using bfs_invar_init assms
  by (intro bfs_invar.in_queue_imp_discovered_loop)

subsubsection \<open>\<close>
(**)

lemma (in bfs) discovered_imp_reachable_fold:
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes IH: "\<And>v. discovered s v \<Longrightarrow> reachable G src v"
  shows "discovered v (fold s) \<Longrightarrow> reachable G src v"
proof (rule ccontr)
  fix v
  assume discovered: "discovered v (fold s)"
  assume not_reachable: "\<not> reachable G src v"

  let ?u = "head (queue s)"
  let ?q = "tail (queue s)"

  have "v \<in> dom (parent (fold s))"
    using discovered
    by (simp add: discovered_def)
  hence "v \<in> dom (\<lambda>v. if v \<in> (out_neighborhood G ?u) \<and> \<not> discovered v (s\<lparr>queue := ?q\<rparr>) then Some ?u else None)"
    using out_neighborhood_finite not_reachable IH
    by (auto simp add: parent_fold_cong discovered_def)
  hence in_neighborhood: "v \<in> (out_neighborhood G ?u)"
    unfolding domIff
    by meson

  (*
    TODO: add invariant
      v \<in># mset (list (queue s)) \<Longrightarrow> discovered s v
      or
      v \<in> ran (parent (fold s)) \<Longrightarrow> v \<in> dom (parent s)
  *)
  have "discovered ?u s"
    sorry
  hence "reachable G src ?u"
    thm IH
    by (intro IH)
  hence "reachable G src v"
    using in_neighborhood
    by (auto simp add: out_neighborhood_def intro: reachable_trans)
  thus "False"
    using not_reachable
    by simp
qed

lemma (in bfs) discovered_imp_reachable_loop:
  assumes "invar (queue s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes "\<And>v. discovered s v \<Longrightarrow> reachable G src v"
  shows "discovered v (loop s) \<Longrightarrow> reachable G src v"
  using assms
proof (induct rule: bfs_induct[OF assms(1, 2)])
  case (1 s)
  thus ?case
  proof (cases "cond s")
    case True
    hence loop: "loop s = loop (fold s)"
      unfolding loop.psimps[OF "1.hyps"(1)]
      by metis

    show ?thesis
    proof (intro "1.hyps"(2))
      show "\<And>v. discovered v (local.fold s) \<Longrightarrow> src \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
        using "1.prems"(2-)
        by (rule discovered_imp_reachable_fold)
    qed using "1.prems" apply (auto intro: tbd)
      using True "1.prems"
      unfolding loop
      apply (rule "1.hyps"(2))
      sledgehammer
      thm "1.hyps"(2)
      
      thm discovered_imp_reachable_fold
      thm "1.hyps"(2)[OF _ _ _ _ discovered_imp_reachable_fold]
      by (smt "1.hyps"(2) bfs.tbd(1) bfs.tbd(2) bfs_axioms discovered_imp_reachable_fold surjective update_convs(1))
    thm discovered_imp_reachable_fold
    find_theorems "\<And>_. _"
find_theorems name: allI
      by (intr tbd discovered_imp_reachable_fold "1.hyps"(2))
  next
    case False
    thus ?thesis
      using "1.hyps"(1) "1.prems"(1, 4)
      by (simp add: loop.psimps)
  qed
qed

lemma (in bfs_invar) discovered_imp_reachable_loop:
  assumes "discovered v (loop s)"
  shows "reachable G src v"
  using invar_queue dom_parent_subset_vertices not_discovered_if_not_reachable assms
  by (intro discovered_imp_reachable_loop)

lemma (in bfs) not_discovered_if_not_reachable_bsf:
  assumes "discovered v bfs"
  shows "reachable G src v"
  using bfs_invar_init assms
  by (intro bfs_invar.discovered_imp_reachable_loop)

section \<open>Correctness\<close>

end