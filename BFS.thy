theory BFS
  imports
    "Graph_Theory/Graph_Theory"
    "HOL-Data_Structures.Map_Specs"
    Queue_Specs
    Tbd
begin

(* TODO: move somewhere else *)
definition (in Map) dom :: "'m \<Rightarrow> 'a set" where
  "dom m \<equiv> {a. lookup m a \<noteq> None}"
thm ran_def

(* TODO: move somewhere else *)
definition (in Map) ran :: "'m \<Rightarrow> 'b set" where
  "ran m \<equiv> {b. \<exists>a. lookup m a = Some b}"

record ('q, 'm) state =
  queue :: 'q
  parent :: "'m"

locale bfs =
  finite_dgraph G +
  Map where empty = Map_empty and update = update and invar = Map_invar +
  Queue where snoc = snoc
  for
    G :: "'a::linorder dgraph" and
    Map_empty and
    update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
    Map_invar and
    snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  fixes src :: 'a
  assumes src_in_vertices: "src \<in> dVs G"

abbreviation (in bfs) dist :: "'a \<Rightarrow> enat" where
  "dist \<equiv> Shortest_Dpath.dist G src"

section \<open>BFS Algorithm\<close>

definition (in bfs) init :: "('q, 'm) state" where
  "init \<equiv>
   \<lparr>queue = snoc empty src,
    parent = Map_empty\<rparr>"

definition (in bfs) cond :: "('q, 'm) state \<Rightarrow> bool" where
  "cond s \<longleftrightarrow> \<not> is_empty (queue s)"

definition (in bfs) discovered :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "discovered s v \<longleftrightarrow> v = src \<or> v \<in> dom (parent s)"

definition (in bfs) discover :: "'a \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "discover u v s \<equiv>
   \<lparr>queue = snoc (queue s) v,
    parent = update v u (parent s)\<rparr>"

definition (in bfs) traverse_edge :: "'a \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "traverse_edge u v s \<equiv>
   if \<not> discovered s v then discover u v s
   else s"

function (in bfs) (domintros) loop :: "('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "loop s =
   (if cond s
    then let
          u = head (queue s);
          q = tail (queue s)
         in loop (fold (traverse_edge u) (sorted_list_of_set (out_neighborhood G u)) (s\<lparr>queue := q\<rparr>))
    else s)"
  by pat_completeness simp

abbreviation (in bfs) bfs :: "('q, 'm) state" where
  "bfs \<equiv> loop init"

section \<open>\<close>

abbreviation (in bfs) fold :: "('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "fold s \<equiv>
   List.fold
    (traverse_edge (head (queue s)))
    (sorted_list_of_set (out_neighborhood G (head (queue s))))
    (s\<lparr>queue := tail (queue s)\<rparr>)"

abbreviation (in bfs) T :: "('q, 'm) state \<Rightarrow> 'a dgraph" where
  "T s \<equiv> {(u, v) |u v. lookup (parent s) v = Some u}"

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
  shows "parent (discover u v s) = update v u (parent s)"
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

subsubsection \<open>lookup \<circ> parent\<close>

lemma (in bfs) lookup_parent_traverse_edge_cong:
  assumes "Map_invar (parent s)"
  shows
    "lookup (parent (traverse_edge u v s)) =
     override_on
      (lookup (parent s))
      (\<lambda>_. Some u)
      (if \<not> discovered s v then {v} else {})"
  using assms
  by (simp add: traverse_edge_def map_update override_on_insert')

subsubsection \<open>Map_invar \<circ> parent\<close>

lemma (in bfs) Map_invar_parent_traverse_edge:
  assumes "Map_invar (parent s)"
  shows "Map_invar (parent (traverse_edge u v s))"
  using assms invar_update
  by (simp add: traverse_edge_def)

subsubsection \<open>@{term bfs.T}\<close>

lemma (in bfs) T_traverse_edge_cong:
  assumes "Map_invar (parent s)"
  shows "T (traverse_edge u v s) = T s \<union> (if \<not> discovered s v then {(u, v)} else {})"
  using assms
  by (auto simp add: lookup_parent_traverse_edge_cong override_on_def discovered_def dom_def)

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
  assumes "Map_invar (parent s)"
  assumes "distinct (v # vs)"
  shows "filter (Not \<circ> discovered (traverse_edge u v s)) vs = filter (Not \<circ> discovered s) vs"
proof (rule filter_cong)
  fix w
  assume "w \<in> set vs"
  hence "discovered (traverse_edge u v s) w = discovered s w"
    using assms
    by (auto simp add: discovered_def dom_def lookup_parent_traverse_edge_cong override_on_insert')
  thus "(Not \<circ> discovered (traverse_edge u v s)) w = (Not \<circ> discovered s) w"
    by simp
qed simp

lemma (in bfs) list_queue_fold_cong:
  assumes "invar (queue s)"
  assumes "Map_invar (parent s)"
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
    by (auto intro: invar_queue_traverse_edge Map_invar_parent_traverse_edge Cons.hyps)
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
    using Cons.prems(2, 3)
    by (simp add: list_queue_fold_cong_aux)
  also have "... = list (queue s) @ filter (Not \<circ> discovered s) (v # vs)"
    by simp
  finally show ?case
    .
qed

lemma (in bfs) list_queue_fold_cong_2:
  assumes "invar (queue s)"
  assumes "Map_invar (parent s)"
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
  thus ?thesis
    unfolding comp_apply
    by (simp add: discovered_def)
qed

subsubsection \<open>parent\<close>

lemma (in bfs) lookup_parent_fold_cong:
  assumes "Map_invar (parent s)"
  assumes "distinct l"
  shows
    "lookup (parent (List.fold (traverse_edge u) l s)) =
     override_on
      (lookup (parent s))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> discovered s) l))"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons v vs)
  have
    "lookup (parent (List.fold (traverse_edge u) (v # vs) s)) =
     lookup (parent (List.fold (traverse_edge u) vs (traverse_edge u v s)))"
    by simp
  also have
    "... =
     override_on
      (lookup (parent (traverse_edge u v s)))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> discovered (traverse_edge u v s)) vs))"
    using Cons.prems
    by (fastforce intro: Map_invar_parent_traverse_edge Cons.hyps)
  also have
    "... =
     override_on
      (override_on (lookup (parent s)) (\<lambda>_. Some u) (if \<not> discovered s v then {v} else {}))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> discovered (traverse_edge u v s)) vs))"
    using Cons.prems(1)
    by (simp add: lookup_parent_traverse_edge_cong)
  also have
    "... =
     override_on
      (override_on (lookup (parent s)) (\<lambda>_. Some u) (if \<not> discovered s v then {v} else {}))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> discovered s) vs))"
    using Cons.prems
    by (simp add: list_queue_fold_cong_aux)
  finally show ?case
    by (simp add: override_on_insert')
qed

lemma (in bfs) lookup_parent_fold_cong_2:
  assumes "Map_invar (parent s)"
  shows
    "lookup (parent (fold s)) =
     override_on
      (lookup (parent s))
      (\<lambda>_. Some (head (queue s)))
      (set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))))"
proof -
  have
    "lookup (parent (fold s)) =
     override_on
      (lookup (parent (s\<lparr>queue := tail (queue s)\<rparr>)))
      (\<lambda>_. Some (head (queue s)))
      (set (filter (Not \<circ> discovered (s\<lparr>queue := tail (queue s)\<rparr>)) (sorted_list_of_set (out_neighborhood G (head (queue s))))))"
    using assms
    by (intro lookup_parent_fold_cong) simp+
  thus ?thesis
    by (simp add: discovered_def)
qed

subsubsection \<open>Map_invar \<circ> parent\<close>

lemma (in bfs) Map_invar_parent_fold:
  assumes "Map_invar (parent s)"
  assumes "distinct l"
  shows "Map_invar (parent (List.fold (traverse_edge u) l s))"
  using assms
  by (induct l arbitrary: s) (simp_all add: Map_invar_parent_traverse_edge)

lemma (in bfs) Map_invar_parent_fold_2:
  assumes "Map_invar (parent s)"
  shows "Map_invar (parent (fold s))"
  using assms
  by (intro Map_invar_parent_fold) simp+

subsubsection \<open>dom \<circ> parent\<close>

lemma (in bfs) dom_parent_fold_subset_vertices:
  assumes "Map_invar (parent s)"
  assumes "distinct l"
  assumes "dom (parent s) \<subseteq> dVs G"
  assumes "set l \<subseteq> dVs G"
  shows "dom (parent (List.fold (traverse_edge u) l s)) \<subseteq> dVs G"
proof
  fix v
  assume assm: "v \<in> dom (parent (List.fold (traverse_edge u) l s))"
  show "v \<in> dVs G"
  proof (cases "v \<in> set (filter (Not \<circ> discovered s) l)")
    case True
    thus ?thesis
      using assms(4)
      by auto
  next
    case False
    have "lookup (parent (List.fold (traverse_edge u) l s)) v \<noteq> None"
      using assm
      by (simp add: dom_def)
    hence "lookup (parent s) v \<noteq> None"
      using assms(1, 2) False
      by (simp add: lookup_parent_fold_cong)
    thus ?thesis
      using assms(3)
      by (auto simp add: dom_def)
  qed
qed

lemma (in bfs) dom_parent_fold_subset_vertices_2:
  assumes "Map_invar (parent s)"
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

subsubsection \<open>ran \<circ> parent\<close>

lemma (in bfs) ran_parent_fold_cong:
  assumes "Map_invar (parent s)"
  shows
    "ran (parent (fold s)) =
     ran (parent s) \<union>
     (if set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))) = {}
      then {}
      else {head (queue s)})"
proof
  let ?S = "set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
  show "ran (parent (fold s)) \<subseteq> ran (parent s) \<union> (if ?S = {} then {} else {head (queue s)})"
    using assms
    by (auto simp add: ran_def lookup_parent_fold_cong_2 override_on_def)
  show "ran (parent s) \<union> (if ?S = {} then {} else {head (queue s)}) \<subseteq> ran (parent (fold s))"
  proof
    fix u
    assume assm: "u \<in> ran (parent s) \<union> (if ?S = {} then {} else {head (queue s)})"
    show "u \<in> ran (parent (fold s))"
    proof (cases "u \<in> ran (parent s)")
      case True
      then obtain v where
        "lookup (parent s) v = Some u"
        by (auto simp add: ran_def)
      moreover hence "discovered s v"
        by (simp add: discovered_def dom_def)
      ultimately show ?thesis
        using assms
        by (auto simp add: ran_def lookup_parent_fold_cong_2 override_on_def)
    next
      case False
      then obtain v where
        "v \<in> ?S"
        using assm
        by (auto split: if_splits(2))
      moreover have "u = head (queue s)"
        using assm False
        by (simp split: if_splits(2))
      ultimately show ?thesis
        using assms
        by (auto simp add: ran_def lookup_parent_fold_cong_2 override_on_def)
    qed
  qed
qed

subsubsection \<open>@{term bfs.T}\<close>

lemma (in bfs) T_fold_cong_aux:
  assumes "Map_invar (parent s)"
  assumes "distinct (v # vs)"
  shows "w \<in> set vs \<and> \<not> discovered (traverse_edge u v s) w \<longleftrightarrow> w \<in> set vs \<and> \<not> discovered s w"
  using assms
  by (auto simp add: discovered_def dom_def lookup_parent_traverse_edge_cong override_on_def)

lemma (in bfs) T_fold_cong:
  assumes "Map_invar (parent s)"
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
    by (intro Map_invar_parent_traverse_edge Cons.hyps) simp+
  also have
    "... =
     T s \<union>
     (if \<not> discovered s v then {(u, v)} else {}) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> discovered (traverse_edge u v s) w}"
    unfolding T_traverse_edge_cong[OF Cons.prems(1)]
    by blast
  also have
    "... =
     T s \<union>
     (if \<not> discovered s v then {(u, v)} else {}) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> discovered s w}"
    using Cons.prems
    by (simp add: T_fold_cong_aux)
  also have "... = T s \<union> {(u, w) |w. w \<in> set (v # vs) \<and> \<not> discovered s w}"
    by force
  finally show ?case
    .
qed

lemma (in bfs) T_fold_cong_2:
  assumes "Map_invar (parent s)"
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
    using assms
    by (intro T_fold_cong) simp+
  thus ?thesis
    by (simp add: discovered_def)
qed

section \<open>Termination\<close>

lemma (in bfs) loop_dom_aux:
  assumes "Map_invar (parent s)"
  assumes "dom (parent s) \<subseteq> dVs G"
  shows
    "card (dom (parent (fold s))) =
     card (dom (parent s)) +
     card (set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))))"
proof -
  let ?S = "set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
  have "dom (parent (fold s)) = dom (parent s) \<union> ?S"
    using assms(1)
    by (auto simp add: dom_def lookup_parent_fold_cong_2 override_on_def)
  moreover have "finite (dom (parent s))"
    using assms(2) vertices_finite
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
  assumes "Map_invar (parent s)"
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
    thm list_queue_fold_cong_2
    thm lookup_parent_fold_cong_2
    let ?u = "head (queue s)"
    let ?q = "tail (queue s)"
    let ?S = "set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"

    have "length (list (queue (fold s))) = length (list ?q) + card ?S"
      using less.prems(1, 2) True
      by (simp add: list_queue_fold_cong_2 distinct_card[symmetric])
    moreover have "card (dom (parent (fold s))) = card (dom (parent s)) + card ?S"
      using less.prems(2, 3)
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
      thm less.hyps
      using less.prems
      by (intro invar_queue_fold_2 Map_invar_parent_fold_2 dom_parent_fold_subset_vertices_2 less.hyps loop.domintros)
  next
    case False
    thus ?thesis
      by (blast intro: loop.domintros)
  qed
qed

section \<open>Invariants\<close>

subsection \<open>\<close>

abbreviation (in bfs) white :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "white s v \<equiv> \<not> discovered s v"

abbreviation (in bfs) gray :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "gray s v \<equiv> discovered s v \<and> v \<in> set (list (queue s))"

lemma (in bfs) gray_imp_not_white:
  assumes "gray s v"
  shows "\<not> white s v"
  using assms
  by simp

abbreviation (in bfs) black :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
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
  bfs where G = G and update = update and snoc = snoc +
  parent "lookup (parent s)"
  for
    G :: "'a::linorder dgraph" and
    update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
    snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
    s :: "('q, 'm) state" +
  assumes invar_queue: "invar (queue s)"
  assumes queue_distinct: "distinct (list (queue s))"
  assumes Map_invar_parent: "Map_invar (parent s)"
  assumes parent_src: "lookup (parent s) src = None"
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

lemma (in bfs_invar) list_queue_fold_cong:
  assumes "cond s"
  shows
    "list (queue (fold s)) =
     list (tail (queue s)) @
     filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))"
  using invar_queue Map_invar_parent assms
  by (intro list_queue_fold_cong_2)

lemma (in bfs_invar) lookup_parent_fold_cong:
  shows
    "lookup (parent (fold s)) =
     override_on
      (lookup (parent s))
      (\<lambda>_. Some (head (queue s)))
      (set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))))"
  using Map_invar_parent
  by (intro lookup_parent_fold_cong_2)

lemma (in bfs_invar) T_fold_cong:
  shows
    "T (fold s) =
     T s \<union>
     {(head (queue s), v) |v.
      v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> \<not> discovered s v}"
  using Map_invar_parent
  by (intro T_fold_cong_2)

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
  assumes "lookup (parent s) v = Some u"
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
    by (simp add: discovered_def dom_def)
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
    "lookup (parent s) v = Some u"
    by (auto simp add: dom_def)
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
  have dpath_length_rev_follow_eq_dist: "\<forall>v\<in>set (list (queue s)). dpath_length (rev (follow v)) = dist v"
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
    using assms queue_sorted_wrt_dpath_length dpath_length_rev_follow_eq_dist
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
  shows "follow_invar' (lookup (parent init))"
  using wf_empty
  by (simp add: init_def map_empty follow_invar'_def)

lemma (in bfs) parent_init:
  shows "Tbd.parent (lookup (parent init))"
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

subsubsection \<open>@{thm bfs_invar.Map_invar_parent}\<close>

lemma (in bfs) Map_invar_parent_init:
  shows "Map_invar (parent init)"
  using map_specs(4)
  by (simp add: init_def)

subsubsection \<open>@{thm bfs_invar.parent_src}\<close>

lemma (in bfs) parent_src_init:
  shows "lookup (parent init) src = None"
  by (simp add: init_def map_empty)

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
  by (simp add: init_def ran_def map_empty)

subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_dpath_length}\<close>

lemma (in bfs) queue_sorted_wrt_dpath_length_init:
  assumes "\<not> is_empty (queue init)"
  shows
    "sorted_wrt
      (\<lambda>u v. dpath_length (rev (parent.follow (lookup (parent init)) u)) \<le>
             dpath_length (rev (parent.follow (lookup (parent init)) v)))
      (list (queue init)) \<and>
     dpath_length (rev (parent.follow (lookup (parent init)) (last (list (queue init))))) \<le>
     dpath_length (rev (parent.follow (lookup (parent init)) (head (queue init)))) + 1"
  using invar_empty invar_queue_init
  by (simp add: init_def list_snoc list_empty list_head)

subsubsection \<open>@{thm bfs_invar.not_white_imp_shortest_dpath}\<close>

lemma (in bfs) not_white_imp_shortest_dpath_init:
  assumes "\<not> white init v"
  shows
    "dpath_bet G (rev (parent.follow (lookup (parent init)) v)) src v \<and>
     dpath_length (rev (parent.follow (lookup (parent init)) v)) = dist v"
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
    by (simp add: discovered_def dom_def init_def map_empty)
  moreover have "rev (parent.follow (lookup (parent init)) src) = [src]"
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
    by (simp add: discovered_def dom_def init_def map_empty)
  moreover have "src \<in> set (list (queue init))"
    using invar_empty
    by (simp add: init_def list_snoc)
  ultimately show ?thesis
    using assms
    by blast
qed

subsubsection \<open>\<close>

lemma (in bfs) bfs_invar_init:
  shows "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc init"
  using bfs_axioms
  using follow_invar'_parent_init
  using invar_queue_init queue_distinct_init Map_invar_parent_init parent_src_init
  using gray_if_mem_queue_init black_if_mem_ran_init queue_sorted_wrt_dpath_length_init
  using not_white_imp_shortest_dpath_init black_imp_out_neighborhood_not_white_init
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

lemma (in bfs_invar) head_queue_imp:
  assumes "cond s"
  shows
    "head (queue s) \<in> set (list (queue s))"
    "head (queue s) \<notin> set (list (queue (fold s)))"
proof -
  let ?u = "head (queue s)"
  show "?u \<in> set (list (queue s))"
    using invar_queue assms list_queue_non_empty
    by (simp add: list_head)
  hence "?u \<notin> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    using gray_if_mem_queue
    by fastforce
  moreover have "?u \<notin> set (list (tail (queue s)))"
    using queue_distinct
    by (simp add: list_queue[OF invar_queue list_queue_non_empty[OF assms]])
  ultimately show "?u \<notin> set (list (queue (fold s)))"
    using assms
    by (simp add: list_queue_fold_cong)
qed

lemma (in bfs_invar) head_queue_if:
  assumes "cond s"
  assumes "v \<in> set (list (queue s))"
  assumes "v \<notin> set (list (queue (fold s)))"
  shows "v = head (queue s)"
proof -
  have "list (queue s) = head (queue s) # list (tail (queue s))"
    using invar_queue assms(1)
    by (intro list_queue_non_empty list_queue)
  thus ?thesis
    using assms
    by (simp add: list_queue_fold_cong)
qed

lemma (in bfs_invar) head_queue_iff:
  assumes "cond s"
  shows "v = head (queue s) \<longleftrightarrow> v \<in> set (list (queue s)) \<and> v \<notin> set (list (queue (fold s)))"
proof (standard, goal_cases)
  case 1
  show ?case
    unfolding 1
    using assms
    by (intro head_queue_imp conjI)
next
  case 2
  thus ?case
    using assms
    by (blast intro: head_queue_if)
qed

lemma (in bfs_invar) not_white_imp_not_white_fold:
  assumes "\<not> white s v"
  shows "\<not> white (fold s) v"
  using assms
  by (auto simp add: discovered_def dom_def lookup_parent_fold_cong)

lemma (in bfs_invar) white_not_white_fold_imp:
  assumes "white s v"
  assumes "\<not> white (fold s) v"
  shows
    "v \<in> out_neighborhood G (head (queue s))"
    "lookup (parent (fold s)) v = Some (head (queue s))"
proof -
  show "v \<in> out_neighborhood G (head (queue s))"
    using assms out_neighborhood_finite
    by (fastforce simp add: discovered_def dom_def lookup_parent_fold_cong)
  thus "lookup (parent (fold s)) v = Some (head (queue s))"
    using assms(1) out_neighborhood_finite
    by (auto simp add: lookup_parent_fold_cong)
qed

subsubsection \<open>\<close>

lemma (in bfs_invar) follow_invar'_parent_fold:
  assumes "cond s"
  shows "follow_invar' (lookup (parent (fold s)))"
  unfolding follow_invar'_def T_fold_cong
proof (rule wf_Un[unfolded follow_invar'_def])
  let ?r =
    "{(head (queue s), v) |v.
      v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<and> \<not> discovered s v}"
  show "wf (T s)"
    using follow_invar'
    by (simp add: follow_invar'_def)
  have "gray s (head (queue s))"
    using assms
    by (intro head_queue_imp(1) gray_if_mem_queue) simp+
  thus "wf ?r"
    by (simp add: wf_def)
  show "Domain (T s) \<inter> Range ?r = {}"
    using black_if_mem_ran
    by (auto simp add: ran_def)
qed

lemma (in bfs_invar) parent_fold:
  assumes "cond s"
  shows "Tbd.parent (lookup (parent (fold s)))"
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
    using assms
    by (simp add: list_queue_fold_cong)
qed

subsubsection \<open>@{thm bfs_invar.Map_invar_parent}\<close>

lemma (in bfs_invar) Map_invar_parent_fold:
  shows "Map_invar (parent (fold s))"
  using Map_invar_parent
  by (intro Map_invar_parent_fold_2)

subsubsection \<open>@{thm bfs_invar.parent_src}\<close>

lemma (in bfs_invar) parent_src_fold:
  shows "lookup (parent (fold s)) src = None"
  using Map_invar_parent src_not_white
  by (simp add: lookup_parent_fold_cong_2 parent_src)

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
    using mem_queue_fold cond
    by (simp add: list_queue_fold_cong)
  hence "\<not> white (fold s) v"
    by (fastforce simp add: discovered_def dom_def lookup_parent_fold_cong)
  thus ?thesis
    using mem_queue_fold
    by blast
qed

subsubsection \<open>@{thm bfs_invar.black_if_mem_ran}\<close>

lemma (in bfs_invar) head_queue_if_2:
  assumes "v \<notin> ran (parent s)"
  assumes "v \<in> ran (parent (fold s))"
  shows "v = head (queue s)"
  using Map_invar_parent assms
  by (auto simp add: ran_parent_fold_cong split: if_splits(2))

lemma (in bfs_invar) black_if_mem_ran_fold:
  assumes cond: "cond s"
  assumes mem_ran_fold: "v \<in> ran (parent (fold s))"
  shows "black (fold s) v"
proof (cases "v \<in> ran (parent s)")
  case True
  show ?thesis
  proof (rule ccontr)
    assume assm: "\<not> black (fold s) v"
    have black: "black s v"
      using True
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
      using cond black
      by (simp add: discovered_def list_queue_fold_cong)
    thus "False"
      using not_white_fold
      by blast
  qed
next
  case False
  have v_eq_head_queue: "v = head (queue s)"
    using invar_queue False mem_ran_fold
    by (intro head_queue_if_2)
  then have "v \<in> set (list (queue s))"
    using cond
    by (blast intro: head_queue_imp(1))
  hence "\<not> white s v"
    by (intro gray_if_mem_queue gray_imp_not_white)
  with cond
  have "\<not> white (fold s) v"
    by (intro not_white_imp_not_white_fold)
  moreover have "v \<notin> set (list (queue (fold s)))"
    unfolding v_eq_head_queue
    using cond
    by (intro head_queue_imp(2))
  ultimately show ?thesis
    by blast
qed

subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_dpath_length}\<close>

lemma (in bfs_invar) not_white_imp_rev_follow_fold_eq_rev_follow:
  assumes "cond s"
  assumes "\<not> white s v"
  shows "rev (parent.follow (lookup (parent (fold s))) v) = rev (follow v)"
  using assms
proof (induct v rule: follow.pinduct[OF follow_dom])
  case (1 v)
  show ?case
  proof (cases "v = src")
    case True
    hence
      "lookup (parent s) v = None"
      "lookup (parent (fold s)) v = None"
      using parent_src parent_src_fold
      by simp+
    hence
      "rev (follow v) = [v]"
      "rev (parent.follow (lookup (parent (fold s))) v) = [v]"
      using "1.prems"(1) parent_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      by fastforce
  next
    case False
    then obtain u where u:
      "lookup (parent s) v = Some u"
      "\<not> white s u"
      using False "1.prems"(2) black_if_mem_ran
      by (auto simp add: discovered_def dom_def ran_def)
    moreover hence "lookup (parent (fold s)) v = Some u"
      using "1.prems"(2)
      by (simp add: lookup_parent_fold_cong map_add_Some_iff)
    ultimately have
      "rev (follow v) = rev (follow u) @ [v]"
      "rev (parent.follow (lookup (parent (fold s))) v) =
       rev (parent.follow (lookup (parent (fold s))) u) @ [v]"
      using "1.prems"(1) parent_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      using u "1.prems"(1)
      by (simp add: "1.hyps"(2))
  qed
qed

lemma (in bfs_invar) mem_filter_imp_dpath_length:
  assumes "cond s"
  assumes "v \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
  shows
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) v)) =
     dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue s)))) + 1"
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue s))))) \<le>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) v))"
proof -
  let ?u = "head (queue s)"
  have "lookup (parent (fold s)) v = Some ?u"
    using assms(2)
    by (simp add: lookup_parent_fold_cong)
  hence
    "rev (parent.follow (lookup (parent (fold s))) v) =
     rev (parent.follow (lookup (parent (fold s))) ?u) @ [v]"
    using assms(1) parent_fold
    by (simp add: parent.follow_psimps)
  thus dpath_length_eq:
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) v)) =
     dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue s)))) + 1"
    using assms(1) parent_fold parent.follow_non_empty
    by (fastforce simp add: dpath_length_snoc)

  have
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue s))))) =
     dpath_length (rev (follow (last (list (queue s)))))"
    using assms list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow ?u)) + 1"
    using assms queue_sorted_wrt_dpath_length
    by (simp add: cond_def)
  also have "... = dpath_length (rev (parent.follow (lookup (parent (fold s))) ?u)) + 1"
    using assms head_queue_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... = dpath_length (rev (parent.follow (lookup (parent (fold s))) v))"
    unfolding dpath_length_eq
    ..
  finally show
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue s))))) \<le>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) v))"
    .
qed

(* TODO: move somewhere else *)
lemma sorted_wrt_if:
  assumes "\<And>x y. x \<in> set l \<Longrightarrow> y \<in> set l \<Longrightarrow> P x y"
  shows "sorted_wrt P l"
  using assms
  by (simp add: sorted_wrt_iff_nth_less)

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_case_1_aux:
  assumes cond: "cond s"
  assumes u_mem_tail_queue: "u \<in> set (list (tail (queue s)))"
  assumes v_mem_filter:
    "v \<in> set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
  shows
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) u)) \<le>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) v))"
proof -
  have u_mem_queue: "u \<in> set (list (queue s))"
    using u_mem_tail_queue invar_queue cond list_queue_non_empty
    by (auto simp add: list_tail intro: list.set_sel(2))
  have
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) u)) =
     dpath_length (rev (follow u))"
    using cond u_mem_queue gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow (last (list (queue s)))))"
    using u_mem_queue
    by (intro mem_queue_imp_dpath_length_last_queue)
  also have "... = dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue s)))))"
    using cond list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (parent.follow (lookup (parent (fold s))) v))"
    using cond v_mem_filter
    by (intro mem_filter_imp_dpath_length(2))
  finally show ?thesis
    .
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_case_2_aux:
  assumes cond: "cond s"
  assumes "\<not> is_empty (queue (fold s))"
  shows
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue (fold s)))))) \<le>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue s)))) + 1"
proof (cases "filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))) = []")
  case True
  hence list_tail_non_empty: "list (tail (queue s)) \<noteq> []"
    using invar_queue assms invar_queue_fold_2
    by (simp add: list_queue_fold_cong is_empty)
  hence "last (list (queue (fold s))) = last (list (tail (queue s)))"
    unfolding list_queue_fold_cong[OF cond] last_appendL[OF True]
    by blast
  hence "last (list (queue (fold s))) = last (list (queue s))"
    using list_tail_non_empty
    by (simp add: list_queue[OF invar_queue list_queue_non_empty[OF assms(1)]])
  hence
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue (fold s)))))) =
     dpath_length (rev (follow (last (list (queue s)))))"
    using cond list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow (head (queue s)))) + 1"
    using invar_queue cond list_queue_non_empty queue_sorted_wrt_dpath_length
    by (simp add: is_empty)
  also have "... = dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue s)))) + 1"
    using cond head_queue_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  finally show ?thesis
    .
next
  case False
  hence
    "last (list (queue (fold s))) \<in>
     set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    unfolding list_queue_fold_cong[OF cond] last_appendR[OF False]
    by (intro last_in_set)
  with cond
  show ?thesis
    by (simp add: mem_filter_imp_dpath_length(1))
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_case_2_aux_2:
  assumes cond: "cond s"
  assumes "\<not> is_empty (queue (fold s))"
  shows
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue s)))) \<le>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue (fold s)))))"
proof (cases "list (tail (queue s)) = []")
  case True
  have "head (queue (fold s)) = hd (list (queue (fold s)))"
    using assms invar_queue invar_queue_fold_2
    by (simp add: is_empty list_head)
  hence
    "head (queue (fold s)) =
     hd (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    using cond True
    by (simp add: list_queue_fold_cong)
  moreover have
    "filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))) \<noteq> []"
    using invar_queue assms invar_queue_fold_2 True
    by (simp add: is_empty list_queue_fold_cong)
  ultimately have head_queue_fold_mem_filter:
    "head (queue (fold s)) \<in>
     set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    using list.set_sel(1)
    by metis

  have
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue s)))) =
     dpath_length (rev (follow (head (queue s))))"
    using cond head_queue_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow (last (list (queue s)))))"
    using cond
    by (intro head_queue_imp(1) mem_queue_imp_dpath_length_last_queue)
  also have
    "... = dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue s)))))"
    using cond list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue (fold s)))))"
    using cond head_queue_fold_mem_filter
    by (intro mem_filter_imp_dpath_length(2))
  finally show ?thesis
    .
next
  case False
  have "head (queue (fold s)) = hd (list (queue (fold s)))"
    using assms invar_queue invar_queue_fold_2
    by (simp add: is_empty list_head)
  hence "head (queue (fold s)) = hd (list (tail (queue s)))"
    using cond False
    by (simp add: list_queue_fold_cong)
  hence head_queue_fold_mem_list_queue: "head (queue (fold s)) \<in> set (list (queue s))"
    using False invar_queue cond list_queue_non_empty
    by (auto simp add: list_tail intro: list.set_sel(2))

  have
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue s)))) =
     dpath_length (rev (follow (head (queue s))))"
    using cond head_queue_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow (head (queue (fold s)))))"
    using head_queue_fold_mem_list_queue
    by (intro mem_queue_imp_dpath_length_head_queue)
  also have "... = dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue (fold s)))))"
    using cond head_queue_fold_mem_list_queue gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  finally show ?thesis
    .
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold:
  assumes cond: "cond s"
  assumes "\<not> is_empty (queue (fold s))"
  shows
    "sorted_wrt
      (\<lambda>u v. dpath_length (rev (parent.follow (lookup (parent (fold s))) u)) \<le>
             dpath_length (rev (parent.follow (lookup (parent (fold s))) v)))
      (list (queue (fold s))) \<and>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue (fold s)))))) \<le>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue (fold s))))) + 1"
proof (rule conjI, goal_cases)
  case 1
  let ?P =
    "\<lambda>u v. dpath_length (rev (parent.follow (lookup (parent (fold s))) u)) \<le>
           dpath_length (rev (parent.follow (lookup (parent (fold s))) v))"
  have list_queue_non_empty: "list (queue s) \<noteq> []"
    using cond
    by (intro list_queue_non_empty)
  hence
    "sorted_wrt
      (\<lambda>u v. dpath_length (rev (follow u)) \<le> dpath_length (rev (follow v)))
      (list (queue s))"
    using invar_queue queue_sorted_wrt_dpath_length
    by (simp add: is_empty)
  hence "sorted_wrt ?P (list (queue s))"
    using cond gray_if_mem_queue sorted_wrt_mono_rel[of "(list (queue s))"]
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  hence "sorted_wrt ?P (list (tail (queue s)))"
    by (simp add: list_queue[OF invar_queue list_queue_non_empty])
  moreover have
    "sorted_wrt
      ?P
      (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s)))))"
    using cond
    by (auto simp add: mem_filter_imp_dpath_length(1) intro: sorted_wrt_if)
  moreover have
    "\<forall>u\<in>set (list (tail (queue s))).
      \<forall>v\<in>set (filter (Not \<circ> discovered s) (sorted_list_of_set (out_neighborhood G (head (queue s))))).
       dpath_length (rev (parent.follow (lookup (parent (fold s))) u)) \<le>
       dpath_length (rev (parent.follow (lookup (parent (fold s))) v))"
    using cond
    by (blast intro: queue_sorted_wrt_dpath_length_fold_case_1_aux)
  ultimately show ?case 
    using cond
    by (simp add: list_queue_fold_cong sorted_wrt_append)
next
  case 2
  have
    "dpath_length (rev (parent.follow (lookup (parent (fold s))) (last (list (queue (fold s)))))) \<le>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue s)))) + 1"
    using assms
    by (intro queue_sorted_wrt_dpath_length_fold_case_2_aux)
  also have "... \<le> dpath_length (rev (parent.follow (lookup (parent (fold s))) (head (queue (fold s))))) + 1"
    using assms
    by (auto intro: queue_sorted_wrt_dpath_length_fold_case_2_aux_2)
  finally show ?case
    .
qed

subsubsection \<open>@{thm bfs_invar.not_white_imp_shortest_dpath}\<close>

lemma (in bfs_invar) not_white_imp_shortest_dpath_fold_case_1_subcase_3_aux:
  assumes cond: "cond s"
  assumes dist_less: "dist v < dist (head (queue s)) + 1"
  assumes dpath_bet: "dpath_bet G (l @ [u, u']) src v"
  assumes dpath_length: "dpath_length (l @ [u, u']) = dist v"
  assumes white: "white s v"
  shows "False"
proof -
  let ?u = "head (queue s)"
  have "dist u + 1 = dist v"
    using dpath_bet dpath_length
    by (auto intro: shortest_dpathE_2)
  hence "dist u + 1 < dist ?u + 1"
    using dist_less
    by simp
  hence "dist u < dist ?u"
    unfolding plus_1_eSuc(2) eSuc_mono
    .
  thus ?thesis
  proof (induct s u rule: vertex_color_induct)
    case white
    have "dist ?u \<le> dist (last (list (queue s)))"
      using cond list_queue_non_empty
      by (intro mem_queue_imp_dist_head_queue) simp
    also have "... \<le> dist u"
      using white.hyps cond white_imp_dist_ge
      by (simp add: cond_def)
    finally show ?case
      using white.prems
      by simp
  next
    case gray
    hence "dist ?u \<le> dist u"
      by (intro mem_queue_imp_dist_head_queue) simp
    thus ?case
      using gray.prems
      by simp
  next
    case black
    have "dpath_bet G [u, v] u v"
      using dpath_bet split_dpath last_of_dpath_bet
      by fastforce
    hence "v \<in> out_neighborhood G u"
      by (simp add: edge_iff_dpath_bet in_out_neighborhood_iff_edge)
    hence "\<not> white s v"
      using black.hyps black_imp_out_neighborhood_not_white
      by blast
    thus ?case
      using white
      by simp
  qed
qed

lemma (in bfs_invar) not_white_imp_shortest_dpath_fold_case_1_aux:
  assumes cond: "cond s"
  assumes white: "white s v"
  assumes reachable: "reachable G src v"
  assumes v_mem_out_neighborhood_head_queue: "v \<in> out_neighborhood G (head (queue s))"
  shows "dist (head (queue s)) + 1 = dist v"
proof (rule antisym, rule ccontr, goal_cases)
  case 1
  let ?u = "head (queue s)"
  assume "\<not> dist ?u + 1 \<le> dist v"
  hence "dist v < dist ?u + 1"
    by fastforce
  moreover obtain p where
    "dpath_bet G p src v"
    "dpath_length p = dist v"
    using reachable
    by (elim dist_dpath_betE)
  ultimately show ?case
    using white
  proof (induct p arbitrary: v rule: dpath_rev_induct)
    case 1
    thus ?case
      by auto
  next
    case (2 u)
    hence "[u] = [src] \<and> src = v"
      by (intro hd_of_dpath_bet' last_of_dpath_bet list_length_1) simp
    hence "white s src"
      using "2.prems"(4)
      by simp
    thus ?case
      by (simp add: discovered_def)
  next
    case (3 u u' l)
    thm "3.prems"
    with cond
    show ?case
      by (intro not_white_imp_shortest_dpath_fold_case_1_subcase_3_aux)
  qed
next
  case 2
  show ?case
    using v_mem_out_neighborhood_head_queue
    by (intro dist_triangle_inequality_edge) (simp add: in_out_neighborhood_iff_edge)
qed

lemma (in bfs_invar) not_white_imp_shortest_dpath_fold:
  assumes cond: "cond s"
  assumes not_white_fold: "\<not> white (fold s) v"
  shows
    "dpath_bet G (rev (parent.follow (lookup (parent (fold s))) v)) src v \<and>
     dpath_length (rev (parent.follow (lookup (parent (fold s))) v)) = dist v"
proof (cases "white s v", standard)
  let ?u = "head (queue s)"
  case True
  hence
    v_mem_out_neighborhood_head_queue: "v \<in> out_neighborhood G ?u" and
    parent_fold_v_eq_head_queue: "lookup (parent (fold s)) v = Some ?u"
    using not_white_fold
    by (auto intro: white_not_white_fold_imp)
  have head_queue_not_white: "\<not> white s ?u"
    using cond
    by (intro head_queue_imp(1) gray_if_mem_queue gray_imp_not_white)
  hence rev_follow_head_queue_shortest_dpath:
    "dpath_bet G (rev (follow ?u)) src ?u \<and> dpath_length (rev (follow ?u)) = dist ?u"
    by (intro not_white_imp_shortest_dpath)
  have
    "rev (parent.follow (lookup (parent (fold s))) v) =
     rev (parent.follow (lookup (parent (fold s))) ?u) @ [v]"
    using cond parent_fold
    by (simp add: parent.follow_psimps parent_fold_v_eq_head_queue)
  hence rev_follow_fold_eq: "rev (parent.follow (lookup (parent (fold s))) v) = rev (follow ?u) @ [v]"
    using cond head_queue_not_white
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  thus "dpath_bet G (rev (parent.follow (lookup (parent (fold s))) v)) src v"
    using rev_follow_head_queue_shortest_dpath
    using v_mem_out_neighborhood_head_queue dpath_bet_transitive
    by (fastforce simp add: in_out_neighborhood_iff_edge edge_iff_dpath_bet)
  hence "reachable G src v"
    by (auto simp add: reachable_iff_dpath_bet)
  with cond True
  have "dist v = dist ?u + 1"
    using True not_white_fold
    by (intro white_not_white_fold_imp(1) not_white_imp_shortest_dpath_fold_case_1_aux[symmetric])
  also have "... = dpath_length (rev (follow ?u)) + 1"
    unfolding plus_enat_simps(1)[symmetric]
    by (simp add: rev_follow_head_queue_shortest_dpath)
  also have "... = dpath_length (rev (parent.follow (lookup (parent (fold s))) v))"
    using follow_non_empty
    by (simp add: rev_follow_fold_eq dpath_length_snoc)
  finally show "dpath_length (rev (parent.follow (lookup (parent (fold s))) v)) = dist v"
    by simp
next
  case False
  thus ?thesis
    using cond not_white_imp_shortest_dpath
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
qed

subsubsection \<open>@{thm bfs_invar.black_imp_out_neighborhood_not_white}\<close>

lemma (in bfs_invar) black_imp_out_neighborhood_not_white_fold:
  assumes cond: "cond s"
  assumes black_fold: "black (fold s) v"
  shows "\<forall>w\<in>out_neighborhood G v. \<not> white (fold s) w"
proof (induct s v rule: vertex_color_induct)
  case white
  hence "v \<in> set (sorted_list_of_set (out_neighborhood G (head (queue s))))"
    using black_fold out_neighborhood_finite
    by (auto intro: white_not_white_fold_imp(1))
  hence "v \<in> set (list (queue (fold s)))"
    using white cond
    by (simp add: discovered_def list_queue_fold_cong)
  thus ?case
    using black_fold
    by blast
next
  case gray
  hence "v = head (queue s)"
    using assms invar_queue
    by (intro head_queue_if) simp+
  thus ?case
    using out_neighborhood_finite
    by (auto simp add: discovered_def dom_def lookup_parent_fold_cong override_on_def)
next
  case black
  hence "\<forall>w\<in>out_neighborhood G v. \<not> white s w"
    by (intro black_imp_out_neighborhood_not_white)
  thus ?case
    using cond not_white_imp_not_white_fold
    by blast
qed

subsubsection \<open>\<close>

lemma (in bfs_invar) bfs_invar_fold:
  assumes "cond s"
  shows "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc (fold s)"
  using assms
  using bfs_axioms
  using follow_invar'_parent_fold
  using invar_queue_fold queue_distinct_fold Map_invar_parent_fold parent_src_fold
  using gray_if_mem_queue_fold black_if_mem_ran_fold queue_sorted_wrt_dpath_length_fold
  using not_white_imp_shortest_dpath_fold black_imp_out_neighborhood_not_white_fold
  by unfold_locales

subsection \<open>@{term bfs.loop}\<close>

lemma (in bfs) loop_psimps:
  assumes "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc s"
  shows "loop s = (if cond s then loop (fold s) else s)"
proof -
  have "invar (queue s)"
    using assms
    by (intro bfs_invar.invar_queue)
  moreover have "Map_invar (parent s)"
    using assms
    by (intro bfs_invar.Map_invar_parent)
  moreover have "dom (parent s) \<subseteq> dVs G"
    using assms
    by (intro bfs_invar.dom_parent_subset_vertices)
  ultimately show ?thesis
    using loop_dom loop.psimps
    by meson
qed

lemma (in bfs) bfs_induct:
  assumes "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc s"
  assumes "\<And>s. loop_dom s \<Longrightarrow> (cond s \<Longrightarrow> P (fold s)) \<Longrightarrow> P s"
  shows "P s"
proof -
  have "invar (queue s)"
    using assms(1)
    by (intro bfs_invar.invar_queue)
  moreover have "Map_invar (parent s)"
    using assms(1)
    by (intro bfs_invar.Map_invar_parent)
  moreover have "dom (parent s) \<subseteq> dVs G"
    using assms(1)
    by (intro bfs_invar.dom_parent_subset_vertices)
  ultimately show ?thesis
    using assms(2)
    by (blast intro: loop_dom loop.pinduct)
qed

lemma (in bfs) bfs_invar_loop:
  assumes "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc s"
  shows "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc (loop s)"
  using assms
proof (induct rule: bfs_induct[OF assms])
  case (1 s)
  thus ?case
    by (fastforce simp add: loop_psimps intro: bfs_invar.bfs_invar_fold)
qed

subsection \<open>@{term bfs.bfs}\<close>

lemma (in bfs) bfs_invar_bfs:
  shows "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc bfs"
  using bfs_invar_init
  by (intro bfs_invar_loop)

section \<open>Correctness\<close>

lemma (in bfs) soundness:
  assumes "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc s"
  assumes "discovered (loop s) v"
  shows
    "dpath_bet G (rev (parent.follow (lookup (parent (loop s))) v)) src v \<and>
     dpath_length (rev (parent.follow (lookup (parent (loop s))) v)) = dist v"
  using assms bfs_invar_loop bfs_invar.not_white_imp_shortest_dpath
  by fast

lemma (in bfs) completeness:
  assumes "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc s"
  assumes "\<not> discovered (loop s) v"
  shows "\<not> reachable G src v"
  using assms
proof (induct rule: bfs_induct[OF assms(1)])
  case (1 s)
  show ?case
  proof (cases "cond s")
    case True
    thus ?thesis
      using "1.prems"
      by (intro bfs_invar.bfs_invar_fold "1.hyps"(2)) (simp_all add: loop_psimps)
  next
    case False
    hence "\<not> discovered s v"
      using "1.prems"
      by (simp add: loop_psimps)
    hence "dist v = \<infinity>"
      using "1.prems"(1) False bfs_invar.white_imp_dist_ge
      by (fastforce simp add: cond_def)
    thus ?thesis
      using dist_eq_\<delta> \<delta>_reachable_conv
      by metis
  qed
qed

lemma (in bfs) correctness:
  assumes "bfs_invar delete lookup empty is_empty head tail invar list Map_empty Map_invar src G update snoc s"
  shows
    "\<And>v.
      discovered (loop s) v \<Longrightarrow>
      dpath_bet G (rev (parent.follow (lookup (parent (loop s))) v)) src v \<and>
      dpath_length (rev (parent.follow (lookup (parent (loop s))) v)) = dist v"
    "\<And>v. \<not> discovered (loop s) v \<Longrightarrow> \<not> reachable G src v"
  using assms soundness completeness
  by simp+

lemma (in bfs) bfs_correct:
  shows
    "\<And>v.
      discovered bfs v \<Longrightarrow>
      dpath_bet G (rev (parent.follow (lookup (parent bfs)) v)) src v \<and>
      dpath_length (rev (parent.follow (lookup (parent bfs)) v)) = dist v"
    "\<And>v. \<not> discovered bfs v \<Longrightarrow> \<not> reachable G src v"
  using bfs_invar_init correctness
  by simp+

end