theory BFS
imports
    "../Map_Specs_Tbd"
    "../Misc_Tbd"
    "../Queue_Specs"
    "../Tbd"
    "../Tbd_Graph"
begin

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
  list = Q_list
  for
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

abbreviation dist :: "'n \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "dist G \<equiv> Shortest_Dpath.dist (G.E G)"

abbreviation is_shortest_dpath :: "'n \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_shortest_dpath G p u v \<equiv> dpath_bet (G.E G) p u v \<and> dpath_length p = dist G u v"

section \<open>BFS algorithm\<close>

definition init :: "'a \<Rightarrow> ('q, 'm) state" where
  "init src \<equiv>
   \<lparr>queue = Q_snoc Q_empty src,
    parent = P_empty\<rparr>"

definition cond :: "('q, 'm) state \<Rightarrow> bool" where
  "cond s \<longleftrightarrow> \<not> Q_is_empty (queue s)"

definition discovered :: "'a \<Rightarrow> ('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "discovered src s v \<longleftrightarrow> v = src \<or> P_lookup (parent s) v \<noteq> None"

definition discover :: "'a \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "discover u v s \<equiv>
   \<lparr>queue = Q_snoc (queue s) v,
    parent = P_update v u (parent s)\<rparr>"

definition traverse_edge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "traverse_edge src u v s \<equiv>
   if \<not> discovered src s v then discover u v s
   else s"

function (domintros) loop :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "loop G src s =
   (if cond s
    then let
          u = Q_head (queue s);
          q = Q_tail (queue s)
         in loop G src (fold (traverse_edge src u) (G.out_neighborhood G u) (s\<lparr>queue := q\<rparr>))
    else s)"
  by pat_completeness simp

abbreviation bfs :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state" where
  "bfs G src \<equiv> loop G src (init src)"

section \<open>\<close>

abbreviation fold :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> ('q, 'm) state" where
  "fold G src s \<equiv>
   List.fold
    (traverse_edge src (Q_head (queue s)))
    (G.out_neighborhood G (Q_head (queue s)))
    (s\<lparr>queue := Q_tail (queue s)\<rparr>)"

abbreviation T :: "('q, 'm) state \<Rightarrow> 'a dgraph" where
  "T s \<equiv> {(u, v) |u v. P_lookup (parent s) v = Some u}"

section \<open>Convenience Lemmas\<close>

subsection \<open>@{term "Q_invar \<circ> queue"}\<close>

lemma tail_invar:
  assumes "Q_invar (queue s)"
  assumes "cond s"
  shows "Q_invar (queue (s\<lparr>queue := Q_tail (queue s)\<rparr>))"
  using assms Q.invar_tail
  by (simp add: cond_def Q.is_empty)

subsection \<open>@{term "Q_list \<circ> queue"}\<close>

lemma list_queue_non_empty:
  assumes "Q_invar (queue s)"
  assumes "cond s"
  shows "Q_list (queue s) \<noteq> []"
  using assms
  by (simp add: cond_def Q.is_empty)

subsection \<open>@{term "Q_head \<circ> queue"}\<close>

lemma head_queue_mem_V:
  assumes "Q_invar (queue s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.V G"
  assumes "cond s"
  shows "Q_head (queue s) \<in> G.V G"
  using assms list_queue_non_empty
  by (auto simp add: Q.list_head)

section \<open>Basic Lemmas\<close>

subsection \<open>@{term discover}\<close>

subsubsection \<open>@{term queue}\<close>

lemma queue_discover_cong [simp]:
  shows "queue (discover u v s) = Q_snoc (queue s) v"
  by (simp add: discover_def)

subsubsection \<open>@{term parent}\<close>

lemma parent_discover_cong [simp]:
  shows "parent (discover u v s) = P_update v u (parent s)"
  by (simp add: discover_def)

subsection \<open>@{term traverse_edge}\<close>

subsubsection \<open>@{term queue}\<close>

lemma queue_traverse_edge_cong:
  shows "queue (traverse_edge src u v s) = (if \<not> discovered src s v then Q_snoc (queue s) v else queue s)"
  by (simp add: traverse_edge_def)

subsubsection \<open>@{term "Q_invar \<circ> queue"}\<close>

lemma queue_traverse_edge_invar:
  assumes "Q_invar (queue s)"
  shows "Q_invar (queue (traverse_edge src u v s))"
  using assms Q.invar_snoc
  by (simp add: queue_traverse_edge_cong)

subsubsection \<open>@{term "Q_list \<circ> queue"}\<close>

lemma list_queue_traverse_edge_cong:
  assumes "Q_invar (queue s)"
  shows
    "Q_list (queue (traverse_edge src u v s)) =
     Q_list (queue s) @ (if \<not> discovered src s v then [v] else [])"
  using assms
  by (simp add: queue_traverse_edge_cong Q.list_snoc)

subsubsection \<open>@{term "P_lookup \<circ> parent"}\<close>

lemma lookup_parent_traverse_edge_cong:
  assumes "P_invar (parent s)"
  shows
    "P_lookup (parent (traverse_edge src u v s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some u)
      (if \<not> discovered src s v then {v} else {})"
  using assms
  by (simp add: traverse_edge_def P.map_update override_on_insert')

subsubsection \<open>@{term "P_invar \<circ> parent"}\<close>

lemma parent_traverse_edge_invar:
  assumes "P_invar (parent s)"
  shows "P_invar (parent (traverse_edge src u v s))"
  using assms P.invar_update
  by (simp add: traverse_edge_def)

subsubsection \<open>@{term T}\<close>

lemma T_traverse_edge_cong:
  assumes "P_invar (parent s)"
  shows "T (traverse_edge src u v s) = T s \<union> (if \<not> discovered src s v then {(u, v)} else {})"
  using assms
  by (auto simp add: lookup_parent_traverse_edge_cong override_on_def discovered_def)

subsection \<open>@{term fold}\<close>

subsubsection \<open>@{term "Q_invar \<circ> queue"}\<close>

lemma queue_fold_invar:
  assumes "Q_invar (queue s)"
  assumes "distinct l"
  shows "Q_invar (queue (List.fold (traverse_edge src u) l s))"
  using assms
  by (induct l arbitrary: s) (simp_all add: queue_traverse_edge_invar)

lemma queue_fold_invar_2:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "cond s"
  shows "Q_invar (queue (fold G src s))"
  using assms
  by (auto intro: G.out_neighborhood_distinct tail_invar queue_fold_invar)

subsubsection \<open>@{term "Q_list \<circ> queue"}\<close>

lemma list_queue_fold_cong_aux:
  assumes "P_invar (parent s)"
  assumes "distinct (v # vs)"
  shows "filter (Not \<circ> discovered src (traverse_edge src u v s)) vs = filter (Not \<circ> discovered src s) vs"
proof (rule filter_cong)
  fix w
  assume "w \<in> set vs"
  hence "discovered src (traverse_edge src u v s) w = discovered src s w"
    using assms
    by (auto simp add: discovered_def lookup_parent_traverse_edge_cong override_on_insert')
  thus "(Not \<circ> discovered src (traverse_edge src u v s)) w = (Not \<circ> discovered src s) w"
    by simp
qed simp

lemma list_queue_fold_cong:
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "distinct l"
  shows
    "Q_list (queue (List.fold (traverse_edge src u) l s)) =
     Q_list (queue s) @ filter (Not \<circ> discovered src s) l"
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
     filter (Not \<circ> discovered src (traverse_edge src u v s)) vs"
    using Cons.prems
    by (auto intro: queue_traverse_edge_invar parent_traverse_edge_invar Cons.hyps)
  also have
    "... =
     Q_list (queue s) @
     (if \<not> discovered src s v then [v] else []) @
     filter (Not \<circ> discovered src (traverse_edge src u v s)) vs"
    using Cons.prems(1)
    by (simp add: list_queue_traverse_edge_cong)
  also have
    "... =
     Q_list (queue s) @
     (if \<not> discovered src s v then [v] else []) @
     filter (Not \<circ> discovered src s) vs"
    using Cons.prems(2, 3)
    by (simp add: list_queue_fold_cong_aux)
  also have "... = Q_list (queue s) @ filter (Not \<circ> discovered src s) (v # vs)"
    by simp
  finally show ?case
    .
qed

lemma list_queue_fold_cong_2:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "cond s"
  shows
    "Q_list (queue (fold G src s)) =
     Q_list (Q_tail (queue s)) @
     filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s)))"
proof -
  have
    "Q_list (queue (fold G src s)) =
     Q_list (queue (s\<lparr>queue := Q_tail (queue s)\<rparr>)) @
     filter
      (Not \<circ> discovered src (s\<lparr>queue := Q_tail (queue s)\<rparr>))
      (G.out_neighborhood G (Q_head (queue s)))"
    using assms
    by (intro tail_invar G.out_neighborhood_distinct list_queue_fold_cong) simp+
  thus ?thesis
    unfolding comp_apply
    by (simp add: discovered_def)
qed

subsubsection \<open>@{term "set \<circ> Q_list \<circ> queue"}\<close>

lemma queue_fold_subset_V:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.V G"
  assumes "cond s"
  shows "set (Q_list (queue (fold G src s))) \<subseteq> G.V G"
proof
  fix v
  assume assm: "v \<in> set (Q_list (queue (fold G src s)))"
  show "v \<in> G.V G"
  proof (cases "v \<in> set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))")
    case True
    have "set (G.out_neighborhood G (Q_head (queue s))) \<subseteq> G.V G"
      using assms
      by (intro head_queue_mem_V G.out_neighborhood_subset_V)
    thus ?thesis
      using True
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

lemma lookup_parent_fold_cong:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  shows
    "P_lookup (parent (List.fold (traverse_edge src u) l s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> discovered src s) l))"
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
      (set (filter (Not \<circ> discovered src (traverse_edge src u v s)) vs))"
    using Cons.prems
    by (fastforce intro: parent_traverse_edge_invar Cons.hyps)
  also have
    "... =
     override_on
      (override_on (P_lookup (parent s)) (\<lambda>_. Some u) (if \<not> discovered src s v then {v} else {}))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> discovered src (traverse_edge src u v s)) vs))"
    using Cons.prems(1)
    by (simp add: lookup_parent_traverse_edge_cong)
  also have
    "... =
     override_on
      (override_on (P_lookup (parent s)) (\<lambda>_. Some u) (if \<not> discovered src s v then {v} else {}))
      (\<lambda>_. Some u)
      (set (filter (Not \<circ> discovered src s) vs))"
    using Cons.prems
    by (simp add: list_queue_fold_cong_aux)
  finally show ?case
    by (simp add: override_on_insert')
qed

lemma lookup_parent_fold_cong_2:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  shows
    "P_lookup (parent (fold G src s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s)))))"
proof -
  have
    "P_lookup (parent (fold G src s)) =
     override_on
      (P_lookup (parent (s\<lparr>queue := Q_tail (queue s)\<rparr>)))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> discovered src (s\<lparr>queue := Q_tail (queue s)\<rparr>)) (G.out_neighborhood G (Q_head (queue s)))))"
    using assms
    by (intro G.out_neighborhood_distinct lookup_parent_fold_cong) simp+
  thus ?thesis
    by (simp add: discovered_def)
qed

subsubsection \<open>@{term "P_invar \<circ> parent"}\<close>

lemma parent_fold_invar:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  shows "P_invar (parent (List.fold (traverse_edge src u) l s))"
  using assms
  by (induct l arbitrary: s) (simp_all add: parent_traverse_edge_invar)

lemma parent_fold_invar_2:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  shows "P_invar (parent (fold G src s))"
  using assms
  by (intro G.out_neighborhood_distinct parent_fold_invar) simp+

subsubsection \<open>@{term "P.dom \<circ> parent"}\<close>

lemma dom_parent_fold_subset_V:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  assumes "P.dom (parent s) \<subseteq> G.V G"
  assumes "set l \<subseteq> G.V G"
  shows "P.dom (parent (List.fold (traverse_edge src u) l s)) \<subseteq> G.V G"
proof
  fix v
  assume assm: "v \<in> P.dom (parent (List.fold (traverse_edge src u) l s))"
  show "v \<in> G.V G"
  proof (cases "v \<in> set (filter (Not \<circ> discovered src s) l)")
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

lemma dom_parent_fold_subset_V_2:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.V G"
  assumes "P.dom (parent s) \<subseteq> G.V G"
  assumes "cond s"
  shows "P.dom (parent (fold G src s)) \<subseteq> G.V G"
proof -
  have "set (G.out_neighborhood G (Q_head (queue s))) \<subseteq> G.V G"
    using assms(2, 4, 6)
    by (intro head_queue_mem_V G.out_neighborhood_subset_V)
  thus ?thesis
    using assms(1, 3, 5)
    by (intro G.out_neighborhood_distinct dom_parent_fold_subset_V) simp+
qed

subsubsection \<open>@{term "P.ran \<circ> parent"}\<close>

lemma ran_parent_fold_cong:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  shows
    "P.ran (parent (fold G src s)) =
     P.ran (parent s) \<union>
     (if set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s)))) = {}
      then {}
      else {Q_head (queue s)})"
proof
  let ?S = "set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
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
      moreover hence "discovered src s v"
        by (simp add: discovered_def)
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

lemma T_fold_cong_aux:
  assumes "P_invar (parent s)"
  assumes "distinct (v # vs)"
  shows "w \<in> set vs \<and> \<not> discovered src (traverse_edge src u v s) w \<longleftrightarrow> w \<in> set vs \<and> \<not> discovered src s w"
  using assms
  by (auto simp add: discovered_def lookup_parent_traverse_edge_cong override_on_def)

lemma T_fold_cong:
  assumes "P_invar (parent s)"
  assumes "distinct l"
  shows "T (List.fold (traverse_edge src u) l s) = T s \<union> {(u, v) |v. v \<in> set l \<and> \<not> discovered src s v}"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by auto
next
  case (Cons v vs)
  have
    "T (List.fold (traverse_edge src u) (v # vs) s) =
     T (List.fold (traverse_edge src u) vs (traverse_edge src u v s))"
    by simp
  also have
    "... =
     T (traverse_edge src u v s) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> discovered src (traverse_edge src u v s) w}"
    using Cons.prems
    by (intro parent_traverse_edge_invar Cons.hyps) simp+
  also have
    "... =
     T s \<union>
     (if \<not> discovered src s v then {(u, v)} else {}) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> discovered src (traverse_edge src u v s) w}"
    unfolding T_traverse_edge_cong[OF Cons.prems(1)]
    by blast
  also have
    "... =
     T s \<union>
     (if \<not> discovered src s v then {(u, v)} else {}) \<union>
     {(u, w) |w. w \<in> set vs \<and> \<not> discovered src s w}"
    using Cons.prems
    by (simp add: T_fold_cong_aux)
  also have "... = T s \<union> {(u, w) |w. w \<in> set (v # vs) \<and> \<not> discovered src s w}"
    by force
  finally show ?case
    .
qed

lemma T_fold_cong_2:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  shows
    "T (fold G src s) =
     T s \<union>
     {(Q_head (queue s), v) |v.
      v \<in> set (G.out_neighborhood G (Q_head (queue s))) \<and> \<not> discovered src s v}"
proof -
  have
    "T (fold G src s) =
     T (s\<lparr>queue := Q_tail (queue s)\<rparr>) \<union>
     {(Q_head (queue s), v) |v.
      v \<in> set (G.out_neighborhood G (Q_head (queue s))) \<and>
      \<not> discovered src (s\<lparr>queue := Q_tail (queue s)\<rparr>) v}"
    using assms
    by (intro G.out_neighborhood_distinct T_fold_cong) simp+
  thus ?thesis
    by (simp add: discovered_def)
qed

section \<open>Termination\<close>

lemma loop_dom_aux:
  assumes "G.invar G"
  assumes "P_invar (parent s)"
  assumes "P.dom (parent s) \<subseteq> G.V G"
  shows
    "card (P.dom (parent (fold G src s))) =
     card (P.dom (parent s)) +
     card (set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s)))))"
proof -
  let ?S = "set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
  have "P.dom (parent (fold G src s)) = P.dom (parent s) \<union> ?S"
    using assms(1, 2)
    by (auto simp add: P.dom_def lookup_parent_fold_cong_2 override_on_def)
  moreover have "finite (P.dom (parent s))"
    using assms(1, 3) finite_subset
    by (fastforce intro: G.E_finite vertices_finite)
  moreover have "finite ?S"
    using G.out_neighborhood_finite
    by simp
  moreover have "P.dom (parent s) \<inter> ?S = {}"
    by (auto simp add: P.dom_def discovered_def)
  ultimately show ?thesis
    by (simp add: card_Un_disjoint)
qed

lemma loop_dom_aux_2:
  assumes G_invar: "G.invar G"
  assumes queue_invar: "Q_invar (queue s)"
  assumes cond: "cond s"
  assumes dom_parent_subset_V: "P.dom (parent s) \<subseteq> G.V G"
  shows
    "card (G.V G) +
     length (Q_list (Q_tail (queue s))) -
     card (P.dom (parent s)) <
     card (G.V G) +
     length (Q_list (queue s)) -
     card (P.dom (parent s))"
proof -
  have "Q_list (queue s) \<noteq> []"
    using queue_invar cond
    by (intro list_queue_non_empty)
  hence "length (Q_list (Q_tail (queue s))) < length (Q_list (queue s))"
    using queue_invar
    by (simp add: Q.list_tail)
  moreover have "card (P.dom (parent s)) \<le> card (G.V G)"
    using G_invar dom_parent_subset_V
    by (intro G.E_finite vertices_finite card_mono)
  ultimately show ?thesis
    by simp
qed

lemma loop_dom:
  assumes "G.invar G"
  assumes "Q_invar (queue s)"
  assumes "P_invar (parent s)"
  assumes "set (Q_list (queue s)) \<subseteq> G.V G"
  assumes "P.dom (parent s) \<subseteq> G.V G"
  shows "loop_dom (G, src, s)"
  using assms
proof (induct "card (G.V G) + length (Q_list (queue s)) - card (P.dom (parent s))"
       arbitrary: s
       rule: less_induct)
  case less
  show ?case
  proof (cases "cond s")
    case True
    let ?u = "Q_head (queue s)"
    let ?q = "Q_tail (queue s)"
    let ?S = "set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"

    have "length (Q_list (queue (fold G src s))) = length (Q_list ?q) + card ?S"
      using less.prems(1-3) True G.out_neighborhood_distinct
      by (simp add: list_queue_fold_cong_2 distinct_card[symmetric])
    moreover have "card (P.dom (parent (fold G src s))) = card (P.dom (parent s)) + card ?S"
      using less.prems(1, 3, 5)
      by (intro loop_dom_aux)
    ultimately have
      "card (G.V G) + length (Q_list (queue (fold G src s))) - card (P.dom (parent (fold G src s))) =
       card (G.V G) + length (Q_list ?q) + card ?S - (card (P.dom (parent s)) + card ?S)"
      by presburger
    also have "... = card (G.V G) + length (Q_list ?q) - card (P.dom (parent s))"
      by simp
    also have "... < card (G.V G) + length (Q_list (queue s)) - card (P.dom (parent s))"
      using less.prems True
      by (intro loop_dom_aux_2)
    finally have
      "card (G.V G) + length (Q_list (queue (fold G src s))) - card (P.dom (parent (fold G src s))) <
       card (G.V G) + length (Q_list (queue s)) - card (P.dom (parent s))"
      .
    thus ?thesis
      using less.prems
      by (intro queue_fold_invar_2 parent_fold_invar_2 queue_fold_subset_V dom_parent_fold_subset_V_2 less.hyps loop.domintros)
  next
    case False
    thus ?thesis
      by (blast intro: loop.domintros)
  qed
qed

end

section \<open>Invariants\<close>

locale bfs_invar_tbd = bfs where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc
  for
    Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
    P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
    Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" +
  fixes G :: 'n
  fixes src :: 'a
  assumes G_invar: "G.invar G"
  assumes src_mem_V: "src \<in> G.V G"
begin

subsection \<open>Convenience Lemmas\<close>

lemma E_finite:
  shows "finite (G.E G)"
  using G_invar
  by (intro G.E_finite)

subsection \<open>\<close>

abbreviation white :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "white s v \<equiv> \<not> discovered src s v"

abbreviation gray :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "gray s v \<equiv> discovered src s v \<and> v \<in> set (Q_list (queue s))"

abbreviation black :: "('q, 'm) state \<Rightarrow> 'a \<Rightarrow> bool" where
  "black s v \<equiv> discovered src s v \<and> v \<notin> set (Q_list (queue s))"

lemma gray_imp_not_white:
  assumes "gray s v"
  shows "\<not> white s v"
  using assms
  by simp

lemma black_imp_not_white:
  assumes "black s v"
  shows "\<not> white s v"
  using assms
  by simp

lemma vertex_color_induct [case_names white gray black]:
  assumes "white s v \<Longrightarrow> P s v"
  assumes "gray s v \<Longrightarrow> P s v"
  assumes "black s v \<Longrightarrow> P s v"
  shows "P s v"
  using assms
  by blast

end

locale bfs_invar =
  bfs_invar_tbd where P_update = P_update and Q_snoc = Q_snoc +
  parent "P_lookup (parent s)"
  for
    P_update :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
    Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
    s :: "('q, 'm) state" +
  assumes queue_invar: "Q_invar (queue s)"
  assumes queue_distinct: "distinct (Q_list (queue s))"
  assumes parent_invar: "P_invar (parent s)"
  assumes parent_src: "P_lookup (parent s) src = None"
  assumes gray_if_mem_queue: "v \<in> set (Q_list (queue s)) \<Longrightarrow> gray s v"
  assumes black_if_mem_ran: "v \<in> P.ran (parent s) \<Longrightarrow> black s v"
  assumes queue_sorted_wrt_dpath_length:
    "sorted_wrt (\<lambda>u v. dpath_length (rev (follow u)) \<le> dpath_length (rev (follow v))) (Q_list (queue s))"
  assumes tbd_dpath_length:
    "\<not> Q_is_empty (queue s) \<Longrightarrow>
     dpath_length (rev (follow (last (Q_list (queue s))))) \<le> dpath_length (rev (follow (Q_head (queue s)))) + 1"
  assumes not_white_imp_shortest_dpath:
    "\<not> white s v \<Longrightarrow> is_shortest_dpath G (rev (follow v)) src v"
  assumes black_imp_out_neighborhood_not_white: "black s v \<Longrightarrow> \<forall>w\<in>set (G.out_neighborhood G v). \<not> white s w"
begin

subsection \<open>Convenience Lemmas\<close>

lemma queue_subset_V:
  shows "set (Q_list (queue s)) \<subseteq> G.V G"
  using gray_if_mem_queue not_white_imp_shortest_dpath
  by (fastforce intro: dpath_bet_endpoints(2))

lemma head_queue_mem_V:
  assumes "cond s"
  shows "Q_head (queue s) \<in> G.V G"
  using queue_invar assms queue_subset_V
  by (intro head_queue_mem_V)

lemma list_queue_fold_cong:
  assumes "cond s"
  shows
    "Q_list (queue (fold G src s)) =
     Q_list (Q_tail (queue s)) @
     filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s)))"
  using G_invar queue_invar parent_invar assms
  by (intro list_queue_fold_cong_2)

lemma lookup_parent_fold_cong:
  shows
    "P_lookup (parent (fold G src s)) =
     override_on
      (P_lookup (parent s))
      (\<lambda>_. Some (Q_head (queue s)))
      (set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s)))))"
  using G_invar parent_invar
  by (intro lookup_parent_fold_cong_2)

lemma T_fold_cong:
  shows
    "T (fold G src s) =
     T s \<union>
     {(Q_head (queue s), v) |v.
      v \<in> set (G.out_neighborhood G (Q_head (queue s))) \<and> \<not> discovered src s v}"
  using G_invar parent_invar
  by (intro T_fold_cong_2)

lemma src_not_white:
  shows "\<not> white s src"
  by (simp add: discovered_def)

lemma mem_queue_imp_dpath_length_head_queue:
  assumes "v \<in> set (Q_list (queue s))"
  shows "dpath_length (rev (follow (Q_head (queue s)))) \<le> dpath_length (rev (follow v))"
proof (cases "v = Q_head (queue s)")
  case True
  thus ?thesis
    by simp
next
  case False
  have "\<not> Q_is_empty (queue s)"
    using queue_invar assms
    by (auto simp add: Q.is_empty)
  moreover hence "Q_head (queue s) = hd (Q_list (queue s))"
    using queue_invar Q.list_head
    by (simp add: Q.is_empty)
  ultimately show ?thesis
    using queue_sorted_wrt_dpath_length assms False sorted_wrt_imp_hd
    by fastforce
qed

lemma mem_queue_imp_dist_head_queue:
  assumes "v \<in> set (Q_list (queue s))"
  shows "dist G src (Q_head (queue s)) \<le> dist G src v"
proof -
  have "Q_list (queue s) \<noteq> []"
    using assms
    by fastforce
  hence "Q_head (queue s) \<in> set (Q_list (queue s))"
    using queue_invar
    by (simp add: Q.list_head)
  hence "dist G src (Q_head (queue s)) = dpath_length (rev (follow (Q_head (queue s))))"
    using gray_if_mem_queue not_white_imp_shortest_dpath
    by force
  also have "... \<le> dpath_length (rev (follow v))"
    using assms
    by (auto intro: mem_queue_imp_dpath_length_head_queue)
  also have "... = dist G src v"
    using assms gray_if_mem_queue
    by (simp add: not_white_imp_shortest_dpath)
  finally show ?thesis
    .
qed

lemma mem_queue_imp_dpath_length_last_queue:
  assumes "v \<in> set (Q_list (queue s))"
  shows "dpath_length (rev (follow v)) \<le> dpath_length (rev (follow (last (Q_list (queue s)))))"
proof (cases "v = last (Q_list (queue s))")
  case True
  thus ?thesis
    by simp
next
  case False
  have "\<not> Q_is_empty (queue s)"
    using queue_invar assms
    by (auto simp add: Q.is_empty)
  thus ?thesis
    using queue_sorted_wrt_dpath_length assms False sorted_wrt_imp_last
    by fastforce
qed

lemma mem_queue_imp_dist_last_queue:
  assumes "v \<in> set (Q_list (queue s))"
  shows "dist G src v \<le> dist G src (last (Q_list (queue s)))"
proof -
  have list_queue_non_empty: "Q_list (queue s) \<noteq> []"
    using assms
    by fastforce
  have "dist G src v = dpath_length (rev (follow v))"
    using assms gray_if_mem_queue not_white_imp_shortest_dpath
    by force
  also have "... \<le> dpath_length (rev (follow (last (Q_list (queue s)))))"
    using assms
    by (auto intro: mem_queue_imp_dpath_length_last_queue)
  also have "... = dist G src (last (Q_list (queue s)))"
    using list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_shortest_dpath)
  finally show ?thesis
    .
qed

lemma mem_queue_dpath_lengthI:
  assumes "v \<in> set (Q_list (queue s))"
  shows
    "dpath_length (rev (follow (Q_head (queue s)))) \<le> dpath_length (rev (follow v))"
    "dpath_length (rev (follow v)) \<le> dpath_length (rev (follow (last (Q_list (queue s)))))"
  using assms
  by (auto intro: mem_queue_imp_dpath_length_head_queue mem_queue_imp_dpath_length_last_queue)

lemma mem_queue_distI:
  assumes "v \<in> set (Q_list (queue s))"
  shows
    "dist G src (Q_head (queue s)) \<le> dist G src v"
    "dist G src v \<le> dist G src (last (Q_list (queue s)))"
  using assms
  by (auto intro: mem_queue_imp_dist_head_queue mem_queue_imp_dist_last_queue)

subsection \<open>Basic Lemmas\<close>

lemma parent_imp_edge:
  assumes "P_lookup (parent s) v = Some u"
  shows "(u, v) \<in> (G.E G)"
proof -
  have "rev (follow v) = rev (follow u) @ [v]"
    using assms
    by (simp add: follow_psimps)
  moreover have "rev (follow u) = (rev (tl (follow u))) @ [u]"
    using follow_non_empty hd_Cons_tl follow_ConsD rev.simps(2)
    by metis
  ultimately have "rev (follow v) = rev (tl (follow u)) @ [u, v]"
    by simp
  moreover have "dpath_bet (G.E G) (rev (follow v)) src v"
    using assms not_white_imp_shortest_dpath
    thm discovered_def
    by (simp add: discovered_def)
  ultimately have "dpath_bet (G.E G) (rev (tl (follow u)) @ [u, v]) src v"
    by simp
  thus ?thesis
    by (auto simp add: edge_iff_dpath_bet intro: split_dpath)
qed

lemma dom_parent_subset_V:
  shows "P.dom (parent s) \<subseteq> G.V G"
proof
  fix v
  assume "v \<in> P.dom (parent s)"
  then obtain u where
    "P_lookup (parent s) v = Some u"
    by (auto simp add: P.dom_def)
  hence "(u, v) \<in> (G.E G)"
    by (intro parent_imp_edge)
  thus "v \<in> G.V G"
    by (intro G.edgeI(2))
qed

lemma queue_sorted_wrt_dist:
  shows "sorted_wrt (\<lambda>u v. dist G src u \<le> dist G src v) (Q_list (queue s))"
proof -
  have "\<forall>v\<in>set (Q_list (queue s)). dpath_length (rev (follow v)) = dist G src v"
    using gray_if_mem_queue not_white_imp_shortest_dpath
    by blast
  hence
    "\<And>u v. u \<in> set (Q_list (queue s)) \<Longrightarrow>
            v \<in> set (Q_list (queue s)) \<Longrightarrow>
            dpath_length (rev (follow u)) \<le> dpath_length (rev (follow v)) \<Longrightarrow>
            (\<lambda>u v. dist G src u \<le> dist G src v) u v"
    by (simp add: enat_ord_simps(1)[symmetric])
  thus ?thesis
    using queue_sorted_wrt_dpath_length sorted_wrt_mono_rel[of "(Q_list (queue s))"]
    by presburger
qed

lemma tbd_dist:
  assumes "\<not> Q_is_empty (queue s)"
  shows "dist G src (last (Q_list (queue s))) \<le> dist G src (Q_head (queue s)) + 1"
proof -
  have "\<forall>v\<in>set (Q_list (queue s)). dpath_length (rev (follow v)) = dist G src v"
    using gray_if_mem_queue not_white_imp_shortest_dpath
    by blast
  moreover have
    "last (Q_list (queue s)) \<in> set (Q_list (queue s))"
    "Q_head (queue s) \<in> set (Q_list (queue s))"
    using queue_invar assms
    by (simp_all add: Q.is_empty Q.list_head)
  ultimately show ?thesis
    using assms tbd_dpath_length
    unfolding enat_ord_simps(1)[symmetric] plus_enat_simps(1)[symmetric] one_enat_def[symmetric]
    by simp
qed

lemma white_imp_gray_ancestor:
  assumes "dpath_bet (G.E G) p u v"
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
    have "dpath_bet (G.E G) (l @ [w]) u w"
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
    have "v \<in> set (G.out_neighborhood G w)"
      using "3.prems"(1)
      by (auto simp add: dpath_bet_def G.mem_out_neighborhood_iff_edge intro: dpath_snoc_edge_2)
    hence "\<not> white s v"
      using black black_imp_out_neighborhood_not_white
      by blast
    thus ?thesis
      using "3.prems"(3)
      by simp
  qed
qed

lemma white_imp_dist_ge_case_1_subcase_3:
  assumes IH:
    "\<And>v. \<lbrakk> dpath_bet (G.E G) (l @ [u]) src v \<and> dpath_length (l @ [u]) = dist G src v; white s v \<rbrakk> \<Longrightarrow>
          (if Q_is_empty (queue s) then \<infinity> else dist G src (last (Q_list (queue s)))) \<le> dist G src v"
  assumes shortest_dpath: "is_shortest_dpath G (l @ [u, u']) src v"
  assumes white: "white s v"
  shows "(if Q_is_empty (queue s) then \<infinity> else dist G src (last (Q_list (queue s)))) \<le> dist G src v"
proof (induct s u rule: vertex_color_induct)
  case white
  have l_Q_snoc_u_shortest_dpath: "is_shortest_dpath G (l @ [u]) src u"
    using G_invar shortest_dpath
    by
      (auto
        simp add: dpath_length_eq_dpath_weight dist_eq_\<delta> is_shortest_dpath_def[symmetric]
        intro: G.E_finite shortest_dpath_prefix_is_shortest_dpath)
  hence "(if Q_is_empty (queue s) then \<infinity> else dist G src (last (Q_list (queue s)))) \<le> dist G src u"
    using white
    by (intro IH)
  also have "... = dpath_length (l @ [u])"
    by (simp add: l_Q_snoc_u_shortest_dpath)
  also have "... \<le> dpath_length (l @ [u, u'])"
    using dpath_length_append[where ?p = "l @ [u]" and ?q = "[u']"]
    by simp
  also have "... = dist G src v"
    by (simp add: shortest_dpath)
  finally show ?case
    .
next
  case gray
  hence "\<exists>v\<in>set (l @ [u, u']). gray s v"
    using src_not_white shortest_dpath white
    by (blast intro: white_imp_gray_ancestor)
  hence queue_non_empty: "\<not> Q_is_empty (queue s)"
    using queue_invar
    by (auto simp add: Q.is_empty)
  hence "dist G src (last (Q_list (queue s))) \<le> dist G src (Q_head (queue s)) + 1"
    by (intro tbd_dist)
  also have "... \<le> dist G src u + 1"
    using gray
    by (blast intro: mem_queue_imp_dist_head_queue add_right_mono)
  also have "... = dist G src v"
    using G_invar shortest_dpath
    by (auto intro: G.E_finite shortest_dpathE_2)
  finally show ?case
    using queue_non_empty
    by simp
next
  case black
  have "v \<in> set (G.out_neighborhood G u)"
    using shortest_dpath
    by (auto simp add: dpath_bet_def G.mem_out_neighborhood_iff_edge intro: dpath_snoc_edge_2)
  hence "\<not> white s v"
    using black black_imp_out_neighborhood_not_white
    by blast
  thus ?case
    using white
    by simp
qed

lemma white_imp_dist_ge:
  assumes "white s v"
  shows "(if Q_is_empty (queue s) then \<infinity> else dist G src (last (Q_list (queue s)))) \<le> dist G src v"
proof (cases "reachable (G.E G) src v")
  case True
  then obtain p where
    "dpath_bet (G.E G) p src v \<and> dpath_length p = dist G src v"
    using E_finite
    by (elim dist_dpath_betE) simp+
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
  hence "dist G src v = \<infinity>"
    unfolding dist_eq_\<delta>
    by (meson \<delta>_reachable_conv)
  thus ?thesis
    by simp
qed

end

abbreviation (in bfs) bfs_invar_tbd' :: "'n \<Rightarrow> 'a \<Rightarrow> bool"  where
  "bfs_invar_tbd' G src \<equiv>
   bfs_invar_tbd
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update P_update Q_snoc G src"

abbreviation (in bfs) bfs_invar' :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> bool"  where
  "bfs_invar' G src s \<equiv>
   bfs_invar
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    Map_update G src P_update Q_snoc s"

abbreviation (in bfs_invar_tbd) bfs_invar'' :: "('q, 'm) state \<Rightarrow> bool"  where
  "bfs_invar'' \<equiv> bfs_invar' G src"

subsection \<open>@{term bfs.init}\<close>

subsubsection \<open>\<close>

lemma (in bfs_invar_tbd) follow_invar'_parent_init:
  shows "follow_invar' (P_lookup (parent (init src)))"
  using wf_empty
  by (simp add: init_def P.map_empty follow_invar'_def)

lemma (in bfs_invar_tbd) parent_init:
  shows "Tbd.parent (P_lookup (parent (init src)))"
  using follow_invar'_parent_init
  by unfold_locales

subsubsection \<open>@{thm bfs_invar.queue_invar}\<close>

lemma (in bfs_invar_tbd) queue_invar_init:
  shows "Q_invar (queue (init src))"
  using Q.invar_empty
  by (auto simp add: init_def intro: Q.invar_snoc)

subsubsection \<open>@{thm bfs_invar.queue_distinct}\<close>

lemma (in bfs_invar_tbd) queue_distinct_init:
  shows "distinct (Q_list (queue (init src)))"
  using Q.invar_empty
  by (simp add: init_def Q.list_snoc Q.list_empty)

subsubsection \<open>@{thm bfs_invar.parent_invar}\<close>

lemma (in bfs_invar_tbd) parent_invar_init:
  shows "P_invar (parent (init src))"
  using P.map_specs(4)
  by (simp add: init_def)

subsubsection \<open>@{thm bfs_invar.parent_src}\<close>

lemma (in bfs_invar_tbd) parent_src_init:
  shows "P_lookup (parent (init src)) src = None"
  by (simp add: init_def P.map_empty)

subsubsection \<open>@{thm bfs_invar.gray_if_mem_queue}\<close>

lemma (in bfs_invar_tbd) gray_if_mem_queue_init:
  assumes "v \<in> set (Q_list (queue (init src)))"
  shows "gray (init src) v"
  using assms Q.invar_empty
  by (simp add: init_def Q.list_snoc Q.list_empty discovered_def)

subsubsection \<open>@{thm bfs_invar.black_if_mem_ran}\<close>

lemma (in bfs_invar_tbd) black_if_mem_ran_init:
  assumes "v \<in> P.ran (parent (init src))"
  shows "black (init src) v"
  using assms
  by (simp add: init_def P.ran_def P.map_empty)

subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_dpath_length}\<close>

lemma (in bfs_invar_tbd) queue_sorted_wrt_dpath_length_init:
  shows
    "sorted_wrt
      (\<lambda>u v. dpath_length (rev (parent.follow (P_lookup (parent (init src))) u)) \<le>
             dpath_length (rev (parent.follow (P_lookup (parent (init src))) v)))
      (Q_list (queue (init src)))"
  using Q.invar_empty
  by (simp add: init_def Q.list_snoc Q.list_empty)

subsubsection \<open>@{thm bfs_invar.tbd_dpath_length}\<close>

lemma (in bfs_invar_tbd) tbd_dpath_length_init:
  assumes "\<not> Q_is_empty (queue (init src))"
  shows
    "dpath_length (rev (parent.follow (P_lookup (parent (init src))) (last (Q_list (queue (init src)))))) \<le>
     dpath_length (rev (parent.follow (P_lookup (parent (init src))) (Q_head (queue (init src))))) + 1"
  using Q.invar_empty queue_invar_init
  by (simp add: init_def Q.list_snoc Q.list_empty Q.list_head)

subsubsection \<open>@{thm bfs_invar.not_white_imp_shortest_dpath}\<close>

lemma (in bfs_invar_tbd) not_white_imp_shortest_dpath_init:
  assumes "\<not> white (init src) v"
  shows "is_shortest_dpath G (rev (parent.follow (P_lookup (parent (init src))) v)) src v"
proof -
  have dpath_bet: "dpath_bet (G.E G) [src] src src"
    using src_mem_V
    by (auto intro: dpath_bet_reflexive)
  have "dpath_length [src] = 0"
    by simp
  also have "... \<le> dist G src src"
    using zero_le
    by (subst zero_enat_def[symmetric])
  finally have "dpath_length [src] \<le> dist G src src"
    .
  hence "dpath_length [src] = dist G src src"
    using E_finite dpath_bet
    by (intro dist_le_dpath_length antisym)
  moreover have "v = src"
    using assms
    by (simp add: discovered_def init_def P.map_empty)
  moreover have "rev (parent.follow (P_lookup (parent (init src))) src) = [src]"
    using parent_init
    by (simp add: parent_src_init parent.follow_psimps)
  ultimately show ?thesis
    using dpath_bet
    by simp
qed

subsubsection \<open>@{thm bfs_invar.black_imp_out_neighborhood_not_white}\<close>

lemma (in bfs_invar_tbd) black_imp_out_neighborhood_not_white_init:
  assumes "black (init src) v"
  shows "\<forall>w\<in>set (G.out_neighborhood G v). \<not> white (init src) w"
proof -
  have "v = src"
    using assms
    by (simp add: discovered_def init_def P.map_empty)
  moreover have "src \<in> set (Q_list (queue (init src)))"
    using Q.invar_empty
    by (simp add: init_def Q.list_snoc)
  ultimately show ?thesis
    using assms
    by blast
qed

subsubsection \<open>\<close>

lemma (in bfs_invar_tbd) bfs_invar_init:
  shows "bfs_invar'' (init src)"
  using bfs_axioms
  using follow_invar'_parent_init
  using queue_invar_init queue_distinct_init parent_invar_init parent_src_init
  using gray_if_mem_queue_init black_if_mem_ran_init queue_sorted_wrt_dpath_length_init tbd_dpath_length_init
  using not_white_imp_shortest_dpath_init black_imp_out_neighborhood_not_white_init
  by unfold_locales

subsection \<open>@{term bfs.fold}\<close>

subsubsection \<open>Convenience Lemmas\<close>

lemma (in bfs_invar) list_queue_non_empty:
  assumes "cond s"
  shows "Q_list (queue s) \<noteq> []"
  using queue_invar assms
  by (intro list_queue_non_empty)

lemma (in bfs_invar) head_queue_imp:
  assumes "cond s"
  shows
    "Q_head (queue s) \<in> set (Q_list (queue s))"
    "Q_head (queue s) \<notin> set (Q_list (queue (fold G src s)))"
proof -
  let ?u = "Q_head (queue s)"
  show "?u \<in> set (Q_list (queue s))"
    using queue_invar assms list_queue_non_empty
    by (simp add: Q.list_head)
  hence "?u \<notin> set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
    using gray_if_mem_queue
    by fastforce
  moreover have "?u \<notin> set (Q_list (Q_tail (queue s)))"
    using queue_distinct
    by (simp add: Q.list_queue[OF queue_invar list_queue_non_empty[OF assms]])
  ultimately show "?u \<notin> set (Q_list (queue (fold G src s)))"
    using assms
    by (simp add: list_queue_fold_cong)
qed

lemma (in bfs_invar) head_queue_if:
  assumes "cond s"
  assumes "v \<in> set (Q_list (queue s))"
  assumes "v \<notin> set (Q_list (queue (fold G src s)))"
  shows "v = Q_head (queue s)"
proof -
  have "Q_list (queue s) = Q_head (queue s) # Q_list (Q_tail (queue s))"
    using queue_invar assms(1)
    by (intro list_queue_non_empty Q.list_queue)
  thus ?thesis
    using assms
    by (simp add: list_queue_fold_cong)
qed

lemma (in bfs_invar) head_queue_iff:
  assumes "cond s"
  shows "v = Q_head (queue s) \<longleftrightarrow> v \<in> set (Q_list (queue s)) \<and> v \<notin> set (Q_list (queue (fold G src s)))"
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
  shows "\<not> white (fold G src s) v"
  using assms
  by (auto simp add: discovered_def lookup_parent_fold_cong)

lemma (in bfs_invar) white_not_white_fold_imp:
  assumes "white s v"
  assumes "\<not> white (fold G src s) v"
  shows
    "v \<in> set (G.out_neighborhood G (Q_head (queue s)))"
    "P_lookup (parent (fold G src s)) v = Some (Q_head (queue s))"
proof -
  show "v \<in> set (G.out_neighborhood G (Q_head (queue s)))"
    using assms G.out_neighborhood_finite
    by (fastforce simp add: discovered_def lookup_parent_fold_cong)
  thus "P_lookup (parent (fold G src s)) v = Some (Q_head (queue s))"
    using assms G.out_neighborhood_finite
    by (auto simp add: lookup_parent_fold_cong)
qed

subsubsection \<open>\<close>

lemma (in bfs_invar) follow_invar'_parent_fold:
  assumes "cond s"
  shows "follow_invar' (P_lookup (parent (fold G src s)))"
  unfolding follow_invar'_def T_fold_cong
proof (rule wf_Un)
  let ?r =
    "{(Q_head (queue s), v) |v.
      v \<in> set (G.out_neighborhood G (Q_head (queue s))) \<and> \<not> discovered src s v}"
  show "wf (T s)"
    using follow_invar'
    by (simp add: follow_invar'_def)
  have "gray s (Q_head (queue s))"
    using assms
    by (intro head_queue_imp(1) gray_if_mem_queue) simp+
  thus "wf ?r"
    by (simp add: wf_def)
  show "Domain (T s) \<inter> Range ?r = {}"
    using black_if_mem_ran
    by (auto simp add: P.ran_def)
qed

lemma (in bfs_invar) parent_fold:
  assumes "cond s"
  shows "Tbd.parent (P_lookup (parent (fold G src s)))"
  using assms
  by unfold_locales (intro follow_invar'_parent_fold)

subsubsection \<open>@{thm bfs_invar.queue_invar}\<close>

lemma (in bfs_invar) queue_invar_fold:
  assumes "cond s"
  shows "Q_invar (queue (fold G src s))"
  using G_invar queue_invar assms
  by (intro queue_fold_invar_2)

subsubsection \<open>@{thm bfs_invar.queue_distinct}\<close>

lemma (in bfs_invar) queue_distinct_fold:
  assumes "cond s"
  shows "distinct (Q_list (queue (fold G src s)))"
proof -
  let ?l1 = "Q_list (Q_tail (queue s))"
  let ?l2 = "filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s)))"
  have list_queue_non_empty: "Q_list (queue s) \<noteq> []"
    using assms
    by (intro list_queue_non_empty)
  hence "\<And>v. v \<in> set ?l1 \<Longrightarrow> \<not> white s v"
    using gray_if_mem_queue queue_invar
    by (auto simp add: Q.list_tail intro: list.set_sel(2))
  hence "set ?l1 \<inter> set ?l2 = {}"
    by fastforce
  moreover have "distinct ?l1"
    using queue_distinct queue_invar list_queue_non_empty
    by (auto simp add: Q.list_tail intro: distinct_tl)
  moreover have "distinct ?l2"
    using G_invar
    by (intro G.out_neighborhood_distinct distinct_filter)
  ultimately show ?thesis
    using assms
    by (simp add: list_queue_fold_cong)
qed

subsubsection \<open>@{thm bfs_invar.parent_invar}\<close>

lemma (in bfs_invar) parent_invar_fold:
  shows "P_invar (parent (fold G src s))"
  using G_invar parent_invar
  by (intro parent_fold_invar_2)

subsubsection \<open>@{thm bfs_invar.parent_src}\<close>

lemma (in bfs_invar) parent_src_fold:
  shows "P_lookup (parent (fold G src s)) src = None"
  using G_invar parent_invar src_not_white
  by (simp add: lookup_parent_fold_cong_2 parent_src)

subsubsection \<open>@{thm bfs_invar.gray_if_mem_queue}\<close>

lemma (in bfs_invar) gray_if_mem_queue_fold:
  assumes cond: "cond s"
  assumes mem_queue_fold: "v \<in> set (Q_list (queue (fold G src s)))"
  shows "gray (fold G src s) v"
proof (cases "v \<in> set (Q_list (queue s))")
  case True
  hence "gray s v"
    by (intro gray_if_mem_queue)
  thus ?thesis
    using cond not_white_imp_not_white_fold mem_queue_fold
    by blast
next
  case False
  have "Q_list (queue s) \<noteq> []"
    using cond
    by (intro list_queue_non_empty)
  hence "v \<notin> set (Q_list (Q_tail (queue s)))"
    using False queue_invar
    by (auto simp add: Q.list_tail intro: list.set_sel(2))
  hence "v \<in> set (G.out_neighborhood G (Q_head (queue s))) \<and> \<not> discovered src s v"
    using mem_queue_fold cond
    by (simp add: list_queue_fold_cong)
  hence "\<not> white (fold G src s) v"
    using assms(1)
    by (fastforce simp add: discovered_def lookup_parent_fold_cong)
  thus ?thesis
    using mem_queue_fold
    by blast
qed

subsubsection \<open>@{thm bfs_invar.black_if_mem_ran}\<close>

lemma (in bfs_invar) head_queue_if_2:
  assumes "v \<notin> P.ran (parent s)"
  assumes "v \<in> P.ran (parent (fold G src s))"
  shows "v = Q_head (queue s)"
  using assms G_invar parent_invar
  by (auto simp add: ran_parent_fold_cong split: if_splits(2))

lemma (in bfs_invar) black_if_mem_ran_fold:
  assumes cond: "cond s"
  assumes mem_ran_fold: "v \<in> P.ran (parent (fold G src s))"
  shows "black (fold G src s) v"
proof (cases "v \<in> P.ran (parent s)")
  case True
  show ?thesis
  proof (rule ccontr)
    assume assm: "\<not> black (fold G src s) v"
    have black: "black s v"
      using True
      by (intro black_if_mem_ran)
    hence not_white_fold: "\<not> white (fold G src s) v"
      by (intro black_imp_not_white not_white_imp_not_white_fold)
    have "Q_list (queue s) \<noteq> []"
      using cond
      by (intro list_queue_non_empty)
    hence "v \<notin> set (Q_list (Q_tail (queue s)))"
      using black queue_invar
      by (auto simp add: Q.list_tail intro: list.set_sel(2))
    moreover have "v \<in> set (Q_list (queue (fold G src s)))"
      using assm not_white_fold
      by blast
    ultimately have "white (fold G src s) v"
      using cond black
      by (simp add: discovered_def list_queue_fold_cong)
    thus "False"
      using not_white_fold
      by blast
  qed
next
  case False
  have v_eq_Q_head_queue: "v = Q_head (queue s)"
    using queue_invar False mem_ran_fold
    by (intro head_queue_if_2)
  then have "v \<in> set (Q_list (queue s))"
    using cond
    by (blast intro: head_queue_imp(1))
  hence "\<not> white s v"
    by (intro gray_if_mem_queue gray_imp_not_white)
  hence "\<not> white (fold G src s) v"
    by (intro not_white_imp_not_white_fold)
  moreover have "v \<notin> set (Q_list (queue (fold G src s)))"
    unfolding v_eq_Q_head_queue
    using cond
    by (intro head_queue_imp(2))
  ultimately show ?thesis
    by blast
qed

subsubsection \<open>@{thm bfs_invar.queue_sorted_wrt_dpath_length}\<close>

lemma (in bfs_invar) not_white_imp_rev_follow_fold_eq_rev_follow:
  assumes "cond s"
  assumes "\<not> white s v"
  shows "rev (parent.follow (P_lookup (parent (fold G src s))) v) = rev (follow v)"
  using assms
proof (induct v rule: follow.pinduct[OF follow_dom])
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
      "rev (follow v) = [v]"
      "rev (parent.follow (P_lookup (parent (fold G src s))) v) = [v]"
      using "1.prems"(1) parent_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      by fastforce
  next
    case False
    then obtain u where u:
      "P_lookup (parent s) v = Some u"
      "\<not> white s u"
      using False "1.prems"(2) black_if_mem_ran
      by (auto simp add: discovered_def P.ran_def)
    moreover hence "P_lookup (parent (fold G src s)) v = Some u"
      using "1.prems"(2)
      by (simp add: lookup_parent_fold_cong map_add_Some_iff)
    ultimately have
      "rev (follow v) = rev (follow u) @ [v]"
      "rev (parent.follow (P_lookup (parent (fold G src s))) v) =
       rev (parent.follow (P_lookup (parent (fold G src s))) u) @ [v]"
      using "1.prems"(1) parent_fold
      by (simp_all add: follow_psimps parent.follow_psimps)
    thus ?thesis
      using u "1.prems"(1)
      by (simp add: "1.hyps"(2))
  qed
qed

lemma (in bfs_invar) mem_filter_imp_dpath_length:
  assumes "cond s"
  assumes "v \<in> set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
  shows
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v)) =
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue s)))) + 1"
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue s))))) \<le>
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v))"
proof -
  let ?u = "Q_head (queue s)"
  have "P_lookup (parent (fold G src s)) v = Some ?u"
    using assms
    by (simp add: lookup_parent_fold_cong)
  hence
    "rev (parent.follow (P_lookup (parent (fold G src s))) v) =
     rev (parent.follow (P_lookup (parent (fold G src s))) ?u) @ [v]"
    using assms(1) parent_fold
    by (simp add: parent.follow_psimps)
  thus dpath_length_eq:
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v)) =
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue s)))) + 1"
    using assms(1) parent_fold parent.follow_non_empty
    by (fastforce simp add: dpath_length_snoc)

  have
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue s))))) =
     dpath_length (rev (follow (last (Q_list (queue s)))))"
    using assms list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow ?u)) + 1"
    using assms tbd_dpath_length
    by (simp add: cond_def)
  also have "... = dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) ?u)) + 1"
    using assms head_queue_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... = dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v))"
    unfolding dpath_length_eq
    ..
  finally show
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue s))))) \<le>
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v))"
    .
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold_aux:
  assumes cond: "cond s"
  assumes u_mem_Q_tail_queue: "u \<in> set (Q_list (Q_tail (queue s)))"
  assumes v_mem_filter:
    "v \<in> set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
  shows
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) u)) \<le>
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v))"
proof -
  have u_mem_queue: "u \<in> set (Q_list (queue s))"
    using u_mem_Q_tail_queue queue_invar cond list_queue_non_empty
    by (auto simp add: Q.list_tail intro: list.set_sel(2))
  have
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) u)) =
     dpath_length (rev (follow u))"
    using cond u_mem_queue gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow (last (Q_list (queue s)))))"
    using u_mem_queue
    by (intro mem_queue_imp_dpath_length_last_queue)
  also have "... = dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue s)))))"
    using cond list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v))"
    using cond v_mem_filter
    by (intro mem_filter_imp_dpath_length(2))
  finally show ?thesis
    .
qed

lemma (in bfs_invar) tbd_dpath_length_fold_aux:
  assumes cond: "cond s"
  assumes "\<not> Q_is_empty (queue (fold G src s))"
  shows
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue (fold G src s)))))) \<le>
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue s)))) + 1"
proof (cases "filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))) = []")
  case True
  hence list_tail_non_empty: "Q_list (Q_tail (queue s)) \<noteq> []"
    using assms G_invar queue_invar queue_fold_invar_2
    by (simp add: list_queue_fold_cong Q.is_empty)

  hence "last (Q_list (queue (fold G src s))) = last (Q_list (Q_tail (queue s)))"
    unfolding list_queue_fold_cong[OF cond] last_appendL[OF True]
    by blast
  hence "last (Q_list (queue (fold G src s))) = last (Q_list (queue s))"
    using list_tail_non_empty
    by (simp add: Q.list_queue[OF queue_invar list_queue_non_empty[OF assms(1)]])
  hence
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue (fold G src s)))))) =
     dpath_length (rev (follow (last (Q_list (queue s)))))"
    using cond list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow (Q_head (queue s)))) + 1"
    using queue_invar cond list_queue_non_empty tbd_dpath_length
    by (simp add: Q.is_empty)
  also have "... = dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue s)))) + 1"
    using cond head_queue_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  finally show ?thesis
    .
next
  case False
  hence
    "last (Q_list (queue (fold G src s))) \<in>
     set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
    unfolding list_queue_fold_cong[OF cond] last_appendR[OF False]
    by (intro last_in_set)
  with cond
  show ?thesis
    by (simp add: mem_filter_imp_dpath_length(1))
qed

lemma (in bfs_invar) tbd_dpath_length_fold_aux_2:
  assumes cond: "cond s"
  assumes "\<not> Q_is_empty (queue (fold G src s))"
  shows
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue s)))) \<le>
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue (fold G src s)))))"
proof (cases "Q_list (Q_tail (queue s)) = []")
  case True
  have "Q_head (queue (fold G src s)) = hd (Q_list (queue (fold G src s)))"
    using assms G_invar queue_invar queue_fold_invar_2
    by (simp add: Q.is_empty Q.list_head)
  hence
    "Q_head (queue (fold G src s)) =
     hd (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
    using cond True
    by (simp add: list_queue_fold_cong)
  moreover have
    "filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))) \<noteq> []"
    using assms G_invar queue_invar queue_fold_invar_2 True
    by (simp add: Q.is_empty list_queue_fold_cong)
  ultimately have Q_head_queue_fold_mem_filter:
    "Q_head (queue (fold G src s)) \<in>
     set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
    using list.set_sel(1)
    by metis

  have
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue s)))) =
     dpath_length (rev (follow (Q_head (queue s))))"
    using cond head_queue_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow (last (Q_list (queue s)))))"
    using cond
    by (intro head_queue_imp(1) mem_queue_imp_dpath_length_last_queue)
  also have
    "... = dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue s)))))"
    using cond list_queue_non_empty gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue (fold G src s)))))"
    using cond Q_head_queue_fold_mem_filter
    by (intro mem_filter_imp_dpath_length(2))
  finally show ?thesis
    .
next
  case False
  have "Q_head (queue (fold G src s)) = hd (Q_list (queue (fold G src s)))"
    using assms G_invar queue_invar queue_fold_invar_2
    by (simp add: Q.is_empty Q.list_head)
  hence "Q_head (queue (fold G src s)) = hd (Q_list (Q_tail (queue s)))"
    using cond False
    by (simp add: list_queue_fold_cong)
  hence Q_head_queue_fold_mem_list_queue: "Q_head (queue (fold G src s)) \<in> set (Q_list (queue s))"
    using False queue_invar cond list_queue_non_empty
    by (auto simp add: Q.list_tail intro: list.set_sel(2))

  have
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue s)))) =
     dpath_length (rev (follow (Q_head (queue s))))"
    using cond head_queue_imp(1) gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  also have "... \<le> dpath_length (rev (follow (Q_head (queue (fold G src s)))))"
    using Q_head_queue_fold_mem_list_queue
    by (intro mem_queue_imp_dpath_length_head_queue)
  also have "... = dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue (fold G src s)))))"
    using cond Q_head_queue_fold_mem_list_queue gray_if_mem_queue
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  finally show ?thesis
    .
qed

lemma (in bfs_invar) queue_sorted_wrt_dpath_length_fold:
  assumes "cond s"
  shows
    "sorted_wrt
      (\<lambda>u v. dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) u)) \<le>
             dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v)))
      (Q_list (queue (fold G src s)))"
proof -
  let ?P =
    "\<lambda>u v. dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) u)) \<le>
           dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v))"
  have list_queue_non_empty: "Q_list (queue s) \<noteq> []"
    using assms
    by (intro list_queue_non_empty)
  hence
    "sorted_wrt
      (\<lambda>u v. dpath_length (rev (follow u)) \<le> dpath_length (rev (follow v)))
      (Q_list (queue s))"
    using queue_invar queue_sorted_wrt_dpath_length
    by (simp add: Q.is_empty)
  hence "sorted_wrt ?P (Q_list (queue s))"
    using assms gray_if_mem_queue sorted_wrt_mono_rel[of "(Q_list (queue s))"]
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  hence "sorted_wrt ?P (Q_list (Q_tail (queue s)))"
    by (simp add: Q.list_queue[OF queue_invar list_queue_non_empty])
  moreover have
    "sorted_wrt
      ?P
      (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s))))"
    using assms
    by (auto simp add: mem_filter_imp_dpath_length(1) intro: sorted_wrt_if)
  moreover have
    "\<forall>u\<in>set (Q_list (Q_tail (queue s))).
      \<forall>v\<in>set (filter (Not \<circ> discovered src s) (G.out_neighborhood G (Q_head (queue s)))).
       dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) u)) \<le>
       dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v))"
    using assms
    by (blast intro: queue_sorted_wrt_dpath_length_fold_aux)
  ultimately show ?thesis 
    using assms
    by (simp add: list_queue_fold_cong sorted_wrt_append)
qed

lemma (in bfs_invar) tbd_dpath_length_fold:
  assumes "cond s"
  assumes "\<not> Q_is_empty (queue (fold G src s))"
  shows
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue (fold G src s)))))) \<le>
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue (fold G src s))))) + 1"
proof -
  have
    "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (last (Q_list (queue (fold G src s)))))) \<le>
     dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue s)))) + 1"
    using assms
    by (intro tbd_dpath_length_fold_aux)
  also have "... \<le> dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) (Q_head (queue (fold G src s))))) + 1"
    using assms
    by (auto intro: tbd_dpath_length_fold_aux_2)
  finally show ?thesis
    .
qed

subsubsection \<open>@{thm bfs_invar.not_white_imp_shortest_dpath}\<close>

lemma (in bfs_invar) not_white_imp_shortest_dpath_fold_case_1_subcase_3_aux:
  assumes cond: "cond s"
  assumes dist_less: "dist G src v < dist G src (Q_head (queue s)) + 1"
  assumes dpath_bet: "dpath_bet (G.E G) (l @ [u, u']) src v"
  assumes dpath_length: "dpath_length (l @ [u, u']) = dist G src v"
  assumes white: "white s v"
  shows "False"
proof -
  let ?u = "Q_head (queue s)"
  have "dist G src u + 1 = dist G src v"
    using E_finite dpath_bet dpath_length
    by (auto intro: shortest_dpathE_2)
  hence "dist G src u + 1 < dist G src ?u + 1"
    using dist_less
    by simp
  hence "dist G src u < dist G src ?u"
    unfolding plus_1_eSuc(2) eSuc_mono
    .
  thus ?thesis
  proof (induct s u rule: vertex_color_induct)
    case white
    have "dist G src ?u \<le> dist G src (last (Q_list (queue s)))"
      using cond list_queue_non_empty
      by (intro mem_queue_imp_dist_head_queue) simp
    also have "... \<le> dist G src u"
      using white.hyps cond white_imp_dist_ge
      by (simp add: cond_def)
    finally show ?case
      using white.prems
      by simp
  next
    case gray
    hence "dist G src ?u \<le> dist G src u"
      by (intro mem_queue_imp_dist_head_queue) simp
    thus ?case
      using gray.prems
      by simp
  next
    case black
    hence "v \<in> set (G.out_neighborhood G u)"
      using dpath_bet
      by (auto simp add: dpath_bet_def G.mem_out_neighborhood_iff_edge intro: dpath_snoc_edge_2)
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
  assumes reachable: "reachable (G.E G) src v"
  assumes v_mem_out_neighborhood: "v \<in> set (G.out_neighborhood G (Q_head (queue s)))"
  shows "dist G src (Q_head (queue s)) + 1 = dist G src v"
proof (rule antisym, rule ccontr, goal_cases)
  case 1
  let ?u = "Q_head (queue s)"
  assume "\<not> dist G src ?u + 1 \<le> dist G src v"
  hence "dist G src v < dist G src ?u + 1"
    by fastforce
  moreover obtain p where
    "dpath_bet (G.E G) p src v"
    "dpath_length p = dist G src v"
    using E_finite reachable
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
    with cond
    show ?case
      by (intro not_white_imp_shortest_dpath_fold_case_1_subcase_3_aux)
  qed
next
  case 2
  show ?case
    using cond head_queue_mem_V v_mem_out_neighborhood E_finite dist_triangle_inequality_edge
    by (simp add: G.mem_out_neighborhood_iff_edge)
qed

lemma (in bfs_invar) not_white_imp_shortest_dpath_fold:
  assumes cond: "cond s"
  assumes not_white_fold: "\<not> white (fold G src s) v"
  shows "is_shortest_dpath G (rev (parent.follow (P_lookup (parent (fold G src s))) v)) src v"
proof (cases "white s v", standard)
  let ?u = "Q_head (queue s)"
  case True
  hence
    v_mem_out_neighborhood: "v \<in> set (G.out_neighborhood G ?u)" and
    parent_fold_v_eq_head_queue: "P_lookup (parent (fold G src s)) v = Some ?u"
    using assms
    by (auto intro: white_not_white_fold_imp)
  have Q_head_queue_not_white: "\<not> white s ?u"
    using cond
    by (intro head_queue_imp(1) gray_if_mem_queue gray_imp_not_white)
  hence rev_follow_head_queue_shortest_dpath: "is_shortest_dpath G (rev (follow ?u)) src ?u"
    by (intro not_white_imp_shortest_dpath)
  have
    "rev (parent.follow (P_lookup (parent (fold G src s))) v) =
     rev (parent.follow (P_lookup (parent (fold G src s))) ?u) @ [v]"
    using cond parent_fold
    by (simp add: parent.follow_psimps parent_fold_v_eq_head_queue)
  hence rev_follow_fold_eq: "rev (parent.follow (P_lookup (parent (fold G src s))) v) = rev (follow ?u) @ [v]"
    using cond Q_head_queue_not_white
    by (simp add: not_white_imp_rev_follow_fold_eq_rev_follow)
  thus "dpath_bet (G.E G) (rev (parent.follow (P_lookup (parent (fold G src s))) v)) src v"
    using rev_follow_head_queue_shortest_dpath
    using v_mem_out_neighborhood dpath_bet_transitive
    by (fastforce simp add: G.mem_out_neighborhood_iff_edge edge_iff_dpath_bet)
  hence "reachable (G.E G) src v"
    by (auto simp add: reachable_iff_dpath_bet)
  with cond True
  have "dist G src v = dist G src ?u + 1"
    using True not_white_fold
    by (intro white_not_white_fold_imp(1) not_white_imp_shortest_dpath_fold_case_1_aux[symmetric])
  also have "... = dpath_length (rev (follow ?u)) + 1"
    unfolding plus_enat_simps(1)[symmetric]
    by (simp add: rev_follow_head_queue_shortest_dpath)
  also have "... = dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v))"
    using follow_non_empty
    by (simp add: rev_follow_fold_eq dpath_length_snoc)
  finally show "dpath_length (rev (parent.follow (P_lookup (parent (fold G src s))) v)) = dist G src v"
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
  assumes black_fold: "black (fold G src s) v"
  shows "\<forall>w\<in>set (G.out_neighborhood G v). \<not> white (fold G src s) w"
proof (induct s v rule: vertex_color_induct)
  case white
  hence "v \<in> set (G.out_neighborhood G (Q_head (queue s)))"
    using assms
    by (intro white_not_white_fold_imp(1)) simp+
  hence "v \<in> set (Q_list (queue (fold G src s)))"
    using white cond
    by (simp add: discovered_def list_queue_fold_cong)
  thus ?case
    using black_fold
    by blast
next
  case gray
  hence "v = Q_head (queue s)"
    using assms queue_invar
    by (intro head_queue_if) simp+
  thus ?case
    by (auto simp add: discovered_def lookup_parent_fold_cong override_on_def)
next
  case black
  hence "\<forall>w\<in>set (G.out_neighborhood G v). \<not> white s w"
    by (intro black_imp_out_neighborhood_not_white)
  thus ?case
    using not_white_imp_not_white_fold
    by blast
qed

subsubsection \<open>\<close>

lemma (in bfs_invar) bfs_invar_fold:
  assumes "cond s"
  shows "bfs_invar'' (fold G src s)"
  using assms
  using bfs_axioms
  using follow_invar'_parent_fold
  using queue_invar_fold queue_distinct_fold parent_invar_fold parent_src_fold
  using gray_if_mem_queue_fold black_if_mem_ran_fold queue_sorted_wrt_dpath_length_fold tbd_dpath_length_fold
  using not_white_imp_shortest_dpath_fold black_imp_out_neighborhood_not_white_fold
  by unfold_locales

subsection \<open>@{term bfs.loop}\<close>

lemma (in bfs) loop_psimps:
  assumes "bfs_invar' G src s"
  shows "loop G src s = (if cond s then loop G src (fold G src s) else s)"
proof -
  have "G.invar G"
    using assms
    by (intro bfs_invar.axioms(1) bfs_invar_tbd.G_invar)
  moreover have "Q_invar (queue s)"
    using assms
    by (intro bfs_invar.queue_invar)
  moreover have "P_invar (parent s)"
    using assms
    by (intro bfs_invar.parent_invar)
  moreover have "set (Q_list (queue s)) \<subseteq> G.V G"
    using assms
    by (intro bfs_invar.queue_subset_V)
  moreover have "P.dom (parent s) \<subseteq> G.V G"
    using assms
    by (intro bfs_invar.dom_parent_subset_V)
  ultimately show ?thesis
    by (metis loop_dom loop.psimps)
qed

lemma (in bfs) bfs_induct:
  assumes "bfs_invar' G src s"
  assumes "\<And>G src s. loop_dom (G, src, s) \<Longrightarrow> (cond s \<Longrightarrow> P G src (fold G src s)) \<Longrightarrow> P G src s"
  shows "P G src s"
proof -
  have "G.invar G"
    using assms(1)
    by (intro bfs_invar.axioms(1) bfs_invar_tbd.G_invar)
  moreover have "Q_invar (queue s)"
    using assms(1)
    by (intro bfs_invar.queue_invar)
  moreover have "P_invar (parent s)"
    using assms(1)
    by (intro bfs_invar.parent_invar)
  moreover have "set (Q_list (queue s)) \<subseteq> G.V G"
    using assms
    by (intro bfs_invar.queue_subset_V)
  moreover have "P.dom (parent s) \<subseteq> G.V G"
    using assms(1)
    by (intro bfs_invar.dom_parent_subset_V)
  ultimately show ?thesis
    using assms(2)
    by (blast intro: loop_dom loop.pinduct)
qed

lemma (in bfs) bfs_invar_loop:
  assumes "bfs_invar' G src s"
  shows "bfs_invar' G src (loop G src s)"
  using assms
proof (induct rule: bfs_induct[OF assms])
  case (1 G src s)
  thus ?case
    by (fastforce simp add: loop_psimps intro: bfs_invar.bfs_invar_fold)
qed

subsection \<open>@{term bfs}\<close>

lemma (in bfs_invar_tbd) bfs_invar_bfs:
  shows "bfs_invar'' (bfs G src)"
  using bfs_invar_init
  by (intro bfs_invar_loop)

section \<open>Correctness\<close>

lemma (in bfs_invar_tbd) soundness:
  assumes "bfs_invar'' s"
  assumes "discovered src (loop G src s) v"
  shows "is_shortest_dpath G (rev (parent.follow (P_lookup (parent (loop G src s))) v)) src v"
  using assms bfs_invar_loop bfs_invar.not_white_imp_shortest_dpath
  by fast

lemma (in bfs_invar_tbd) completeness:
  assumes "bfs_invar'' s"
  assumes "\<not> discovered src (loop G src s) v"
  shows "\<not> reachable (G.E G) src v"
  using assms
proof (induct rule: bfs_induct[OF assms(1)])
  case (1 G src s)
  show ?case
  proof (cases "cond s")
    case True
    thus ?thesis
      using "1.prems"
      by (intro bfs_invar.bfs_invar_fold "1.hyps"(2)) (simp_all add: loop_psimps)
  next
    case False
    hence "\<not> discovered src s v"
      using "1.prems"
      by (simp add: loop_psimps)
    from bfs_invar.white_imp_dist_ge[OF "1.prems"(1) this]
    have "dist G src v = \<infinity>"
      using "1.prems"(1) False bfs_invar.white_imp_dist_ge
      by (fastforce simp add: cond_def)
    thus ?thesis
      using dist_eq_\<delta> \<delta>_reachable_conv
      by metis
  qed
qed

abbreviation (in bfs) is_shortest_dpath_Map :: "'n \<Rightarrow> 'a \<Rightarrow> ('q, 'm) state \<Rightarrow> bool" where
  "is_shortest_dpath_Map G src s \<equiv>
   \<forall>v. 
    discovered src s v \<longrightarrow> is_shortest_dpath G (rev (parent.follow (P_lookup (parent s)) v)) src v \<and>
    \<not> discovered src s v \<longrightarrow> \<not> reachable (G.E G) src v"

lemma (in bfs_invar_tbd) correctness:
  assumes "bfs_invar'' s"
  shows "is_shortest_dpath_Map G src (loop G src s)"
  using assms soundness completeness
  by simp+

theorem (in bfs_invar_tbd) bfs_correct:
  shows "is_shortest_dpath_Map G src (bfs G src)"
  using bfs_invar_init correctness
  by simp+

corollary (in bfs) bfs_correct:
  assumes "bfs_invar_tbd' G src"
  shows "is_shortest_dpath_Map G src (bfs G src)"
  using assms
  by (intro bfs_invar_tbd.bfs_correct)

end