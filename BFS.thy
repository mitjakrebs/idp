theory BFS
  imports
    "Graph_Theory/Graph_Theory"
    Misc
    Queue_Specs
    Tbd
begin

record ('q, 'v) state =
  queue :: 'q
  distance :: "'v \<rightharpoonup> nat"
  parent :: "'v \<rightharpoonup> 'v"

locale bfs =
  finite_dgraph G +
  (* tbd where fold = fold + *)
  Queue where snoc = snoc
  for
    G :: "'v dgraph" and
    (* fold :: "('v \<Rightarrow> ('q, 'v) state \<Rightarrow> ('q, 'v) state) \<Rightarrow> 'v set \<Rightarrow> ('q, 'v) state \<Rightarrow> ('q, 'v) state" and *)
    snoc :: "'q \<Rightarrow> 'v \<Rightarrow> 'q" +
  fixes src :: 'v
  assumes src_in_V: "src \<in> dVs G"

section \<open>bfs Algorithm\<close>

definition (in bfs) init :: "('q, 'v) state" where
  "init \<equiv> \<lparr>queue = snoc empty src,
           distance = [src \<mapsto> 0],
           parent = [src \<mapsto> src]\<rparr>"

definition (in bfs) cond :: "('q, 'v) state \<Rightarrow> bool" where
  "cond s \<longleftrightarrow> \<not> is_empty (queue s)"

definition (in bfs) discovered :: "'v \<Rightarrow> ('q, 'v) state \<Rightarrow> bool" where
  "discovered v s \<longleftrightarrow> v \<in> dom (parent s)"

definition (in bfs) discover :: "'v \<Rightarrow> 'v \<Rightarrow> ('q, 'v) state \<Rightarrow> ('q, 'v) state" where
  "discover u v s \<equiv>
    if discovered v s then s
    else
      let
        q = snoc (queue s) v;
        d = distance s(v \<mapsto>
          case distance s u of
            Some n \<Rightarrow> Suc n);
        p = parent s(v \<mapsto> u)
      in \<lparr>queue = q, distance = d, parent = p\<rparr>"

function (in bfs) loop :: "('q, 'v) state \<Rightarrow> ('q, 'v) state" where
  "loop s =
    (if cond s then
       let
        u = head (queue s);
        q = tail (queue s)
       in loop (Finite_Set.fold (discover u) (s\<lparr>queue := q\<rparr>) (out_neighborhood G u))
     else s)"
  by pat_completeness simp

definition (in bfs) bfs :: "('q, 'v) state" where
  "bfs \<equiv> loop init"

section \<open>Invariants\<close>

locale bfs_invar = bfs where G = G and (* fold = fold and *) snoc = snoc
  for
    G :: "'v dgraph" and
    (* fold :: "('v \<Rightarrow> ('q, 'v) state \<Rightarrow> ('q, 'v) state) \<Rightarrow> 'v set \<Rightarrow> ('q, 'v) state \<Rightarrow> ('q, 'v) state" and *)
    snoc :: "'q \<Rightarrow> 'v \<Rightarrow> 'q" +
  fixes s :: "('q, 'v) state"
  assumes queue_subset_V: "set (list (queue s)) \<subseteq> dVs G"
  assumes distance_src: "distance s src = Some 0"
  assumes parent_src: "parent s src = Some src"
  assumes parent_edge: "\<lbrakk> v \<noteq> src; parent s v = Some u \<rbrakk> \<Longrightarrow> (u, v) \<in> G"
  assumes distance_parent:
    "\<lbrakk> v \<noteq> src; parent s v = Some u \<rbrakk> \<Longrightarrow> distance s v = Some m \<and> distance s u = Some n \<and> m = Suc n"
  assumes distance_min: "distance s v = Some n \<Longrightarrow> shortest_dpath_length G src v = Some n"

subsection \<open>\<close>

lemma (in bfs) init_queue_subset_V:
  shows "set (list (queue init)) \<subseteq> dVs G"
proof -
  have "set (list (queue init)) = {src}"
    using invar_empty
    by (simp add: init_def list_snoc list_empty)
  also have "... \<subseteq> dVs G"
    using src_in_V
    by (simp add: dVs_def)
  finally show ?thesis
    .
qed

lemma (in bfs) init_distance_src:
  shows "distance init src = Some 0"
  by (simp add: init_def)

lemma (in bfs) init_parent_src:
  shows "parent init src = Some src"
  by (simp add: init_def)

lemma (in bfs) init_parent_edge:
  assumes "v \<noteq> src"
  assumes "parent init v = Some u"
  shows "(u, v) \<in> G"
  using assms
  by (simp add: init_def)

lemma (in bfs) init_distance_parent:
  assumes "v \<noteq> src"
  assumes "parent init v = Some u"
  shows "distance init v = Some m \<and> distance init u = Some n \<and> m = Suc n"
  using assms
  by (simp add: init_def)

lemma (in bfs) init_distance_min:
  shows "distance init v = Some n \<Longrightarrow> shortest_dpath_length G src v = Some n"
  using src_in_V
  by (simp add: init_def shortest_dpath_length_singleton split: if_splits)

lemma (in bfs) init_bfs_invar:
  shows "bfs_invar empty is_empty head tail invar list src G snoc init"
  using
    bfs_axioms
    init_queue_subset_V init_distance_src init_parent_src init_parent_edge init_distance_parent
    init_distance_min
  by (intro bfs_invar.intro bfs_invar_axioms.intro)

subsection \<open>\<close>

section \<open>Termination\<close>

(* TODO *)
lemma (in bfs) invar_queue:
  shows "invar (queue s)"
  sorry

(* TODO *)
lemma (in bfs) dom_parent_subset_V:
  shows "dom (parent s) \<subseteq> dVs G"
  sorry

(* TODO *)
lemma (in bfs) fold_insert:
  assumes "finite A"
  assumes "x \<notin> A"
  shows "g (Finite_Set.fold f z (insert x A)) = g (f x (Finite_Set.fold f z A))"
  sorry

subsubsection \<open>parent\<close>

lemma (in bfs) parent_discover_cong:
  shows
    "parent (discover u v s) =
      parent s ++ (if discovered v s then Map.empty else [v \<mapsto> u])"
  by (simp add: discover_def)

lemma (in bfs) discovered_fold_cong:
  assumes "finite N"
  assumes "v \<notin> N"
  shows "discovered v (Finite_Set.fold (discover u) s N) = discovered v s"
  using assms
  by (induct N) (simp_all add: discovered_def fold_insert parent_discover_cong)

lemma (in bfs) parent_fold_discover_insert:
  assumes "finite N"
  assumes "v \<notin> N"
  shows
    "parent (Finite_Set.fold (discover u) s (insert v N)) =
      parent (Finite_Set.fold (discover u) s N) ++
      (if discovered v s then Map.empty else [v \<mapsto> u])"
  using assms
  by (simp add: fold_insert parent_discover_cong discovered_fold_cong)

lemma (in bfs) parent_fold_discover_cong:
  assumes "finite N"
  shows
    "parent (Finite_Set.fold (discover u) s N) =
      parent s ++ (\<lambda>v. if v \<in> N \<and> \<not> discovered v s then Some u else None)"
  using assms
  by (induct N) (auto simp add: parent_fold_discover_insert map_add_def)

(*
lemma (in bfs) parent_discover_comm:
  shows
    "parent \<circ> (discover u v) \<circ> (discover u w) =
      parent \<circ> (discover u w) \<circ> (discover u v)"
proof
  fix s
  show
    "(parent \<circ> (discover u v) \<circ> (discover u w)) s =
      (parent \<circ> (discover u w) \<circ> (discover u v)) s"
  proof (cases "v = w")
    case True
    thus ?thesis
      by simp
  next
    case False
    fix s
    have "dom [v \<mapsto> u] \<inter> dom [w \<mapsto> u] = {}"
      using False
      by simp
    hence "[v \<mapsto> u] ++ [w \<mapsto> u] = [w \<mapsto> u] ++ [v \<mapsto> u]"
      by (intro map_add_comm)
    thus ?thesis
      using parent_discover_cong
      by simp
  qed
qed
*)

subsubsection \<open>queue\<close>

lemma (in bfs) queue_discover_cong:
  shows
    "list (queue (discover u v s)) =
      list (queue s) @ (if discovered v s then Nil else [v])"
  using invar_queue[where ?s = s]
  by (simp add: discover_def list_snoc)

lemma (in bfs) queue_fold_discover_insert:
  assumes "finite N"
  assumes "v \<notin> N"
  shows
    "mset (list (queue (Finite_Set.fold (discover u) s (insert v N)))) =
      mset (list (queue (Finite_Set.fold (discover u) s N))) +
      (if discovered v s then {#} else {#v#})"
  using assms
  by (simp add: fold_insert queue_discover_cong discovered_fold_cong)

lemma (in bfs) queue_fold_discover_cong:
  assumes "finite N"
  shows
    "mset (list (queue (Finite_Set.fold (discover u) s N))) =
      mset (list (queue s)) + {#v \<in># mset_set N. \<not> discovered v s#}"
  using assms
  by (induct N) (simp_all add: queue_fold_discover_insert)

lemma (in bfs) termination_aux:
  assumes "S = {v \<in> (out_neighborhood G u). \<not> discovered v s}"
  assumes
    "dom (parent s ++
      (\<lambda>v. if v \<in> (out_neighborhood G u) \<and> \<not> discovered v s then Some u else None)) =
      dom (parent s) \<union> S"
  shows
    "card (dom (parent s ++
      (\<lambda>v. if v \<in> (out_neighborhood G u) \<and> \<not> discovered v s then Some u else None))) =
      card (dom (parent s)) + card S"
proof -
  have "finite (dom (parent s))"
    using dom_parent_subset_V[where ?s = s] vertices_finite
    by (auto intro: finite_subset)
  moreover have "finite {v \<in> (out_neighborhood G u). \<not> discovered v s}"
    using out_neighborhood_finite
    by simp
  moreover have "dom (parent s) \<inter> S = {}"
    by (auto simp add: assms discovered_def)
  ultimately show ?thesis
    using assms
    by (simp add: card_Un_disjoint)
qed

lemma (in bfs) termination_aux2:
  fixes s :: "('q, 'v) state"
  assumes "cond s"
  shows
    "card (dVs G) +
      length (list (queue (s\<lparr>queue := (tail (queue s))\<rparr>))) -
      card (dom (parent (s\<lparr>queue := (tail (queue s))\<rparr>))) <
      card (dVs G) +
      length (list (queue s)) -
      card (dom (parent s))"
proof -
  have "list (queue s) \<noteq> Nil"
    using invar_queue[where ?s = s] assms
    by (simp add: is_empty cond_def)
  hence "length (list (queue (s\<lparr>queue := (tail (queue s))\<rparr>))) < length (list (queue s))"
    using invar_queue[where ?s = s]
    by (simp add: length_tail)
  moreover have "card (dom (parent s)) \<le> card (dVs G)"
    using vertices_finite dom_parent_subset_V
    by (intro card_mono)
  ultimately show ?thesis
    by simp
qed

termination (in bfs) loop
proof (relation "measure (\<lambda>s. card (dVs G) + length (list (queue s)) - card (dom (parent s)))")
  fix s u q
  assume assms:
    "cond s"
    "u = head (queue s)"
    "q = tail (queue s)"
  
  define S :: "'v set" where "S \<equiv> {v \<in> (out_neighborhood G u). \<not> discovered v (s\<lparr>queue := q\<rparr>)}"
  
  have
    "dom (\<lambda>v. if v \<in> (out_neighborhood G u) \<and> \<not> discovered v (s\<lparr>queue := q\<rparr>) then Some u else None) =
      {v \<in> (out_neighborhood G u). \<not> discovered v (s\<lparr>queue := q\<rparr>)}"
    by (simp add: dom_def)
  hence
    "dom (parent (s\<lparr>queue := q\<rparr>) ++
      (\<lambda>v. if v \<in> (out_neighborhood G u) \<and> \<not> discovered v (s\<lparr>queue := q\<rparr>) then Some u else None)) =
      dom (parent (s\<lparr>queue := q\<rparr>)) \<union> S"
    by (auto simp add: S_def)
  with S_def have
    "card (dom (parent (s\<lparr>queue := q\<rparr>) ++
      (\<lambda>v. if v \<in> (out_neighborhood G u) \<and> \<not> discovered v (s\<lparr>queue := q\<rparr>) then Some u else None))) =
      card (dom (parent (s\<lparr>queue := q\<rparr>))) + card S"
    by (intro termination_aux) blast+
  hence
    "card (dom (parent (Finite_Set.fold (discover u) (s\<lparr>queue := q\<rparr>) (out_neighborhood G u)))) =
      card (dom (parent (s\<lparr>queue := q\<rparr>))) + card S"
    using out_neighborhood_finite
    by (simp add: parent_fold_discover_cong)
  moreover have
    "length (list (queue (Finite_Set.fold (discover u) (s\<lparr>queue := q\<rparr>) (out_neighborhood G u)))) =
      length (list (queue (s\<lparr>queue := q\<rparr>))) + card S"
    unfolding size_mset[symmetric]
    using out_neighborhood_finite
    by (simp add: S_def queue_fold_discover_cong)
  ultimately have
    "card (dVs G) +
      length (list (queue (Finite_Set.fold (discover u) (s\<lparr>queue := q\<rparr>) (out_neighborhood G u)))) -
      card (dom (parent (Finite_Set.fold (discover u) (s\<lparr>queue := q\<rparr>) (out_neighborhood G u)))) =
      card (dVs G) +
      length (list (queue (s\<lparr>queue := q\<rparr>))) + card (out_neighborhood G u - dom (parent (s\<lparr>queue := q\<rparr>))) -
      (card (dom (parent (s\<lparr>queue := q\<rparr>))) + card (out_neighborhood G u - dom (parent (s\<lparr>queue := q\<rparr>))))"
    by simp
  also have "... = card (dVs G) + length (list (queue (s\<lparr>queue := q\<rparr>))) - card (dom (parent (s\<lparr>queue := q\<rparr>)))"
    by simp
  also have "... < card (dVs G) + length (list (queue s)) - card (dom (parent s))"
    unfolding assms(3)
    using assms(1)
    by (intro termination_aux2)
  finally show
    "Finite_Set.fold (discover u) (s\<lparr>queue := q\<rparr>) (out_neighborhood G u)
      \<rightarrow>\<^bsub>measure (\<lambda>s. card (dVs G) + length (list (queue s)) - card (dom (parent s)))\<^esub>s"
    by simp
qed simp

section \<open>Correctness\<close>

end