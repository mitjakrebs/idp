subsection \<open>Medium level\<close>

subsubsection \<open>Adjacency structure\<close>

theory Adjacency
  imports
    "HOL-Data_Structures.Set_Specs"
    "../../Map/Map_Specs_Ext"
    "../../Orderings_Ext"
begin

text \<open>
As mentioned above, a graph on the high level of abstraction is a set of edges. Hence, we would
expect a graph to provide basic set operations such as insert, delete, union, intersection, and
difference. Moreover, many graph algorithms, including breadth-first and depth-first search, involve
iterating, or folding, over all vertices adjacent to a given vertex. Thus, we would have liked to
specify a graph on the medium level of abstraction via the following locales.
\<close>

locale Adjacency_Structure =
  fixes empty :: "'g"
  fixes insert :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'g \<Rightarrow> 'g"
  fixes delete :: "'a \<Rightarrow> 'a \<Rightarrow> 'g \<Rightarrow> 'g"
  fixes adj :: "'a \<Rightarrow> 'g \<Rightarrow> 'a list"
  fixes inv :: "'g \<Rightarrow> bool"
  assumes adj_empty: "adj v empty = []"
  assumes adj_insert:
    "inv G \<and> Sorted_Less.sorted (adj u G) \<Longrightarrow>
     adj u (insert v w G) = (if u = v then ins_list w (adj u G) else adj u G)"
  assumes adj_delete:
    "inv G \<and> Sorted_Less.sorted (adj u G) \<Longrightarrow>
     adj u (delete v w G) = (if u = v then List_Ins_Del.del_list w (adj u G) else adj u G)"
  assumes inv_empty: "inv empty"
  assumes inv_insert: "inv G \<and> Sorted_Less.sorted (adj u G) \<Longrightarrow> inv (insert u v G)"
  assumes inv_delete: "inv G \<and> Sorted_Less.sorted (adj u G) \<Longrightarrow> inv (delete u v G)"

definition \<^marker>\<open>tag invisible\<close> (in Adjacency_Structure) invar :: "'g \<Rightarrow> bool" where
  "invar G \<equiv> inv G \<and> (\<forall>v. Sorted_Less.sorted (adj v G))"

lemma \<^marker>\<open>tag invisible\<close> (in Adjacency_Structure) invarD:
  assumes "invar G"
  shows
    "inv G"
    "\<forall>v. Sorted_Less.sorted (adj v G)"
  using assms
  by (simp_all add: invar_def)

lemma \<^marker>\<open>tag invisible\<close> (in Adjacency_Structure) invar_empty:
  shows "invar empty"
  using inv_empty
  by (simp add: invar_def adj_empty)

lemma \<^marker>\<open>tag invisible\<close> (in Adjacency_Structure) invar_insert:
  assumes "invar G"
  shows "invar (insert u v G)"
  using assms
  by (auto simp add: invar_def adj_insert intro: inv_insert sorted_ins_list)

lemma \<^marker>\<open>tag invisible\<close> (in Adjacency_Structure) invar_delete:
  assumes "invar G"
  shows "invar (delete u v G)"
  using assms
  by (auto simp add: invar_def adj_delete intro: inv_delete List_Ins_Del.sorted_del_list)

lemma \<^marker>\<open>tag invisible\<close> (in Adjacency_Structure) distinct_adj:
  assumes "inv G \<and> Sorted_Less.sorted (adj v G)"
  shows "distinct (adj v G)"
  using assms
  by (intro sorted_imp_distinct) (drule conjunct2)

locale Finite_Adjacency_Structure = Adjacency_Structure where insert = insert for
  insert :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'g \<Rightarrow> 'g" +
  assumes finite_domain_tbd: "inv G \<Longrightarrow> finite {v. adj v G \<noteq> []}"

locale Adjacency_Structure_2 = Adjacency_Structure where insert = insert for
  insert :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'g \<Rightarrow> 'g" +
  fixes union :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
  fixes difference :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
  assumes adj_union:
    "\<lbrakk> inv G1; Sorted_Less.sorted (adj v G1); inv G2; Sorted_Less.sorted (adj v G2) \<rbrakk> \<Longrightarrow>
     adj v (union G1 G2) = fold ins_list (adj v G2) (adj v G1)"
  assumes adj_difference:
    "\<lbrakk> inv G1; Sorted_Less.sorted (adj v G1); inv G2; Sorted_Less.sorted (adj v G2) \<rbrakk> \<Longrightarrow>
     adj v (difference G1 G2) = fold List_Ins_Del.del_list (adj v G2) (adj v G1)"
  assumes inv_union: "inv G1 \<Longrightarrow> inv G2 \<Longrightarrow> inv (union G1 G2)"
  assumes inv_difference: "inv G1 \<Longrightarrow> inv G2 \<Longrightarrow> inv (difference G1 G2)"

locale Finite_Adjacency_Structure_2 = Adjacency_Structure_2 where insert = insert for
  insert :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'g \<Rightarrow> 'g" +
  assumes finite_domain_tbd: "inv G \<Longrightarrow> finite {v. adj v G \<noteq> []}"

text \<open>
Unfortunately, we were not able to refactor in time the entire formalization such that it uses
locale @{locale Finite_Adjacency_Structure_2} instead of the following one.
\<close>

(* TODO Use Set2 instead of Set_by_Ordered to obtain more efficient union and difference operations? *)
locale adjacency =
  M: Map_by_Ordered where
  empty = Map_empty and
  update = Map_update and
  delete = Map_delete and
  lookup = Map_lookup and
  inorder = Map_inorder and
  inv = Map_inv +
  S: Set_by_Ordered where
  empty = Set_empty and
  insert = Set_insert and
  delete = Set_delete and
  isin = Set_isin and
  inorder = Set_inorder and
  inv = Set_inv for
  Map_empty and
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'm \<Rightarrow> 'm" and
  Map_delete and
  Map_lookup and
  Map_inorder and
  Map_inv and
  Set_empty and
  Set_insert :: "'a \<Rightarrow> 's \<Rightarrow> 's" and
  Set_delete and
  Set_isin and
  Set_inorder and
  Set_inv

definition (in adjacency) invar :: "'m \<Rightarrow> bool" where
  "invar G \<equiv> M.invar G \<and> Ball (M.ran G) S.invar"

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) invarD:
  assumes "invar G"
  shows
    "M.invar G"
    "Ball (M.ran G) S.invar"
  using assms
  by (simp_all add: invar_def)

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) invar_empty:
  shows "invar Map_empty"
  unfolding invar_def
proof (standard, goal_cases)
  case 1
  show ?case
    using M.invar_empty
    .
next
  case 2
  show ?case
    by (simp add: M.ran_def M.map_empty)
qed

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) invar_update:
  assumes "invar G"
  assumes "S.invar s"
  shows "invar (Map_update v s G)"
  unfolding invar_def
proof (standard, goal_cases)
  case 1
  show ?case
    using assms(1)
    by (auto simp add: invar_def intro: M.invar_update)
next
  case 2
  show ?case
  proof
    fix s'
    assume assm: "s' \<in> M.ran (Map_update v s G)"
    then obtain v' where
      "Map_lookup (Map_update v s G) v' = Some s'"
      unfolding M.ran_def
      by blast
    thus "S.invar s'"
      using assms
      by (cases "v' = v") (auto simp add: invar_def M.map_update M.ran_def)
  qed
qed

definition (in adjacency) adjacency_list :: "'m \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "adjacency_list G u \<equiv> case Map_lookup G u of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s"

lemma (in adjacency) finite_adjacency:
  shows "finite (set (adjacency_list G v))"
  using finite_set
  .

lemma (in adjacency) distinct_adjacency_list:
  assumes "invar G"
  shows "distinct (adjacency_list G v)"
  using assms
  unfolding adjacency_list_def
  by (cases "Map_lookup G v") (auto simp add: invar_def M.ran_def S.invar_def intro: sorted_imp_distinct)

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) mem_adjacency_iff_lookup_eq_Some:
  shows "v \<in> set (adjacency_list G u) \<longleftrightarrow> (\<exists>s. Map_lookup G u = Some s \<and> v \<in> S.set s)"
  by (force simp add: adjacency_list_def S.set_def)

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) mem_adjacencyE:
  assumes "v \<in> set (adjacency_list G u)"
  obtains s where
    "Map_lookup G u = Some s"
    "v \<in> S.set s"
  using assms
  by (auto simp add: mem_adjacency_iff_lookup_eq_Some)

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) mem_adjacency_iff_mem_inorder:
  assumes "invar G"
  shows "v \<in> set (adjacency_list G u) \<longleftrightarrow> (\<exists>s. (u, s) \<in> set (Map_inorder G) \<and> v \<in> S.set s)"
proof (standard, goal_cases)
  case 1
  then obtain s where
    "Map_lookup G u = Some s"
    "v \<in> S.set s"
    by (elim mem_adjacencyE)
  thus ?case
    using assms
    by (force simp add: M.mem_inorder_iff_lookup_eq_Some dest: invarD(1))
next
  case 2
  then obtain s where
    "(u, s) \<in> set (Map_inorder G) \<and> v \<in> S.set s"
    by (elim exE)
  hence "Map_lookup G u = Some s \<and> v \<in> S.set s"
    using assms
    by (auto simp add: M.mem_inorder_iff_lookup_eq_Some dest: invarD(1))
  thus ?case
    by (simp add: S.set_def adjacency_list_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in adjacency) adjacency_inorder_cong:
  assumes "invar G"
  shows "set (adjacency_list G u) = (\<Union>p\<in>set (Map_inorder G). if u = fst p then S.set (snd p) else {})"
proof -
  { fix v
    have "v \<in> set (adjacency_list G u) \<longleftrightarrow> (\<exists>s. (u, s) \<in> set (Map_inorder G) \<and> v \<in> S.set s)"
      using assms
      by (intro mem_adjacency_iff_mem_inorder)
    also have "... \<longleftrightarrow> (\<exists>p\<in>set (Map_inorder G). u = fst p \<and> v \<in> S.set (snd p))"
      by force
    also have "... \<longleftrightarrow> v \<in> (\<Union>p\<in>set (Map_inorder G). if u = fst p then S.set (snd p) else {})"
      by auto
    finally have
      "v \<in> set (adjacency_list G u) \<longleftrightarrow>
       v \<in> (\<Union>p\<in>set (Map_inorder G). if u = fst p then S.set (snd p) else {})"
      . }
  thus ?thesis
    by blast
qed

text \<open>
This locale specifies a graph as a @{term Map_by_Ordered} mapping a vertex to its adjacency, which
is specified as a @{term Set_by_Ordered}.
\<close>

text \<open>
We define graph operations insert, delete, union, as well as difference, and show that they
correspond to the respective set operations in terms of @{term adjacency.adjacency_list}. Let us
first look at inserting an edge into a graph.
\<close>

definition (in adjacency) insert :: "'a \<times> 'a \<Rightarrow> 'm \<Rightarrow> 'm" where
  "insert p G \<equiv>
   let u = fst p; v = snd p
   in let s = case Map_lookup G u of None \<Rightarrow> Set_empty | Some s' \<Rightarrow> s'
      in Map_update u (Set_insert v s) G"

lemma (in adjacency) invar_insert:
  assumes "invar G"
  shows "invar (insert p G)"
proof (cases "Map_lookup G (fst p)")
  case None
  thus ?thesis
    using assms S.invar_empty
    by (auto simp add: insert_def intro: S.invar_insert invar_update)
next
  case (Some s)
  hence "S.invar s"
    using assms
    by (auto simp add: invar_def M.ran_def)
  thus ?thesis
    using assms
    by (auto simp add: insert_def Some intro: S.invar_insert invar_update)
qed

lemma (in adjacency) adjacency_list_insert_cong:
  assumes "invar G"
  shows
    "adjacency_list (insert p G) w =
     (if w = fst p then ins_list (snd p) (adjacency_list G w) else adjacency_list G w)"
proof (cases "Map_lookup G (fst p)")
  case None
  let ?u = "fst p"
  let ?v = "snd p"
  let ?singleton = "Set_insert (snd p) Set_empty"
  have
    "adjacency_list (insert p G) w =
     (case Map_lookup (insert p G) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    by (simp add: adjacency_list_def)
  also have "... = (case Map_lookup (Map_update ?u ?singleton G) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    by (simp add: insert_def None)
  also have "... = (case (Map_lookup G(?u \<mapsto> ?singleton)) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    using assms
    by (simp add: invar_def M.map_update)
  also have "... = (if w = ?u then ins_list ?v (adjacency_list G w) else adjacency_list G w)"
  proof (cases "w = ?u")
    case True
    hence
      "(case (Map_lookup G(?u \<mapsto> ?singleton)) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s) =
       ins_list ?v []"
      using S.inorder_inv_empty
      by (simp add: S.inorder_empty S.inorder_insert)
    thus ?thesis
      by (auto simp add: adjacency_list_def None)
  next
    case False
    then show ?thesis
      by (simp add: adjacency_list_def)
  qed
  finally show ?thesis
    .
next
  case (Some s)
  hence invar: "S.invar s"
    using assms
    by (auto simp add: invar_def M.ran_def)
  let ?u = "fst p"
  let ?v = "snd p"
  let ?insert = "Set_insert ?v s"
  have
    "adjacency_list (insert p G) w =
     (case Map_lookup (insert p G) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    by (simp add: adjacency_list_def)
  also have "... = (case Map_lookup (Map_update ?u ?insert G) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    by (simp add: insert_def Some)
  also have "... = (case (Map_lookup G(?u \<mapsto> ?insert)) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    using assms
    by (simp add: invar_def M.map_update)
  also have "... = (if w = ?u then ins_list ?v (adjacency_list G w) else adjacency_list G w)"
  proof (cases "w = ?u")
    case True
    hence
      "(case (Map_lookup G(?u \<mapsto> ?insert)) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s) =
       ins_list ?v (Set_inorder s)"
      using invar
      by (simp add: S.invar_def S.inorder_insert)
    thus ?thesis
      by (auto simp add: adjacency_list_def Some)
  next
    case False
    then show ?thesis
      by (simp add: adjacency_list_def)
  qed
  finally show ?thesis
    .
qed

lemma (in adjacency) adjacency_insert_cong:
  assumes "invar G"
  shows
    "set (adjacency_list (insert p G) u) =
     set (adjacency_list G u) \<union> (if u = fst p then {snd p} else {})"
proof (cases "Map_lookup G (fst p)")
  case None
  let ?singleton = "Set_insert (snd p) Set_empty"
  { fix v
    have
      "v \<in> set (adjacency_list (insert p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list (Map_update (fst p) ?singleton G) u)"
      by (simp add: insert_def None)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) ?singleton G) u = Some s \<and> v \<in> S.set s)"
      by (simp add: mem_adjacency_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup G(fst p \<mapsto> ?singleton)) u = Some s \<and> v \<in> S.set s)"
      using assms
      by (auto simp add: M.map_update dest: invarD(1))
    also have "... \<longleftrightarrow> v \<in> set (adjacency_list G u) \<union> (if u = fst p then {snd p} else {})"
      using S.invar_empty
      by (simp add: None mem_adjacency_iff_lookup_eq_Some S.set_insert S.set_empty)
    finally have
      "v \<in> set (adjacency_list (insert p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list G u) \<union> (if u = fst p then {snd p} else {})"
      . }
  thus ?thesis
    by blast
next
  case (Some s)
  hence invar: "S.invar s"
    using assms
    by (auto simp add: invar_def M.ran_def)
  let ?insert = "Set_insert (snd p) s"
  { fix v
    have
      "v \<in> set (adjacency_list (insert p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list (Map_update (fst p) ?insert G) u)"
      by (simp add: insert_def Some)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) ?insert G) u = Some s \<and> v \<in> S.set s)"
      by (simp add: mem_adjacency_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup G(fst p \<mapsto> ?insert)) u = Some s \<and> v \<in> S.set s)"
      using assms
      by (auto simp add: M.map_update dest: invarD(1))
    also have "... \<longleftrightarrow> v \<in> set (adjacency_list G u) \<union> (if u = fst p then {snd p} else {})"
      using invar
      by (auto simp add: Some mem_adjacency_iff_lookup_eq_Some S.set_insert)
    finally have
      "v \<in> set (adjacency_list (insert p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list G u) \<union> (if u = fst p then {snd p} else {})"
      . }
  thus ?thesis
    by blast
qed

lemma (in adjacency) invar_fold_insert:
  assumes "invar G"
  shows "invar (fold insert l G)"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case Cons
  thus ?case
    by (auto intro: invar_insert Cons.hyps)
qed

lemma (in adjacency) adjacency_fold_insert_cong:
  assumes "invar G"
  shows
    "set (adjacency_list (fold insert l G) v) =
     set (adjacency_list G v) \<union> (\<Union>p\<in>set l. if v = fst p then {snd p} else {})"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  have
    "set (adjacency_list (fold insert (p # ps) G) v) =
     set (adjacency_list (fold insert ps (insert p G)) v)"
    by simp
  also have
    "... =
     set (adjacency_list (insert p G) v) \<union>
     (\<Union>p\<in>set ps. if v = fst p then {snd p} else {})"
    using Cons.prems
    by (intro invar_insert Cons.hyps)
  also have
    "... =
     set (adjacency_list G v) \<union>
     (if v = fst p then {snd p} else {}) \<union>
     (\<Union>p\<in>set ps. if v = fst p then {snd p} else {})"
    using Cons.prems
    by (simp add: adjacency_insert_cong)
  also have "... = set (adjacency_list G v) \<union> (\<Union>p\<in>set (p # ps). if v = fst p then {snd p} else {})"
    by force
  finally show ?case
    .
qed

definition (in adjacency) insert' :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" where
  "insert' \<equiv> curry insert"

lemma (in adjacency) invar_insert':
  assumes "invar G"
  shows "invar (insert' u v G)"
  using assms
  by (auto simp add: insert'_def intro: invar_insert)

lemma (in adjacency) adjacency_list_insert'_cong:
  assumes "invar G"
  shows
    "adjacency_list (insert' u v G) w =
     (if w = u then ins_list v (adjacency_list G w) else adjacency_list G w)"
  using assms
  by (simp add: insert'_def adjacency_list_insert_cong)

lemma (in adjacency) adjacency_insert'_cong:
  assumes "invar G"
  shows
    "set (adjacency_list (insert' u v G) w) =
     set (adjacency_list G w) \<union> (if w = u then {v} else {})"
  using assms
  by (simp add: insert'_def adjacency_insert_cong)

lemma (in adjacency) invar_fold_insert':
  assumes "invar G"
  shows "invar (fold (insert' u) l G)"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case Cons
  thus ?case
    by (auto intro: invar_insert' Cons.hyps)
qed

lemma (in adjacency) adjacency_fold_insert'_cong:
  assumes "invar G"
  shows
    "set (adjacency_list (fold (insert' u) l G) v) =
     set (adjacency_list G v) \<union> (\<Union>w\<in>set l. if v = u then {w} else {})"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons w ws)
  have
    "set (adjacency_list (fold (insert' u) (w # ws) G) v) =
     set (adjacency_list (fold (insert' u) ws (insert' u w G)) v)"
    by simp
  also have "... = set (adjacency_list (insert' u w G) v) \<union> (\<Union>x\<in>set ws. if v = u then {x} else {})"
    using Cons.prems
    by (intro invar_insert' Cons.hyps)
  also have
    "... =
     set (adjacency_list G v) \<union>
     (if v = u then {w} else {}) \<union>
     (\<Union>x\<in>set ws. if v = u then {x} else {})"
    using Cons.prems
    by (simp add: adjacency_insert'_cong)
  also have "... = set (adjacency_list G v) \<union> (\<Union>x\<in>set (w # ws). if v = u then {x} else {})"
    by force
  finally show ?case
    .
qed

text \<open>Next, let us look at deleting an edge from a graph.\<close>

definition (in adjacency) delete :: "'a \<times> 'a \<Rightarrow> 'm \<Rightarrow> 'm" where
  "delete p G \<equiv>
   case Map_lookup G (fst p) of
     None \<Rightarrow> G |
     Some s \<Rightarrow> Map_update (fst p) (Set_delete (snd p) s) G"

lemma (in adjacency) invar_delete:
  assumes "invar G"
  shows "invar (delete p G)"
proof (cases "Map_lookup G (fst p)")
  case None
  thus ?thesis
    using assms
    by (simp add: delete_def)
next
  case (Some s)
  hence "S.invar s"
    using assms
    by (auto simp add: invar_def M.ran_def)
  thus ?thesis
    using assms
    by (auto simp add: delete_def Some intro: S.invar_delete intro: invar_update)
qed

lemma (in adjacency) adjacency_list_delete_cong:
  assumes "invar G"
  shows
    "adjacency_list (delete p G) w =
     (if w = fst p then List_Ins_Del.del_list (snd p) (adjacency_list G w) else adjacency_list G w)"
proof (cases "Map_lookup G (fst p)")
  case None
  let ?u = "fst p"
  let ?v = "snd p"
  let ?singleton = "Set_insert (snd p) Set_empty"
  have
    "adjacency_list (delete p G) w =
     (case Map_lookup (delete p G) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    by (simp add: adjacency_list_def)
  also have "... = (case Map_lookup G w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    by (simp add: delete_def None)
  also have "... = (if w = ?u then List_Ins_Del.del_list ?v (adjacency_list G w) else adjacency_list G w)"
    by (simp add: adjacency_list_def None)
  finally show ?thesis
    .
next
  case (Some s)
  hence invar: "S.invar s"
    using assms(1)
    by (auto simp add: invar_def M.ran_def)
  let ?u = "fst p"
  let ?v = "snd p"
  let ?delete = "Set_delete ?v s"
  have
    "adjacency_list (delete p G) w =
     (case Map_lookup (delete p G) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    by (simp add: adjacency_list_def)
  also have "... = (case Map_lookup (Map_update ?u ?delete G) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    by (simp add: delete_def Some)
  also have "... = (case (Map_lookup G(?u \<mapsto> ?delete)) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s)"
    using assms
    by (simp add: invar_def M.map_update)
  also have "... = (if w = ?u then List_Ins_Del.del_list ?v (adjacency_list G w) else adjacency_list G w)"
  proof (cases "w = ?u")
    case True
    hence
      "(case (Map_lookup G(?u \<mapsto> ?delete)) w of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s) =
       List_Ins_Del.del_list ?v (Set_inorder s)"
      using invar
      by (simp add: S.invar_def S.inorder_delete)
    thus ?thesis
      by (auto simp add: adjacency_list_def Some)
  next
    case False
    then show ?thesis
      by (simp add: adjacency_list_def)
  qed
  finally show ?thesis
    .
qed

definition (in adjacency) delete' :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" where
  "delete' \<equiv> curry delete"

lemma (in adjacency) invar_delete':
  assumes "invar G"
  shows "invar (delete' u v G)"
  using assms
  by (auto simp add: delete'_def intro: invar_delete)

lemma (in adjacency) adjacency_list_delete'_cong:
  assumes "invar G"
  shows
    "adjacency_list (delete' u v G) w =
     (if w = u then List_Ins_Del.del_list v (adjacency_list G w) else adjacency_list G w)"
  using assms
  by (simp add: delete'_def adjacency_list_delete_cong)

text \<open>Let us now look at computing the union two graphs.\<close>

definition (in adjacency) insert_2 :: "'a \<times> 's \<Rightarrow> 'm \<Rightarrow> 'm" where
  "insert_2 p G \<equiv>
   let v = fst p; s = snd p
   in let s' = case Map_lookup G v of None \<Rightarrow> s | Some s'' \<Rightarrow> fold Set_insert (Set_inorder s) s''
      in Map_update v s' G"

lemma \<^marker>\<open>tag invisible\<close> (in Set_by_Ordered) invar_fold_insert:
  assumes "invar s"
  shows "invar (fold insert l s)"
  using assms
  by (induct l arbitrary: s) (auto intro: invar_insert)

lemma \<^marker>\<open>tag invisible\<close> (in Set_by_Ordered) fold_insert_cong:
  assumes "invar s"
  shows "set (fold insert l s) = set s \<union> List.set l"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons x xs)
  have "set (fold insert (x # xs) s) = set (fold insert xs (insert x s))"
    by force
  also have "... = set (insert x s) \<union> List.set xs"
    using Cons.prems
    by (intro invar_insert Cons.hyps)
  also have "... = set s \<union> {x} \<union> List.set xs"
    using Cons.prems
    by (simp add: set_insert)
  also have "... = set s \<union> List.set (x # xs)"
    by simp
  finally show ?case
    .
qed

lemma (in adjacency) invar_insert_2:
  assumes "invar G"
  assumes "S.invar (snd p)"
  shows "invar (insert_2 p G)"
proof (cases "Map_lookup G (fst p)")
  case None
  thus ?thesis
    using assms
    by (auto simp add: insert_2_def intro: invar_update)
next
  case (Some s)
  hence "S.invar s"
    using assms(1)
    by (auto simp add: invar_def M.ran_def)
  thus ?thesis
    using assms(1)
    by (auto simp add: insert_2_def Some intro: S.invar_fold_insert invar_update)
qed

lemma (in adjacency) adjacency_insert_2_cong:
  assumes "invar G"
  assumes "S.invar (snd p)"
  shows
    "set (adjacency_list (insert_2 p G) u) =
     set (adjacency_list G u) \<union> (if u = fst p then S.set (snd p) else {})"
proof (cases "Map_lookup G (fst p)")
  case None
  { fix v
    have
      "v \<in> set (adjacency_list (insert_2 p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list (Map_update (fst p) (snd p) G) u)"
      by (simp add: insert_2_def None)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) (snd p) G) u = Some s \<and> v \<in> S.set s)"
      by (simp add: mem_adjacency_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup G(fst p \<mapsto> snd p)) u = Some s \<and> v \<in> S.set s)"
      using assms(1)
      by (auto simp add: M.map_update dest: invarD(1))
    also have "... \<longleftrightarrow> v \<in> set (adjacency_list G u) \<union> (if u = fst p then S.set (snd p) else {})"
      by (auto simp add: None mem_adjacency_iff_lookup_eq_Some)
    finally have
      "v \<in> set (adjacency_list (insert_2 p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list G u) \<union> (if u = fst p then S.set (snd p) else {})"
      . }
  thus ?thesis
    by blast
next
  case (Some s')
  hence invar: "S.invar s'"
    using assms(1)
    by (auto simp add: invar_def M.ran_def)
  let ?fold = "fold Set_insert (Set_inorder (snd p)) s'"
  { fix v
    have
      "v \<in> set (adjacency_list (insert_2 p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list (Map_update (fst p) ?fold G) u)"
      by (simp add: insert_2_def Some)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) ?fold G) u = Some s \<and> v \<in> S.set s)"
      by (simp add: mem_adjacency_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup G(fst p \<mapsto> ?fold)) u = Some s \<and> v \<in> S.set s)"
      using assms(1)
      by (auto simp add: M.map_update dest: invarD(1))
    also have "... \<longleftrightarrow> v \<in> set (adjacency_list G u) \<union> (if u = fst p then S.set (snd p) else {})"
      using invar S.fold_insert_cong Some
      by (simp add: S.set_def mem_adjacency_iff_lookup_eq_Some)
    finally have
      "v \<in> set (adjacency_list (insert_2 p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list G u) \<union> (if u = fst p then S.set (snd p) else {})"
      . }
  thus ?thesis
    by blast
qed

lemma (in adjacency) invar_fold_insert_2:
  assumes "invar G"
  assumes "Ball (set l) (S.invar \<circ> snd)"
  shows "invar (fold insert_2 l G)"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  hence
    "S.invar (snd p)"
    "Ball (set ps) (S.invar \<circ> snd)"
    by simp+
  thus?case
    using Cons.prems(1)
    by (fastforce intro: invar_insert_2 Cons.hyps)
qed

lemma (in adjacency) adjacency_fold_insert_2_cong:
  assumes "invar G"
  assumes "Ball (set l) (S.invar \<circ> snd)"
  shows
    "set (adjacency_list (fold insert_2 l G) v) =
     set (adjacency_list G v) \<union> (\<Union>p\<in>set l. if v = fst p then S.set (snd p) else {})"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  hence
    prems: "S.invar (snd p)"
    "Ball (set ps) (S.invar \<circ> snd)"
    by simp+

  have
    "set (adjacency_list (fold insert_2 (p # ps) G) v) =
     set (adjacency_list (fold insert_2 ps (insert_2 p G)) v)"
    by simp
  also have
    "... =
     set (adjacency_list (insert_2 p G) v) \<union>
     (\<Union>p\<in>set ps. if v = fst p then S.set (snd p) else {})"
    using Cons.prems(1) prems
    by (intro invar_insert_2 Cons.hyps)
  also have
    "... =
     set (adjacency_list G v) \<union>
     (if v = fst p then S.set (snd p) else {}) \<union>
     (\<Union>p\<in>set ps. if v = fst p then S.set (snd p) else {})"
    using Cons.prems(1) prems(1)
    by (simp add: adjacency_insert_2_cong)
  also have
    "... =
     set (adjacency_list G v) \<union>
     (\<Union>p\<in>set (p # ps). if v = fst p then S.set (snd p) else {})"
    by force
  finally show ?case
    .
qed

definition (in adjacency) union :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" where
  "union G1 G2 \<equiv> fold insert_2 (Map_inorder G2) G1"

lemma (in adjacency) invar_union:
  assumes "invar G1"
  assumes "invar G2"
  shows "invar (union G1 G2)"
proof -
  have "Ball (set (Map_inorder G2)) (S.invar \<circ> snd)"
    using assms(2)
    by (fastforce simp add: invar_def M.ran_def M.mem_inorder_iff_lookup_eq_Some)
  thus ?thesis
    unfolding union_def
    using assms(1)
    by (intro invar_fold_insert_2)
qed

lemma (in adjacency) adjacency_union_cong:
  assumes "invar G1"
  assumes "invar G2"
  shows
    "set (adjacency_list (union G1 G2) v) =
     set (adjacency_list G1 v) \<union> set (adjacency_list G2 v)"
proof -
  have "Ball (set (Map_inorder G2)) (S.invar \<circ> snd)"
    using assms(2)
    by (fastforce simp add: invar_def M.ran_def M.mem_inorder_iff_lookup_eq_Some)
  with assms(1)
  have
    "set (adjacency_list (union G1 G2) v) =
     set (adjacency_list G1 v) \<union> (\<Union>p\<in>set (Map_inorder G2). if v = fst p then S.set (snd p) else {})"
    unfolding union_def
    by (intro adjacency_fold_insert_2_cong)
  also have "... = set (adjacency_list G1 v) \<union> set (adjacency_list G2 v)"
    using assms(2)
    by (simp add: adjacency_inorder_cong)
  finally show ?thesis
    .
qed

text \<open>Finally, let us look at computing the difference of two graphs.\<close>

definition (in adjacency) delete_2 :: "'a \<times> 's \<Rightarrow> 'm \<Rightarrow> 'm" where
  "delete_2 p G \<equiv>
   let v = fst p; s = snd p
   in case Map_lookup G v of
        None \<Rightarrow> G |
        Some s' \<Rightarrow> Map_update v (fold Set_delete (Set_inorder s) s') G"

lemma \<^marker>\<open>tag invisible\<close> (in Set_by_Ordered) invar_fold_delete:
  assumes "invar s"
  shows "invar (fold delete l s)"
  using assms
  by (induct l arbitrary: s) (auto intro: invar_delete)

lemma \<^marker>\<open>tag invisible\<close> (in Set_by_Ordered) fold_delete_cong:
  assumes "invar s"
  shows "set (fold delete l s) = set s - List.set l"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons x xs)
  have "set (fold delete (x # xs) s) = set (fold delete xs (delete x s))"
    by simp
  also have "... = set (delete x s) - List.set xs"
    using Cons.prems
    by (intro invar_delete Cons.hyps)
  also have "... = set s - {x} - List.set xs"
    using Cons.prems
    by (simp add: set_delete)
  also have "... = set s - List.set (x # xs)"
    by auto
  finally show ?case
    .
qed

lemma (in adjacency) invar_delete_2:
  assumes "invar G"
  shows "invar (delete_2 p G)"
proof (cases "Map_lookup G (fst p)")
  case None
  thus ?thesis
    using assms
    by (simp add: delete_2_def)
next
  case (Some s)
  hence "S.invar s"
    using assms
    by (auto simp add: invar_def M.ran_def)
  thus ?thesis
    using assms
    by (auto simp add: delete_2_def Some intro: S.invar_fold_delete invar_update)
qed

lemma (in adjacency) adjacency_delete_2_cong:
  assumes "invar G"
  shows
    "set (adjacency_list (delete_2 p G) u) =
     set (adjacency_list G u) - (if u = fst p then S.set (snd p) else {})"
proof (cases "Map_lookup G (fst p)")
  case None
  thus ?thesis
    by (simp add: adjacency_list_def delete_2_def)
next
  case (Some s')
  hence invar: "S.invar s'"
    using assms
    by (auto simp add: invar_def M.ran_def)
  let ?fold = "fold Set_delete (Set_inorder (snd p)) s'"
  { fix v
    have
      "v \<in> set (adjacency_list (delete_2 p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list (Map_update (fst p) ?fold G) u)"
      by (simp add: delete_2_def Some)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) ?fold G) u = Some s \<and> v \<in> S.set s)"
      by (simp add: mem_adjacency_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup G(fst p \<mapsto> ?fold)) u = Some s \<and> v \<in> S.set s)"
      using assms
      by (auto simp add: M.map_update dest: invarD(1))
    also have "... \<longleftrightarrow> v \<in> set (adjacency_list G u) - (if u = fst p then S.set (snd p) else {})"
      using invar S.fold_delete_cong Some
      by (simp add: S.set_def mem_adjacency_iff_lookup_eq_Some)
    finally have
      "v \<in> set (adjacency_list (delete_2 p G) u) \<longleftrightarrow>
       v \<in> set (adjacency_list G u) - (if u = fst p then S.set (snd p) else {})"
      . }
  thus ?thesis
    by blast
qed

lemma (in adjacency) invar_fold_delete_2:
  assumes "invar G"
  assumes "Ball (set l) (S.invar \<circ> snd)"
  shows "invar (fold delete_2 l G)"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  hence
    "S.invar (snd p)"
    "Ball (set ps) (S.invar \<circ> snd)"
    by simp+
  thus ?case
    using Cons.prems(1)
    by (fastforce intro: invar_delete_2 Cons.hyps)
qed

lemma (in adjacency) adjacency_fold_delete_2_cong:
  assumes "invar G"
  assumes "Ball (set l) (S.invar \<circ> snd)"
  shows
    "set (adjacency_list (fold delete_2 l G) v) =
     set (adjacency_list G v) - (\<Union>p\<in>set l. if v = fst p then S.set (snd p) else {})"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  hence
    prems: "S.invar (snd p)"
    "Ball (set ps) (S.invar \<circ> snd)"
    by simp+

  have
    "set (adjacency_list (fold delete_2 (p # ps) G) v) =
     set (adjacency_list (fold delete_2 ps (delete_2 p G)) v)"
    by simp
  also have
    "... =
     set (adjacency_list (delete_2 p G) v) -
     (\<Union>p\<in>set ps. if v = fst p then S.set (snd p) else {})"
    using Cons.prems(1) prems
    by (intro invar_delete_2 Cons.hyps)
  also have
    "... =
     set (adjacency_list G v) -
     (if v = fst p then S.set (snd p) else {}) -
     (\<Union>p\<in>set ps. if v = fst p then S.set (snd p) else {})"
    using Cons.prems(1) prems(1)
    by (simp add: adjacency_delete_2_cong)
  also have
    "... =
     set (adjacency_list G v) -
     (\<Union>p\<in>set (p # ps). if v = fst p then S.set (snd p) else {})"
    by force
  finally show ?case
    .
qed


definition (in adjacency) difference :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" where
  "difference G1 G2 \<equiv> fold delete_2 (Map_inorder G2) G1"

lemma (in adjacency) invar_difference:
  assumes "invar G1"
  assumes "invar G2"
  shows "invar (difference G1 G2)"
proof -
  have "Ball (set (Map_inorder G2)) (S.invar \<circ> snd)"
    using assms(2)
    by (fastforce simp add: invar_def M.ran_def M.mem_inorder_iff_lookup_eq_Some)
  thus ?thesis
    unfolding difference_def
    using assms(1)
    by (intro invar_fold_delete_2)
qed

lemma (in adjacency) adjacency_difference_cong:
  assumes "invar G1"
  assumes "invar G2"
  shows
    "set (adjacency_list (difference G1 G2) v) =
     set (adjacency_list G1 v) - set (adjacency_list G2 v)"
proof -
  have "Ball (set (Map_inorder G2)) (S.invar \<circ> snd)"
    using assms(2)
    by (fastforce simp add: invar_def M.ran_def M.mem_inorder_iff_lookup_eq_Some)
  with assms(1)
  have
    "set (adjacency_list (difference G1 G2) v) =
     set (adjacency_list G1 v) - (\<Union>p\<in>set (Map_inorder G2). if v = fst p then S.set (snd p) else {})"
    unfolding difference_def
    by (intro adjacency_fold_delete_2_cong)
  also have "... = set (adjacency_list G1 v) - set (adjacency_list G2 v)"
    using assms(2)
    by (simp add: adjacency_inorder_cong)
  finally show ?thesis
    .
qed

text \<open>
We show that our specifications of operations insert and delete satisfy all assumptions of locale
@{locale Finite_Adjacency_Structure}.
\<close>

context adjacency
begin
sublocale G: Finite_Adjacency_Structure where
  empty = Map_empty and
  insert = insert' and
  delete = delete' and
  adj = "(\<lambda>v G. adjacency_list G v)" and
  inv = invar
proof (standard, goal_cases)
  case (1 v)
  show ?case
    by (simp add: adjacency_list_def M.map_empty)
next
  case (2 G u v w)
  thus ?case
    by (intro adjacency_list_insert'_cong) (drule conjunct1)
next
  case (3 G u v w)
  thus ?case
    by (intro adjacency_list_delete'_cong) (drule conjunct1)
next
  case 4
  show ?case
    using invar_empty
    .
next
  case (5 G u v)
  thus ?case
    by (intro invar_insert') (drule conjunct1)
next
  case (6 G u v)
  thus ?case
    by (intro invar_delete') (drule conjunct1)
next
  case (7 G)
  show ?case
  proof (rule finite_subset)
    show "{v. adjacency_list G v \<noteq> []} \<subseteq> M.dom G"
      by (auto simp add: adjacency_list_def M.mem_dom_iff split: option.splits)
    show "finite ..."
      using 7
      unfolding invar_def
      by (intro M.finite_dom) (drule conjunct1)
  qed
qed
end

text \<^marker>\<open>tag invisible\<close> \<open>
In the following locale, we convert a graph specified as a @{term Map_by_Ordered} mapping a vertex
to its adjacency, which is specified as a @{term Set_by_Ordered}, to a graph specified as a
@{term Set_by_Ordered} of edges. As of 2022-02-21, the locale is not used anywhere outside of this
theory.
\<close>

locale \<^marker>\<open>tag invisible\<close> fukakyo =
  G: adjacency where Map_update = Map_update +
  E: Set_by_Ordered where
  empty = E_empty and
  insert = E_insert and
  delete = E_delete and
  isin = E_isin and
  inorder = E_inorder and
  inv = E_inv for
  Map_update :: "'a::linorder \<Rightarrow> 't \<Rightarrow> 'm \<Rightarrow> 'm" and
  E_empty and
  E_insert :: "'a \<times> 'a \<Rightarrow> 's \<Rightarrow> 's" and
  E_delete and
  E_isin and
  E_inorder and
  E_inv
begin

abbreviation \<^marker>\<open>tag invisible\<close> f :: "'a \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 's" where
  "f u v \<equiv> E_insert (u, v)"

abbreviation \<^marker>\<open>tag invisible\<close> g :: "'a \<times> 't \<Rightarrow> 's \<Rightarrow> 's"  where
  "g p \<equiv> fold (f (fst p)) (Set_inorder (snd p))"

abbreviation \<^marker>\<open>tag invisible\<close> E :: "'m \<Rightarrow> 's" where
  "E G \<equiv> fold g (Map_inorder G) E_empty"

lemma \<^marker>\<open>tag invisible\<close> invar_f:
  assumes "E.invar s"
  shows "E.invar (f u v s)"
  using assms
  by (intro E.invar_insert)

lemma \<^marker>\<open>tag invisible\<close> set_f_cong:
  assumes "E.invar s"
  shows "E.set (f u v s) = E.set s \<union> {(u, v)}"
  using assms
  by (intro E.set_insert)

lemma \<^marker>\<open>tag invisible\<close> invar_fold_f:
  assumes "E.invar s"
  shows "E.invar (fold (f u) l s)"
  using assms
  by (induct l arbitrary: s) (auto intro: invar_f)

lemma \<^marker>\<open>tag invisible\<close> invar_g:
  assumes "E.invar s"
  shows "E.invar (g p s)"
  using assms
  by (intro invar_fold_f)

lemma \<^marker>\<open>tag invisible\<close> set_fold_f_cong:
  assumes "E.invar s"
  shows "E.set (fold (f u) l s) = E.set s \<union> {u} \<times> set l"
  using assms
proof (induct l arbitrary: s)
  case Nil
  show ?case
    by simp
next
  case (Cons v vs)
  have "E.set (fold (f u) (v # vs) s) = E.set (fold (f u) vs (f u v s))"
    by simp
  also have "... = E.set (f u v s) \<union> {u} \<times> set vs"
    using Cons.prems
    by (intro invar_f Cons.hyps)
  also have "... = E.set s \<union> {(u, v)} \<union> {u} \<times> set vs"
    using Cons.prems
    by (simp add: set_f_cong)
  also have "... = E.set s \<union> {u} \<times> set (v # vs)"
    by simp
  finally show ?case
    .
qed

lemma \<^marker>\<open>tag invisible\<close> set_g_cong:
  assumes "E.invar s"
  shows "E.set (g p s) = E.set s \<union> {fst p} \<times> G.S.set (snd p)"
  using assms
  by (simp add: set_fold_f_cong G.S.set_def)

lemma \<^marker>\<open>tag invisible\<close> invar_fold_g:
  assumes "E.invar s"
  shows "E.invar (fold g l s)"
  using assms
  by (induct l arbitrary: s) (auto intro: invar_g)

lemma \<^marker>\<open>tag invisible\<close> invar_E:
  shows "E.invar (E G)"
  using E.invar_empty
  by (intro invar_fold_g)

lemma \<^marker>\<open>tag invisible\<close> set_fold_g_cong:
  assumes "E.invar s"
  shows "E.set (fold g l s) = E.set s \<union> (\<Union>p\<in>set l. {fst p} \<times> G.S.set (snd p))"
  using assms
proof (induct l arbitrary: s)
  case Nil
  show ?case
    by simp
next
  case (Cons p ps)
  have "E.set (fold g (p # ps) s) = E.set (fold g ps (g p s))"
    by simp
  also have "... = E.set (g p s) \<union> (\<Union>p\<in>set ps. {fst p} \<times> G.S.set (snd p))"
    using Cons.prems
    by (intro invar_g Cons.hyps)
  also have "... = E.set s \<union> {fst p} \<times> G.S.set (snd p) \<union> (\<Union>p\<in>set ps. {fst p} \<times> G.S.set (snd p))"
    using Cons.prems
    by (simp add: set_g_cong)
  also have "... = E.set s \<union> (\<Union>q\<in>set (p # ps). {fst q} \<times> G.S.set (snd q))"
    by force
  finally show ?case
    .
qed

lemma \<^marker>\<open>tag invisible\<close> set_E_cong:
  assumes "G.invar G"
  shows "E.set (E G) = {(u, v). v \<in> set (G.adjacency_list G u)}"
  using assms E.invar_empty
  by (auto simp add: G.mem_adjacency_iff_mem_inorder set_fold_g_cong E.set_empty)

end \<^marker>\<open>tag invisible\<close> 

end