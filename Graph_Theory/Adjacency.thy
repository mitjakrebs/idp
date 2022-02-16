theory Adjacency
  imports
    "HOL-Data_Structures.Set_Specs"
    "../Map_Specs_Tbd"
    "../Orderings_Tbd"
begin

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

definition (in adjacency) adjacency :: "'m \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "adjacency G u \<equiv> case Map_lookup G u of None \<Rightarrow> [] | Some s \<Rightarrow> Set_inorder s"

subsection \<open>\<close>

subsubsection \<open>@{term adjacency.invar}\<close>

lemma (in adjacency) invarD:
  assumes "invar G"
  shows
    "M.invar G"
    "Ball (M.ran G) S.invar"
  using assms
  by (simp_all add: invar_def)

lemma (in adjacency) invar_empty:
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

lemma (in adjacency) invar_update:
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

subsubsection \<open>@{term adjacency.adjacency}\<close>

lemma (in adjacency) finite_adjacency:
  shows "finite (set (adjacency G v))"
  using finite_set
  .

lemma (in adjacency) distinct_adjacency:
  assumes "invar G"
  shows "distinct (adjacency G v)"
  using assms
  unfolding adjacency_def
  by (cases "Map_lookup G v") (auto simp add: invar_def M.ran_def S.invar_def intro: sorted_imp_distinct)

lemma (in adjacency) mem_adjacency_iff:
  shows "v \<in> set (adjacency G u) \<longleftrightarrow> (\<exists>s. Map_lookup G u = Some s \<and> v \<in> S.set s)"
  by (force simp add: adjacency_def S.set_def)

lemma (in adjacency) mem_adjacencyE:
  assumes "v \<in> set (adjacency G u)"
  obtains s where
    "Map_lookup G u = Some s"
    "v \<in> S.set s"
  using assms
  by (auto simp add: mem_adjacency_iff)

lemma (in adjacency) mem_adjacency_iff_2:
  assumes "invar G"
  shows "v \<in> set (adjacency G u) \<longleftrightarrow> (\<exists>s. (u, s) \<in> set (Map_inorder G) \<and> v \<in> S.set s)"
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
    by (simp add: S.set_def adjacency_def)
qed

lemma (in adjacency) adjacency_inorder_cong:
  assumes "invar m"
  shows "set (adjacency m a) = (\<Union>p\<in>set (Map_inorder m). if a = fst p then S.set (snd p) else {})"
proof -
  { fix b
    have "b \<in> set (adjacency m a) \<longleftrightarrow> (\<exists>s. (a, s) \<in> set (Map_inorder m) \<and> b \<in> S.set s)"
      using assms
      by (intro mem_adjacency_iff_2)
    also have "... \<longleftrightarrow> (\<exists>p\<in>set (Map_inorder m). a = fst p \<and> b \<in> S.set (snd p))"
      by force
    also have "... \<longleftrightarrow> b \<in> (\<Union>p\<in>set (Map_inorder m). if a = fst p then S.set (snd p) else {})"
      by auto
    finally have "b \<in> set (adjacency m a) \<longleftrightarrow> b \<in> (\<Union>p\<in>set (Map_inorder m). if a = fst p then S.set (snd p) else {})"
      . }
  thus ?thesis
    by blast
qed

subsection \<open>Union\<close>

definition (in adjacency) f :: "'a \<times> 's \<Rightarrow> 'm \<Rightarrow> 'm" where
  "f p m \<equiv>
   let a = fst p; s = snd p
   in case Map_lookup m a of
        None \<Rightarrow> Map_update a s m |
        Some s' \<Rightarrow> Map_update a (fold Set_insert (Set_inorder s) s') m"

abbreviation (in adjacency) union :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" where
  "union m1 m2 \<equiv> fold f (Map_inorder m2) m1"

subsubsection \<open>\<close>

lemma (in adjacency) invar_fold_insert:
  assumes "S.invar s"
  shows "S.invar (fold Set_insert l s)"
  using assms
  by (induct l arbitrary: s) (auto intro: S.invar_insert)

lemma (in adjacency) fold_insert_cong:
  assumes "S.invar s"
  shows "S.set (fold Set_insert l s) = S.set s \<union> set l"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons v vs)
  have "S.set (fold Set_insert (v # vs) s) = S.set (fold Set_insert vs (Set_insert v s))"
    by force
  also have "... = S.set (Set_insert v s) \<union> set vs"
    using Cons.prems
    by (intro S.invar_insert Cons.hyps)
  also have "... = S.set s \<union> {v} \<union> set vs"
    using Cons.prems
    by (simp add: S.set_insert)
  also have "... = S.set s \<union> set (v # vs)"
    by simp
  finally show ?case
    .
qed

subsubsection \<open>@{term adjacency.f}\<close>

lemma (in adjacency) invar_f:
  assumes "invar m"
  assumes "S.invar (snd p)"
  shows "invar (f p m)"
proof (cases "Map_lookup m (fst p)")
  case None
  thus ?thesis
    using assms
    by (auto simp add: f_def intro: invar_update)
next
  case (Some s)
  hence "S.invar s"
    using assms(1)
    by (auto simp add: invar_def M.ran_def)
  thus ?thesis
    using assms(1)
    by (auto simp add: f_def Some intro: invar_fold_insert invar_update)
qed

lemma (in adjacency) f_cong:
  assumes "invar m"
  assumes "S.invar (snd p)"
  shows "set (adjacency (f p m) a) = set (adjacency m a) \<union> (if a = fst p then S.set (snd p) else {})"
proof (cases "Map_lookup m (fst p)")
  case None
  { fix b
    have "b \<in> set (adjacency (f p m) a) \<longleftrightarrow> b \<in> set (adjacency (Map_update (fst p) (snd p) m) a)"
      by (simp add: f_def None)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) (snd p) m) a = Some s \<and> b \<in> S.set s)"
      by (simp add: mem_adjacency_iff)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup m(fst p \<mapsto> snd p)) a = Some s \<and> b \<in> S.set s)"
      using assms(1)
      by (auto simp add: M.map_update dest: invarD(1))
    also have "... \<longleftrightarrow> b \<in> set (adjacency m a) \<union> (if a = fst p then S.set (snd p) else {})"
      by (auto simp add: None mem_adjacency_iff)
    finally have
      "b \<in> set (adjacency (f p m) a) \<longleftrightarrow>
       b \<in> set (adjacency m a) \<union> (if a = fst p then S.set (snd p) else {})"
      . }
  thus ?thesis
    by blast
next
  case (Some s')
  hence invar: "S.invar s'"
    using assms(1)
    by (auto simp add: invar_def M.ran_def)
  let ?fold = "fold Set_insert (Set_inorder (snd p)) s'"
  { fix b
    have
      "b \<in> set (adjacency (f p m) a) \<longleftrightarrow> b \<in> set (adjacency (Map_update (fst p) ?fold m) a)"
      by (simp add: f_def Some)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) ?fold m) a = Some s \<and> b \<in> S.set s)"
      by (simp add: mem_adjacency_iff)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup m(fst p \<mapsto> ?fold)) a = Some s \<and> b \<in> S.set s)"
      using assms(1)
      by (auto simp add: M.map_update dest: invarD(1))
    also have "... \<longleftrightarrow> b \<in> set (adjacency m a) \<union> (if a = fst p then S.set (snd p) else {})"
      using invar fold_insert_cong Some
      by (simp add: S.set_def mem_adjacency_iff)
    finally have
      "b \<in> set (adjacency (f p m) a) \<longleftrightarrow>
       b \<in> set (adjacency m a) \<union> (if a = fst p then S.set (snd p) else {})"
      . }
  thus ?thesis
    by blast
qed

subsubsection \<open>\<close>

lemma (in adjacency) invar_fold_f:
  assumes "invar m"
  assumes "Ball (set l) (S.invar \<circ> snd)"
  shows "invar (fold f l m)"
  using assms
proof (induct l arbitrary: m)
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
    by (fastforce intro: invar_f Cons.hyps)
qed

lemma (in adjacency) fold_f_cong:
  assumes "invar m"
  assumes "Ball (set l) (S.invar \<circ> snd)"
  shows
    "set (adjacency (fold f l m) a) =
     set (adjacency m a) \<union> (\<Union>p\<in>set l. if a = fst p then S.set (snd p) else {})"
  using assms
proof (induct l arbitrary: m)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  hence
    prems: "S.invar (snd p)"
    "Ball (set ps) (S.invar \<circ> snd)"
    by simp+

  have "set (adjacency (fold f (p # ps) m) a) = set (adjacency (fold f ps (f p m)) a)"
    by simp
  also have "... = set (adjacency (f p m) a) \<union> (\<Union>p\<in>set ps. if a = fst p then S.set (snd p) else {})"
    using Cons.prems(1) prems
    by (intro invar_f Cons.hyps)
  also have
    "... =
     set (adjacency m a) \<union>
     (if a = fst p then S.set (snd p) else {}) \<union>
     (\<Union>p\<in>set ps. if a = fst p then S.set (snd p) else {})"
    using Cons.prems(1) prems(1)
    by (simp add: f_cong)
  also have "... = set (local.adjacency m a) \<union> (\<Union>p\<in>set (p # ps). if a = fst p then S.set (snd p) else {})"
    by force
  finally show ?case
    .
qed

subsubsection \<open>@{term adjacency.union}\<close>

lemma (in adjacency) invar_union:
  assumes "invar m1"
  assumes "invar m2"
  shows "invar (union m1 m2)"
proof -
  have "Ball (set (Map_inorder m2)) (S.invar \<circ> snd)"
    using assms(2)
    by (fastforce simp add: invar_def M.ran_def M.mem_inorder_iff_lookup_eq_Some)
  thus ?thesis
    using assms(1)
    by (intro invar_fold_f)
qed

lemma (in adjacency) adjacency_union_cong:
  assumes "invar m1"
  assumes "invar m2"
  shows "set (adjacency (union m1 m2) a) = set (adjacency m1 a) \<union> set (adjacency m2 a)"
proof -
  have "Ball (set (Map_inorder m2)) (S.invar \<circ> snd)"
    using assms(2)
    by (fastforce simp add: invar_def M.ran_def M.mem_inorder_iff_lookup_eq_Some)
  with assms(1)
  have
    "set (adjacency (union m1 m2) a) =
     set (adjacency m1 a) \<union> (\<Union>p\<in>set (Map_inorder m2). if a = fst p then S.set (snd p) else {})"
    by (intro fold_f_cong)
  also have "... = set (adjacency m1 a) \<union> set (adjacency m2 a)"
    using assms(2)
    by (simp add: adjacency_inorder_cong)
  finally show ?thesis
    .
qed

subsection \<open>Difference\<close>

definition (in adjacency) g :: "'a \<times> 's \<Rightarrow> 'm \<Rightarrow> 'm" where
  "g p m \<equiv>
   let a = fst p; s = snd p
   in case Map_lookup m a of
        None \<Rightarrow> m |
        Some s' \<Rightarrow> Map_update a (fold Set_delete (Set_inorder s) s') m"

abbreviation (in adjacency) difference :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" where
  "difference m1 m2 \<equiv> fold g (Map_inorder m2) m1"

subsubsection \<open>\<close>

lemma (in adjacency) invar_fold_delete:
  assumes "S.invar s"
  shows "S.invar (fold Set_delete l s)"
  using assms
  by (induct l arbitrary: s) (auto intro: S.invar_delete)

lemma (in adjacency) fold_delete_cong:
  assumes "S.invar s"
  shows "S.set (fold Set_delete l s) = S.set s - set l"
  using assms
proof (induct l arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons a l)
  have "S.set (fold Set_delete (a # l) s) = S.set (fold Set_delete l (Set_delete a s))"
    by simp
  also have "... = S.set (Set_delete a s) - set l"
    using Cons.prems
    by (intro S.invar_delete Cons.hyps)
  also have "... = S.set s - {a} - set l"
    using Cons.prems
    by (simp add: S.set_delete)
  also have "... = S.set s - set (a # l)"
    by auto
  finally show ?case
    .
qed

subsubsection \<open>@{term adjacency.g}\<close>

lemma (in adjacency) invar_g:
  assumes "invar m"
  shows "invar (g p m)"
proof (cases "Map_lookup m (fst p)")
  case None
  thus ?thesis
    using assms
    by (simp add: g_def)
next
  case (Some s)
  hence "S.invar s"
    using assms
    by (auto simp add: invar_def M.ran_def)
  thus ?thesis
    using assms
    by (auto simp add: g_def Some intro: invar_fold_delete invar_update)
qed

lemma (in adjacency) g_cong:
  assumes "invar m"
  shows "set (adjacency (g p m) a) = set (adjacency m a) - (if a = fst p then S.set (snd p) else {})"
proof (cases "Map_lookup m (fst p)")
  case None
  thus ?thesis
    by (simp add: adjacency_def g_def)
next
  case (Some s')
  hence invar: "S.invar s'"
    using assms
    by (auto simp add: invar_def M.ran_def)
  let ?fold = "fold Set_delete (Set_inorder (snd p)) s'"
  { fix b
    have "b \<in> set (adjacency (g p m) a) \<longleftrightarrow> b \<in> set (adjacency (Map_update (fst p) ?fold m) a)"
      by (simp add: g_def Some)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) ?fold m) a = Some s \<and> b \<in> S.set s)"
      by (simp add: mem_adjacency_iff)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup m(fst p \<mapsto> ?fold)) a = Some s \<and> b \<in> S.set s)"
      using assms
      by (auto simp add: M.map_update dest: invarD(1))
    also have "... \<longleftrightarrow> b \<in> set (adjacency m a) - (if a = fst p then S.set (snd p) else {})"
      using invar fold_delete_cong Some
      by (simp add: S.set_def mem_adjacency_iff)
    finally have
      "b \<in> set (adjacency (g p m) a) \<longleftrightarrow>
       b \<in> set (adjacency m a) - (if a = fst p then S.set (snd p) else {})"
      . }
  thus ?thesis
    by blast
qed

subsubsection \<open>\<close>

lemma (in adjacency) invar_fold_g:
  assumes "invar m"
  assumes "Ball (set l) (S.invar \<circ> snd)"
  shows "invar (fold g l m)"
  using assms
proof (induct l arbitrary: m)
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
    thm invar_g Cons.hyps
    by (fastforce intro: invar_g Cons.hyps)
qed

lemma (in adjacency) fold_g_cong:
  assumes "invar m"
  assumes "Ball (set l) (S.invar \<circ> snd)"
  shows
    "set (adjacency (fold g l m) a) =
     set (adjacency m a) - (\<Union>p\<in>set l. if a = fst p then S.set (snd p) else {})"
  using assms
proof (induct l arbitrary: m)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  hence
    prems: "S.invar (snd p)"
    "Ball (set ps) (S.invar \<circ> snd)"
    by simp+

  have "set (adjacency (fold g (p # ps) m) a) = set (adjacency (fold g ps (g p m)) a)"
    by simp
  also have "... = set (adjacency (g p m) a) - (\<Union>p\<in>set ps. if a = fst p then S.set (snd p) else {})"
    using Cons.prems(1) prems
    by (intro invar_g Cons.hyps)
  also have
    "... =
     set (adjacency m a) -
     (if a = fst p then S.set (snd p) else {}) -
     (\<Union>p\<in>set ps. if a = fst p then S.set (snd p) else {})"
    using Cons.prems(1) prems(1)
    by (simp add: g_cong)
  also have "... = set (local.adjacency m a) - (\<Union>p\<in>set (p # ps). if a = fst p then S.set (snd p) else {})"
    by force
  finally show ?case
    .
qed

subsubsection \<open>@{term adjacency.difference}\<close>

lemma (in adjacency) invar_difference:
  assumes "invar m1"
  assumes "invar m2"
  shows "invar (difference m1 m2)"
proof -
  have "Ball (set (Map_inorder m2)) (S.invar \<circ> snd)"
    using assms(2)
    by (fastforce simp add: invar_def M.ran_def M.mem_inorder_iff_lookup_eq_Some)
  thus ?thesis
    using assms(1)
    by (intro invar_fold_g)
qed

lemma (in adjacency) adjacency_difference_cong:
  assumes "invar m1"
  assumes "invar m2"
  shows "set (adjacency (difference m1 m2) a) = set (adjacency m1 a) - set (adjacency m2 a)"
proof -
  have "Ball (set (Map_inorder m2)) (S.invar \<circ> snd)"
    using assms(2)
    by (fastforce simp add: invar_def M.ran_def M.mem_inorder_iff_lookup_eq_Some)
  with assms(1)
  have
    "set (adjacency (difference m1 m2) a) =
     set (adjacency m1 a) - (\<Union>p\<in>set (Map_inorder m2). if a = fst p then S.set (snd p) else {})"
    by (intro fold_g_cong)
  also have "... = set (adjacency m1 a) - set (adjacency m2 a)"
    using assms(2)
    by (simp add: adjacency_inorder_cong)
  finally show ?thesis
    .
qed

section \<open>\<close>

locale adjacency' = adjacency where
  Map_update = Map_update for
  Map_update :: "'a::linorder \<Rightarrow> 't \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes G :: 'm
  assumes invar: "invar G"

locale symmetric_adjacency = adjacency' where
  Map_update = Map_update for
  Map_update :: "'a::linorder \<Rightarrow> 't \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes symmetric: "v \<in> set (adjacency G u) \<longleftrightarrow> u \<in> set (adjacency G v)"

lemmas (in symmetric_adjacency) invar = invar

abbreviation (in adjacency) symmetric_adjacency' :: "'m \<Rightarrow> bool" where
  "symmetric_adjacency' G \<equiv>
   symmetric_adjacency
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    G
    Map_update"

section \<open>\<close>

locale fukakyo =
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

abbreviation f :: "'a \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 's" where
  "f u v \<equiv> E_insert (u, v)"

abbreviation g :: "'a \<times> 't \<Rightarrow> 's \<Rightarrow> 's"  where
  "g p \<equiv> fold (f (fst p)) (Set_inorder (snd p))"

abbreviation E :: "'m \<Rightarrow> 's" where
  "E G \<equiv> fold g (Map_inorder G) E_empty"

subsection \<open>@{term f}\<close>

subsubsection \<open>@{term E.invar}\<close>

lemma f_invar:
  assumes "E.invar s"
  shows "E.invar (f u v s)"
  using assms
  by (intro E.invar_insert)

subsubsection \<open>@{term E.set}\<close>

lemma set_f_cong:
  assumes "E.invar s"
  shows "E.set (f u v s) = E.set s \<union> {(u, v)}"
  using assms
  by (intro E.set_insert)

subsection \<open>@{term g}\<close>

subsubsection \<open>@{term E.invar}\<close>

lemma fold_f_invar:
  assumes "E.invar s"
  shows "E.invar (fold (f u) l s)"
  using assms
  by (induct l arbitrary: s) (auto intro: f_invar)

lemma g_invar:
  assumes "E.invar s"
  shows "E.invar (g p s)"
  using assms
  by (intro fold_f_invar)

subsubsection \<open>@{term E.set}\<close>

lemma set_fold_f_cong:
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
    by (intro f_invar Cons.hyps)
  also have "... = E.set s \<union> {(u, v)} \<union> {u} \<times> set vs"
    using Cons.prems
    by (simp add: set_f_cong)
  also have "... = E.set s \<union> {u} \<times> set (v # vs)"
    by simp
  finally show ?case
    .
qed

lemma set_g_cong:
  assumes "E.invar s"
  shows "E.set (g p s) = E.set s \<union> {fst p} \<times> G.S.set (snd p)"
  using assms
  by (simp add: set_fold_f_cong G.S.set_def)

subsection \<open>@{term E}\<close>

subsubsection \<open>@{term E.invar}\<close>

lemma fold_g_invar:
  assumes "E.invar s"
  shows "E.invar (fold g l s)"
  using assms
  by (induct l arbitrary: s) (auto intro: g_invar)

lemma E_invar:
  shows "E.invar (E G)"
  using E.invar_empty
  by (intro fold_g_invar)

subsubsection \<open>@{term E.set}\<close>

lemma set_fold_g_cong:
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
    by (intro g_invar Cons.hyps)
  also have "... = E.set s \<union> {fst p} \<times> G.S.set (snd p) \<union> (\<Union>p\<in>set ps. {fst p} \<times> G.S.set (snd p))"
    using Cons.prems
    by (simp add: set_g_cong)
  also have "... = E.set s \<union> (\<Union>q\<in>set (p # ps). {fst q} \<times> G.S.set (snd q))"
    by force
  finally show ?case
    .
qed

lemma mem_adjacency_iff_2:
  assumes "G.invar G"
  shows "v \<in> set (G.adjacency G u) \<longleftrightarrow> (\<exists>s. (u, s) \<in> set (Map_inorder G) \<and> v \<in> G.S.set s)"
proof (standard, goal_cases)
  case 1
  then obtain s where
    "Map_lookup G u = Some s"
    "v \<in> G.S.set s"
    by (elim G.mem_adjacencyE)
  thus ?case
    using assms
    by (force simp add: G.M.mem_inorder_iff_lookup_eq_Some dest: G.invarD(1))
next
  case 2
  then obtain s where
    "(u, s) \<in> set (Map_inorder G) \<and> v \<in> G.S.set s"
    by (elim exE)
  hence "Map_lookup G u = Some s \<and> v \<in> G.S.set s"
    using assms
    by (auto simp add: G.M.mem_inorder_iff_lookup_eq_Some dest: G.invarD(1))
  thus ?case
    by (simp add: G.S.set_def G.adjacency_def)
qed

lemma set_E_cong:
  assumes "G.invar G"
  shows "E.set (E G) = {(u, v). v \<in> set (G.adjacency G u)}"
  using assms E.invar_empty
  by (auto simp add: mem_adjacency_iff_2 set_fold_g_cong E.set_empty)

end

end