theory Map_Specs_Tbd
  imports "HOL-Data_Structures.Map_Specs"
begin

section \<open>@{term Map}\<close>

definition (in Map) dom :: "'m \<Rightarrow> 'a set" where
  "dom m \<equiv> {a. lookup m a \<noteq> None}"

lemma (in Map) mem_dom_iff:
  shows "a \<in> dom m \<longleftrightarrow> lookup m a \<noteq> None"
  by (simp add: dom_def)

definition (in Map) ran :: "'m \<Rightarrow> 'b set" where
  "ran m \<equiv> {b. \<exists>a. lookup m a = Some b}"

lemma (in Map) finite_dom_imp_finite_ran:
  assumes "finite (dom m)"
  shows "finite (ran m)"
proof -
  have "ran m = (the \<circ> lookup m) ` dom m"
    by (force simp add: ran_def dom_def)
  thus ?thesis
    using assms
    by simp
qed

section \<open>@{term Map_by_Ordered}\<close>

lemma map_of_eq_Some_imp_mem:
  assumes "map_of l a = Some b"
  shows "(a, b) \<in> set l"
  using assms
proof (induction l rule: map_of.induct)
  case 1
  thus ?case
    by simp
next
  case (2 c _ ps)
  thus ?case
    by (cases "a = c") auto
qed

(* TODO Move somewhere else. *)
lemma sorted_imp_distinct:
  assumes "sorted l"
  shows "distinct l"
  using assms
  by (simp add: strict_sorted_sorted_wrt[symmetric] strict_sorted_iff)

lemma map_of_eq_Some_if_mem:
  assumes "sorted1 l"
  assumes "(a, b) \<in> set l"
  shows "map_of l a = Some b"
  using assms
proof (induction l rule: map_of.induct)
  case 1
  thus ?case
    by simp
next
  case (2 c d ps)
  show ?case
  proof (cases "a = c")
    case True
    thus ?thesis
      using "2.prems" sorted_imp_distinct
      by force
  next
    case False
    thus ?thesis
      using "2.prems"
      by (auto intro: sorted_cons "2.IH")
  qed
qed

lemma map_of_eq_Some_iff_mem:
  assumes "sorted1 l"
  shows "map_of l a = Some b \<longleftrightarrow> (a, b) \<in> set l"
  using assms
  by (auto intro: map_of_eq_Some_imp_mem map_of_eq_Some_if_mem)

lemma (in Map_by_Ordered) mem_inorder_iff_lookup_eq_Some:
  assumes "invar m"
  shows "lookup m a = Some b \<longleftrightarrow> (a, b) \<in> set (inorder m)"
  using assms
  by (simp add: invar_def inorder_lookup map_of_eq_Some_iff_mem)

lemma (in Map_by_Ordered) dom_inorder_cong:
  assumes "invar m"
  shows "dom m = fst ` set (inorder m)"
proof -
  { fix a
    have "a \<in> dom m \<longleftrightarrow> (\<exists>b. lookup m a = Some b)"
      by (simp add: dom_def)
    also have "... \<longleftrightarrow> (\<exists>b. (a, b) \<in> set (inorder m))"
      using assms
      by (simp add: mem_inorder_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (\<exists>p\<in>set (inorder m). a = fst p)"
      by force
    also have "... \<longleftrightarrow> a \<in> fst ` set (inorder m)"
      by (simp add: image_iff)
    finally have "a \<in> dom m \<longleftrightarrow> a \<in> fst ` set (inorder m)"
      . }
  thus ?thesis
    by blast
qed

lemma (in Map_by_Ordered) finite_dom:
  assumes "invar m"
  shows "finite (dom m)"
  using assms
  by (simp add: dom_inorder_cong)

lemma (in Map_by_Ordered) finite_ran:
  assumes "invar m"
  shows "finite (ran m)"
  using assms
  by (intro finite_dom finite_dom_imp_finite_ran)

(**)
lemma (in Map_by_Ordered) set_filter_inorder_cong:
  assumes "invar m"
  shows "set (filter (\<lambda>p. fst p = a) (inorder m)) = (case lookup m a of None \<Rightarrow> {} | Some b \<Rightarrow> {(a, b)})"
proof -
  { fix p
    have "p \<in> set (filter (\<lambda>p. fst p = a) (inorder m)) \<longleftrightarrow> (\<exists>b. (a, b) \<in> set (inorder m) \<and> p = (a, b))"
      unfolding filter_set[symmetric] member_filter
      by (auto simp add: eq_fst_iff)
    also have "... \<longleftrightarrow> (\<exists>b. lookup m a = Some b \<and> p = (a, b))"
      using assms
      by (simp add: mem_inorder_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> p \<in> (case lookup m a of None \<Rightarrow> {} | Some b \<Rightarrow> {(a, b)})"
      by (simp split: option.split)
    finally have "p \<in> set (filter (\<lambda>p. fst p = a) (inorder m)) \<longleftrightarrow> p \<in> (case lookup m a of None \<Rightarrow> {} | Some b \<Rightarrow> {(a, b)})"
      . }
  thus ?thesis
    by simp
qed

(**)
lemma sorted1D:
  assumes "sorted (a # map fst ps)"
  shows "(a, y) \<notin> set ps"
proof -
  have "map_of ps a = None"
    using assms
    by (intro map_of_None) simp
  thus ?thesis
    using assms
    by (auto simp add: map_of_eq_Some_iff_mem[symmetric] dest: sorted_cons)
qed

lemma sorted1D_2:
  assumes "sorted (a # map fst ps)"
  assumes "x < a"
  shows "(x, y) \<notin> set ps"
proof -
  have "map_of ps x = None"
    using assms
    by (intro map_of_sorted_Cons) simp
  thus ?thesis
    using assms
    by (auto simp add: map_of_eq_Some_iff_mem[symmetric] dest: sorted_cons)
qed

(**)
lemma set_del_list_cong:
  assumes "sorted1 l"
  shows "set (del_list x l) = set l - set (filter (\<lambda>p. fst p = x) l)"
  using assms
proof (induct l rule: del_list.induct)
  case (1 x)
  thus ?case
    by simp
next
  case (2 x a b ps)
  show ?case
  proof (cases "x = a")
    case True
    hence "set (del_list x ((a, b) # ps)) = set ps"
      by simp
    also have "... = set ((a, b) # ps) - {(a, b)}"
      using "2.prems"
      by (auto dest: sorted1D)
    also have "... = set ((a, b) # ps) - set (filter (\<lambda>p. fst p = x) ((a, b) # ps))"
      using "2.prems" True
      by (auto dest: sorted1D)
    finally show ?thesis
      .
  next
    case False
    hence "set (del_list x ((a, b) # ps)) = set ((a, b) # del_list x ps)"
      by simp
    also have "... = {(a, b)} \<union> set (del_list x ps)"
      by force
    also have "... = {(a, b)} \<union> set ps - set (filter (\<lambda>p. fst p = x) ps)"
      using False "2.prems"
      by (subst "2.hyps") (auto dest: sorted_cons)
    also have "... = set ((a, b) # ps) - set (filter (\<lambda>p. fst p = x) ((a, b) # ps))"
      using False
      by force
    finally show ?thesis
      .
  qed
qed

lemma (in Map_by_Ordered) set_inorder_delete_cong:
  assumes "invar m"
  shows "set (inorder (delete a m)) = set (inorder m) - (case lookup m a of None \<Rightarrow> {} | Some b \<Rightarrow> {(a, b)})"
proof -
  have "set (inorder (delete a m)) = set (del_list a (inorder m))"
    using assms
    by (simp add: invar_def inorder_delete)
  also have "... = set (inorder m) - set (filter (\<lambda>p. fst p = a) (inorder m))"
    using assms
    by (simp add: invar_def set_del_list_cong)
  also have "... = set (inorder m) - (case lookup m a of None \<Rightarrow> {} | Some b \<Rightarrow> {(a, b)})"
    unfolding set_filter_inorder_cong[OF assms]
    ..
  finally show ?thesis
    .
qed

(**)
lemma set_upd_list_cong:
  assumes "sorted1 l"
  shows "set (upd_list x y l) = set l - set (filter (\<lambda>p. fst p = x) l) \<union> {(x, y)}"
  using assms
proof (induct l rule: upd_list.induct)
  case (1 x y)
  thus ?case
    by simp
next
  case (2 x y a b ps)
  consider (l) "x < a" | (e) "x = a" | (g) "x > a"
    by fastforce
  thus ?case
  proof (cases)
    case l
    have "set (upd_list x y ((a, b) # ps)) = set ((x, y) # (a, b) # ps)"
      using l
      by simp
    also have "... = set ((a, b) # ps) \<union> {(x, y)}"
      by simp
    also have "... = set ((a, b) # ps) - set (filter (\<lambda>p. fst p = x) ((a, b) # ps)) \<union> {(x, y)}"
      using "2.prems" l
      by (auto simp add: filter_empty_conv dest: sorted1D_2)
    finally show ?thesis
      .
  next
    case e
    hence "set (upd_list x y ((a, b) # ps)) = set ((x, y) # ps)"
      by simp
    also have "... = set ps \<union> {(x, y)}"
      by simp
    also have "... = set ((a, b) # ps) - {(a, b)} \<union> {(x, y)}"
      using "2.prems"
      by (auto dest: sorted1D)
    also have "... = set ((a, b) # ps) - set (filter (\<lambda>p. fst p = x) ((a, b) # ps)) \<union> {(x, y)}"
      using "2.prems" e
      by (auto dest: sorted1D)
    finally show ?thesis
      .
  next
    case g
    hence "set (upd_list x y ((a, b) # ps)) = set ((a, b) # upd_list x y ps)"
      by force
    also have "... = {(a, b)} \<union> set (upd_list x y ps)"
      by force
    also have "... = {(a, b)} \<union> set ps - set (filter (\<lambda>p. fst p = x) ps) \<union> {(x, y)}"
      using g "2.prems"
      by (subst "2.hyps") (auto dest: sorted_cons)
    also have "... = set ((a, b) # ps) - set (filter (\<lambda>p. fst p = x) ((a, b) # ps)) \<union> {(x, y)}"
      using g
      by force
    finally show ?thesis
    .
  qed
qed

lemma (in Map_by_Ordered) set_inorder_update_cong:
  assumes "invar m"
  shows "set (inorder (update a b m)) = set (inorder m) - (case lookup m a of None \<Rightarrow> {} | Some y \<Rightarrow> {(a, y)}) \<union> {(a, b)}"
proof -
  have "set (inorder (update a b m)) = set (upd_list a b (inorder m))"
    using assms
    by (simp add: invar_def inorder_update)
  also have "... = set (inorder m) - set (filter (\<lambda>p. fst p = a) (inorder m)) \<union> {(a, b)}"
    using assms
    by (simp add: invar_def set_upd_list_cong)
  also have "... = set (inorder m) - (case lookup m a of None \<Rightarrow> {} | Some y \<Rightarrow> {(a, y)}) \<union> {(a, b)}"
    unfolding set_filter_inorder_cong[OF assms]
    ..
  finally show ?thesis
    .
qed

end