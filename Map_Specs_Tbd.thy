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

lemma (in Map) dom_finite_imp_ran_finite:
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

lemma (in Map_by_Ordered) dom_finite:
  assumes "invar m"
  shows "finite (dom m)"
  using assms
  by (simp add: dom_inorder_cong)

lemma (in Map_by_Ordered) ran_finite:
  assumes "invar m"
  shows "finite (ran m)"
  using assms
  by (intro dom_finite dom_finite_imp_ran_finite)

end