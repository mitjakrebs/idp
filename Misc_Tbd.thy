theory Misc_Tbd
  imports
    "HOL-Data_Structures.List_Ins_Del"
    "HOL-Data_Structures.Set_Specs"
    Queue_Specs
begin

section \<open>list\<close>

subsection \<open>@{term ins_list}\<close>

lemma ins_list_distinct_imp:
  assumes "distinct (ins_list x xs)"
  shows "distinct xs"
  using assms
proof (induction xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons y ys)
  consider
    (l) "x < y" |
    (eq) "x = y" |
    (g) "\<not> x < y \<and> \<not> x = y"
    by fastforce
  thus ?case
  proof (cases)
    case l
    thus ?thesis
      using Cons.prems
      by fastforce
  next
    case eq
    thus ?thesis
      using Cons.prems
      by simp
  next
    case g
    hence
      "y \<notin> set (ins_list x ys)"
      "distinct (ins_list x ys)"
      using Cons.prems
      by simp+
    hence
      "y \<notin> set ys"
      "distinct ys"
      by (auto simp add: set_ins_list intro: Cons.IH)
    thus ?thesis
      by simp
  qed
qed

lemma ins_list_distinct_if:
  assumes "Sorted_Less.sorted xs"
  assumes "distinct xs"
  shows "distinct (ins_list x xs)"
  using assms
proof (induction xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons y ys)
  consider
    (l) "x < y" |
    (eq) "x = y" |
    (g) "\<not> x < y \<and> \<not> x = y"
    by fastforce
  thus ?case
  proof (cases)
    case l
    thus ?thesis
      using Cons.prems
      by fastforce
  next
    case eq
    thus ?thesis
      using Cons.prems
      by simp
  next
    case g
    hence "y \<notin> set (ins_list x ys)"
      using Cons.prems
      by (auto simp add: set_ins_list)
    moreover have "distinct (ins_list x ys)"
      using Cons.prems
      by (auto intro: Cons.IH)
    ultimately show ?thesis
      using g
      by force
  qed
qed

lemma ins_list_distinct_cong:
  assumes "Sorted_Less.sorted xs"
  shows "distinct (ins_list x xs) = distinct xs"
  using assms
  by (auto intro: ins_list_distinct_imp ins_list_distinct_if)

subsection \<open>@{term sorted_wrt}\<close>

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

lemma sorted_wrt_if:
  assumes "\<And>x y. x \<in> set l \<Longrightarrow> y \<in> set l \<Longrightarrow> P x y"
  shows "sorted_wrt P l"
  using assms
  by (simp add: sorted_wrt_iff_nth_less)

section \<open>@{term Queue}\<close>

lemma (in Queue) list_queue:
  assumes "invar q"
  assumes "list q \<noteq> []"
  shows "list q = head q # list (tail q)"
  using assms
  by (simp add: list_head list_tail)

section \<open>@{term Set_by_Ordered}\<close>

lemma (in Set_by_Ordered) inorder_distinct:
  assumes "invar s"
  shows "distinct (inorder s)"
  using assms
proof (induct "inorder s" arbitrary: s)
  case Nil
  thus ?case
    by simp
next
  case (Cons x xs)
  have "xs = List_Ins_Del.del_list x (x # xs)"
    by simp
  also have "... = inorder (delete x s)"
    using Cons.prems
    by (simp add: Cons.hyps(2) invar_def inorder_delete)
  finally obtain t where t:
    "xs = inorder t"
    "invar t"
    using Cons.prems
    by (blast intro: invar_delete)
  hence "distinct (inorder t)"
    by (rule Cons.hyps(1))
  hence "distinct (ins_list x (inorder t))"
    using t(2)
    by (simp add: invar_def ins_list_distinct_cong)
  hence "distinct (ins_list x xs)"
    by (simp add: t(1))
  thus ?case
    using Cons.prems
    by (simp add: invar_def Cons.hyps(2) ins_list_Cons)
qed

end