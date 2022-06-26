theory \<^marker>\<open>tag invisible\<close> Misc_Ext
  imports
    "HOL-Library.Extended_Nat"
    "HOL-Data_Structures.List_Ins_Del"
    "HOL-Data_Structures.Set_Specs"
begin

subsection \<^marker>\<open>tag invisible\<close> \<open>@{type enat}\<close>

lemma \<^marker>\<open>tag invisible\<close> enat_add_strict_right_mono:
  fixes a b c :: enat
  assumes "a < b"
  assumes "c \<noteq> \<infinity>"
  shows "a + c < b + c"
  using assms
  by (metis enat_add_left_cancel_less add.commute)

lemma \<^marker>\<open>tag invisible\<close> enat_add_strict_left_mono:
  fixes a b c :: enat
  assumes "b < c"
  assumes "a \<noteq> \<infinity>"
  shows "a + b < a + c"
  using assms
  by (simp add: enat_add_left_cancel_less)

lemma \<^marker>\<open>tag invisible\<close> INF_in_image:
  fixes f :: "'a \<Rightarrow> enat"
  assumes S_finite: "finite S"
  assumes S_non_empty: "S \<noteq> {}"
  shows "Inf (f ` S) \<in> f ` S"
proof -
  have image_finite: "finite (f ` S)"
    using S_finite
    by simp
  have image_non_empty: "(f ` S) \<noteq> {}"
    using S_non_empty
    by simp

  have "Inf (f ` S) = Min (f ` S)"
    using image_finite image_non_empty
    by (rule cInf_eq_Min)
  moreover have "Min (f ` S) \<in> (f ` S)"
    using image_finite image_non_empty
    by (rule Min_in)
  ultimately show ?thesis
    by simp
qed

subsection \<^marker>\<open>tag invisible\<close> \<open>@{type list}\<close>

subsubsection \<^marker>\<open>tag invisible\<close> \<open>@{term length}\<close>

lemma \<^marker>\<open>tag invisible\<close> length_ge_2D:
  assumes "2 \<le> length l"
  shows
    "l \<noteq> []"
    "tl l \<noteq> []"
    "butlast l \<noteq> []"
proof (goal_cases)
  case 1
  show ?case
    using assms
    by fastforce
next
  case 2
  have "1 \<le> length (tl l)"
    using assms
    by fastforce
  thus ?case
    by force
next
  case 3
  have "1 \<le> length (butlast l)"
    using assms
    by fastforce
  thus ?case
    by force
qed

lemma \<^marker>\<open>tag invisible\<close> length_ge_2E:
  assumes "2 \<le> length l"
  obtains x xs y where
    "l = x # xs @ [y]"
proof (cases l)
  case Nil
  thus ?thesis
    using assms
    by simp
next
  case (Cons a l)
  hence "l \<noteq> []"
    using assms
    by force
  hence "l = butlast l @ [last l]"
    by simp
  hence "a # l = a # butlast l @ [last l]"
    by fast
  thus ?thesis
    by (auto simp add: Cons[symmetric] intro: that)
qed

lemma \<^marker>\<open>tag invisible\<close> length_butlast_tl:
  assumes "2 \<le> length l"
  shows "length (butlast (tl l)) = length l - 2"
  using assms
  by (auto simp add: tl_def elim: length_ge_2E)

subsubsection \<^marker>\<open>tag invisible\<close> \<open>@{term distinct}\<close>

lemma \<^marker>\<open>tag invisible\<close> distinct_ins_listD:
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

lemma \<^marker>\<open>tag invisible\<close> distinct_ins_listI:
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

lemma \<^marker>\<open>tag invisible\<close> distinct_ins_list_cong:
  assumes "Sorted_Less.sorted xs"
  shows "distinct (ins_list x xs) = distinct xs"
  using assms
  by (auto intro: distinct_ins_listD distinct_ins_listI)

lemma \<^marker>\<open>tag invisible\<close> distinct_imp_hd_not_mem_set_tl:
  assumes "l \<noteq> []"
  assumes "distinct l"
  shows "hd l \<notin> set (tl l)"
  using assms
  by (induct l) simp+

lemma \<^marker>\<open>tag invisible\<close> distinct_imp_last_not_mem_set_butlast:
  assumes "l \<noteq> []"
  assumes "distinct l"
  shows "last l \<notin> set (butlast l)"
  using assms
  by (induct l) auto

subsubsection \<^marker>\<open>tag invisible\<close> \<open>@{term sorted_wrt}\<close>

lemma \<^marker>\<open>tag invisible\<close> sorted_wrt_imp_hd:
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

lemma \<^marker>\<open>tag invisible\<close> sorted_wrt_imp_last_aux:
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

lemma \<^marker>\<open>tag invisible\<close> sorted_wrt_imp_last:
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

lemma \<^marker>\<open>tag invisible\<close> sorted_wrt_if:
  assumes "\<And>x y. x \<in> set l \<Longrightarrow> y \<in> set l \<Longrightarrow> P x y"
  shows "sorted_wrt P l"
  using assms
  by (simp add: sorted_wrt_iff_nth_less)

subsubsection \<^marker>\<open>tag invisible\<close> \<open>@{term sorted}\<close>

lemma \<^marker>\<open>tag invisible\<close> sorted_imp_distinct:
  assumes "sorted l"
  shows "distinct l"
  using assms
  by (simp add: strict_sorted_sorted_wrt[symmetric] strict_sorted_iff)

subsubsection \<^marker>\<open>tag invisible\<close> \<open>\<close>

lemma \<^marker>\<open>tag invisible\<close> list_split_tbd:
  assumes "l \<noteq> []"
  assumes "hd l \<noteq> last l"
  obtains l' where
    "l = hd l # l' @ [last l]"
proof
  have tl_non_empty: "tl l \<noteq> []"
    using assms Nil_tl
    by fastforce
  have "l = hd l # tl l"
    using assms(1)
    by simp
  also have "... = hd l # (butlast (tl l) @ [last (tl l)])"
    using tl_non_empty
    by simp
  finally show "l = hd l # (butlast (tl l) @ [last l])"
    using tl_non_empty
    by (simp add: last_tl)
qed

lemma \<^marker>\<open>tag invisible\<close> butlast_tl_conv:
  assumes "l1 \<noteq> []"
  assumes "l2 \<noteq> []"
  assumes "last l1 = hd l2"
  shows "butlast l1 @ l2 = l1 @ tl l2"
proof -
  have "butlast l1 @ l2 = butlast l1 @ hd l2 # tl l2"
    using assms(2)
    by simp
  also have "... = butlast l1 @ last l1 # tl l2"
    by (simp add: assms(3))
  also have "... = l1 @ tl l2"
    using assms(1)
    by simp
  finally show ?thesis
    .
qed

subsection \<^marker>\<open>tag invisible\<close> \<open>@{term Set_by_Ordered}\<close>

lemma \<^marker>\<open>tag invisible\<close> (in Set_by_Ordered) inorder_distinct:
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
    by (simp add: invar_def distinct_ins_list_cong)
  hence "distinct (ins_list x xs)"
    by (simp add: t(1))
  thus ?case
    using Cons.prems
    by (simp add: invar_def Cons.hyps(2) ins_list_Cons)
qed

end \<^marker>\<open>tag invisible\<close> 