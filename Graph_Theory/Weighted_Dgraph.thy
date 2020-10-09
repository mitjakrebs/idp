theory Weighted_Dgraph
  imports Dpath
begin

type_synonym 'a weight_fun = "'a \<times> 'a \<Rightarrow> nat"

definition edges_weight :: "'a weight_fun \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> nat" where
  "edges_weight f l = sum_list (map f l)"

definition dpath_weight :: "'a weight_fun \<Rightarrow> 'a dpath \<Rightarrow> nat" where
  "dpath_weight f p = edges_weight f (edges_of_dpath p)"

section \<open>@{term "dpath"}, @{term "dpath_bet"}\<close>

subsection \<open>Basic Lemmas\<close>

lemma edges_weight_Nil [simp]:
  shows "edges_weight f [] = 0"
  by (simp add: edges_weight_def)

lemma dpath_weight_Nil [simp]:
  shows "dpath_weight f [] = 0"
  by (simp add: dpath_weight_def)

lemma edges_weight_Cons [simp]:
  shows "edges_weight f (x # xs) = f x + edges_weight f xs"
  by (simp add: edges_weight_def)

subsection \<open>Appending\<close>

lemma edges_weight_append [simp]:
  shows "edges_weight f (xs @ ys) = edges_weight f xs + edges_weight f ys"
  by (simp add: edges_weight_def)

lemma dpath_weight_append:
  assumes "p \<noteq> []"
  shows "dpath_weight f (p @ q) = dpath_weight f p + dpath_weight f (last p # q)"
  using assms
  by (simp add: dpath_weight_def edges_of_dpath_append_3)

lemma dpath_weight_append_2:
  assumes "p \<noteq> []"
  assumes "q \<noteq> []"
  assumes "last p = hd q"
  shows "dpath_weight f (p @ tl q) = dpath_weight f p + dpath_weight f q"
  using assms
  by (simp add: dpath_weight_append)

lemma dpath_weight_append_3:
  assumes "q \<noteq> []"
  shows "dpath_weight f (p @ q) = dpath_weight f (p @ [hd q]) + dpath_weight f q"
  using assms dpath_weight_append[of "p @ [hd q]" _ "tl q"]
  by simp

lemma dpath_weight_append_append:
  assumes "p \<noteq> []"
  assumes "Suc 0 < length q"
  assumes "r \<noteq> []"
  assumes "last p = hd q"
  assumes "last q = hd r"
  shows "dpath_weight f (p @ tl q @ tl r) = dpath_weight f p + dpath_weight f q + dpath_weight f r"
proof -
  have "dpath_weight f (p @ tl q @ tl r) = dpath_weight f (p @ tl q) + dpath_weight f r"
    using assms(2, 3, 5) dpath_weight_append[where ?p = "p @ tl q"]
    by (simp add: tl_non_empty_conv last_tl)
  also have "... = dpath_weight f p + dpath_weight f q + dpath_weight f r"
    using assms(1, 2, 4)
    by (auto intro: dpath_weight_append_2)
  finally show ?thesis
    .
qed

subsection \<open>Decomposing\<close>

lemma dpath_weight_closed_dpath_bet_decomp:
  assumes "dpath_bet G p u v"
  assumes "\<not> distinct p"
  assumes "closed_dpath_bet_decomp G p = (q, r, s)"
  shows "dpath_weight f p = dpath_weight f q + dpath_weight f r + dpath_weight f s"
proof -
  obtain
    "p = q @ tl r @ tl s"
    "\<exists>w. dpath_bet G q u w \<and> closed_dpath_bet G r w \<and> dpath_bet G s w v"
    using assms
    by (elim closed_dpath_bet_decompE_2)
  thus ?thesis
    by (auto simp add: dpath_bet_nonempty_dpath(3, 4) intro: dpath_weight_append_append)
qed

section \<open>@{term "distinct_dpath_bet"}\<close>

lemma dpath_weight_ge_dpath_bet_to_distinct_weight:
  assumes "dpath_bet G p u v"
  shows "dpath_weight f (dpath_bet_to_distinct G p) \<le> dpath_weight f p"
  using assms
proof (induction rule: dpath_bet_to_distinct_induct)
  case path
  thus ?case
    by simp
next
  case (decomp p q r s)
  have dpaths: "\<exists>w. dpath_bet G q u w \<and> closed_dpath_bet G r w \<and> dpath_bet G s w v"
    using decomp.hyps
    by (elim closed_dpath_bet_decompE_2)

  have "dpath_weight f (dpath_bet_to_distinct G p) = dpath_weight f (dpath_bet_to_distinct G (q @ tl s))"
    using decomp.hyps(1, 2)
    by (auto simp add: decomp.hyps(3))
  also have "... \<le> dpath_weight f (q @ tl s)"
    using decomp.IH
    .
  also have "... = dpath_weight f q + dpath_weight f s"
    using dpaths
    by (auto simp add: dpath_bet_nonempty_dpath(3, 4) intro: dpath_weight_append_2)
  also have "... \<le> dpath_weight f q + dpath_weight f r + dpath_weight f s"
    by simp
  also have "... = dpath_weight f p"
    using decomp.hyps
    by (intro dpath_weight_closed_dpath_bet_decomp[symmetric])
  finally show ?case
    .
qed

section \<open>\<close>

lemma dpath_length_eq_dpath_weight:
  shows "dpath_length p = dpath_weight (\<lambda>_. 1) p"
proof (induction p rule: dpath_induct)
case 1
  thus ?case
    by simp
next
  case (2 _)
  thus ?case
    by (simp add: dpath_weight_def)
next
  case (3 v v' vs)
  let ?f = "(\<lambda>_. 1)"
  have "dpath_length (v # v' # vs) = 1 + dpath_length (v' # vs)"
    by simp
  also have "... = 1 + dpath_weight ?f (v' # vs)"
    by (simp add: "3.IH")
  also have "... = ?f (v, v') + edges_weight ?f (edges_of_dpath (v' # vs))"
    by (simp add: dpath_weight_def)
  also have "... = dpath_weight ?f (v # v' # vs)"
    by (simp add: dpath_weight_def)
  finally show ?case
    .
qed

end