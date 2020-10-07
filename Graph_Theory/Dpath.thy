theory Dpath
  imports
    Dgraph
    Ports.Berge_to_DDFS
    Ports.Mitja_to_DDFS
    Ports.Noschinski_to_DDFS
begin

type_synonym 'a dpath = "'a list"

lemmas dpath_induct = edges_of_dpath.induct

lemma dpath_rev_induct:
  assumes "P []"
  assumes "\<And>v. P [v]"
  assumes "\<And>u v l. P (l @ [u]) \<Longrightarrow> P (l @ [u, v])"
  shows "P p"
  using assms
proof (induct "rev p" arbitrary: p rule: dpath_induct)
  case 1
  thus ?case
    by simp
next
  case (2 _)
  thus ?case
    by simp
next
  case (3 v v' l)
  have "rev l @ [v'] @ [v] = p"
    using "3.hyps"(2)
    unfolding append.assoc[symmetric] rev.simps(2)[symmetric]
    by auto
  hence "rev l @ [v', v] = p"
    by simp
  moreover have "P (rev l @ [v', v])"
    using 3
    by simp
  ultimately show ?case
    by simp
qed

text \<open>The length of a @{term dpath} is the number of its edges.\<close>

abbreviation dpath_length :: "'a dpath \<Rightarrow> nat" where
  "dpath_length p \<equiv> length (edges_of_dpath p)"


lemma dpath_length_Cons:
  assumes "vs \<noteq> []"
  shows "dpath_length (v # vs) = dpath_length vs + 1"
  apply (subst hd_Cons_tl[OF assms, symmetric])
  apply (subst edges_of_dpath.simps(3))
  apply (subst list.size(4))
  apply (subst hd_Cons_tl[OF assms])
  apply (subst One_nat_def)
  ..

lemma dpath_length_snoc:
  assumes "vs \<noteq> []"
  shows "dpath_length (vs @ [v]) = dpath_length vs + 1"
  using assms
  by (simp add: edges_of_dpath_append_3)

lemma dpath_length_append:
  assumes "p \<noteq> []"
  shows "dpath_length (p @ q) = dpath_length p + dpath_length (last p # q)"
  using assms
  by (simp add: edges_of_dpath_append_3)

lemma dpath_length_append_2:
  assumes "p \<noteq> []"
  assumes "q \<noteq> []"
  assumes "last p = hd q"
  shows "dpath_length (p @ tl q) = dpath_length p + dpath_length q"
  using assms
  by (simp add: dpath_length_append)

section \<open>Reachability\<close>

lemma reachable_iff_dpath_bet:
  shows "reachable G u v \<longleftrightarrow> (\<exists>p. dpath_bet G p u v)"
  by (auto simp add: reachable_awalk intro: awalk_imp_dpath dpath_imp_awalk)

lemma reachable_trans:
  assumes "reachable G u v"
  assumes "reachable G v w"
  shows "reachable G u w"
  using assms
  by (blast intro: trancl_trans)

end