theory Dpath
  imports
    Dgraph
    Ports.Berge_to_DDFS
    Ports.Mitja_to_DDFS
    Ports.Noschinski_to_DDFS
begin

text \<open>
A directed path (@{term dpath} and @{term dpath_bet}) is a sequence $v_0,\dots,v_k$ of vertices such
that $(v_{i-1},v_i)$ is an edge for every $i=1,\dots,k$.
\<close>

type_synonym 'a dpath = "'a list"

lemmas dpath_induct = edges_of_dpath.induct

lemma \<^marker>\<open>tag invisible\<close> dpath_betD:
  assumes "dpath_bet G p u v"
  shows
    "dpath G p"
    "p \<noteq> []"
    "hd p = u"
    "last p = v"
  using assms
  by (simp_all add: dpath_bet_def)

lemma \<^marker>\<open>tag invisible\<close> dpath_betI:
  assumes "dpath G p"
  assumes "p \<noteq> []"
  assumes "hd p = u"
  assumes "last p = v"
  shows "dpath_bet G p u v"
  using assms
  by (simp add: dpath_bet_def)

lemma \<^marker>\<open>tag invisible\<close> dpath_bet_ConsI:
  assumes "(u, v) \<in> G"
  assumes "dpath_bet G p v w"
  shows "dpath_bet G (u # p) u w"
proof (rule dpath_betI)
  show "dpath G (u # p)"
    using assms
    by (auto dest: dpath_betD(1, 3) intro: dpathI)
  show "last (u # p) = w"
    using assms(2)
    by (auto dest: dpath_betD(4))
qed simp+

lemma \<^marker>\<open>tag invisible\<close> dpath_bet_snocI:
  assumes "dpath_bet G p u v"
  assumes "(v, w) \<in> G"
  shows "dpath_bet G (p @ [w]) u w"
proof (rule dpath_betI)
  show "dpath G (p @ [w])"
    using assms
    by (auto dest: dpath_betD(1, 4) intro: dpath_append_single)
  show "hd (p @ [w]) = u"
    using assms(1)
    by (auto dest: dpath_betD(3))
qed simp+

lemma dpath_rev_induct:
  assumes "P []"
  assumes "\<And>v. P [v]"
  assumes "\<And>v v' l. P (l @ [v]) \<Longrightarrow> P (l @ [v, v'])"
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

text \<open>The length of a @{type dpath} is the number of its edges.\<close>

abbreviation dpath_length :: "'a dpath \<Rightarrow> nat" where
  "dpath_length p \<equiv> length (edges_of_dpath p)"

lemma \<^marker>\<open>tag invisible\<close> dpath_length_geq_1I:
  assumes "dpath_bet G p u v"
  assumes "u \<noteq> v"
  shows "1 \<le> dpath_length p"
  using assms
proof (induct p rule: dpath_induct)
  case 2
  thus ?case
    using hd_of_dpath_bet' last_of_dpath_bet
    by fastforce
qed simp+

lemma \<^marker>\<open>tag invisible\<close> dpath_length_Cons:
  assumes "vs \<noteq> []"
  shows "dpath_length (v # vs) = dpath_length vs + 1"
  apply (subst hd_Cons_tl[OF assms, symmetric])
  apply (subst edges_of_dpath.simps(3))
  apply (subst list.size(4))
  apply (subst hd_Cons_tl[OF assms])
  apply (subst One_nat_def)
  ..

lemma \<^marker>\<open>tag invisible\<close> dpath_length_snoc:
  assumes "vs \<noteq> []"
  shows "dpath_length (vs @ [v]) = dpath_length vs + 1"
  using assms
  by (simp add: edges_of_dpath_append_3)

lemma \<^marker>\<open>tag invisible\<close> dpath_length_append:
  assumes "p \<noteq> []"
  shows "dpath_length (p @ q) = dpath_length p + dpath_length (last p # q)"
  using assms
  by (simp add: edges_of_dpath_append_3)

lemma \<^marker>\<open>tag invisible\<close> dpath_length_append_2:
  assumes "p \<noteq> []"
  assumes "q \<noteq> []"
  assumes "last p = hd q"
  shows "dpath_length (p @ tl q) = dpath_length p + dpath_length q"
  using assms
  by (simp add: dpath_length_append)

lemma \<^marker>\<open>tag invisible\<close> closed_dpath_bet_decompE_3:
  assumes "dpath_bet G p u v"
  assumes "\<not> distinct p"
  assumes "closed_dpath_bet_decomp G p = (q, r, s)"
  obtains
    "q \<noteq> []"
    "s \<noteq> []"
    "last q = hd s"
proof
  have
    "p = q @ tl r @ tl s"
    "\<exists>w. dpath_bet G q u w \<and> closed_dpath_bet G r w \<and> dpath_bet G s w v"
    using assms
    by (blast elim: closed_dpath_bet_decompE_2)+
  thus
    "q \<noteq> []"
    "s \<noteq> []"
    "last q = hd s"
    by (auto dest: dpath_bet_nonempty_dpath(2-4))
qed

lemma \<^marker>\<open>tag invisible\<close> edges_of_dpath_decomp:
  assumes "dpath_bet G p u v"
  assumes "\<not> distinct p"
  assumes "closed_dpath_bet_decomp G p = (q, r, s)"
  shows "edges_of_dpath p = edges_of_dpath q @ edges_of_dpath r @ edges_of_dpath s"
proof -
  have
    p_def: "p = q @ tl r @ tl s" and
    "\<exists>w. dpath_bet G q u w \<and> closed_dpath_bet G r w \<and> dpath_bet G s w v"
    using assms
    by (blast elim: closed_dpath_bet_decompE_2)+
  hence
    "q \<noteq> []"
    "r \<noteq> []"
    "s \<noteq> []"
    "last q = hd r"
    "last r = hd s"
    by (auto dest: dpath_bet_nonempty_dpath(2-4))
  thus ?thesis
    by (auto simp add: p_def edges_of_dpath_append_3 append_Cons[symmetric])
qed

text \<open>
A simple directed path is a directed path in which all vertices are distinct. Any directed path can
be transformed into a directed simple path via function @{term dpath_bet_to_distinct}.
\<close>

lemma distinct_dpath_length_le_dpath_length:
  assumes "dpath_bet G p u v"
  shows "dpath_length (dpath_bet_to_distinct G p) \<le> dpath_length p"
  using assms
proof (induction rule: dpath_bet_to_distinct_induct)
  case (path p)
  thus ?case
    by simp
next
  case (decomp p q r s)
  hence "dpath_length (dpath_bet_to_distinct G p) = dpath_length (dpath_bet_to_distinct G (q @ tl s))"
    by (auto simp add: decomp.hyps(3))
  also have "... \<le> dpath_length (q @ tl s)"
    by (intro decomp.IH)
  also have "... = dpath_length q + dpath_length s"
    using decomp.hyps
    by (blast elim: closed_dpath_bet_decompE_3 intro: dpath_length_append_2)
  also have "... \<le> dpath_length q + dpath_length r + dpath_length s"
    by simp
  also have "... = dpath_length p"
    using decomp.hyps
    by (simp add: edges_of_dpath_decomp)
  finally show ?case
    .
qed

text \<open>
A vertex $v$ is reachable from a vertex $u$ if and only if there is a directed path from $u$ to $v$.
\<close>

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