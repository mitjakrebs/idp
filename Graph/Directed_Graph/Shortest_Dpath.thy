theory Shortest_Dpath
  imports
    "../../Misc_Ext"
    Ports.Mitja_to_DDFS
    Ports.Noschinski_to_DDFS
    Weighted_Dpath
begin

text \<open>We extend theory @{theory Ports.Mitja_to_DDFS} and formalize shortest directed paths.\<close>

definition \<delta> :: "'a dgraph \<Rightarrow> 'a weight_fun \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "\<delta> G f u v \<equiv> INF p\<in>{p. dpath_bet G p u v}. enat (dpath_weight f p)"

definition is_shortest_dpath :: "'a dgraph \<Rightarrow> 'a weight_fun \<Rightarrow> 'a dpath \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_shortest_dpath G f p u v \<equiv> dpath_bet G p u v \<and> dpath_weight f p = \<delta> G f u v"

lemma \<^marker>\<open>tag invisible\<close> is_shortest_dpathI:
  assumes "dpath_bet G p u v"
  assumes "dpath_weight f p = \<delta> G f u v"
  shows "is_shortest_dpath G f p u v"
  using assms
  by (simp add: is_shortest_dpath_def)

lemma \<^marker>\<open>tag invisible\<close> \<delta>_le_dpath_weight:
  assumes "dpath_bet G p u v"
  shows "\<delta> G f u v \<le> dpath_weight f p"
  using assms
  by (auto simp add: \<delta>_def intro: INF_lower)

lemma \<^marker>\<open>tag invisible\<close> \<delta>_edge_le_weight:
  assumes "(u, v) \<in> G"
  shows "\<delta> G f u v \<le> f (u, v)"
proof -
  have "dpath_bet G [u, v] u v"
    using assms
    by (intro edges_are_dpath_bet)
  hence "\<delta> G f u v \<le> dpath_weight f [u, v]"
    by (intro \<delta>_le_dpath_weight)
  also have "... = f (u, v)"
    by (simp add: dpath_weight_def)
  finally show ?thesis
    .
qed

lemma \<^marker>\<open>tag invisible\<close> \<delta>_reachable_conv:
  shows "\<delta> G f u v \<noteq> \<infinity> = reachable G u v"
proof (standard, goal_cases)
  case 1
  show ?case
  proof (rule ccontr)
    assume "\<not> reachable G u v"
    hence "{p. dpath_bet G p u v} = {}"
      by (simp add: reachable_iff_dpath_bet)
    thus "False"
      using 1
      by (simp add: \<delta>_def top_enat_def)
  qed
next
  case 2
  then obtain p where
    "dpath_bet G p u v"
    by (auto simp add: reachable_iff_dpath_bet)
  hence "\<delta> G f u v \<le> dpath_weight f p"
    by (intro \<delta>_le_dpath_weight)
  also have "... < \<infinity>"
    by simp
  finally show ?case
    by simp
qed

lemma \<^marker>\<open>tag invisible\<close> is_shortest_dpath_singleton:
  assumes "v \<in> dVs G"
  shows "is_shortest_dpath G f [v] v v"
proof (intro antisym is_shortest_dpathI)
  show v_dpath_bet: "dpath_bet G [v] v v"
    using assms
    by (intro dpath_bet_reflexive)
  have "dpath_weight f [v] = 0"
    by (simp add: dpath_weight_def)
  also have "... \<le> \<delta> G f v v"
    unfolding zero_enat_def[symmetric]
    using zero_le
    .
  finally show "dpath_weight f [v] \<le> \<delta> G f v v"
    .
  show "\<delta> G f v v \<le> dpath_weight f [v]"
    using v_dpath_bet
    by (intro \<delta>_le_dpath_weight)
qed

lemma \<^marker>\<open>tag invisible\<close> \<delta>_ge_dpath_weight_is_shortest_dpath_bet_to_distinct:
  shows "(INF p\<in>{p. dpath_bet G p u v}. enat (dpath_weight f (dpath_bet_to_distinct G p))) \<le> \<delta> G f u v"
proof -
  { fix p
    assume "p \<in> {p. dpath_bet G p u v}"
    hence "\<exists>q\<in>{p. dpath_bet G p u v}. dpath_weight f (dpath_bet_to_distinct G q) \<le> dpath_weight f p"
      by (blast intro: dpath_weight_ge_dpath_weight_dpath_bet_to_distinct) }
  thus ?thesis
    by (auto simp add: \<delta>_def intro: INF_mono)
qed

lemma \<^marker>\<open>tag invisible\<close> \<delta>_eq_dpath_weight_shortest_distinct_dpath_bet_if_reachable:
  shows "\<delta> G f u v = (INF p\<in>{p. distinct_dpath_bet G p u v}. enat (dpath_weight f p))"
proof (rule antisym)
  let ?dpaths = "{p. dpath_bet G p u v}"
  let ?distinct_dpaths = "{p. distinct_dpath_bet G p u v}"

  have "?distinct_dpaths \<subseteq> ?dpaths"
    by (auto simp add: distinct_dpath_bet_def)
  thus "\<delta> G f u v \<le> (INF p\<in>{p. distinct_dpath_bet G p u v}. enat (dpath_weight f p))"
    unfolding \<delta>_def
    by (intro INF_superset_mono) simp+

  have "dpath_bet_to_distinct G ` ?dpaths \<subseteq> ?distinct_dpaths"
    by (blast intro: dpath_bet_to_distinct_is_distinct_dpath_bet)
  hence
    "(INF p\<in>?distinct_dpaths. enat (dpath_weight f p)) \<le>
     (INF p\<in>dpath_bet_to_distinct G ` ?dpaths. enat (dpath_weight f p))"
    by (intro INF_superset_mono) simp+
  also have "... = (INF p\<in>?dpaths. enat (dpath_weight f (dpath_bet_to_distinct G p)))"
    unfolding image_image
    by simp
  also have "... \<le> (INF p\<in>?dpaths. enat (dpath_weight f p))" 
    unfolding \<delta>_def[symmetric]
    by (intro \<delta>_ge_dpath_weight_is_shortest_dpath_bet_to_distinct)
  finally show "(INF p\<in>{p. distinct_dpath_bet G p u v}. enat (dpath_weight f p)) \<le> \<delta> G f u v"
    by (simp add: \<delta>_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_dgraph) shortest_distinct_dpath_bet_if_reachable:
  assumes "reachable G u v"
  shows "\<exists>p. distinct_dpath_bet G p u v \<and> dpath_weight f p = \<delta> G f u v"
proof -
  have distinct_dpaths_non_empty: "{p. distinct_dpath_bet G p u v} \<noteq> {}"
    (is "?A \<noteq> {}")
    using assms
    by (auto simp add: reachable_iff_dpath_bet intro: dpath_bet_to_distinct_is_distinct_dpath_bet)

  have "\<delta> G f u v = (INF p\<in>?A. enat (dpath_weight f p))"
    by (intro \<delta>_eq_dpath_weight_shortest_distinct_dpath_bet_if_reachable)
  also have "... \<in> (\<lambda>p. enat (dpath_weight f p)) ` ?A"
    using finite_edges distinct_dpaths_non_empty
    by (intro distinct_dpath_bets_finite Misc_Ext.INF_in_image)
  finally show ?thesis
    by (auto simp add: image_def)
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_dgraph) is_shortest_dpath_if_reachable:
  assumes "reachable G u v"
  obtains p where
    "dpath_bet G p u v"
    "dpath_weight f p = \<delta> G f u v"
  using assms shortest_distinct_dpath_bet_if_reachable
  by (force simp add: distinct_dpath_bet_def)

lemma \<^marker>\<open>tag invisible\<close> (in finite_dgraph) \<delta>_triangle_inequality_case_enat:
  assumes assm: "\<delta> G f u v + \<delta> G f v w < \<delta> G f u w"
    (is "?b + ?c < ?a")
  assumes enat: "\<delta> G f u w = enat n"
  shows "False"
proof -
  have
    "?b \<noteq> \<infinity>"
    "?c \<noteq> \<infinity>"
    using assm plus_eq_infty_iff_enat
    by fastforce+
  hence
    "reachable G u v"
    "reachable G v w"
    unfolding \<delta>_reachable_conv
    by simp+
  then obtain p q where
    p_dpath_bet: "dpath_bet G p u v" and
    p_weight: "dpath_weight f p = ?b" and
    q_dpath_bet: "dpath_bet G q v w" and
    q_weight: "dpath_weight f q = ?c"
    by (elim is_shortest_dpath_if_reachable)

  have "dpath_bet G (p @ tl q) u w"
    using p_dpath_bet q_dpath_bet
    by (intro dpath_bet_transitive)
  hence "?a \<le> dpath_weight f (p @ tl q)"
    by (intro \<delta>_le_dpath_weight)
  also have "... = dpath_weight f p + dpath_weight f q"
    using p_dpath_bet q_dpath_bet
    by (auto simp add: dpath_bet_nonempty_dpath(3, 4) intro: dpath_weight_append_2)
  finally have "?a \<le> ?b + ?c"
    by (simp add: plus_enat_simps(1)[symmetric] p_weight q_weight)
  thus ?thesis
    using assm
    by simp
qed

lemma \<^marker>\<open>tag invisible\<close> \<delta>_triangle_inequality_case_infinity:
  assumes assm: "\<delta> G f u v + \<delta> G f v w < \<delta> G f u w"
    (is "?b + ?c < ?a")
  assumes infinity: "\<delta> G f u w = \<infinity>"
  shows "False"
proof -
  have
    "?b \<noteq> \<infinity>"
    "?c \<noteq> \<infinity>"
    using assm plus_eq_infty_iff_enat
    by fastforce+
  hence
    "reachable G u v"
    "reachable G v w"
    unfolding \<delta>_reachable_conv
    by simp+
  hence "reachable G u w"
    by (rule reachable_trans)
  hence "\<delta> G f u w \<noteq> \<infinity>"
    unfolding \<delta>_reachable_conv
    .
  thus ?thesis
    using infinity
    by simp
qed

theorem \<^marker>\<open>tag invisible\<close> (in finite_dgraph) \<delta>_triangle_inequality:
  shows "\<delta> G f u w \<le> \<delta> G f u v + \<delta> G f v w"
    (is "?a \<le> ?b + ?c")
proof (rule ccontr)
  assume "\<not> ?a \<le> ?b + ?c"
  hence assm: "?b + ?c < ?a"
    by simp
  show "False"
  proof (cases ?a)
    case (enat _)
    with assm
    show ?thesis
      by (intro \<delta>_triangle_inequality_case_enat)
  next
    case infinity
    with assm
    show ?thesis
      by (intro \<delta>_triangle_inequality_case_infinity)
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> is_shortest_dpath_prefI_aux:
  assumes "\<not> is_shortest_dpath G f p u v"
  assumes "dpath_bet G p u v"
  shows "\<delta> G f u v < dpath_weight f p"
  using assms
  by (auto simp add: is_shortest_dpath_def intro: \<delta>_le_dpath_weight neq_le_trans)

lemma \<^marker>\<open>tag invisible\<close> is_shortest_dpath_prefI_aux_2:
  assumes "dpath_bet G (p @ [v] @ q) u w"
  assumes "dpath_bet G p' u v"
  shows "dpath_bet G (p' @ q) u w"
  using assms dpath_bet_transitive
  by (fastforce intro: split_dpath)

lemma \<^marker>\<open>tag invisible\<close> (in finite_dgraph) is_shortest_dpath_prefI:
  assumes "is_shortest_dpath G f (p @ [v] @ q) u w"
  shows "is_shortest_dpath G f (p @ [v]) u v"
proof (rule ccontr)
  assume assm: "\<not> is_shortest_dpath G f (p @ [v]) u v"
  have p_snoc_v_dpath_bet: "dpath_bet G (p @ [v]) u v"
    using assms
    by (auto simp add: is_shortest_dpath_def intro: dpath_bet_pref)
  
  have "reachable G u v"
    using p_snoc_v_dpath_bet
    by (auto simp add: reachable_iff_dpath_bet)
  then obtain p' where
    p'_dpath_bet: "dpath_bet G p' u v" and
    p'_dpath_weight_eq_\<delta>: "dpath_weight f p' = \<delta> G f u v"
    by (elim is_shortest_dpath_if_reachable)

  have "dpath_weight f (p' @ q) = dpath_weight f p' + dpath_weight f (v # q)"
    using p'_dpath_bet
    by (simp add: dpath_bet_def dpath_weight_append)
  also have "... = \<delta> G f u v + dpath_weight f (v # q)"
    by (simp add: p'_dpath_weight_eq_\<delta> plus_enat_simps(1)[symmetric])
  also have "... < dpath_weight f (p @ [v]) + dpath_weight f (v # q)"
    unfolding plus_enat_simps[symmetric]
    using assm p_snoc_v_dpath_bet
    by (intro is_shortest_dpath_prefI_aux enat_add_strict_right_mono) simp+
  also have "... = dpath_weight f (p @ [v] @ q)"
    using p_snoc_v_dpath_bet
    by (simp add: dpath_bet_def dpath_weight_append_2[symmetric])
  also have "... = \<delta> G f u w"
    using assms
    by (simp add: is_shortest_dpath_def)
  finally have "dpath_weight f (p' @ q) < \<delta> G f u w"
    .
  thus "False"
    using assms p'_dpath_bet
    by
      (fastforce
        simp add: not_le[symmetric] is_shortest_dpath_def
        intro: is_shortest_dpath_prefI_aux_2 \<delta>_le_dpath_weight)
qed

lemma \<^marker>\<open>tag invisible\<close> is_shortest_dpath_suffixI_aux:
  assumes "dpath_bet G (p @ [v] @ q) u w"
  assumes "dpath_bet G q' v w"
  shows "dpath_bet G (p @ q') u w"
proof -
  obtain q'' where
    q': "q' = v # q''"
    using assms(2)
    by (metis hd_of_dpath_bet)
  have "dpath_bet G (p @ [v]) u v"
    using assms(1)
    by (intro dpath_bet_pref)
  thus "dpath_bet G (p @ q') u w"
    using assms(2) dpath_bet_transitive
    by (fastforce simp add: q')
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_dgraph) is_shortest_dpath_suffixI:
  assumes "is_shortest_dpath G f (p @ [v] @ q) u w"
  shows "is_shortest_dpath G f (v # q) v w"
proof (rule ccontr)
  assume assm: "\<not> is_shortest_dpath G f (v # q) v w"
  have v_Cons_q_dpath_bet: "dpath_bet G (v # q) v w"
    using assms
    by (auto simp add: is_shortest_dpath_def intro: dpath_bet_suff)
  
  have "reachable G v w"
    using v_Cons_q_dpath_bet
    by (auto simp add: reachable_iff_dpath_bet)
  then obtain q' where
    q'_dpath_bet: "dpath_bet G q' v w" and
    q'_dpath_weight_eq_\<delta>: "dpath_weight f q' = \<delta> G f v w"
    by (elim is_shortest_dpath_if_reachable)

  have "dpath_weight f (p @ q') = dpath_weight f (p @ [v]) + dpath_weight f q'"
    using q'_dpath_bet 
    by (auto simp add: dpath_bet_def intro: dpath_weight_append_3)
  also have "... = dpath_weight f (p @ [v]) + \<delta> G f v w"
    by (simp add: q'_dpath_weight_eq_\<delta> plus_enat_simps(1)[symmetric])
  also have "... < dpath_weight f (p @ [v]) + dpath_weight f (v # q)"
    unfolding plus_enat_simps[symmetric]
    using assm v_Cons_q_dpath_bet
    by (intro is_shortest_dpath_prefI_aux enat_add_strict_left_mono) simp+
  also have "... = dpath_weight f (p @ [v] @ q)"
    using v_Cons_q_dpath_bet
    by (simp add: dpath_bet_def dpath_weight_append_2[symmetric])
  also have "... = \<delta> G f u w"
    using assms
    by (simp add: is_shortest_dpath_def)
  finally have "dpath_weight f (p @ q') < \<delta> G f u w"
    .
  thus "False"
    using assms q'_dpath_bet
    by
      (fastforce
        simp add: not_le[symmetric] is_shortest_dpath_def
        intro: is_shortest_dpath_suffixI_aux \<delta>_le_dpath_weight)
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_dgraph) is_shortest_dpathE:
  assumes "is_shortest_dpath G f (p @ [v] @ q) u w"
  obtains
    "is_shortest_dpath G f (p @ [v]) u v"
    "is_shortest_dpath G f (v # q) v w"
    "\<delta> G f u w = \<delta> G f u v + \<delta> G f v w"
proof
  show prefix: "is_shortest_dpath G f (p @ [v]) u v"
    using assms
    by (intro is_shortest_dpath_prefI)
  show suffix: "is_shortest_dpath G f (v # q) v w"
    using assms
    by (intro is_shortest_dpath_suffixI)
  have "\<delta> G f u w = dpath_weight f (p @ [v] @ q)"
    using assms
    by (simp add: is_shortest_dpath_def)
  also have "... = dpath_weight f (p @ [v]) + dpath_weight f (v # q)"
    using dpath_weight_append[where ?p = "p @ [v]" and ?q = q]
    by fastforce
  also have "... = \<delta> G f u v + \<delta> G f v w"
    using prefix suffix
    by (simp add: plus_enat_simps(1)[symmetric] is_shortest_dpath_def)
  finally show "\<delta> G f u w = \<delta> G f u v + \<delta> G f v w"
    .
qed

definition dist :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "dist G u v \<equiv> INF p\<in>{p. dpath_bet G p u v}. enat (dpath_length p)"

theorem dist_eq_\<delta>:
  shows "dist G = \<delta> G (\<lambda>_. 1)"
  by (standard, standard) (simp add: dist_def dpath_length_eq_dpath_weight \<delta>_def)

lemma (in finite_dgraph) dist_le_dpath_length:
  assumes "dpath_bet G p u v"
  shows "dist G u v \<le> dpath_length p"
  using assms
  by (auto simp add: dist_eq_\<delta> dpath_length_eq_dpath_weight intro: \<delta>_le_dpath_weight)

lemma (in finite_dgraph) is_shortest_dpath_if_reachable_2:
  assumes "reachable G u v"
  obtains p where
    "dpath_bet G p u v"
    "dpath_length p = dist G u v"
  using assms
  by (auto simp add: dpath_length_eq_dpath_weight dist_eq_\<delta> elim: is_shortest_dpath_if_reachable)

lemma (in finite_dgraph) is_shortest_dpathE_2:
  assumes "dpath_bet G (p @ [v] @ q) u w \<and> dpath_length (p @ [v] @ q) = dist G u w"
  obtains
    "dpath_bet G (p @ [v]) u v \<and> dpath_length (p @ [v]) = dist G u v"
    "dpath_bet G (v # q) v w \<and> dpath_length (v # q) = dist G v w"
    "dist G u w = dist G u v + dist G v w"
  using assms
  unfolding dpath_length_eq_dpath_weight dist_eq_\<delta> is_shortest_dpath_def[symmetric]
  by (elim is_shortest_dpathE)

lemma (in finite_dgraph) dist_triangle_inequality_edge:
  assumes "(v, w) \<in> G"
  shows "dist G u w \<le> dist G u v + 1"
proof -
  have "dist G u w \<le> dist G u v + dist G v w"
    unfolding dist_eq_\<delta>
    by (intro \<delta>_triangle_inequality)
  also have "... \<le> dist G u v + 1"
    unfolding dist_eq_\<delta> one_enat_def
    using assms
    by (intro \<delta>_edge_le_weight conjI add_mono_thms_linordered_semiring(2)) simp
  finally show ?thesis
    .
qed

end