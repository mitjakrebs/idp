theory Path_Adaptor
  imports
    "../Directed_Graph/Dpath"
    Graph_Adaptor
    "../Undirected_Graph/Path"
begin

text \<open>
Since undirected and directed paths are defined in a very similar way, it is no surprise that the
transition between them is very smooth.
\<close>

lemmas path_induct = dpath_induct
lemmas path_rev_induct = dpath_rev_induct

lemma (in graph) path_length_eq_dpath_length:
  shows "path_length p = dpath_length p"
  by (simp add: edges_of_path_length edges_of_dpath_length)

lemma (in graph) path_iff_dpath:
  shows "path G p \<longleftrightarrow> dpath dEs p"
  sorry

lemma (in graph) walk_betw_iff_dpath_bet:
  shows "walk_betw G u p v \<longleftrightarrow> dpath_bet dEs p u v"
  unfolding walk_betw_def dpath_bet_def
  by (auto simp add: path_iff_dpath)

lemma \<^marker>\<open>tag invisible\<close> (in graph) path_length_geq_1I:
  assumes "walk_betw G u p v"
  assumes "u \<noteq> v"
  shows "1 \<le> path_length p"
  using assms
  unfolding walk_betw_iff_dpath_bet path_length_eq_dpath_length
  by (intro dpath_length_geq_1I)

lemma \<^marker>\<open>tag invisible\<close> (in graph) path_length_Cons:
  assumes "vs \<noteq> []"
  shows "path_length (v # vs) = path_length vs + 1"
  unfolding path_length_eq_dpath_length
  using assms
  by (intro dpath_length_Cons)

lemma \<^marker>\<open>tag invisible\<close> (in graph) path_length_snoc:
  assumes "vs \<noteq> []"
  shows "path_length (vs @ [v]) = path_length vs + 1"
  unfolding path_length_eq_dpath_length
  using assms
  by (intro dpath_length_snoc)

lemma \<^marker>\<open>tag invisible\<close> (in graph) path_length_append:
  assumes "p \<noteq> []"
  shows "path_length (p @ q) = path_length p + path_length (last p # q)"
  unfolding path_length_eq_dpath_length
  using assms
  by (intro dpath_length_append)

lemma \<^marker>\<open>tag invisible\<close> (in graph) path_length_append_2:
  assumes "p \<noteq> []"
  assumes "q \<noteq> []"
  assumes "last p = hd q"
  shows "path_length (p @ tl q) = path_length p + path_length q"
  unfolding path_length_eq_dpath_length
  using assms
  by (intro dpath_length_append_2)

lemma \<^marker>\<open>tag invisible\<close> (in graph) path_vertex_decompE:
  assumes "walk_betw G u p v"
  assumes "p = xs @ y # ys"
  obtains q r where
    "p = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "walk_betw G u q y"
    "walk_betw G y r v"
  using assms
  unfolding walk_betw_iff_dpath_bet
  by (erule dpath_bet_vertex_decompE)

lemma \<^marker>\<open>tag invisible\<close> (in graph) distinct_path_iff_distinct_dpath_bet:
  shows "distinct_path G p u v \<longleftrightarrow> distinct_dpath_bet dEs p u v"
  unfolding distinct_path_def distinct_dpath_bet_def
  by (simp add: walk_betw_iff_dpath_bet)

lemma \<^marker>\<open>tag invisible\<close> (in finite_graph) distinct_paths_finite:
  shows "finite {p. distinct_path G p u v}"
  using F.finite_edges
  by (auto simp add: distinct_path_iff_distinct_dpath_bet intro: distinct_dpath_bets_finite)

lemma \<^marker>\<open>tag invisible\<close> (in graph) closed_path_iff_closed_dpath_bet:
  shows "closed_path G c v \<longleftrightarrow> closed_dpath_bet dEs c v"
  by (simp add: walk_betw_iff_dpath_bet)

lemma \<^marker>\<open>tag invisible\<close> (in graph) is_closed_path_decomp_iff_is_closed_decomp:
  shows "is_closed_path_decomp G p (q, r, s) \<longleftrightarrow> is_closed_decomp dEs p (q, r, s)"
  by (simp add: walk_betw_iff_dpath_bet closed_path_iff_closed_dpath_bet)

lemma \<^marker>\<open>tag invisible\<close> (in graph) closed_path_decomp_eq_closed_dpath_bet_decomp:
  shows "closed_path_decomp G p = closed_dpath_bet_decomp dEs p"
  unfolding closed_path_decomp_def closed_dpath_bet_decomp_def
  by (metis is_closed_path_decomp_iff_is_closed_decomp prod_cases3)

lemma \<^marker>\<open>tag invisible\<close> (in graph) closed_path_decompE_2:
  assumes "walk_betw G u p v"
  assumes "\<not> distinct p"
  assumes "closed_path_decomp G p = (q, r, s)"
  obtains
    "p = q @ tl r @ tl s"
    "\<exists>w. walk_betw G u q w \<and> closed_path G r w \<and> walk_betw G w s v"
    "distinct q"
  using assms
  unfolding walk_betw_iff_dpath_bet closed_path_decomp_eq_closed_dpath_bet_decomp
  by (erule closed_dpath_bet_decompE_2)

lemma \<^marker>\<open>tag invisible\<close> (in graph) closed_path_decompE_3:
  assumes "walk_betw G u p v"
  assumes "\<not> distinct p"
  assumes "closed_path_decomp G p = (q, r, s)"
  obtains
    "q \<noteq> []"
    "s \<noteq> []"
    "last q = hd s"
  using assms
  unfolding walk_betw_iff_dpath_bet closed_path_decomp_eq_closed_dpath_bet_decomp
  by (erule closed_dpath_bet_decompE_3)

lemma \<^marker>\<open>tag invisible\<close> (in graph) edges_of_path_decomp:
  assumes "walk_betw G u p v"
  assumes "\<not> distinct p"
  assumes "closed_path_decomp G p = (q, r, s)"
  shows "edges_of_path p = edges_of_path q @ edges_of_path r @ edges_of_path s"
proof -
  have
    p_def: "p = q @ tl r @ tl s" and
    "\<exists>w. walk_betw G u q w \<and> closed_path G r w \<and> walk_betw G w s v"
    using assms
    by (blast elim: closed_path_decompE_2)+
  hence
    "q \<noteq> []"
    "r \<noteq> []"
    "s \<noteq> []"
    "last q = hd r"
    "last r = hd s"
    by (auto dest: walk_between_nonempty_path(2-4))
  thus ?thesis
    by (auto simp add: p_def edges_of_path_append_3 append_Cons[symmetric])
qed

function \<^marker>\<open>tag invisible\<close> (in graph) path_to_distinct where
  "path_to_distinct p =
    (if (\<exists>u v. walk_betw G u p v) \<and> \<not> distinct p
     then let (q, r, s) = closed_path_decomp G p in path_to_distinct (q @ tl s)
     else p)"
  by auto

termination \<^marker>\<open>tag invisible\<close> (in graph) path_to_distinct
proof (relation "measure length")
  fix p qrs rs q r s
  assume
    p_not_distinct: "(\<exists>u v. walk_betw G u p v) \<and> \<not> distinct p" and
    assms: "qrs = closed_path_decomp G p"
    "(q, rs) = qrs"
    "(r, s) = rs"
  then obtain u v where
    p_path: "walk_betw G u p v"
    by blast
  hence "(q, r, s) = closed_path_decomp G p"
    using assms
    by simp
  then obtain
    "p = q @ tl r @ tl s"
    "Suc 0 < length r"
    using p_path p_not_distinct
    by (elim closed_path_decompE_2) auto
  thus "(q @ tl s, p) \<in> measure length"
    by auto
qed simp

lemma \<^marker>\<open>tag invisible\<close> (in graph) path_to_distinct_induct [consumes 1, case_names path decomp]:
  assumes "walk_betw G u p v"
  assumes "\<And>p. \<lbrakk> walk_betw G u p v; distinct p \<rbrakk> \<Longrightarrow> P p"
  assumes "\<And>p q r s. \<lbrakk> walk_betw G u p v; \<not> distinct p; closed_path_decomp G p = (q, r, s); P (q @ tl s) \<rbrakk> \<Longrightarrow> P p"
  shows "P p"
  using assms
  unfolding walk_betw_iff_dpath_bet closed_path_decomp_eq_closed_dpath_bet_decomp
  by (rule dpath_bet_to_distinct_induct)

lemma \<^marker>\<open>tag invisible\<close> (in graph) path_to_distinct_eq_dpath_bet_to_distinct:
  assumes "walk_betw G u p v"
  shows "path_to_distinct p = dpath_bet_to_distinct dEs p"
  using assms
  by (induct p rule: path_to_distinct_induct) (auto simp add: walk_betw_iff_dpath_bet closed_path_decomp_eq_closed_dpath_bet_decomp)

lemma \<^marker>\<open>tag invisible\<close> (in graph) distinct_path_length_le_path_length:
  assumes "walk_betw G u p v"
  shows "path_length (path_to_distinct p) \<le> path_length p"
  using assms
  unfolding walk_betw_iff_dpath_bet path_length_eq_dpath_length path_to_distinct_eq_dpath_bet_to_distinct[OF assms]
  by (intro distinct_dpath_length_le_dpath_length)

lemma (in graph) reachable_iff_reachable:
  shows "reachable G u v \<longleftrightarrow> Noschinski_to_DDFS.reachable dEs u v"
  unfolding reachable_def reachable_iff_dpath_bet
  by (simp add: walk_betw_iff_dpath_bet)

end