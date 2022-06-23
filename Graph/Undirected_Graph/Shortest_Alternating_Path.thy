theory Shortest_Alternating_Path
  imports
    Alternating_Path
    Shortest_Path
begin

text \<open>We generalize the notion of shortest paths to alternating paths in the natural way.\<close>

definition alt_dist :: "('a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "alt_dist P Q G u v \<equiv> INF p\<in>{p. alt_path P Q G p u v}. enat (path_length p)"

definition is_shortest_alt_path :: "('a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_shortest_alt_path P Q G p u v \<equiv> path_length p = alt_dist P Q G u v \<and> alt_path P Q G p u v"

lemma \<^marker>\<open>tag invisible\<close> is_shortest_alt_pathI:
  assumes "path_length p = alt_dist P Q G u v"
  assumes "alt_path P Q G p u v"
  shows "is_shortest_alt_path P Q G p u v"
  using assms
  by (simp add: is_shortest_alt_path_def)

lemma \<^marker>\<open>tag invisible\<close> is_shortest_alt_pathD:
  assumes "is_shortest_alt_path P Q G p u v"
  shows
    "path_length p = alt_dist P Q G u v"
    "alt_path P Q G p u v"
  using assms
  by (simp add: is_shortest_alt_path_def)+

lemma \<^marker>\<open>tag invisible\<close> is_shortest_alt_path_snoc_snoc:
  assumes "is_shortest_alt_path P Q G (p @ [v, v']) u w"
  shows "is_shortest_alt_path P Q G (p @ [v, w]) u w"
proof -
  have "v' = w"
    using assms
    by (fastforce dest: alt_pathD(2) is_shortest_alt_pathD(2) walk_between_nonempty_path(4))
  thus ?thesis
    using assms
    by simp
qed

lemma \<^marker>\<open>tag invisible\<close> alt_dist_ge_dist:
  shows "dist G u v \<le> alt_dist P Q G u v"
proof -
  have "{p. alt_path P Q G p u v} \<subseteq> {p. walk_betw G u p v}"
    by (auto dest: alt_pathD(2))
  thus ?thesis
    by (auto simp add: dist_def alt_dist_def intro: INF_superset_mono)
qed

lemma alt_dist_le_alt_path_length:
  assumes "alt_path P Q G p u v"
  shows "alt_dist P Q G u v \<le> path_length p"
  using assms
  by (auto simp add: alt_dist_def intro: INF_lower)

lemma \<^marker>\<open>tag invisible\<close> not_is_shortest_alt_pathD:
  assumes "\<not> is_shortest_alt_path P Q G p u v"
  assumes "alt_path P Q G p u v"
  shows "alt_dist P Q G u v < path_length p"
  using assms
  by (auto simp add: is_shortest_alt_path_def dest: alt_dist_le_alt_path_length)


lemma alt_dist_alt_reachable_conv:
  shows "alt_dist P Q G u v \<noteq> \<infinity> = alt_reachable P Q G u v"
proof (standard, goal_cases)
  case 1
  show ?case
  proof (rule ccontr)
    assume "\<not> alt_reachable P Q G u v"
    hence "{p. alt_path P Q G p u v} = {}"
      by (simp add: alt_reachable_def)
    thus "False"
      using 1
      by (simp add: alt_dist_def top_enat_def)
  qed
next
  case 2
  then obtain p where
    "alt_path P Q G p u v"
    by (auto simp add: alt_reachable_def)
  hence "alt_dist P Q G u v \<le> path_length p"
    by (intro alt_dist_le_alt_path_length)
  also have "... < \<infinity>"
    by simp
  finally show ?case
    by simp
qed

lemma \<^marker>\<open>tag invisible\<close> (in graph) alt_dist_ge_shortest_distinct_path_length:
  shows
    "(INF p\<in>{p. alt_path P Q G p u v}. enat (path_length (path_to_distinct p))) \<le>
     alt_dist P Q G u v"
proof -
  { fix p
    assume "p \<in> {p. alt_path P Q G p u v}"
    hence "path_length (path_to_distinct p) \<le> path_length p"
      by (fastforce dest: alt_pathD(2) intro: distinct_path_length_le_path_length) }
  thus ?thesis
    by (fastforce simp add: alt_dist_def intro: INF_mono)
qed

lemma (in graph) alt_dist_eq_shortest_distinct_alt_path_length:
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows
    "alt_dist P Q G u v =
     (INF p\<in>{p. distinct_alt_path P Q G p u v}. enat (path_length p))"
proof (rule antisym)
  let ?alt_paths = "{p. alt_path P Q G p u v}"
  let ?distinct_alt_paths = "{p. distinct_alt_path P Q G p u v}"

  have "?distinct_alt_paths \<subseteq> ?alt_paths"
    by (auto simp add: distinct_alt_path_def alt_path_def)
  thus "alt_dist P Q G u v \<le> (INF p\<in>?distinct_alt_paths. enat (path_length p))"
    by (auto simp add: alt_dist_def intro: INF_superset_mono)

  have "path_to_distinct ` ?alt_paths \<subseteq> ?distinct_alt_paths"
    using assms
    by (blast intro: distinct_alt_path_alt_path_to_distinct)
  hence
    "(INF p\<in>?distinct_alt_paths. enat (path_length p)) \<le>
     (INF p\<in>path_to_distinct ` ?alt_paths. enat (path_length p))"
    by (intro INF_superset_mono) simp+
  also have "... = (INF p\<in>?alt_paths. enat (path_length (path_to_distinct p)))"
    unfolding image_image
    by simp
  also have "... \<le> alt_dist P Q G u v"
    by (intro alt_dist_ge_shortest_distinct_path_length)
  finally show "(INF p\<in>?distinct_alt_paths. enat (path_length p)) \<le> alt_dist P Q G u v"
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_graph) is_shortest_distinct_alt_pathE:
  assumes "alt_reachable P Q G u v"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  obtains p where
    "distinct_alt_path P Q G p u v"
    "path_length p = alt_dist P Q G u v"
proof -
  let ?A = "{p. distinct_alt_path P Q G p u v}"

  have distinct_alt_paths_non_empty: "?A \<noteq> {}"
    using assms
    by (auto simp add: alt_reachable_def intro: distinct_alt_path_alt_path_to_distinct)

  have "alt_dist P Q G u v = (INF p\<in>?A. enat (path_length p))"
    using assms(2)
    by (intro alt_dist_eq_shortest_distinct_alt_path_length)
  also have "... \<in> (\<lambda>p. enat (path_length p)) ` ?A"
    using distinct_alt_paths_finite distinct_alt_paths_non_empty
    by (simp add: cInf_eq_Min)
  finally show ?thesis
    by (auto intro: that)
qed

lemma (in finite_graph) is_shortest_alt_pathE:
  assumes "alt_reachable P Q G u v"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  obtains p where "is_shortest_alt_path P Q G p u v"
  using assms
  by
    (fastforce
      dest: distinct_alt_pathD(1)
      elim: is_shortest_distinct_alt_pathE
      intro: is_shortest_alt_pathI)

lemma \<^marker>\<open>tag invisible\<close> (in finite_graph) is_shortest_alt_path_rev_oddI:
  assumes "is_shortest_alt_path P Q G p u v"
  assumes "odd (path_length p)"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows "is_shortest_alt_path P Q G (rev p) v u"
proof (rule ccontr)
  assume assm: "\<not> is_shortest_alt_path P Q G (rev p) v u"
  have alt_path_rev_p: "alt_path P Q G (rev p) v u "
    using assms(1, 2)
    by (intro is_shortest_alt_pathD(2) alt_path_rev_oddI)
  hence "alt_reachable P Q G v u"
    by (auto simp add: alt_reachable_def)
  then obtain q where
    is_shortest_alt_path_q: "is_shortest_alt_path P Q G q v u"
    using assms(3)
    by (elim is_shortest_alt_pathE)
  hence "odd (path_length q)"
    using alt_path_rev_p assms(2, 3)
    by (auto simp add: edges_of_path_length dest: is_shortest_alt_pathD(2) two_alt_pathsD)
  hence "alt_path P Q G (rev q) u v"
    using is_shortest_alt_path_q
    by (intro is_shortest_alt_pathD(2) alt_path_rev_oddI)
  hence "alt_dist P Q G u v \<le> path_length (rev q)"
    by (intro alt_dist_le_alt_path_length)
  also have "... = path_length q"
    by (simp add: edges_of_path_length)
  also have "... = alt_dist P Q G v u"
    using is_shortest_alt_path_q
    by (intro is_shortest_alt_pathD(1))
  also have "... < path_length (rev p)"
    using assm alt_path_rev_p
    by (intro not_is_shortest_alt_pathD)
  also have "... = path_length p"
    by (simp add: edges_of_path_length)
  also have "... = alt_dist P Q G u v"
    using assms(1)
    by (intro is_shortest_alt_pathD(1))
  finally show False
    ..
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_graph) is_shortest_alt_path_rev_evenI:
  assumes "is_shortest_alt_path P Q G p u v"
  assumes "even (path_length p)"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows "is_shortest_alt_path Q P G (rev p) v u"
proof (rule ccontr)
  assume assm: "\<not> is_shortest_alt_path Q P G (rev p) v u"
  have alt_path_rev_p: "alt_path Q P G (rev p) v u "
    using assms(1, 2)
    by (intro is_shortest_alt_pathD(2) alt_path_rev_evenI)
  hence "alt_reachable Q P G v u"
    by (auto simp add: alt_reachable_def)
  then obtain q where
    is_shortest_alt_path_q: "is_shortest_alt_path Q P G q v u"
    using assms(3)
    by (elim is_shortest_alt_pathE)
  hence "even (path_length q)"
    using alt_path_rev_p assms(2, 3)
    by (auto simp add: edges_of_path_length dest: is_shortest_alt_pathD(2) two_alt_pathsD)
  hence "alt_path P Q G (rev q) u v"
    using is_shortest_alt_path_q
    by (intro is_shortest_alt_pathD(2) alt_path_rev_evenI)
  hence "alt_dist P Q G u v \<le> path_length (rev q)"
    by (intro alt_dist_le_alt_path_length)
  also have "... = path_length q"
    by (simp add: edges_of_path_length)
  also have "... = alt_dist Q P G v u"
    using is_shortest_alt_path_q
    by (intro is_shortest_alt_pathD(1))
  also have "... < path_length (rev p)"
    using assm alt_path_rev_p
    by (intro not_is_shortest_alt_pathD)
  also have "... = path_length p"
    by (simp add: edges_of_path_length)
  also have "... = alt_dist P Q G u v"
    using assms(1)
    by (intro is_shortest_alt_pathD(1))
  finally show False
    ..
qed

text \<open>Again, we can reverse shortest alternating paths.\<close>

lemma (in finite_graph) is_shortest_alt_path_revI:
  assumes "is_shortest_alt_path P Q G p u v"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows "is_shortest_alt_path P Q G (rev p) v u \<or> is_shortest_alt_path Q P G (rev p) v u"
  using assms
  by (auto intro: is_shortest_alt_path_rev_oddI is_shortest_alt_path_rev_evenI)

text \<open>And we can split shortest alternating paths.\<close>

lemma (in finite_graph) is_shortest_alt_path_pref:
  assumes "is_shortest_alt_path P Q G (p @ v # q) u w"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows "is_shortest_alt_path P Q G (p @ [v]) u v"
proof (rule ccontr, goal_cases)
  case 1
  have alt_path_p_snoc_v: "alt_path P Q G (p @ [v]) u v"
    using assms(1)
    by (auto dest: is_shortest_alt_pathD(2) intro: alt_path_pref)
  hence "alt_reachable P Q G u v"
    by (auto simp add: alt_reachable_def)
  then obtain p' where
    is_shortest_alt_path_p': "is_shortest_alt_path P Q G p' u v"
    using assms(2)
    by (elim is_shortest_alt_pathE)

  have "alt_dist P Q G u w \<le> path_length (p' @ q)"
    using assms is_shortest_alt_path_p'
    by (auto dest: is_shortest_alt_pathD(2) intro: alt_path_subst_pref alt_dist_le_alt_path_length)
  also have "... = path_length p' + path_length (v # q)"
    using is_shortest_alt_path_p'
    by (fastforce simp add: path_length_append dest: is_shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(2, 4))
  also have "... = alt_dist P Q G u v + path_length (v # q)"
    using is_shortest_alt_path_p'
    by (simp add: is_shortest_alt_pathD(1) plus_enat_simps(1)[symmetric])
  also have "... < path_length (p @ [v]) + path_length (v # q)"
    unfolding plus_enat_simps[symmetric]
    using 1 alt_path_p_snoc_v
    by (intro not_is_shortest_alt_pathD enat_add_strict_right_mono) simp+
  also have "... = path_length (p @ v # q)"
    by (simp add: edges_of_path_length)
  also have "... = alt_dist P Q G u w"
    using assms(1)
    by (intro is_shortest_alt_pathD(1))
  finally show ?case
    ..
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_graph) is_shortest_alt_path_suf_odd:
  assumes "is_shortest_alt_path P Q G (p @ v # q) u w"
  assumes "odd (path_length (p @ [v]))"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows "is_shortest_alt_path Q P G (v # q) v w"
proof (cases "odd (path_length (p @ v # q))")
  case True
  hence "is_shortest_alt_path P Q G (rev (p @ v # q)) w u"
    using assms(1, 3)
    by (intro is_shortest_alt_path_rev_oddI)
  hence "is_shortest_alt_path P Q G (rev q @ [v]) w v"
    using assms(3)
    by (intro is_shortest_alt_path_pref) simp
  moreover have "even (path_length (rev q @ [v]))"
    using True assms(2)
    by (simp add: edges_of_path_length)
  ultimately show ?thesis
    using assms(3)
    by (auto dest: is_shortest_alt_path_rev_evenI)
next
  case False
  hence "is_shortest_alt_path Q P G (rev (p @ v # q)) w u"
    using assms(1, 3)
    by (intro is_shortest_alt_path_rev_evenI) simp+
  hence "is_shortest_alt_path Q P G (rev q @ [v]) w v"
    using assms(3)
    by (intro is_shortest_alt_path_pref) simp
  moreover have "odd (path_length (rev q @ [v]))"
    using False assms(2)
    by (simp add: edges_of_path_length)
  ultimately show ?thesis
    using assms(3)
    by (auto dest: is_shortest_alt_path_rev_oddI)
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_graph) is_shortest_alt_path_suf_even:
  assumes "is_shortest_alt_path P Q G (p @ v # q) u w"
  assumes "even (path_length (p @ [v]))"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows "is_shortest_alt_path P Q G (v # q) v w"
proof (cases "odd (path_length (p @ v # q))")
  case True
  hence "is_shortest_alt_path P Q G (rev (p @ v # q)) w u"
    using assms(1, 3)
    by (intro is_shortest_alt_path_rev_oddI)
  hence "is_shortest_alt_path P Q G (rev q @ [v]) w v"
    using assms(3)
    by (intro is_shortest_alt_path_pref) simp
  moreover have "odd (path_length (rev q @ [v]))"
    using True assms(2)
    by (simp add: edges_of_path_length)
  ultimately show ?thesis
    using assms(3)
    by (auto dest: is_shortest_alt_path_rev_oddI)
next
  case False
  hence "is_shortest_alt_path Q P G (rev (p @ v # q)) w u"
    using assms(1, 3)
    by (intro is_shortest_alt_path_rev_evenI) simp+
  hence "is_shortest_alt_path Q P G (rev q @ [v]) w v"
    using assms(3)
    by (intro is_shortest_alt_path_pref) simp
  moreover have "even (path_length (rev q @ [v]))"
    using False assms(2)
    by (simp add: edges_of_path_length)
  ultimately show ?thesis
    using assms(3)
    by (auto dest: is_shortest_alt_path_rev_evenI)
qed

lemma (in finite_graph) is_shortest_alt_path_suf:
  assumes "is_shortest_alt_path P Q G (p @ v # q) u w"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows "is_shortest_alt_path P Q G (v # q) v w \<or> is_shortest_alt_path Q P G (v # q) v w"
  using assms
  by (auto dest: is_shortest_alt_path_suf_odd is_shortest_alt_path_suf_even)

lemma \<^marker>\<open>tag invisible\<close> (in finite_graph) is_shortest_alt_path_append_evenD:
  assumes "is_shortest_alt_path P Q G (p @ v # q) u w"
  assumes "even (path_length (p @ [v]))"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows
    "is_shortest_alt_path P Q G (p @ [v]) u v"
    "is_shortest_alt_path P Q G (v # q) v w"
    "alt_dist P Q G u w = alt_dist P Q G u v + alt_dist P Q G v w"
proof -
  show pref: "is_shortest_alt_path P Q G (p @ [v]) u v"
    using assms(1, 3)
    by (intro is_shortest_alt_path_pref)
  show suf: "is_shortest_alt_path P Q G (v # q) v w"
    using assms
    by (intro is_shortest_alt_path_suf_even)
  have "alt_dist P Q G u w = path_length (p @ v # q)"
    using assms(1)
    by (intro is_shortest_alt_pathD(1)[symmetric])
  also have "... = path_length (p @ [v]) + path_length (v # q)"
    by (simp add: edges_of_path_length)
  also have "... = alt_dist P Q G u v + alt_dist P Q G v w"
    using pref suf
    by (simp add: plus_enat_simps(1)[symmetric] is_shortest_alt_pathD(1))
  finally show "alt_dist P Q G u w = alt_dist P Q G u v + alt_dist P Q G v w"
    .
qed

lemma \<^marker>\<open>tag invisible\<close> (in finite_graph) is_shortest_alt_path_append_oddD:
  assumes "is_shortest_alt_path P Q G (p @ v # q) u w"
  assumes "odd (path_length (p @ [v]))"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows
    "is_shortest_alt_path P Q G (p @ [v]) u v"
    "is_shortest_alt_path Q P G (v # q) v w"
    "alt_dist P Q G u w = alt_dist P Q G u v + alt_dist Q P G v w"
proof -
  show pref: "is_shortest_alt_path P Q G (p @ [v]) u v"
    using assms(1, 3)
    by (intro is_shortest_alt_path_pref)
  show suf: "is_shortest_alt_path Q P G (v # q) v w"
    using assms
    by (intro is_shortest_alt_path_suf_odd)
  have "alt_dist P Q G u w = path_length (p @ v # q)"
    using assms(1)
    by (intro is_shortest_alt_pathD(1)[symmetric])
  also have "... = path_length (p @ [v]) + path_length (v # q)"
    by (simp add: edges_of_path_length)
  also have "... = alt_dist P Q G u v + alt_dist Q P G v w"
    using pref suf
    by (simp add: plus_enat_simps(1)[symmetric] is_shortest_alt_pathD(1))
  finally show "alt_dist P Q G u w = alt_dist P Q G u v + alt_dist Q P G v w"
    .
qed

lemma (in finite_graph) is_shortest_alt_path_snoc_snocD:
  assumes "is_shortest_alt_path P Q G (p @ [v, w]) u w"
  assumes "\<not> (\<exists>c. path G c \<and> odd_cycle c)"
  shows "alt_dist P Q G u w = alt_dist P Q G u v + 1"
proof (cases "even (path_length (p @ [v]))")
  case True
  hence
    "is_shortest_alt_path P Q G [v, w] v w"
    "alt_dist P Q G u w = alt_dist P Q G u v + alt_dist P Q G v w"
    using assms is_shortest_alt_path_append_evenD(2, 3)
    by auto
  thus ?thesis
    by (simp add: is_shortest_alt_pathD(1)[symmetric])
next
  case False
  hence
    "is_shortest_alt_path Q P G [v, w] v w"
    "alt_dist P Q G u w = alt_dist P Q G u v + alt_dist Q P G v w"
    using assms is_shortest_alt_path_append_oddD(2, 3)
    by auto
  thus ?thesis
    by (simp add: is_shortest_alt_pathD(1)[symmetric])
qed

end