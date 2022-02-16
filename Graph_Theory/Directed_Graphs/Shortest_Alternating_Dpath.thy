theory Shortest_Alternating_Dpath
  imports
    Alternating_Dpath
    Odd_Cycle
    Shortest_Dpath
begin

definition alt_dist :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "alt_dist P Q G u v \<equiv> INF p\<in>{p. alt_dpath_bet P Q G p u v}. enat (dpath_length p)"

definition shortest_alt_dpath :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a dgraph \<Rightarrow> 'a dpath \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "shortest_alt_dpath P Q G p u v \<equiv> dpath_length p = alt_dist P Q G u v \<and> alt_dpath_bet P Q G p u v"

lemma shortest_alt_dpathI:
  assumes "dpath_length p = alt_dist P Q G u v"
  assumes "alt_dpath_bet P Q G p u v"
  shows "shortest_alt_dpath P Q G p u v"
  using assms
  by (simp add: shortest_alt_dpath_def)

lemma shortest_alt_dpathD:
  assumes "shortest_alt_dpath P Q G p u v"
  shows
    "dpath_length p = alt_dist P Q G u v"
    "alt_dpath_bet P Q G p u v"
  using assms
  by (simp add: shortest_alt_dpath_def)+

subsection \<open>\<close>

lemma alt_dist_ge_dist:
  shows "dist G u v \<le> alt_dist P Q G u v"
proof -
  have "{p. alt_dpath_bet P Q G p u v} \<subseteq> {p. dpath_bet G p u v}"
    by (auto dest: alt_dpath_betD(2))
  thus ?thesis
    by (auto simp add: dist_def alt_dist_def intro: INF_superset_mono)
qed

lemma alt_dist_le_alt_dpath_length:
  assumes "alt_dpath_bet P Q G p u v"
  shows "alt_dist P Q G u v \<le> dpath_length p"
  using assms
  by (auto simp add: alt_dist_def intro: INF_lower)

lemma alt_dist_alt_reachable_conv:
  shows "alt_dist P Q G u v \<noteq> \<infinity> = alt_reachable P Q G u v"
proof (standard, goal_cases)
  case 1
  show ?case
  proof (rule ccontr)
    assume "\<not> alt_reachable P Q G u v"
    hence "{p. alt_dpath_bet P Q G p u v} = {}"
      by (simp add: alt_reachable_def)
    thus "False"
      using 1
      by (simp add: alt_dist_def top_enat_def)
  qed
next
  case 2
  then obtain p where
    "alt_dpath_bet P Q G p u v"
    by (auto simp add: alt_reachable_def)
  hence "alt_dist P Q G u v \<le> dpath_length p"
    by (intro alt_dist_le_alt_dpath_length)
  also have "... < \<infinity>"
    by simp
  finally show ?case
    by simp
qed

subsection \<open>Shortest distinct alternating directed paths\<close>

lemma alt_dist_ge_shortest_distinct_dpath_length:
  shows
    "(INF p\<in>{p. alt_dpath_bet P Q G p u v}. enat (dpath_length (dpath_bet_to_distinct G p))) \<le>
     alt_dist P Q G u v"
proof -
  { fix p
    assume "p \<in> {p. alt_dpath_bet P Q G p u v}"
    hence "dpath_length (dpath_bet_to_distinct G p) \<le> dpath_length p"
      by (fastforce dest: alt_dpath_betD(2) intro: distinct_dpath_length_le_dpath_length) }
  thus ?thesis
    by (fastforce simp add: alt_dist_def intro: INF_mono)
qed

lemma alt_dist_eq_shortest_distinct_alt_dpath_length:
  assumes "\<nexists>c. dpath G c \<and> odd_cycle c"
  shows
    "alt_dist P Q G u v =
     (INF p\<in>{p. distinct_alt_dpath_bet P Q G p u v}. enat (dpath_length p))"
proof (rule antisym)
  let ?alt_dpaths = "{p. alt_dpath_bet P Q G p u v}"
  let ?distinct_alt_dpaths = "{p. distinct_alt_dpath_bet P Q G p u v}"

  have "?distinct_alt_dpaths \<subseteq> ?alt_dpaths"
    by (auto simp add: distinct_alt_dpath_bet_def alt_dpath_bet_def)
  thus "alt_dist P Q G u v \<le> (INF p\<in>?distinct_alt_dpaths. enat (dpath_length p))"
    by (auto simp add: alt_dist_def intro: INF_superset_mono)

  have "dpath_bet_to_distinct G ` ?alt_dpaths \<subseteq> ?distinct_alt_dpaths"
    using assms
    by (blast intro: alt_dpath_bet_to_distinct_is_distinct_alt_dpath_bet)
  hence
    "(INF p\<in>?distinct_alt_dpaths. enat (dpath_length p)) \<le>
     (INF p\<in>dpath_bet_to_distinct G ` ?alt_dpaths. enat (dpath_length p))"
    by (intro INF_superset_mono) simp+
  also have "... = (INF p\<in>?alt_dpaths. enat (dpath_length (dpath_bet_to_distinct G p)))"
    unfolding image_image
    by simp
  also have "... \<le> alt_dist P Q G u v"
    by (intro alt_dist_ge_shortest_distinct_dpath_length)
  finally show "(INF p\<in>?distinct_alt_dpaths. enat (dpath_length p)) \<le> alt_dist P Q G u v"
    .
qed

lemma (in finite_dgraph) shortest_distinct_alt_dpathE:
  assumes reachable: "alt_reachable P Q G u v"
  assumes no_odd_cycle: "\<nexists>c. dpath G c \<and> odd_cycle c"
  obtains p where
    "distinct_alt_dpath_bet P Q G p u v"
    "dpath_length p = alt_dist P Q G u v"
proof -
  let ?A = "{p. distinct_alt_dpath_bet P Q G p u v}"

  have distinct_alt_dpaths_non_empty: "?A \<noteq> {}"
    using assms
    by (auto simp add: alt_reachable_def intro: alt_dpath_bet_to_distinct_is_distinct_alt_dpath_bet)

  have "alt_dist P Q G u v = (INF p\<in>?A. enat (dpath_length p))"
    using no_odd_cycle
    by (intro alt_dist_eq_shortest_distinct_alt_dpath_length)
  also have "... \<in> (\<lambda>p. enat (dpath_length p)) ` ?A"
    using distinct_alt_dpaths_finite distinct_alt_dpaths_non_empty
    by (intro INF_in_image)
  finally show ?thesis
    by (auto intro: that)
qed

subsection \<open>\<close>

lemma (in finite_dgraph) shortest_alt_dpathE:
  assumes "alt_reachable P Q G u v"
  assumes "\<nexists>c. dpath G c \<and> odd_cycle c"
  obtains p where "shortest_alt_dpath P Q G p u v"
  using assms
  by (fastforce dest: distinct_alt_dpath_betD(1) elim: shortest_distinct_alt_dpathE intro: shortest_alt_dpathI)

end