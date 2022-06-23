theory Augmenting_Path
  imports
    Alternating_Path
begin

thm augmenting_path_def
lemma augmenting_pathD:
  assumes "augmenting_path M p"
  shows
    "2 \<le> length p"
    "Berge.alt_path M p"
    "hd p \<notin> Vs M"
    "last p \<notin> Vs M"
  using assms
  by (simp_all add: augmenting_path_def)

lemma augmenting_pathI:
  assumes "2 \<le> length p"
  assumes "Berge.alt_path M p"
  assumes "hd p \<notin> Vs M"
  assumes "last p \<notin> Vs M"
  shows "augmenting_path M p"
  using assms
  by (simp add: augmenting_path_def)

lemma augmenting_path_rev_if_augmenting_path:
  assumes "augmenting_path M p"
  shows "augmenting_path M (rev p)"
proof (rule augmenting_pathI, goal_cases)
  case 1
  show ?case
    using assms
    by (auto dest: augmenting_pathD(1))
next
  case 2
  show ?case
    using assms
    by
      (auto
       simp add: edges_of_path_rev[symmetric]
       dest: augmenting_pathD(2) augmenting_path_odd_length
       intro: alt_list_rev)
next
  case 3
  have "p \<noteq> []"
    using assms
    by (auto dest: augmenting_pathD(1))
  thus ?case
    using assms
    by (auto simp add: hd_rev dest: augmenting_pathD(4))
next
  case 4
  have "p \<noteq> []"
    using assms
    by (auto dest: augmenting_pathD(1))
  thus ?case
    using assms
    by (auto simp add: last_rev dest: augmenting_pathD(3))
qed

term augpath
lemma augpathD:
  assumes "augpath G M p"
  shows
    "path G p"
    "distinct p"
    "augmenting_path M p"
  using assms
  by simp_all

lemma augpathI:
  assumes "path G p"
  assumes "distinct p"
  assumes "augmenting_path M p"
  shows "augpath G M p"
  using assms
  by simp

lemma augpath_rev_if_augpath:
  assumes "augpath G M p"
  shows "augpath G M (rev p)"
proof (rule augpathI, goal_cases)
  case 1
  show ?case
    using assms
    by (intro rev_path_is_path) simp
next
  case 2
  show ?case
    using assms
    by force
next
  case 3
  show ?case
    using assms
    by (intro augmenting_path_rev_if_augmenting_path) simp
qed

end