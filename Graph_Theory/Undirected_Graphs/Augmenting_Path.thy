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

end