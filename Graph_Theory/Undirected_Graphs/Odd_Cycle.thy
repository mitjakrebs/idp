theory Odd_Cycle
  imports
    Path
begin

definition odd_cycle where
  "odd_cycle p \<equiv> odd (path_length p) \<and> hd p = last p"

lemma odd_cycleD:
  assumes "odd_cycle p"
  shows
    "odd (path_length p)"
    "hd p = last p"
  using assms
  by (simp_all add: odd_cycle_def)

lemma odd_cycleI:
  assumes "odd (path_length p)"
  assumes "hd p = last p"
  shows "odd_cycle p"
  using assms
  by (simp add: odd_cycle_def)

(* TODO Rename. *)
lemma tbd:
  assumes "\<nexists>c. path G c \<and> odd_cycle c"
  assumes "closed_path G c v"
  shows "even (path_length c)"
  using assms
  by (auto simp add: odd_cycle_def walk_betw_def)

end