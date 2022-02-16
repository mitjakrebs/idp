theory Odd_Cycle
  imports
    "../../../matching/Graph_Quotient"
    Dpath
begin

thm odd_cycle_def
definition odd_cycle where
  "odd_cycle p \<equiv> odd (dpath_length p) \<and> hd p = last p"

thm odd_cycle_feats
lemma odd_cycleD:
  assumes "odd_cycle p"
  shows
    "odd (dpath_length p)"
    "hd p = last p"
  using assms
  by (simp_all add: odd_cycle_def)

lemma odd_cycleI:
  assumes "odd (dpath_length p)"
  assumes "hd p = last p"
  shows "odd_cycle p"
  using assms
  by (simp add: odd_cycle_def)

(* TODO Rename. *)
lemma tbd:
  assumes no_odd_cycle: "\<nexists>c. dpath G c \<and> odd_cycle c"
  assumes closed_dpath_bet: "closed_dpath_bet G c v"
  shows "even (dpath_length c)"
  using assms
  by (auto simp add: odd_cycle_def dpath_bet_def)

end