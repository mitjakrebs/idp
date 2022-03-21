theory Odd_Cycle
  imports
    Path
begin

text \<open>This theory formalizes odd cycles.\<close>

text \<open>
We redefine odd cycles to also include loops for the following reason. We show that to find a
shortest alternating path it suffices to consider a finite number of alternating paths. For this, we
show that if there are no odd cycles, we can convert any alternating path into a simple alternating
path by repeatedly removing cycles. If we allow loops, however, removing a single loop may destroy
the alternation.
\<close>

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

lemma even_path_length_cycleI:
  assumes "\<nexists>c. path G c \<and> odd_cycle c"
  assumes "closed_path G c v"
  shows "even (path_length c)"
  using assms
  by (auto simp add: odd_cycle_def walk_betw_def)

end