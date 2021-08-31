theory Map_Specs_Tbd
  imports "HOL-Data_Structures.Map_Specs"
begin

definition (in Map) dom :: "'m \<Rightarrow> 'a set" where
  "dom m \<equiv> {a. lookup m a \<noteq> None}"

lemma (in Map) mem_dom_iff:
  shows "a \<in> dom m \<longleftrightarrow> lookup m a \<noteq> None"
  by (simp add: dom_def)

definition (in Map) ran :: "'m \<Rightarrow> 'b set" where
  "ran m \<equiv> {b. \<exists>a. lookup m a = Some b}"

lemma (in Map) dom_finite_imp_ran_finite:
  assumes "finite (dom m)"
  shows "finite (ran m)"
proof -
  have "ran m = (the \<circ> lookup m) ` dom m"
    by (force simp add: ran_def dom_def)
  thus ?thesis
    using assms
    by simp
qed

end