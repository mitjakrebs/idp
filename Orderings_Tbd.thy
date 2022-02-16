theory Orderings_Tbd
  imports Main
begin

instantiation prod :: (linorder, linorder) linorder
begin

abbreviation less_prod' where
  "less_prod' p1 p2 \<equiv>
   case p1 of (a1::'a::linorder, b1::'b::linorder) \<Rightarrow>
     case p2 of (a2::'a::linorder, b2::'b::linorder) \<Rightarrow>
       if (a1 < a2) \<or> (a1 = a2 \<and> b1 < b2) then True else False"

definition less_prod where
  "less_prod \<equiv> less_prod'"

definition eq_prod where
  "eq_prod p1 p2 \<equiv>
   case p1 of (a1::'a::linorder, b1::'b::linorder) \<Rightarrow>
     case p2 of (a2::'a::linorder, b2::'b::linorder) \<Rightarrow>
       if (a1 = a2) \<and> (b1 = b2) then True else False"

definition less_eq_prod where
  "less_eq_prod p1 p2 \<equiv> less_prod' p1 p2 \<or> eq_prod p1 p2"

instance proof
  show "x \<le> x" for x :: "'a \<times> 'b"
    by (auto simp add: less_eq_prod_def eq_prod_def)
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" for x y :: "'a \<times> 'b"
    by (auto simp add: less_prod_def less_eq_prod_def eq_prod_def)
  show " x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" for x y z :: "'a \<times> 'b"
    by (auto simp add: less_eq_prod_def eq_prod_def split: if_splits)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" for x y :: "'a \<times> 'b"
    by (auto simp add: less_eq_prod_def eq_prod_def split: if_splits)
  show "x \<le> y \<or> y \<le> x" for x y :: "'a \<times> 'b"
    by (auto simp add: less_eq_prod_def eq_prod_def)
qed

end

end