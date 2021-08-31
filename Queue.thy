theory Queue
  imports Queue_Specs
begin

section \<open>\<close>

text \<open>
This implementation is taken from
Okasaki, C. (1999). Purely functional data structures. Cambridge University Press.
\<close>

type_synonym 'a queue = "'a list \<times> 'a list"

definition empty :: "'a queue" where
  "empty = ([], [])"

fun is_empty :: "'a queue \<Rightarrow> bool" where
  "is_empty (f, _) \<longleftrightarrow> f = []"

fun queue :: "'a queue \<Rightarrow> 'a queue" where
  "queue ([], r) = (rev r, [])" |
  "queue (f, r) = (f, r)"

fun snoc :: "'a queue \<Rightarrow> 'a \<Rightarrow> 'a queue" where
  "snoc (f, r) x = queue (f, x # r)"

fun head :: "'a queue \<Rightarrow> 'a" where
  "head (x # f, _) = x"

fun tail :: "'a queue \<Rightarrow> 'a queue" where
  "tail (x # f, r) = queue (f, r)"

fun invar :: "'a queue \<Rightarrow> bool" where
  "invar ([], r) \<longleftrightarrow> r = []" |
  "invar (f, r) = True"

fun list :: "'a queue \<Rightarrow> 'a list" where
  "list (f, r) = f @ (rev r)"

subsection \<open>Functional correctness\<close>

lemma list_empty:
  shows "list empty = []"
  by (simp add: empty_def)

lemma is_empty:
  assumes "invar q"
  shows "is_empty q \<longleftrightarrow> list q = []"
proof -
  obtain f r where
    "q = (f, r)"
    by fastforce
  thus ?thesis
    using assms
    by fastforce
qed

lemma list_snoc:
  assumes "invar q"
  shows "list (snoc q x) = list q @ [x]"
proof -
  obtain f r where
    "q = (f, r)"
    by fastforce
  thus ?thesis
    using assms
    by (cases f) auto
qed

lemma list_non_emptyE:
  assumes "invar q"
  assumes "list q \<noteq> []"
  obtains x f r where
    "q = (x # f, r)"
proof -
  obtain f r where
    q: "q = (f, r)"
    by fastforce
  hence "\<not> is_empty (f, r)"
    using assms
    by (auto simp add: is_empty)
  hence "f \<noteq> []"
    by (simp add: is_empty_def)
  then obtain x f' where
    "f = x # f'"
    by (induction f) simp+
  thus ?thesis
    by (intro that) (simp add: q)
qed

lemma list_head:
  assumes "invar q"
  assumes "list q \<noteq> []"
  shows "head q = hd (list q)"
  using assms
  by (auto elim: list_non_emptyE)

lemma list_tail:
  assumes "invar q"
  assumes "list q \<noteq> []"
  shows "list (tail q) = tl (list q)"
proof -
  obtain f x r where
    "q = (x # f, r)"
    using assms
    by (elim list_non_emptyE)
  thus ?thesis
    by (cases f) simp+
qed

lemma invar_empty:
  shows "invar empty"
  by (simp add: empty_def)

lemma invar_snoc:
  assumes "invar q"
  shows "invar (snoc q x)"
proof -
  obtain f r where
    "q = (f, r)"
    by fastforce
  thus ?thesis
    using assms
    by (cases f) auto
qed

lemma invar_if_r_empty:
  assumes "r = []"
  shows "invar (f, r)"
  using assms
  by (cases f) simp+

lemma invar_tail:
  assumes "invar q"
  assumes "list q \<noteq> []"
  shows "invar (tail q)"
proof -
  obtain f x r where
    q: "q = (x # f, r)"
    using assms
    by (elim list_non_emptyE)
  thus ?thesis
  proof (cases f)
    case Nil
    thus ?thesis
      using assms
      by (auto simp add: q intro: invar_if_r_empty)
  next
    case (Cons y ys)
    thus ?thesis
      by (simp add: q)
  qed
qed

interpretation Q: Queue where
  empty = empty and
  is_empty = is_empty and
  snoc = snoc and
  head = head and
  tail = tail and
  invar = invar and
  list = list
  using list_empty invar_empty
  by (intro is_empty list_snoc list_head list_tail invar_snoc invar_tail Queue.intro)

end