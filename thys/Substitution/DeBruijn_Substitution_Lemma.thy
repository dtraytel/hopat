theory DeBruijn_Substitution_Lemma
imports Main
begin

no_notation inverse_divide (infixl "'/" 70) \<comment> \<open>avoid clash with division notation\<close>

datatype "term" = Var nat | App "term" "term" | Lam "term"

fun shift :: "term \<Rightarrow> nat \<Rightarrow> term" where
  "shift (Var i) k = (if i < k then Var i else Var (i + 1))"
| "shift (App s t) k = App (shift s k) (shift t k)"
| "shift (Lam s) k = Lam (shift s (k + 1))"

fun subst :: "term \<Rightarrow> term \<Rightarrow> nat \<Rightarrow> term" ("_[_ '/ _]" [1000, 49, 49] 1000) where
  "(Var i)[s / k] = (if k < i then Var (i - 1) else if i = k then s else Var i)"
| "(App t u)[s / k] = App (t[s / k]) (u[s / k])"
| "(Lam t)[s / k] = Lam (t[shift s 0 / k + 1])"

lemma shift_shift[simp]: "i \<le> k \<Longrightarrow> shift (shift t i) (Suc k) = shift (shift t k) i"
  by (induct t arbitrary: i k) auto

lemma shift_subst[simp]: "j < i \<Longrightarrow> shift (t[s / j]) i = (shift t (i + 1))[shift s i / j]"
  by (induct t arbitrary: i j s) (auto simp: diff_Suc split: nat.split)

lemma shift_subst_lt[simp]: "i \<le> j \<Longrightarrow> shift (t[s / j]) i = (shift t i)[shift s i / j + 1]"
  by (induct t arbitrary: i j s) (auto simp: not_less)

lemma subst_shift [simp]: "(shift t k)[s / k] = t"
  by (induct t arbitrary: k s) auto

lemma subst_subst: "i1 \<le> i2 \<Longrightarrow> t[s1 / i1][s2 / i2] = t[shift s2 i1 / i2 + 1][s1[s2 / i2] / i1]"
  by (induct t arbitrary: i1 i2 s1 s2) auto

end