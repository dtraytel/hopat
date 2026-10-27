theory Nominal_Substitution_Lemma
imports "HOL-Nominal.Nominal"
begin

no_notation inverse_divide (infixl "'/" 70) \<comment> \<open>avoid clash with division notation\<close>

atom_decl var

nominal_datatype "term" = Var var | App "term" "term" | Lam "\<guillemotleft>var\<guillemotright> term"

nominal_primrec subst :: "term \<Rightarrow> term \<Rightarrow> var \<Rightarrow> term" ("_[_ '/ _]" [1000, 49, 49] 1000) where
  "(Var x)[s / y] = (if x = y then s else Var x)"
| "(App t u)[s / y] = App (t[s / y]) (u[s / y])"
| "x \<sharp> (y, s) \<Longrightarrow> (Lam x t)[s / y] = Lam x (t[s / y])"
  by (finite_guess | fresh_guess | auto simp: abs_fresh split: if_splits)+

lemma fresh_subst[simp]: "x \<sharp> t \<Longrightarrow> x \<sharp> s \<Longrightarrow> (x :: var) \<sharp> t[s / y]"
  by (nominal_induct t avoiding: s y rule: term.strong_induct) (auto simp: abs_fresh)

lemma subst_idle[simp]: "y \<sharp> t \<Longrightarrow> t[s / y] = t"
  by (nominal_induct t avoiding: s y rule: term.strong_induct) (auto simp: abs_fresh fresh_atm)

thm term.strong_induct[no_vars]

lemma subst_subst: "y1 \<noteq> y2 \<Longrightarrow> y1 \<sharp> s2 \<Longrightarrow> t[s1 / y1][s2 / y2] = t[s2 / y2][s1[s2 / y2] / y1]"
  by (nominal_induct t avoiding: y1 y2 s1 s2 rule: term.strong_induct) auto

end