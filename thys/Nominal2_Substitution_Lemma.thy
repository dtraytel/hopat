theory Nominal2_Substitution_Lemma
imports Nominal2.Nominal2
begin

no_notation inverse_divide (infixl "'/" 70) \<comment> \<open>avoid clash with division notation\<close>

atom_decl var

nominal_datatype "term" = Var var | App "term" "term" | Lam x::"var" t::"term" binds x in t

nominal_function subst :: "term \<Rightarrow> term \<Rightarrow> var \<Rightarrow> term" ("_[_ '/ _]" [1000, 49, 49] 1000) where
  "(Var x)[s / y] = (if x = y then s else Var x)"
| "(App t u)[s / y] = App (t[s / y]) (u[s / y])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam x t)[s / y] = Lam x (t[s / y])"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def subst_graph_aux_def)
  subgoal by (erule subst_graph.induct) (auto simp: fresh_star_def fresh_at_base)
                      apply clarify
  subgoal for P t s y
    by (rule term.strong_exhaust[of t P "(s, y)"]) (auto simp: fresh_star_def fresh_Pair)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal for x' y' s' t' x y s t
    apply (erule conjE)+
    apply (erule Abs_lst1_fcb2'[where c = "(s, y)"])
       apply (simp_all add: eqvt_at_def fresh_star_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    apply (metis fresh_star_def fresh_star_supp_conv supp_perm_eq_test)
    apply (metis fresh_star_def fresh_star_supp_conv supp_perm_eq_test)
    done
  done
nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_subst[simp]: "atom x \<sharp> t \<Longrightarrow> atom x \<sharp> s \<Longrightarrow> atom (x :: var) \<sharp> t[s / y]"
  by (nominal_induct t avoiding: s y rule: term.strong_induct) auto

lemma subst_idle[simp]: "atom y \<sharp> t \<Longrightarrow> t[s / y] = t"
  by (nominal_induct t avoiding: s y rule: term.strong_induct)
    (auto simp: fresh_at_base)

thm term.strong_induct[no_vars]

lemma subst_subst: "y1 \<noteq> y2 \<Longrightarrow> atom y1 \<sharp> s2 \<Longrightarrow> t[s1 / y1][s2 / y2] = t[s2 / y2][s1[s2 / y2] / y1]"
  by (nominal_induct t avoiding: y1 y2 s1 s2 rule: term.strong_induct) auto

end