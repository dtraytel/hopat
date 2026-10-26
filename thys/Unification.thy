theory Unification
  imports Lemmas
begin

fun dest_comb :: "dB \<Rightarrow> (dB \<times> dB list)" where
  "dest_comb (t1 \<degree> t2) = (let (s, xs) = dest_comb t1 in (s, xs @ [t2]))" |
  "dest_comb t = (t, [])"

inductive BVars :: "dB list \<Rightarrow> bool" where
  "BVars []"
| "BVars xs \<Longrightarrow> BVars (BVar x # xs)"

fun FV :: "dB \<Rightarrow> nat set" where
  "FV (Var x) = {x}"
| "FV (t1 \<degree> t2) = FV t1 \<union> FV t2"
| "FV (Abs t) = FV t"
| "FV (BVar _) = {}"

fun mk_bind :: "nat \<Rightarrow> dB \<Rightarrow> nat \<Rightarrow> dB" where
  "mk_bind F t G = (if F = G then t else Var G)"

abbreviation "binding F t \<equiv> mk_subst (mk_bind F t)"

fun idx :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "idx [] _ = None" |
  "idx (x # xs) y = (if x = y then Some (length xs) else idx xs y)"

fun flex_flex_1_zs :: "dB list \<Rightarrow> dB list \<Rightarrow> nat \<Rightarrow> dB list" where
  "flex_flex_1_zs [] [] _ = []" |
  "flex_flex_1_zs (BVar x # xs) (BVar y # ys) k = (if x = y
  then BVar k # (flex_flex_1_zs xs ys (k - 1))
  else flex_flex_1_zs xs ys (k - 1))"

fun flex_flex_2_xs_ys' :: "dB list \<Rightarrow> dB list \<Rightarrow> nat \<Rightarrow> (dB \<times> dB) list" where
  "flex_flex_2_xs_ys' [] _ _ = []" |
  "flex_flex_2_xs_ys' _ [] _ = []" |
  "flex_flex_2_xs_ys' (x # xs) ys i = (case (idx ys x) of
  Some k \<Rightarrow> (BVar i, BVar k) # flex_flex_2_xs_ys' xs ys (i - 1) |
  None \<Rightarrow> flex_flex_2_xs_ys' xs ys (i - 1))"

fun unzip' :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)" where
  "unzip' [] xs ys = (xs, ys)" |
  "unzip' ((x, y) # zs) xs ys = unzip' zs (x # xs) (y # ys)"

fun unzip :: "('a \<times> 'a) list \<Rightarrow> ('a list \<times> 'a list)" where
  "unzip zs = (let result = unzip' zs [] [] in (rev (fst result), rev (snd result)))"

fun flex_flex_2_xs_ys :: "dB list \<Rightarrow> dB list \<Rightarrow> (dB list \<times> dB list)" where
  "flex_flex_2_xs_ys x_m y_n = unzip (flex_flex_2_xs_ys' x_m y_n (length x_m - 1))"

datatype unif_problem = Problem dB dB | Marker

fun cases :: "nat \<Rightarrow> nat set \<Rightarrow> ((dB \<times> dB list) \<times> (dB \<times> dB list)) \<Rightarrow>
(nat \<times> nat set \<times> unif_problem list \<times> (dB \<Rightarrow> dB)) option" where
  rr: "cases k fr ((BVar p, s_n), (BVar p', t_n)) = (if p = p' \<and> length s_n = length t_n then
    Some (k, fr, map2 Problem s_n t_n, id) else None)" |
  fr: "cases k fr ((Var F, x_m), (BVar p, s_n)) = (if BVars x_m then
  (if F \<in> \<Union>(FV ` set s_n)
    then None
    else (if BVar p \<notin> set x_m
      then None
      else let m = length x_m in let n = length s_n in
        let j = case (idx x_m (BVar p)) of Some i \<Rightarrow> i | None \<Rightarrow> 0 in
        let zs = map BVar (downt (m - 1) 0) in let H_n = map Var (upt (k + 1) (k + n)) in
        Some (k + n, fr \<union> set (upt (k + 1) (k + n)),
          (map2 Problem (map (\<lambda>h. h \<degree>\<degree> x_m) H_n) s_n) @ [Marker],
          binding F (Abs_m m (BVar j) \<degree>\<degree> (map (\<lambda>h. h \<degree>\<degree> zs) H_n)))))
  else None)" |
  ff: "cases k fr ((Var F, x_m), (Var G, y_n)) = (if BVars x_m \<and> BVars y_n then
  (if F = G \<and> length x_m = length y_n then
    let m = length x_m in let H = Var (Suc k) in let zs = flex_flex_1_zs x_m y_n (m - 1) in
    Some (Suc k, fr, [], binding F (Abs_m m H \<degree>\<degree> zs))
  else
    let m = length x_m in let n = length y_n in let H = Var (Suc k) in
    let (xs, ys) = flex_flex_2_xs_ys x_m y_n in
    Some (Suc k, fr, [], (binding F (Abs_m m (H \<degree>\<degree> xs))) \<circ> (binding G (Abs_m n (H \<degree>\<degree> ys)))))
  else None)" |
  "cases _ _ _ = None"

fun_cases cases_SomeE: "cases k fr u = Some (k', fr', us', phi)"

fun count_Abs :: "dB \<Rightarrow> nat" where
  "count_Abs (Abs t) = 1 + count_Abs t" |
  "count_Abs (t1 \<degree> t2) = count_Abs t1 + count_Abs t2" |
  "count_Abs t = 0"

lemma count_Abs_lift: "count_Abs (lift t i) = count_Abs t"
  apply (induction arbitrary: i rule: count_Abs.induct)
  by auto

function(sequential) otf\<eta> :: "(dB \<times> dB) \<Rightarrow> (dB \<times> dB)" where
  "otf\<eta> (Abs s', Abs t') = otf\<eta> (s', t')" |
  "otf\<eta> (Abs s', t) = otf\<eta> (s', lift t 0 \<degree> BVar 0)" |
  "otf\<eta> (s, Abs t') = otf\<eta> (lift s 0 \<degree> BVar 0, t')" |
  "otf\<eta> t = t"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s, t). count_Abs s + count_Abs t)")
  by (auto simp add: count_Abs_lift)

fun tw :: "(dB \<times> dB) \<Rightarrow> (dB \<times> dB)" where
  "tw (s, t) = (case (dest_comb s) of
  (Var F, _) \<Rightarrow> (s, t) |
  _ \<Rightarrow> (t, s))"

fun_cases tw_casesE: "tw p = (s, t)"

fun map_unif_problem :: "(dB \<Rightarrow> dB) \<Rightarrow> unif_problem \<Rightarrow> unif_problem" where
  "map_unif_problem _ Marker = Marker" |
  "map_unif_problem f (Problem u1 u2) = Problem (f u1) (f u2)"

fun count_Var :: "nat set \<Rightarrow> dB \<Rightarrow> nat" where
  "count_Var fr (Var x) = (if x \<in> fr then 0 else 1)" |
  "count_Var fr (Abs t) = count_Var fr t" |
  "count_Var fr (t1 \<degree> t2) = count_Var fr t1 + count_Var fr t2" |
  "count_Var _ (BVar _) = 0"

fun unif_term_n :: "nat set \<Rightarrow> (unif_problem) list \<Rightarrow> nat" where
  "unif_term_n _ [] = 0" |
  "unif_term_n fr (Marker # us) = unif_term_n fr us" |
  "unif_term_n fr (Problem lhs rhs # us) = count_Var fr lhs + count_Var fr rhs + unif_term_n fr us"

(*
lemma "length xs = length ys \<Longrightarrow> count_Var fr t = 0 \<Longrightarrow>
  unif_term_n fr (map2 Problem xs ys) = count_Var fr (t \<degree>\<degree> xs) + count_Var fr (t \<degree>\<degree> ys)"
  apply (induct xs ys arbitrary: t rule: list_induct2)
  apply auto
  sledgehammer
*)

lemma unif_term_n_append: "unif_term_n fr (xs @ ys) = unif_term_n fr xs + unif_term_n fr ys"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  moreover obtain x where "unif_term_n fr ((a # xs) @ ys) = x + unif_term_n fr (xs @ ys)"
    by (cases a) auto
  moreover then have "unif_term_n fr (a # xs) = x + unif_term_n fr xs" by (cases a) auto
  ultimately show ?case by presburger
qed

function complexity :: "dB \<Rightarrow> nat" where
  "complexity t = (case (dest_comb t) of
  (t', []) \<Rightarrow> (case t' of
    Abs _ \<Rightarrow> 0 |
    _ \<Rightarrow> 1
    ) |
  (t', xs) \<Rightarrow> 1 + sum_list (map complexity xs)
)"
  by auto
termination oops

fun unif_term_c_m' :: "nat \<Rightarrow> (unif_problem) list \<Rightarrow> nat" where
  "unif_term_c_m' _ [] = 0" |
  "unif_term_c_m' 0 _ = 0" |
  "unif_term_c_m' i (Marker # us) = unif_term_c_m' (i - 1) us" |
  "unif_term_c_m' i (Problem lhs rhs # us) = complexity rhs + unif_term_c_m' i us"

definition unif_term_c_m :: "(unif_problem) list \<Rightarrow> nat" where
  "unif_term_c_m us = unif_term_c_m' (length (filter ((=) Marker) us)) us"

lemma unif_term_c_m_Marker: "unif_term_c_m (Marker # us) = unif_term_c_m us"
  by (simp add: unif_term_c_m_def)

fun unif_term_c' :: "(unif_problem) list \<Rightarrow> nat" where
  "unif_term_c' [] = 0" |
  "unif_term_c' (Marker # us) = 0" |
  "unif_term_c' (Problem lhs rhs # us) = complexity lhs + complexity rhs + unif_term_c' us"

definition unif_term_c :: "(unif_problem) list \<Rightarrow> nat" where
  "unif_term_c us = unif_term_c' (rev us)"

lemma unif_term_c_Marker: "unif_term_c (Marker # us) = unif_term_c us"
  apply (simp add: unif_term_c_def)
  apply (induction us rule: rev_induct)
  apply simp
proof -
  fix x :: unif_problem
  fix xs :: "unif_problem list"
  show "unif_term_c' (rev xs @ [Marker]) = unif_term_c' (rev xs) \<Longrightarrow>
    unif_term_c' (rev (xs @ [x]) @ [Marker]) = unif_term_c' (rev (xs @ [x]))"
    apply (cases x) by auto
qed

abbreviation "sndthird \<equiv> (\<lambda>(a, b, c, d). (b, c))"
abbreviation "third x \<equiv> (fst \<circ> snd \<circ> snd) x"

abbreviation "term_order \<equiv> measures
[case_prod unif_term_n \<circ> sndthird, unif_term_c_m \<circ> third, unif_term_c \<circ> third, length \<circ> third]"

definition \<beta>_normal_form :: "dB \<Rightarrow> dB" where
  "\<beta>_normal_form t = t"

function (domintros) unif :: "nat \<Rightarrow> nat set \<Rightarrow> (unif_problem) list \<Rightarrow> (dB \<Rightarrow> dB) \<Rightarrow> (dB \<Rightarrow> dB) option" where
  "unif _ _ [] phi = Some phi" |
  "unif k fr (Marker # us) phi = unif k fr us phi" |
  "unif k fr ((Problem u1 u2) # us) phi = (case ((cases k fr \<circ>
(\<lambda>(u1', u2'). (dest_comb u1', dest_comb u2')) \<circ> tw \<circ> otf\<eta>) (u1, u2)) of
  None \<Rightarrow> None |
  Some (k', fr', us', phi') \<Rightarrow> unif k' fr' (us' @ map (map_unif_problem (\<beta>_normal_form \<circ> phi')) us)
    (phi' \<circ> phi))"
  by pat_completeness auto

abbreviation "beta_normal t \<equiv> \<nexists>t'. beta t t'"

inductive list_all_unif_problem :: "(dB \<Rightarrow> bool) \<Rightarrow> unif_problem list \<Rightarrow> bool" where
  "list_all_unif_problem _ []" |
  "list_all_unif_problem p us \<Longrightarrow> list_all_unif_problem p (Marker # us)" |
  "list_all_unif_problem p us \<Longrightarrow> p u1 \<Longrightarrow> p u2 \<Longrightarrow> list_all_unif_problem p (Problem u1 u2 # us)"

lemma dest_comb_eq_iff:
  "dest_comb t = (u, xs) \<longleftrightarrow> (t = u \<degree>\<degree> xs \<and> \<not>(\<exists>u1 u2. u = u1 \<degree> u2))"
  apply (induct t arbitrary: u xs rule: dest_comb.induct)
  apply (auto simp: App_eq_foldl_conv split: prod.splits if_splits)
  apply (smt prod.inject)
  apply (smt prod.inject)
  apply (smt prod.inject)
  apply (smt prod.inject)
  done

lemma dest_comb_BVar[simp]: "dest_comb (BVar b \<degree>\<degree> xs) = (BVar b, xs)"
  by (induct xs rule: rev_induct) auto

lemma unif_termination: "\<lbrakk>list_all_unif_problem beta_normal us\<rbrakk> \<Longrightarrow> unif_dom (k, fr, us, phi)"
proof (induction "(k, fr, us, phi)" arbitrary: k fr us phi rule: wf_induct[of term_order])
  case 1
  then show ?case by simp
next
  case (2 k0 fr0 us0 phi0)
  then show ?case proof (cases "(k0, fr0, us0, phi0)" rule: unif.cases)
    case (1 uu uv phi)
    with unif.domintros(1) show ?thesis by presburger
  next
    case two: (2 k fr us phi)
    with 2 show ?thesis
      by (auto simp add: unif_term_c_Marker unif_term_c_m_Marker
          intro!: unif.domintros(2) elim: list_all_unif_problem.cases)
  next
    case (3 k fr u1 u2 us phi)
    with 2 show ?thesis
      apply (auto simp add: unif_term_c_Marker unif_term_c_m_Marker
          intro!: unif.domintros(3) elim: list_all_unif_problem.cases)
      apply (erule list_all_unif_problem.cases)
      apply (auto split: prod.splits)
      apply (erule cases_SomeE)
      apply (auto split: prod.splits if_splits simp: dest_comb_eq_iff)
      subgoal premises prems for xs b ys
        using prems(1-7,9-10)
        apply (elim tw_casesE)
        apply (auto split: prod.splits)
        apply (auto split: dB.splits)
        apply (rule prems(8)[rule_format, THEN conjunct2, rule_format])
        apply (auto simp: unif_term_n_append)
        thm prems(8)[rule_format, THEN conjunct2, rule_format]
        apply (drule spec, drule spec, drule spec, drule spec, drule mp)
        sorry
      subgoal sorry
      subgoal sorry
      subgoal sorry
      subgoal sorry
      done
  qed
qed

end