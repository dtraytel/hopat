section \<open>Soundness of \<open>MATCH\<close>\<close>

theory Unify_Match_Sound
  imports Unify_Simpl_Sound
begin

context pure_sig
begin

subsection \<open>Abstractions over types and their application\<close>

lemma types_abs_abs_list: "types_abs Ts u = abs_list (map (\<lambda>T. (STR '''', T)) Ts) u"
  by (induction Ts) simp_all

lemma types_abs_append: "types_abs (Ts @ Us) u = types_abs Ts (types_abs Us u)"
  by (induction Ts) simp_all

lemma inst_types_abs: "inst \<rho> (types_abs Ts u) = types_abs (map (tsubst \<rho>) Ts) (inst \<rho> u)"
  by (induction Ts) simp_all

lemma vsubst_types_abs: "vsubst \<sigma> (types_abs Ts u) = types_abs Ts (vsubst \<sigma> u)"
  by (induction Ts) simp_all

lemma ap_types_abs: "ap \<rho> \<sigma> (types_abs Ts u) = types_abs (map (tsubst \<rho>) Ts) (ap \<rho> \<sigma> u)"
  by (simp add: ap_def inst_types_abs vsubst_types_abs)

lemma vars_types_abs [simp]: "vars (types_abs Ts u) = vars u"
  by (induction Ts) simp_all

lemma loose_bvar_types_abs: "loose_bvar (types_abs Ts u) k \<longleftrightarrow> loose_bvar u (k + ilength Ts)"
  by (simp add: types_abs_abs_list loose_bvar_abs_list)

lemma closed_types_abs: "\<not> loose_bvar u (ilength Ts) \<Longrightarrow> closed (types_abs Ts u)"
  by (simp add: closed_def loose_bvar_types_abs)

lemma pushes_append: "pushes e (Ts @ Us) = pushes (pushes e Ts) Us"
  by (induction Ts arbitrary: e) simp_all

lemma typing_types_abs:
  "pushes e Ts \<turnstile> u : U \<Longrightarrow> \<forall>T\<in>set Ts. cert_typ alg ar T \<Longrightarrow> e \<turnstile> types_abs Ts u : Ts \<Rrightarrow> U"
  using typing_abs_list[of e "map (\<lambda>T. (STR '''', T)) Ts" u U]
  by (simp add: types_abs_abs_list comp_def)

lemma incr_bv_incr_bv: "0 \<le> m \<Longrightarrow> 0 \<le> n \<Longrightarrow> incr_bv m k (incr_bv n k t) = incr_bv (m + n) k t"
  by (induction n k t arbitrary: m rule: incr_bv.induct) (auto simp: algebra_simps)

lemma subst_types_abs:
  "0 \<le> k \<Longrightarrow> (types_abs Ts u)[s/k] = types_abs Ts (u[incr_bv (ilength Ts) 0 s / k + ilength Ts])"
proof (induction Ts arbitrary: s k)
  case (Cons T Ts)
  have "incr_bv (ilength Ts) 0 (lift s 0) = incr_bv (ilength (T # Ts)) 0 s"
    by (simp add: incr_bv_incr_bv)
  with Cons.IH[of "k + 1" "lift s 0"] Cons.prems show ?case by (simp add: algebra_simps)
qed simp

text \<open>
  The simultaneous substitution of \<open>ts\<close> for the loose bound variables of \<open>u\<close>: the last
  term of \<open>ts\<close> replaces \<open>Bound 0\<close>. It is the \<open>\<beta>\<close>-normal form of the application of an
  abstraction over \<open>length ts\<close> types to \<open>ts\<close>.
\<close>

fun cpy :: "pterm list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "cpy [] u = u"
| "cpy (t # ts) u = cpy ts (u[incr_bv (ilength ts) 0 t / ilength ts])"

lemma beta_cpy: "length Ts = length ts \<Longrightarrow> types_abs Ts u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* cpy ts u"
proof (induction ts arbitrary: Ts u)
  case (Cons t ts)
  then obtain T Ts' where Ts: "Ts = T # Ts'" and l: "length Ts' = length ts" by (cases Ts) auto
  have il: "ilength Ts' = ilength ts" using l by (simp add: ilength_eq)
  have "Abs STR '''' T (types_abs Ts' u) $ t \<rightarrow>\<^sub>\<beta> (types_abs Ts' u)[t/0]" by (rule beta.beta)
  also have "(types_abs Ts' u)[t/0] = types_abs Ts' (u[incr_bv (ilength ts) 0 t / ilength ts])"
    by (simp add: subst_types_abs il)
  finally have "types_abs Ts u \<degree>\<degree> (t # ts) \<rightarrow>\<^sub>\<beta>\<^sup>* types_abs Ts' (u[incr_bv (ilength ts) 0 t / ilength ts]) \<degree>\<degree> ts"
    unfolding Ts by (simp add: r_into_rtranclp)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* cpy (t # ts) u" using Cons.IH[OF l] by simp
  finally show ?case .
qed simp

lemma cpy_App: "cpy ts (s $ t) = cpy ts s $ cpy ts t"
  by (induction ts arbitrary: s t) simp_all

lemma cpy_apps: "cpy ts (s \<degree>\<degree> us) = cpy ts s \<degree>\<degree> map (cpy ts) us"
  by (induction us arbitrary: s) (simp_all add: cpy_App)

lemma cpy_closed: "closed h \<Longrightarrow> cpy ts h = h"
  by (induction ts) (simp_all add: subst_no_loose closed_loose_bvar)

lemma subst_incr_bv_Suc:
  "0 \<le> k \<Longrightarrow> 0 \<le> n \<Longrightarrow> (incr_bv (n + 1) k t)[s/k + n] = incr_bv n k t"
proof (induction t arbitrary: k s)
  case (Bound i)
  then show ?case by (auto simp: subst_Bound integer_arith)
next
  case (Abs a T t)
  from Abs.IH[of "k + 1" "lift s 0"] Abs.prems show ?case by (simp add: algebra_simps)
qed auto

lemma cpy_incr: "cpy ts (incr_bv (ilength ts) 0 t) = t"
proof (induction ts arbitrary: t)
  case (Cons s ts)
  have "(incr_bv (ilength ts + 1) 0 t)[incr_bv (ilength ts) 0 s/ilength ts] = incr_bv (ilength ts) 0 t"
    using subst_incr_bv_Suc[of 0 "ilength ts" t] by simp
  with Cons.IH show ?case by simp
qed simp

lemma cpy_Bound:
  "0 \<le> j \<Longrightarrow> j < ilength ts \<Longrightarrow> cpy ts (Bound j) = ts ! (length ts - 1 - nat_of_integer j)"
proof (induction ts)
  case (Cons t ts)
  show ?case
  proof (cases "j = ilength ts")
    case True
    then have "nat_of_integer j = length ts" by (simp add: ilength_eq)
    with True show ?thesis by (simp add: cpy_incr)
  next
    case False
    with Cons.prems have j: "j < ilength ts" by (simp add: integer_arith)
    then have "nat_of_integer j < length ts" using Cons.prems(1) nat_of_integer_less_ilength by blast
    then have "(t # ts) ! (length (t # ts) - 1 - nat_of_integer j) = ts ! (length ts - 1 - nat_of_integer j)"
      by (simp add: nth_Cons' Suc_diff_Suc)
    with j Cons.IH Cons.prems False show ?thesis by (simp add: subst_Bound)
  qed
qed simp

text \<open>The bound variables \<open>Bound (n - 1), \<dots>, Bound 0\<close>:\<close>

abbreviation bvs :: "nat \<Rightarrow> pterm list" where
  "bvs n \<equiv> map (\<lambda>i. Bound (integer_of_nat i)) (rev [0..<n])"

lemma combound_apps: "combound t m k = t \<degree>\<degree> map (\<lambda>i. Bound (m + integer_of_nat i)) (rev [0..<k])"
proof (induction k arbitrary: m)
  case (Suc k)
  have r: "rev [0..<Suc k] = map Suc (rev [0..<k]) @ [0]"
    by (simp add: upt_conv_Cons map_Suc_upt[symmetric] rev_map del: upt_Suc)
  show ?case using Suc.IH[of "m + 1"] by (simp add: r comp_def algebra_simps integer_of_nat_eq_of_nat del: upt_Suc)
qed simp

lemma combound_bvs: "combound t 0 k = t \<degree>\<degree> bvs k"
  by (simp add: combound_apps)

lemma map_cpy_bvs: "map (cpy ts) (bvs (length ts)) = ts"
proof (rule nth_equalityI)
  fix j assume j: "j < length (map (cpy ts) (bvs (length ts)))"
  then have j': "j < length ts" by simp
  have "rev [0..<length ts] ! j = length ts - 1 - j" using j' by (simp add: rev_nth)
  moreover have "0 \<le> integer_of_nat (length ts - 1 - j)" "integer_of_nat (length ts - 1 - j) < ilength ts"
    using j' by (simp_all add: ilength_eq integer_reps)
  ultimately show "map (cpy ts) (bvs (length ts)) ! j = ts ! j"
    using j' by (simp add: cpy_Bound)
qed simp

lemma typings_iff: "e \<tturnstile> ts : Ts \<longleftrightarrow> list_all2 (typing e) ts Ts"
  by (induction ts arbitrary: Ts) (auto split: list.splits simp: list_all2_Cons1)

lemma typings_bvs: "pushes e Ts \<tturnstile> bvs (length Ts) : Ts"
proof -
  let ?ks = "map integer_of_nat (rev [0..<length Ts])"
  have "pushes e Ts \<tturnstile> map Bound ?ks : map (\<lambda>k. rev Ts ! nat_of_integer k) ?ks"
    by (rule typings_Bounds) (auto simp: pushes_nth ilength_eq integer_of_nat_eq_of_nat)
  moreover have "map (\<lambda>k. rev Ts ! nat_of_integer k) ?ks = Ts"
    by (rule nth_equalityI) (simp_all add: rev_nth)
  ultimately show ?thesis by (simp add: comp_def)
qed

lemma loose_bvar_bvs: "t \<in> set (bvs n) \<Longrightarrow> \<not> loose_bvar t (integer_of_nat n)"
  by (auto simp: integer_of_nat_eq_of_nat)

text \<open>Applying the abstraction of a copy to the arguments is its simultaneous substitution:\<close>

lemma beta_reds_inst: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> inst \<rho> s \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl beta_inst)

lemma beta_reds_ap: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> ap \<rho> \<sigma> s \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> t"
  unfolding ap_def by (intro beta_reds_vsubst beta_reds_inst) (auto simp: wt_subst_def)

lemma conv_cpy:
  assumes "e \<turnstile> inst \<rho> (types_abs Ts u \<degree>\<degree> ts) : U" "wt_subst \<sigma>" "length Ts = length ts"
  shows "ap \<rho> \<sigma> (types_abs Ts u \<degree>\<degree> ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (cpy ts u)" "e \<turnstile> inst \<rho> (cpy ts u) : U"
proof -
  have b: "types_abs Ts u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* cpy ts u" by (rule beta_cpy[OF assms(3)])
  show "ap \<rho> \<sigma> (types_abs Ts u \<degree>\<degree> ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (cpy ts u)"
    by (rule conv_beta_eta[OF wt_ap[OF assms(1,2)] beta_reds_ap[OF b assms(2)]])
  show "e \<turnstile> inst \<rho> (cpy ts u) : U"
    by (rule subject_reduction_beta'[OF beta_reds_inst[OF b] assms(1)])
qed

end

end
