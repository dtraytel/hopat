section \<open>Soundness of \<open>MATCH\<close>\<close>

theory Unify_Match_Sound
  imports Unify_Simpl_Sound Unify_Seq
begin

text \<open>
  The goals of the elements of the sequences (as in the old development): unifiers
  (\<open>GR env0 dps0\<close>), reduced problems (\<open>GE env0 dps0\<close>), copies of a term \<open>u\<close> into a variable
  applied to \<open>targs\<close> of types \<open>Ts\<close> under the binders \<open>rb\<close> (\<open>GC env0 rb targs Ts u dps0 ot\<close>,
  where \<open>ot = Some t\<close> restricts the typings to those in which the flexible side \<open>t\<close> has the type of
  \<open>u\<close>), copies
  of argument lists (\<open>GD\<close>), and single steps of matching (\<open>GS env0 dps0 Ts B\<close>), whose copies
  have type \<open>B\<close> under binders of types \<open>Ts\<close>. The invariant \<open>seqinv\<close> of the sequences below covers
  those of \<open>MATCH\<close>; the search, whose elements are unifiers, is treated in theory
  \<open>Unify_Pull_Fin\<close>, since the soundness of \<open>MATCH\<close> rests on the invariant of its termination
  proof.
\<close>

datatype goal =
  GR env "dpair list"
| GE env "dpair list"
| GC env binders "pterm list" "ptyp list" pterm "dpair list" "pterm option"
| GD env binders "pterm list" "ptyp list" "pterm list" "dpair list"
| GS env "dpair list" "ptyp list" ptyp

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

lemma subst_abs_list:
  "0 \<le> k \<Longrightarrow> (abs_list bs u)[s/k] = abs_list bs (u[incr_bv (ilength bs) 0 s / k + ilength bs])"
proof (induction bs arbitrary: s k)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by (cases b)
  have "incr_bv (ilength bs) 0 (lift s 0) = incr_bv (ilength (b # bs)) 0 s"
    by (simp add: incr_bv_incr_bv)
  with Cons.IH[of "k + 1" "lift s 0"] Cons.prems show ?case by (simp add: b algebra_simps)
qed simp

lemma subst_types_abs:
  "0 \<le> k \<Longrightarrow> (types_abs Ts u)[s/k] = types_abs Ts (u[incr_bv (ilength Ts) 0 s / k + ilength Ts])"
  by (simp add: types_abs_abs_list subst_abs_list)

text \<open>
  The simultaneous substitution of \<open>ts\<close> for the loose bound variables of \<open>u\<close>: the last
  term of \<open>ts\<close> replaces \<open>Bound 0\<close>. It is the \<open>\<beta>\<close>-normal form of the application of an
  abstraction over \<open>length ts\<close> variables to \<open>ts\<close>.
\<close>

fun cpy :: "pterm list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "cpy [] u = u"
| "cpy (t # ts) u = cpy ts (u[incr_bv (ilength ts) 0 t / ilength ts])"

lemma beta_cpy_abs_list: "length bs = length ts \<Longrightarrow> abs_list bs u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* cpy ts u"
proof (induction ts arbitrary: bs u)
  case (Cons t ts)
  then obtain x T bs' where bs: "bs = (x, T) # bs'" and l: "length bs' = length ts" by (cases bs) auto
  have il: "ilength bs' = ilength ts" using l by (simp add: ilength_eq)
  have "Abs x T (abs_list bs' u) $ t \<rightarrow>\<^sub>\<beta> (abs_list bs' u)[t/0]" by (rule beta.beta)
  also have "(abs_list bs' u)[t/0] = abs_list bs' (u[incr_bv (ilength ts) 0 t / ilength ts])"
    by (simp add: subst_abs_list il)
  finally have "abs_list bs u \<degree>\<degree> (t # ts) \<rightarrow>\<^sub>\<beta>\<^sup>* abs_list bs' (u[incr_bv (ilength ts) 0 t / ilength ts]) \<degree>\<degree> ts"
    unfolding bs by (simp add: r_into_rtranclp)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* cpy (t # ts) u" using Cons.IH[OF l] by simp
  finally show ?case .
qed simp

lemma beta_cpy: "length Ts = length ts \<Longrightarrow> types_abs Ts u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* cpy ts u"
  unfolding types_abs_abs_list by (rule beta_cpy_abs_list) simp

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


subsection \<open>Goals, elements and the invariant of sequences\<close>

abbreviation tps_dps :: "(pterm \<times> pterm) list \<Rightarrow> dpair list" where
  "tps_dps tps \<equiv> map (\<lambda>(t, u). ([], t, u)) tps"

abbreviation lvars :: "pterm list \<Rightarrow> (indexname \<times> ptyp) set" where
  "lvars ts \<equiv> \<Union> (vars ` set ts)"

text \<open>
  Copies \<open>us'\<close> of the terms \<open>us\<close> into a variable applied to \<open>targs\<close>: for every type instantiation
  as in \<^const>\<open>dstep\<close>, if the terms \<open>us\<close> and the arguments \<open>targs\<close> are well-typed, the
  arguments with the types \<open>Ts\<close>, the copies are well-typed terms under binders of types \<open>Ts\<close>
  (their loose bound variables stand for the arguments), and every solution of the final
  environment that solves the pairs \<open>dps\<close> equates the abstractions of the copies, applied to the
  arguments, with the terms, and solves the pairs \<open>dps0\<close>.
\<close>

definition astep :: "env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm list \<Rightarrow> dpair list \<Rightarrow>
    pterm list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "astep env0 rb targs Ts us dps0 us' env dps \<longleftrightarrow> extends env0 env \<and> length us' = length us \<and>
    (\<forall>\<rho> env'' X e Us. tsol (tyenv env'') \<rho> \<longrightarrow> extends env env'' \<longrightarrow> wt_env \<rho> env0 \<longrightarrow> dtyped \<rho> dps0 \<longrightarrow>
      bs_env \<rho> e rb \<longrightarrow> e \<tturnstile> map (inst \<rho>) us : Us \<longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<longrightarrow>
      (\<forall>t\<in>set (us @ targs). \<not> loose_bvar t (ilength rb)) \<longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars (us @ targs)) \<longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> lvars us') \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) us' : Us) \<and>
      (\<forall>t\<in>set us'. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) us' us \<and> dsolved \<rho> \<sigma> dps0))"

text \<open>
  Copies for a goal with a flexible side \<open>t\<close> (\<open>ot = Some t\<close>) need to be correct only for the
  typings in which \<open>t\<close> has the type of the copied terms (\<open>tyok\<close>).
\<close>

fun tyok :: "pterm option \<Rightarrow> tinst \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "tyok None \<rho> e Us \<longleftrightarrow> True"
| "tyok (Some t) \<rho> e Us \<longleftrightarrow> (\<forall>U\<in>set Us. e \<turnstile> inst \<rho> t : U)"

definition astepo :: "pterm option \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm list \<Rightarrow>
    dpair list \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "astepo ot env0 rb targs Ts us dps0 us' env dps \<longleftrightarrow> extends env0 env \<and> length us' = length us \<and>
    (\<forall>\<rho> env'' X e Us. tsol (tyenv env'') \<rho> \<longrightarrow> extends env env'' \<longrightarrow> wt_env \<rho> env0 \<longrightarrow> dtyped \<rho> dps0 \<longrightarrow>
      bs_env \<rho> e rb \<longrightarrow> tyok ot \<rho> e Us \<longrightarrow> e \<tturnstile> map (inst \<rho>) us : Us \<longrightarrow>
      e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<longrightarrow>
      (\<forall>t\<in>set (us @ targs). \<not> loose_bvar t (ilength rb)) \<longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars (us @ targs)) \<longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> lvars us') \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) us' : Us) \<and>
      (\<forall>t\<in>set us'. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) us' us \<and> dsolved \<rho> \<sigma> dps0))"

lemma astepo_None: "astepo None env0 rb targs Ts us dps0 us' env dps \<longleftrightarrow> astep env0 rb targs Ts us dps0 us' env dps"
  unfolding astepo_def astep_def by simp

lemma astep_astepo: "astep env0 rb targs Ts us dps0 us' env dps \<Longrightarrow> astepo ot env0 rb targs Ts us dps0 us' env dps"
  unfolding astepo_def astep_def by blast

text \<open>
  A single step of matching keeps the pairs: the term \<open>u'\<close>, abstracted over \<open>Ts\<close>, has the type
  of the variable of type \<open>T\<close>.
\<close>

definition mstep1 :: "env \<Rightarrow> dpair list \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "mstep1 env0 dps0 Ts T u' env dps \<longleftrightarrow> extends env0 env \<and>
    (\<forall>\<rho> env'' X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env env'' \<longrightarrow> wt_env \<rho> env0 \<longrightarrow> dtyped \<rho> dps0 \<longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0) \<longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> vars u') \<and>
      (\<exists>B. tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> B \<and> (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> u' : B)) \<and>
      \<not> loose_bvar u' (ilength Ts) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow> dsolved \<rho> \<sigma> dps0))"

fun elem_ok :: "goal \<Rightarrow> elem \<Rightarrow> bool" where
  "elem_ok (GR env0 dps0) (El_R env tps) \<longleftrightarrow> dstep env0 dps0 env (tps_dps tps)"
| "elem_ok (GE env0 dps0) (El_E env dps) \<longleftrightarrow> dstep env0 dps0 env dps"
| "elem_ok (GC env0 rb targs Ts u dps0 ot) (El_C u' env dps) \<longleftrightarrow> astepo ot env0 rb targs Ts [u] dps0 [u'] env dps"
| "elem_ok (GD env0 rb targs Ts us dps0) (El_D us' env dps) \<longleftrightarrow> astep env0 rb targs Ts us dps0 us' env dps"
| "elem_ok (GS env0 dps0 Ts T) (El_C u' env dps) \<longleftrightarrow> mstep1 env0 dps0 Ts T u' env dps"
| "elem_ok _ _ \<longleftrightarrow> False"

text \<open>The arguments of the flexible side have the types \<open>Ts\<close>:\<close>

definition targs_ok :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "targs_ok env rb t targs Ts \<longleftrightarrow> (\<forall>\<rho> e U. tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow>
    e \<turnstile> inst \<rho> t : U \<longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts)"

text \<open>A projection on the argument \<open>targ\<close> of the copy goal, after the type unification:\<close>

definition proj_ok :: "env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> ptyp list \<Rightarrow>
    ptyp list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm option \<Rightarrow> bool" where
  "proj_ok env rb targs Ts u env' Ts' Us head targ ot \<longleftrightarrow> extends env env' \<and> tenv env' = tenv env \<and>
    length Ts' = length targs \<and>
    (\<exists>j. head = Bound j \<and> 0 \<le> j \<and> j < ilength targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j)) \<and>
    (\<forall>\<rho> e U. tsol (tyenv env') \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow> e \<turnstile> inst \<rho> u : U \<longrightarrow> tyok ot \<rho> e [U] \<longrightarrow>
      e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<longrightarrow>
      (\<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb)) \<longrightarrow>
      map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts \<and> e \<turnstile> inst \<rho> targ : map (tsubst \<rho>) Us \<Rrightarrow> U)"

inductive seqinv :: "goal \<Rightarrow> seq \<Rightarrow> bool" where
  Empty: "seqinv G S_Empty"
| Single: "elem_ok G x \<Longrightarrow> seqinv G (S_Single x)"
| Append: "seqinv G xq \<Longrightarrow> seqinv G yq \<Longrightarrow> seqinv G (S_Append xq yq)"
| NewDset: "dstep env0 dps0 env1 ((rb, t, u) # dps1 @ others) \<Longrightarrow> strip_comb t = (Var v T, targs) \<Longrightarrow>
    targs_ok env1 rb t targs Ts \<Longrightarrow> seqinv (GC env1 rb targs Ts u dps1 (Some t)) xq \<Longrightarrow>
    seqinv (GE env0 dps0) (S_MapNewDset (v, T) Ts others xq)"
| NewDset1: "dstep env0 dps0 env1 dps1 \<Longrightarrow> (v, T) \<in> dvars dps1 \<Longrightarrow> seqinv (GS env1 dps1 Ts T) xq \<Longrightarrow>
    seqinv (GE env0 dps0) (S_MapNewDset (v, T) Ts [] xq)"
| MapAbs: "seqinv (GC env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) (Ts @ [T]) body dps0 None) xq \<Longrightarrow>
    seqinv (GC env0 rb targs Ts (Abs a T body) dps0 ot) (S_MapAbs a T xq)"
| Proj: "proj_ok env rb targs Ts u env' Ts' Us head targ ot \<Longrightarrow> seqinv (GC env rb targs Ts u dps ot) tail \<Longrightarrow>
    seqinv (GC env rb targs Ts u dps ot) (S_Proj vname env' Ts' Us targs rb u dps head targ tail)"
| MapJoin: "closed uhead \<Longrightarrow> vars uhead = {} \<Longrightarrow> seqinv (GD env0 rb targs Ts uargs dps0) xq \<Longrightarrow>
    seqinv (GC env0 rb targs Ts (uhead \<degree>\<degree> uargs) dps0 ot) (S_MapJoin uhead xq)"
| Maps: "seqinv (GD env0 rb targs Ts uargs dps0) xq \<Longrightarrow>
    seqinv (GD env0 rb targs Ts (uarg # uargs) dps0) (S_Maps vname rb targs uarg xq)"
| MapCons: "astep env0 rb targs Ts uargs dps0 uargs' env dps \<Longrightarrow> tconv env rb uarg u2 \<Longrightarrow>
    seqinv (GC env rb targs Ts u2 dps None) xq \<Longrightarrow> seqinv (GD env0 rb targs Ts (uarg # uargs) dps0) (S_MapCons uargs' xq)"

text \<open>Reduced problems compose with steps before them:\<close>

lemma seqinv_GE_dstep: "seqinv G s \<Longrightarrow> G = GE env1 dps1 \<Longrightarrow> dstep env0 dps0 env1 dps1 \<Longrightarrow> seqinv (GE env0 dps0) s"
proof (induction arbitrary: env1 dps1 rule: seqinv.induct)
  case (Single G x)
  then show ?case by (cases x) (auto intro!: seqinv.Single intro: dstep_trans)
qed (auto intro: seqinv.intros dstep_trans)


lemma astepI:
  assumes "extends env0 env" "length us' = length us"
    and "\<And>\<rho> env'' X e Us. tsol (tyenv env'') \<rho> \<Longrightarrow> extends env env'' \<Longrightarrow> wt_env \<rho> env0 \<Longrightarrow> dtyped \<rho> dps0 \<Longrightarrow>
      bs_env \<rho> e rb \<Longrightarrow> e \<tturnstile> map (inst \<rho>) us : Us \<Longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow>
      \<forall>t\<in>set (us @ targs). \<not> loose_bvar t (ilength rb) \<Longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars (us @ targs)) \<Longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> lvars us') \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) us' : Us) \<and>
      (\<forall>t\<in>set us'. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) us' us \<and> dsolved \<rho> \<sigma> dps0)"
  shows "astep env0 rb targs Ts us dps0 us' env dps"
  using assms unfolding astep_def by blast

lemma astepD:
  assumes "astep env0 rb targs Ts us dps0 us' env dps"
  shows "extends env0 env" "length us' = length us"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env env'' \<Longrightarrow> wt_env \<rho> env0 \<Longrightarrow> dtyped \<rho> dps0 \<Longrightarrow>
      bs_env \<rho> e rb \<Longrightarrow> e \<tturnstile> map (inst \<rho>) us : Us \<Longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow>
      \<forall>t\<in>set (us @ targs). \<not> loose_bvar t (ilength rb) \<Longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars (us @ targs)) \<Longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> lvars us') \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) us' : Us) \<and>
      (\<forall>t\<in>set us'. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) us' us \<and> dsolved \<rho> \<sigma> dps0)"
  using assms unfolding astep_def by blast+

lemma astepoI:
  assumes "extends env0 env" "length us' = length us"
    and "\<And>\<rho> env'' X e Us. tsol (tyenv env'') \<rho> \<Longrightarrow> extends env env'' \<Longrightarrow> wt_env \<rho> env0 \<Longrightarrow> dtyped \<rho> dps0 \<Longrightarrow>
      bs_env \<rho> e rb \<Longrightarrow> tyok ot \<rho> e Us \<Longrightarrow> e \<tturnstile> map (inst \<rho>) us : Us \<Longrightarrow>
      e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow>
      \<forall>t\<in>set (us @ targs). \<not> loose_bvar t (ilength rb) \<Longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars (us @ targs)) \<Longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> lvars us') \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) us' : Us) \<and>
      (\<forall>t\<in>set us'. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) us' us \<and> dsolved \<rho> \<sigma> dps0)"
  shows "astepo ot env0 rb targs Ts us dps0 us' env dps"
  using assms unfolding astepo_def by blast

lemma astepoD:
  assumes "astepo ot env0 rb targs Ts us dps0 us' env dps"
  shows "extends env0 env" "length us' = length us"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env env'' \<Longrightarrow> wt_env \<rho> env0 \<Longrightarrow> dtyped \<rho> dps0 \<Longrightarrow>
      bs_env \<rho> e rb \<Longrightarrow> tyok ot \<rho> e Us \<Longrightarrow> e \<tturnstile> map (inst \<rho>) us : Us \<Longrightarrow>
      e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow>
      \<forall>t\<in>set (us @ targs). \<not> loose_bvar t (ilength rb) \<Longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars (us @ targs)) \<Longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> lvars us') \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) us' : Us) \<and>
      (\<forall>t\<in>set us'. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) us' us \<and> dsolved \<rho> \<sigma> dps0)"
  using assms unfolding astepo_def by blast+


subsection \<open>Copies of terms\<close>

lemma cert_targs:
  assumes "bs_env \<rho> e rb" "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
  shows "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
proof
  fix T assume "T \<in> set Ts"
  then obtain i where i: "i < length Ts" "T = Ts ! i" by (auto simp: in_set_conv_nth)
  from typings_nth[OF assms(2)] i have l: "i < length targs" "e \<turnstile> inst \<rho> (targs ! i) : tsubst \<rho> T"
    by auto
  show "cert_typ alg ar (tsubst \<rho> T)"
    by (rule bs_env_cert[OF assms(1) l(2)]) (use assms(3) l(1) in auto)
qed

lemma typing_tabs_app:
  assumes "pushes e (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> u' : U" "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
  shows "e \<turnstile> inst \<rho> (types_abs Ts u' \<degree>\<degree> targs) : U"
proof -
  have "e \<turnstile> types_abs (map (tsubst \<rho>) Ts) (inst \<rho> u') : map (tsubst \<rho>) Ts \<Rrightarrow> U"
    by (rule typing_types_abs[OF assms(1)]) (use assms(3) in auto)
  then show ?thesis using assms(2) by (simp add: inst_apps inst_types_abs list_app_typeI)
qed

lemma conv_eta_lift: "wt (Abs a T (lift w 0 $ Bound 0)) \<Longrightarrow> Abs a T (lift w 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> w"
proof -
  assume w: "wt (Abs a T (lift w 0 $ Bound 0))"
  have "Abs a T (lift w 0 $ Bound 0) \<rightarrow>\<^sub>\<eta> (lift w 0)[d/0]" for d by (rule eta.eta) simp
  then have "Abs a T (lift w 0 $ Bound 0) \<rightarrow>\<^sub>\<eta> w" by simp
  then show ?thesis using w by (intro beta_eta_conv) auto
qed

lemma astep_Nil: "astep env rb targs Ts [] dps [] env dps"
  by (rule astepI) (auto elim: vinv_mono)

text \<open>The copies of an argument and of the further arguments:\<close>

lemma astep_cons:
  assumes a1: "astep env0 rb targs Ts uargs dps0 uargs' env dps" and tc: "tconv env rb uarg u2"
    and a2: "astep env rb targs Ts [u2] dps [u'] env' dps'"
  shows "astep env0 rb targs Ts (uarg # uargs) dps0 (u' # uargs') env' dps'"
proof (rule astepI)
  have e1: "extends env0 env" and l1: "length uargs' = length uargs" by (fact astepD(1,2)[OF a1])+
  have e2: "extends env env'" by (fact astepD(1)[OF a2])
  show "extends env0 env'" by (rule extends_trans[OF e1 e2])
  show "length (u' # uargs') = length (uarg # uargs)" using l1 by simp
  fix \<rho> env'' X e Us0
  assume tsol: "tsol (tyenv env'') \<rho>" and ext: "extends env' env''" and wte: "wt_env \<rho> env0"
    and dt: "dtyped \<rho> dps0" and bs: "bs_env \<rho> e rb" and tys: "e \<tturnstile> map (inst \<rho>) (uarg # uargs) : Us0"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    and lb: "\<forall>t\<in>set ((uarg # uargs) @ targs). \<not> loose_bvar t (ilength rb)"
    and vi: "vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars ((uarg # uargs) @ targs))"
  from tys obtain U Us where Us0: "Us0 = U # Us" and tyu: "e \<turnstile> inst \<rho> uarg : U"
    and tyus: "e \<tturnstile> map (inst \<rho>) uargs : Us"
    by (auto split: list.splits)
  have ext1: "extends env env''" by (rule extends_trans[OF e2 ext])
  have tsol1: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol ext1])
  have lb1: "\<forall>t\<in>set (uargs @ targs). \<not> loose_bvar t (ilength rb)" using lb by auto
  have vi1: "vinv \<rho> env0 ((X \<union> vars uarg \<union> lvars targs) \<union> dvars dps0 \<union> lvars (uargs @ targs))"
    using vi by (auto simp: Un_ac intro: vinv_mono)
  note R1 = astepD(3)[OF a1 tsol ext1 wte dt bs tyus tyt lb1 vi1]
  have luarg: "\<not> loose_bvar uarg (ilength rb)" using lb by simp
  from tc[unfolded tconv_def] tsol1 R1 bs tyu luarg
  have tc1: "vars u2 \<subseteq> vars uarg \<union> evars env" "e \<turnstile> inst \<rho> u2 : U" "\<not> loose_bvar u2 (ilength rb)"
    "\<forall>\<sigma>. solution \<rho> \<sigma> env \<longrightarrow> ap \<rho> \<sigma> uarg \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u2"
    by blast+
  have vi2: "vinv \<rho> env ((X \<union> lvars uargs') \<union> dvars dps \<union> lvars ([u2] @ targs))"
  proof -
    have "vinv \<rho> env ((X \<union> lvars uargs' \<union> dvars dps) \<union> (vars uarg \<union> lvars targs))"
      using R1 by (simp add: Un_ac)
    then have "vinv \<rho> env ((X \<union> lvars uargs' \<union> dvars dps) \<union> (vars u2 \<union> lvars targs))"
      by (rule vinv_hn) (use tc1(1) in auto)
    then show ?thesis by (simp add: Un_ac)
  qed
  have tyu2: "e \<tturnstile> map (inst \<rho>) [u2] : [U]" using tc1(2) by simp
  have lb2: "\<forall>t\<in>set ([u2] @ targs). \<not> loose_bvar t (ilength rb)" using tc1(3) lb by auto
  note R2 = astepD(3)[OF a2 tsol ext R1[THEN conjunct1] R1[THEN conjunct2, THEN conjunct1] bs tyu2 tyt lb2 vi2]
  show "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps' \<union> lvars (u' # uargs')) \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) (u' # uargs') : Us0) \<and>
      (\<forall>t\<in>set (u' # uargs'). \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps' \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) (u' # uargs') (uarg # uargs) \<and>
        dsolved \<rho> \<sigma> dps0)"
  proof (intro conjI allI impI)
    show "wt_env \<rho> env'" "dtyped \<rho> dps'" using R2 by blast+
    show "vinv \<rho> env' (X \<union> dvars dps' \<union> lvars (u' # uargs'))" using R2 by (simp add: Un_ac)
    show "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) (u' # uargs') : Us0" for e'
      using R1 R2 by (simp add: Us0)
    show "\<forall>t\<in>set (u' # uargs'). \<not> loose_bvar t (ilength Ts)" using R1 R2 by simp
    fix \<sigma> assume sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> dps'"
    from R2 sol ds have c2: "ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u2" and ds1: "dsolved \<rho> \<sigma> dps"
      by auto
    from R1 sol ds1 have c1: "list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) uargs' uargs"
      and "dsolved \<rho> \<sigma> dps0" by auto
    then show "dsolved \<rho> \<sigma> dps0" by simp
    have "ap \<rho> \<sigma> uarg \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u2" using tc1(4) solution_extends[OF sol ext1] by blast
    with c2 have "ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> uarg" by (blast intro: conv_trans conv_sym)
    with c1 show "list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) (u' # uargs') (uarg # uargs)"
      by simp
  qed
qed

lemma ilength_append [simp]: "ilength (xs @ ys) = ilength xs + ilength ys"
  by (induction xs) simp_all

lemma closed_inst: "closed h \<Longrightarrow> closed (inst \<rho> h)"
  by (simp add: closed_def)

text \<open>Imitation: the head applied to the copies of the arguments.\<close>

lemma astep_join:
  assumes a: "astep env0 rb targs Ts uargs dps0 uargs' env dps" and c: "closed h" and vh: "vars h = {}"
  shows "astep env0 rb targs Ts [h \<degree>\<degree> uargs] dps0 [h \<degree>\<degree> uargs'] env dps"
proof (rule astepI)
  show "extends env0 env" by (fact astepD(1)[OF a])
  show "length [h \<degree>\<degree> uargs'] = length [h \<degree>\<degree> uargs]" by simp
  fix \<rho> env'' X e Us0
  assume tsol: "tsol (tyenv env'') \<rho>" and ext: "extends env env''" and wte: "wt_env \<rho> env0"
    and dt: "dtyped \<rho> dps0" and bs: "bs_env \<rho> e rb" and tys: "e \<tturnstile> map (inst \<rho>) [h \<degree>\<degree> uargs] : Us0"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    and lb: "\<forall>t\<in>set ([h \<degree>\<degree> uargs] @ targs). \<not> loose_bvar t (ilength rb)"
    and vi: "vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars ([h \<degree>\<degree> uargs] @ targs))"
  from tys obtain U where Us0: "Us0 = [U]" and tyu: "e \<turnstile> inst \<rho> h \<degree>\<degree> map (inst \<rho>) uargs : U"
    by (auto split: list.splits simp: inst_apps)
  from tyu obtain Us where th: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> U" and tus: "e \<tturnstile> map (inst \<rho>) uargs : Us"
    by (rule list_app_typeE)
  have lb1: "\<forall>t\<in>set (uargs @ targs). \<not> loose_bvar t (ilength rb)" using lb by (auto simp: loose_bvar_apps)
  have vi1: "vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars (uargs @ targs))" using vi by (simp add: vars_apps vh)
  note R = astepD(3)[OF a tsol ext wte dt bs tus tyt lb1 vi1]
  have len: "length Ts = length targs" using typings_nth[OF tyt] by simp
  have cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF bs tyt]) (use lb in auto)
  have tyh: "e' \<turnstile> inst \<rho> h : Us \<Rrightarrow> U" for e' by (rule typing_closed[OF th closed_inst[OF c]])
  have tyc: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (h \<degree>\<degree> uargs') : U" for e'
    using R tyh by (auto simp: inst_apps intro: list_app_typeI)
  show "wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> lvars [h \<degree>\<degree> uargs']) \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) [h \<degree>\<degree> uargs'] : Us0) \<and>
      (\<forall>t\<in>set [h \<degree>\<degree> uargs']. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) [h \<degree>\<degree> uargs'] [h \<degree>\<degree> uargs] \<and>
        dsolved \<rho> \<sigma> dps0)"
  proof (intro conjI allI impI)
    show "wt_env \<rho> env" "dtyped \<rho> dps" using R by blast+
    show "vinv \<rho> env (X \<union> dvars dps \<union> lvars [h \<degree>\<degree> uargs'])" using R by (simp add: vars_apps vh)
    show "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) [h \<degree>\<degree> uargs'] : Us0" for e'
      using tyc by (simp add: Us0)
    show "\<forall>t\<in>set [h \<degree>\<degree> uargs']. \<not> loose_bvar t (ilength Ts)"
      using R c by (auto simp: loose_bvar_apps closed_loose_bvar)
    fix \<sigma> assume sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> dps"
    note \<sigma> = solutionD(3)[OF sol]
    from R sol ds have l: "list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) uargs' uargs"
      and "dsolved \<rho> \<sigma> dps0" by auto
    then show "dsolved \<rho> \<sigma> dps0" by simp
    have tyw: "e \<turnstile> inst \<rho> (types_abs Ts (h \<degree>\<degree> uargs') \<degree>\<degree> targs) : U"
      by (rule typing_tabs_app[OF tyc tyt cert])
    note cw = conv_cpy[OF tyw \<sigma> len]
    have cp: "cpy targs (h \<degree>\<degree> uargs') = h \<degree>\<degree> map (cpy targs) uargs'" by (simp add: cpy_apps cpy_closed[OF c])
    have tyus': "pushes e (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) uargs' : Us" using R by blast
    have la: "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) (map (cpy targs) uargs')) (map (ap \<rho> \<sigma>) uargs)"
    proof (rule list_all2_all_nthI)
      show "length (map (ap \<rho> \<sigma>) (map (cpy targs) uargs')) = length (map (ap \<rho> \<sigma>) uargs)"
        using l by (simp add: list_all2_lengthD)
      fix i assume i: "i < length (map (ap \<rho> \<sigma>) (map (cpy targs) uargs'))"
      then have i': "i < length uargs'" "i < length Us" using typings_nth[OF tyus'] by simp_all
      have "e \<turnstile> inst \<rho> (types_abs Ts (uargs' ! i) \<degree>\<degree> targs) : Us ! i"
        using typings_nth[OF tyus'] i' by (intro typing_tabs_app[OF _ tyt cert]) simp
      from conv_cpy(1)[OF this \<sigma> len] list_all2_nthD[OF l i'(1)]
      have "ap \<rho> \<sigma> (cpy targs (uargs' ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (uargs ! i)"
        by (blast intro: conv_trans conv_sym)
      then show "map (ap \<rho> \<sigma>) (map (cpy targs) uargs') ! i \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> map (ap \<rho> \<sigma>) uargs ! i"
        using i' l by (simp add: list_all2_lengthD)
    qed
    have "ap \<rho> \<sigma> (cpy targs (h \<degree>\<degree> uargs')) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (h \<degree>\<degree> uargs)"
      unfolding cp ap_apps
    proof (rule conv_apps[OF la])
      show "wt (ap \<rho> \<sigma> h \<degree>\<degree> map (ap \<rho> \<sigma>) (map (cpy targs) uargs'))"
        using wt_ap[OF cw(2) \<sigma>] by (simp add: cp ap_apps)
      show "wt (ap \<rho> \<sigma> h \<degree>\<degree> map (ap \<rho> \<sigma>) uargs)"
        using wt_ap[OF tyu[folded inst_apps] \<sigma>] by (simp add: ap_apps)
    qed simp
    with cw(1) show "list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)
        [h \<degree>\<degree> uargs'] [h \<degree>\<degree> uargs]"
      by (auto intro: conv_trans)
  qed
qed

text \<open>The copy of an abstraction is the abstraction of the copy of its body:\<close>

lemma astep_abs:
  assumes a: "astep env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) (Ts @ [T]) [body] dps0 [b'] env dps"
  shows "astep env0 rb targs Ts [Abs a T body] dps0 [Abs a T b'] env dps"
proof (rule astepI)
  show "extends env0 env" by (fact astepD(1)[OF a])
  show "length [Abs a T b'] = length [Abs a T body]" by simp
  fix \<rho> env'' X e Us0
  assume tsol: "tsol (tyenv env'') \<rho>" and ext: "extends env env''" and wte: "wt_env \<rho> env0"
    and dt: "dtyped \<rho> dps0" and bs: "bs_env \<rho> e rb" and tys: "e \<tturnstile> map (inst \<rho>) [Abs a T body] : Us0"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    and lb: "\<forall>t\<in>set ([Abs a T body] @ targs). \<not> loose_bvar t (ilength rb)"
    and vi: "vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars ([Abs a T body] @ targs))"
  from tys obtain U where Us0: "Us0 = [U]" and tyu: "e \<turnstile> Abs a (tsubst \<rho> T) (inst \<rho> body) : U"
    by (auto split: list.splits)
  then obtain W where U: "U = tsubst \<rho> T \<rightarrow>\<^sub>T W" and cT: "cert_typ alg ar (tsubst \<rho> T)"
    and tyb: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> body : W"
    by auto
  define targs1 where "targs1 = map (\<lambda>t. lift t 0) targs @ [Bound 0]"
  have it: "map (incr_boundvars 1) targs = map (\<lambda>t. lift t 0) targs"
    by (simp add: incr_boundvars_def)
  note a' = a[unfolded it, folded targs1_def]
  have bs1: "bs_env \<rho> (e\<langle>0:tsubst \<rho> T\<rangle>) ((a, T) # rb)" by (rule bs_env_Cons[OF bs cT])
  have tyt1: "e\<langle>0:tsubst \<rho> T\<rangle> \<tturnstile> map (inst \<rho>) targs1 : map (tsubst \<rho>) (Ts @ [T])"
  proof -
    have "list_all2 (typing (e\<langle>0:tsubst \<rho> T\<rangle>)) (map (\<lambda>t. lift t 0) (map (inst \<rho>) targs)) (map (tsubst \<rho>) Ts)"
      using lift_types[OF tyt, of 0 "tsubst \<rho> T"] by (simp add: typings_iff)
    then show ?thesis by (auto simp: targs1_def typings_iff comp_def intro!: list_all2_appendI)
  qed
  have tyb1: "e\<langle>0:tsubst \<rho> T\<rangle> \<tturnstile> map (inst \<rho>) [body] : [W]" using tyb by simp
  have nn: "0 \<le> ilength rb" by simp
  have llt: "\<not> loose_bvar (lift t 0) (ilength rb + 1)" if "t \<in> set targs" for t
    using loose_bvar_lift[OF order_refl nn, of t] lb that by auto
  have b0: "\<not> ilength rb + 1 \<le> 0" using nn by (simp add: integer_arith)
  have lb1: "\<forall>t\<in>set ([body] @ targs1). \<not> loose_bvar t (ilength ((a, T) # rb))"
    using lb llt b0 by (auto simp: targs1_def)
  have vi1: "vinv \<rho> env0 (X \<union> dvars dps0 \<union> lvars ([body] @ targs1))"
    using vi by (simp add: targs1_def)
  note R = astepD(3)[OF a' tsol ext wte dt bs1 tyb1 tyt1 lb1 vi1]
  have len: "length Ts = length targs" using typings_nth[OF tyt] by simp
  have cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF bs tyt]) (use lb in auto)
  have tyc: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Abs a T b') : U" for e'
  proof -
    from R have "pushes e' (map (tsubst \<rho>) (Ts @ [T])) \<turnstile> inst \<rho> b' : W" by auto
    then have "(pushes e' (map (tsubst \<rho>) Ts))\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> b' : W" by (simp add: pushes_append)
    with cT show ?thesis by (auto simp: U)
  qed
  have lbb: "\<not> loose_bvar b' (ilength Ts + 1)" using R by auto
  show "wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> lvars [Abs a T b']) \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) [Abs a T b'] : Us0) \<and>
      (\<forall>t\<in>set [Abs a T b']. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) [Abs a T b'] [Abs a T body] \<and>
        dsolved \<rho> \<sigma> dps0)"
  proof (intro conjI allI impI)
    show "wt_env \<rho> env" "dtyped \<rho> dps" using R by blast+
    show "vinv \<rho> env (X \<union> dvars dps \<union> lvars [Abs a T b'])" using R by simp
    show "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) [Abs a T b'] : Us0" for e'
      using tyc by (simp add: Us0)
    show "\<forall>t\<in>set [Abs a T b']. \<not> loose_bvar t (ilength Ts)" using lbb by simp
    fix \<sigma> assume sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> dps"
    note \<sigma> = solutionD(3)[OF sol]
    from R sol ds have cb: "ap \<rho> \<sigma> (types_abs (Ts @ [T]) b' \<degree>\<degree> targs1) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body"
      and "dsolved \<rho> \<sigma> dps0" by auto
    then show "dsolved \<rho> \<sigma> dps0" by simp
    define W0 where "W0 = types_abs Ts (Abs a T b') \<degree>\<degree> targs"
    have ty0: "e \<turnstile> inst \<rho> W0 : U" unfolding W0_def by (rule typing_tabs_app[OF tyc tyt cert])
    have cl: "closed (types_abs Ts (Abs a T b'))" by (rule closed_types_abs) (use lbb in simp)
    have len1: "length (map (\<lambda>T. (STR '''', T)) Ts @ [(a, T)]) = length targs1" using len by (simp add: targs1_def)
    have "lift W0 0 $ Bound 0 = abs_list (map (\<lambda>T. (STR '''', T)) Ts @ [(a, T)]) b' \<degree>\<degree> targs1"
      using incr_bv_no_loose[OF closed_loose_bvar[OF cl order_refl]]
      by (simp add: W0_def incr_bv_apps targs1_def types_abs_abs_list)
    then have b1: "lift W0 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* cpy targs1 b'" using beta_cpy_abs_list[OF len1] by simp
    have b2: "types_abs (Ts @ [T]) b' \<degree>\<degree> targs1 \<rightarrow>\<^sub>\<beta>\<^sup>* cpy targs1 b'"
      by (rule beta_cpy) (use len in \<open>simp add: targs1_def\<close>)
    have tyl: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> (lift W0 0 $ Bound 0) : W"
      using typing.App[OF lift_type[OF ty0[unfolded U], of 0 "tsubst \<rho> T"] typing.Bound[of 0]] by simp
    have cert1: "\<forall>T'\<in>set (Ts @ [T]). cert_typ alg ar (tsubst \<rho> T')" using cert cT by simp
    have ty2: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> (types_abs (Ts @ [T]) b' \<degree>\<degree> targs1) : W"
      using R by (intro typing_tabs_app[OF _ tyt1 cert1]) auto
    have "ap \<rho> \<sigma> (lift W0 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (cpy targs1 b')"
      by (rule conv_beta_eta[OF wt_ap[OF tyl \<sigma>] beta_reds_ap[OF b1 \<sigma>]])
    also have "ap \<rho> \<sigma> (cpy targs1 b') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs (Ts @ [T]) b' \<degree>\<degree> targs1)"
      by (rule conv_sym, rule conv_beta_eta[OF wt_ap[OF ty2 \<sigma>] beta_reds_ap[OF b2 \<sigma>]])
    also note cb
    finally have c1: "ap \<rho> \<sigma> (lift W0 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body" .
    have apl: "ap \<rho> \<sigma> (lift W0 0 $ Bound 0) = lift (ap \<rho> \<sigma> W0) 0 $ Bound 0"
      using \<sigma> by (simp add: ap_lift)
    have "e \<turnstile> Abs a (tsubst \<rho> T) (lift (ap \<rho> \<sigma> W0) 0 $ Bound 0) : tsubst \<rho> T \<rightarrow>\<^sub>T W"
      using typing.Abs[OF cT typing_ap[OF tyl \<sigma>, unfolded apl]] .
    then have wa: "wt (Abs a (tsubst \<rho> T) (lift (ap \<rho> \<sigma> W0) 0 $ Bound 0))" by (auto simp: wt_def)
    have wb: "wt (Abs a (tsubst \<rho> T) (ap \<rho> \<sigma> body))"
      using typing_vsubst[OF tyu \<sigma>] by (auto simp: wt_def ap_def)
    have "ap \<rho> \<sigma> W0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> T) (lift (ap \<rho> \<sigma> W0) 0 $ Bound 0)"
      by (rule conv_sym, rule conv_eta_lift[OF wa])
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> T) (ap \<rho> \<sigma> body)"
      by (rule conv_Abs[OF wa wb]) (use c1 apl in simp)
    finally show "list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)
        [Abs a T b'] [Abs a T body]"
      by (simp add: W0_def)
  qed
qed

subsection \<open>New variables\<close>

text \<open>\<^const>\<open>genvars\<close> creates distinct names: \<^const>\<open>radixstring\<close> is injective (as in session
  \<open>Pure_Unify_Correctness\<close>).\<close>

lemma radix26_append: "radix26 n ds = radix26 n [] @ ds"
proof (induction n arbitrary: ds rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have "n div 26 < n" by simp
    from less.IH[OF this, of "(n mod 26) # ds"] less.IH[OF this, of "[n mod 26]"] False show ?thesis
      by (subst (1 2) radix26.simps) simp
  qed (subst (1 2) radix26.simps; simp)
qed

lemma radix26_step: "\<not> n < 26 \<Longrightarrow> radix26 n [] = radix26 (n div 26) [] @ [n mod 26]"
  by (subst radix26.simps) (simp add: radix26_append[of "n div 26" "[n mod 26]"])

lemma radix26_small: "n < 26 \<Longrightarrow> radix26 n [] = [n]"
  by (subst radix26.simps) simp

lemma radix26_digits: "d \<in> set (radix26 n []) \<Longrightarrow> d < 26"
proof (induction n arbitrary: d rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have lt: "n div 26 < n" by simp
    have "d \<in> set (radix26 (n div 26) []) \<or> d = n mod 26" using less.prems False by (auto simp: radix26_step)
    then show ?thesis using less.IH[OF lt] by auto
  qed (use less in \<open>simp add: radix26_small\<close>)
qed

lemma radix26_val: "foldl (\<lambda>a d. a * 26 + d) 0 (radix26 n []) = n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have "n div 26 < n" by simp
    with less False show ?thesis by (simp add: radix26_step)
  qed (simp add: radix26_small)
qed

lemma radix26_inj: "radix26 n [] = radix26 m [] \<Longrightarrow> n = m"
  by (metis radix26_val)

lemma radix26_nonempty: "radix26 n [] \<noteq> []"
  by (cases "n < 26") (simp_all add: radix26_step radix26_small)

lemma radix_char_inj:
  fixes d d' :: nat
  assumes "d < 26" "d' < 26" "String.ascii_of (char_of (97 + d)) = String.ascii_of (char_of (97 + d'))"
  shows "d = d'"
proof -
  have "of_char (String.ascii_of (char_of (97 + x))) = (97 + x :: nat)" if "x < 26" for x :: nat
    using that by (simp add: String.ascii_of_char_of of_char_of take_bit_eq_mod)
  from this[OF assms(1)] this[OF assms(2)] assms(3) show ?thesis by simp
qed

lemma radixstring_inj:
  assumes "0 \<le> n" "0 \<le> m" "radixstring n = radixstring m"
  shows "n = m"
proof -
  let ?f = "\<lambda>d::nat. String.ascii_of (char_of (97 + d))"
  from assms(3) have "String.explode (radixstring n) = String.explode (radixstring m)" by simp
  then have eq: "map ?f (radix26 (nat_of_integer n) []) = map ?f (radix26 (nat_of_integer m) [])"
    unfolding radixstring_def by (simp add: String.explode_implode_eq comp_def)
  have "inj_on ?f {d. d < 26}" by (auto intro!: inj_onI radix_char_inj)
  moreover have "set (radix26 (nat_of_integer n) []) \<union> set (radix26 (nat_of_integer m) []) \<subseteq> {d. d < 26}"
    using radix26_digits by blast
  ultimately have "inj_on ?f (set (radix26 (nat_of_integer n) []) \<union> set (radix26 (nat_of_integer m) []))"
    by (rule inj_on_subset)
  with eq have "radix26 (nat_of_integer n) [] = radix26 (nat_of_integer m) []"
    by (simp add: inj_on_map_eq_map)
  then have "nat_of_integer n = nat_of_integer m" by (rule radix26_inj)
  with assms(1,2) show ?thesis by (simp add: integer_eq_iff nat_of_integer.rep_eq less_eq_integer.rep_eq eq_nat_nat_iff)
qed

lemma radixstring_nonempty: "radixstring n \<noteq> STR ''''"
proof
  assume "radixstring n = STR ''''"
  then have "String.explode (radixstring n) = []" by (simp add: String.zero_literal.rep_eq)
  then show False unfolding radixstring_def using radix26_nonempty by (simp add: String.explode_implode_eq)
qed

lemma plus_literal_cancel: "(a :: String.literal) + b = a + c \<longleftrightarrow> b = c"
  by (metis String.plus_literal.rep_eq literal.explode_inject same_append_eq)

lemma plus_literal_neq: "b \<noteq> STR '''' \<Longrightarrow> (a :: String.literal) + b \<noteq> a"
  by (metis String.plus_literal.rep_eq literal.explode_inject append_self_conv zero_literal.rep_eq
      String.zero_literal_def)

fun var_of :: "pterm \<Rightarrow> indexname" where
  "var_of (Var x T) = x"
| "var_of _ = undefined"

lemma genvs_names:
  "0 \<le> n \<Longrightarrow> v \<in> set (genvs name i n Ts) \<Longrightarrow>
    \<exists>T. v = Var (name, i) T \<or> (\<exists>k\<ge>n. v = Var (name + radixstring k, i) T)"
proof (induction name i n Ts rule: genvs.induct)
  case (3 name i n T v va)
  then show ?case by (fastforce dest: order_trans[of n "n + 1", rotated])
qed auto

lemma genvs_distinct: "0 \<le> n \<Longrightarrow> distinct (map var_of (genvs name i n Ts))"
proof (induction name i n Ts rule: genvs.induct)
  case (3 name i n T v va)
  have "(name + radixstring n, i) \<notin> var_of ` set (genvs name i (n + 1) (v # va))"
  proof
    assume "(name + radixstring n, i) \<in> var_of ` set (genvs name i (n + 1) (v # va))"
    then obtain w where w: "w \<in> set (genvs name i (n + 1) (v # va))" "var_of w = (name + radixstring n, i)"
      by (auto simp: image_iff)
    from genvs_names[OF _ w(1)] "3.prems" obtain U where
      "w = Var (name, i) U \<or> (\<exists>k\<ge>n + 1. w = Var (name + radixstring k, i) U)" by fastforce
    then show False
    proof (elim disjE exE conjE)
      assume "w = Var (name, i) U"
      with w(2) plus_literal_neq[OF radixstring_nonempty, of name n] show False by simp
    next
      fix k assume "n + 1 \<le> k" "w = Var (name + radixstring k, i) U"
      with w(2) "3.prems" radixstring_inj[of k n] show False by (auto simp: plus_literal_cancel)
    qed
  qed
  with "3.IH" "3.prems" show ?case by simp
qed auto

lemma genvs_vars: "list_all2 (\<lambda>v T. \<exists>a. v = Var (a, i) T) (genvs name i n Ts) Ts"
  by (induction name i n Ts rule: genvs.induct) auto

lemma genvars_props:
  assumes "genvars name env Ts = (env', vs)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env' = maxidx env + 1"
    "list_all2 (\<lambda>v T. \<exists>a. v = Var (a, maxidx env + 1) T) vs Ts" "distinct (map var_of vs)"
  using assms genvs_vars genvs_distinct[of 0] by (auto simp: genvars_def split: env.splits)

lemma vinv_genvars:
  assumes g: "genvars name env Ts = (env', vs)" and vi: "vinv \<rho> env X"
  shows "vinv \<rho> env' (lvars vs \<union> X)"
proof -
  note g' = genvars_props[OF g]
  have ev: "evars env' = evars env" by (simp add: evars_def bnds_def g'(1))
  have b: "below (maxidx env) (X \<union> evars env)" and c: "vcons \<rho> (X \<union> evars env)"
    using vi by (simp_all add: vinv_def)
  have new: "\<exists>k < length vs. vs ! k = Var x W \<and> snd x = maxidx env + 1" if "(x, W) \<in> lvars vs" for x W
  proof -
    from that obtain v where v: "v \<in> set vs" "(x, W) \<in> vars v" by blast
    then obtain k where k: "k < length vs" "vs ! k = v" by (auto simp: in_set_conv_nth)
    from g'(4) k obtain a where "v = Var (a, maxidx env + 1) (Ts ! k)" by (auto dest: list_all2_nthD)
    with v k show ?thesis by auto
  qed
  have le: "maxidx env \<le> maxidx env'" using g' by (simp add: integer_arith)
  have "below (maxidx env') (lvars vs \<union> X \<union> evars env')"
    using below_mono[OF b _ le] g'(3) ev new by (fastforce simp: below_def)
  moreover have "vcons \<rho> (lvars vs \<union> X \<union> evars env')"
    unfolding vcons_def
  proof (intro allI impI)
    fix x U V assume U: "(x, U) \<in> lvars vs \<union> X \<union> evars env'" and V: "(x, V) \<in> lvars vs \<union> X \<union> evars env'"
    have old: "snd x \<le> maxidx env" if "(x, W) \<in> X \<union> evars env" for W
      using belowD[OF b that] .
    have clash: False if "(x, W) \<in> lvars vs" "(x, W') \<in> X \<union> evars env" for W W'
      using new[OF that(1)] old[OF that(2)] by (auto simp: integer_arith)
    have both: "U = V" if "(x, U) \<in> lvars vs" "(x, V) \<in> lvars vs"
    proof -
      from new[OF that(1)] new[OF that(2)] obtain k l where
        k: "k < length vs" "vs ! k = Var x U" and l: "l < length vs" "vs ! l = Var x V" by blast
      have "map var_of vs ! k = map var_of vs ! l" using k l by simp
      then have "k = l" using nth_eq_iff_index_eq[OF g'(5), of k l] k(1) l(1) by simp
      with k l show ?thesis by simp
    qed
    have U': "(x, U) \<in> lvars vs \<or> (x, U) \<in> X \<union> evars env" and V': "(x, V) \<in> lvars vs \<or> (x, V) \<in> X \<union> evars env"
      using U V ev by blast+
    show "tsubst \<rho> U = tsubst \<rho> V"
    proof (cases "(x, U) \<in> lvars vs")
      case True
      show ?thesis
      proof (cases "(x, V) \<in> lvars vs")
        case True
        with \<open>(x, U) \<in> lvars vs\<close> show ?thesis using both by simp
      next
        case False
        with V' have "(x, V) \<in> X \<union> evars env" by simp
        from clash[OF True this] show ?thesis ..
      qed
    next
      case False
      with U' have u: "(x, U) \<in> X \<union> evars env" by simp
      show ?thesis
      proof (cases "(x, V) \<in> lvars vs")
        case True
        from clash[OF True u] show ?thesis ..
      next
        case False
        with V' have "(x, V) \<in> X \<union> evars env" by simp
        from vconsD[OF c u this] show ?thesis .
      qed
    qed
  qed
  ultimately show ?thesis by (simp add: vinv_def ev)
qed

text \<open>The new arguments of a projection or an imitation:\<close>

lemma make_args_props:
  assumes "make_args name Ts env Us = (env', args)"
  obtains Gs where "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<And>\<rho> X. vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' (lvars Gs \<union> X)"
proof (cases "Us = []")
  case True
  with assms have "env' = env" "args = []" by (simp_all add: make_args_def)
  with True show ?thesis by (intro that[of "[]"]) simp_all
next
  case False
  obtain env1 vs where g: "genvars name env (map (\<lambda>T. Ts \<Rrightarrow> T) Us) = (env1, vs)" by fastforce
  with assms False have e: "env' = env1" "args = map (\<lambda>var. combound var 0 (length Ts)) vs"
    by (auto simp: make_args_def List.null_iff)
  note g' = genvars_props[OF g]
  show ?thesis
  proof (rule that[of vs])
    show "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) vs" by (simp add: e combound_bvs)
    show "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) vs Us"
      using g'(4) by (fastforce simp: list_all2_conv_all_nth)
    show "tenv env' = tenv env" "tyenv env' = tyenv env" using g' e by simp_all
    show "maxidx env \<le> maxidx env'" using g' e by (simp add: integer_arith)
    show "vinv \<rho> env' (lvars vs \<union> X)" if "vinv \<rho> env X" for \<rho> X
      using vinv_genvars[OF g that] e by simp
  qed
qed

lemma extends_tenv_eq: "tenv env' = tenv env \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> maxidx env \<le> maxidx env' \<Longrightarrow>
    extends env env'"
  by (simp add: extends_def)

lemma head_of_apps: "head_of (s \<degree>\<degree> ts) = head_of s"
  by (induction ts arbitrary: s) simp_all

lemma inst_bvs [simp]: "map (inst \<rho>) (bvs n) = bvs n"
  by simp

lemma vars_bvs [simp]: "lvars (bvs n) = {}"
  by auto

lemma loose_bvar_bvs_ilength: "length Ts = n \<Longrightarrow> \<forall>t\<in>set (bvs n). \<not> loose_bvar t (ilength Ts)"
  by (auto simp: ilength_eq integer_of_nat_eq_of_nat)

lemma cpy_new_arg: "closed G \<Longrightarrow> cpy ts (G \<degree>\<degree> bvs (length ts)) = G \<degree>\<degree> ts"
  by (simp only: cpy_apps cpy_closed map_cpy_bvs)

text \<open>A new variable applied to the arguments, with a new pair for the copied term:\<close>

lemma astep_newflex:
  assumes g: "genvar a env (Ts' \<Rrightarrow> A) = (env', newhd)" and l: "length Ts' = length targs"
    and ty: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> tyok ot \<rho> e [U] \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts \<and> tsubst \<rho> A = U"
  shows "astepo ot env rb targs Ts [u] dps [combound newhd 0 (length Ts')] env' ((rb, newhd \<degree>\<degree> targs, u) # dps)"
proof (rule astepoI)
  show ext0: "extends env env'" by (rule extends_genvar[OF g])
  show "length [combound newhd 0 (length Ts')] = length [u]" by simp
  fix \<rho> env'' X e Us0
  assume tsol: "tsol (tyenv env'') \<rho>" and ext: "extends env' env''" and wte: "wt_env \<rho> env"
    and dt: "dtyped \<rho> dps" and bs: "bs_env \<rho> e rb" and tyo: "tyok ot \<rho> e Us0"
    and tys: "e \<tturnstile> map (inst \<rho>) [u] : Us0"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    and lb: "\<forall>t\<in>set ([u] @ targs). \<not> loose_bvar t (ilength rb)"
    and vi: "vinv \<rho> env (X \<union> dvars dps \<union> lvars ([u] @ targs))"
  from tys obtain U where Us0: "Us0 = [U]" and tyu: "e \<turnstile> inst \<rho> u : U" by (auto split: list.splits)
  have tsol1: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol extends_trans[OF ext0 ext]])
  from ty[OF tsol1 bs tyo[unfolded Us0] tyu tyt] have ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts" and A: "tsubst \<rho> A = U"
    by blast+
  note g' = genvar_simps[OF g]
  have len: "length Ts = length targs" using typings_nth[OF tyt] by simp
  have cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF bs tyt]) (use lb in auto)
  have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu]) (use lb in simp)
  have tyN: "tsubst \<rho> (Ts' \<Rrightarrow> A) = map (tsubst \<rho>) Ts \<Rrightarrow> U" by (simp add: tsubst_funs ts A)
  have tynew: "e' \<turnstile> inst \<rho> newhd : map (tsubst \<rho>) Ts \<Rrightarrow> U" for e'
    using cert cU by (auto simp: g'(4) tyN cert_typ_funs)
  have n: "length Ts' = length Ts" using l len by simp
  show "wt_env \<rho> env' \<and> dtyped \<rho> ((rb, newhd \<degree>\<degree> targs, u) # dps) \<and>
      vinv \<rho> env' (X \<union> dvars ((rb, newhd \<degree>\<degree> targs, u) # dps) \<union> lvars [combound newhd 0 (length Ts')]) \<and>
      (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) [combound newhd 0 (length Ts')] : Us0) \<and>
      (\<forall>t\<in>set [combound newhd 0 (length Ts')]. \<not> loose_bvar t (ilength Ts)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> ((rb, newhd \<degree>\<degree> targs, u) # dps) \<longrightarrow>
        list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) [combound newhd 0 (length Ts')] [u] \<and>
        dsolved \<rho> \<sigma> dps)"
  proof (intro conjI allI impI)
    show "wt_env \<rho> env'" using wte by (simp add: wt_env_genvar[OF g])
    have "e \<turnstile> inst \<rho> (newhd \<degree>\<degree> targs) : U" using list_app_typeI[OF tynew tyt] by (simp add: inst_apps)
    then show "dtyped \<rho> ((rb, newhd \<degree>\<degree> targs, u) # dps)"
      using dt bs tyu lb by (auto simp: g'(4) loose_bvar_apps)
    have "vinv \<rho> env' (vars newhd \<union> (X \<union> dvars dps \<union> lvars ([u] @ targs)))" by (rule vinv_genvar[OF g vi])
    then show "vinv \<rho> env' (X \<union> dvars ((rb, newhd \<degree>\<degree> targs, u) # dps) \<union> lvars [combound newhd 0 (length Ts')])"
      by (rule vinv_mono) (auto simp: vars_apps combound_bvs)
    have cb: "combound newhd 0 (length Ts') = newhd \<degree>\<degree> bvs (length (map (tsubst \<rho>) Ts))"
      using n by (simp add: combound_bvs)
    have tyc: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (combound newhd 0 (length Ts')) : U" for e'
      using list_app_typeI[OF tynew typings_bvs[of e' "map (tsubst \<rho>) Ts"]]
      by (simp only: cb inst_apps inst_bvs)
    then show "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) [combound newhd 0 (length Ts')] : Us0" for e'
      by (simp add: Us0)
    show "\<forall>t\<in>set [combound newhd 0 (length Ts')]. \<not> loose_bvar t (ilength Ts)"
      unfolding cb using loose_bvar_bvs_ilength[of "map (tsubst \<rho>) Ts", OF refl] by (simp add: loose_bvar_apps g'(4))
    fix \<sigma> assume sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> ((rb, newhd \<degree>\<degree> targs, u) # dps)"
    note \<sigma> = solutionD(3)[OF sol]
    from ds show "dsolved \<rho> \<sigma> dps" by simp
    have tyw: "e \<turnstile> inst \<rho> (types_abs Ts (combound newhd 0 (length Ts')) \<degree>\<degree> targs) : U"
      by (rule typing_tabs_app[OF tyc tyt cert])
    have "cpy targs (combound newhd 0 (length Ts')) = newhd \<degree>\<degree> targs"
      using cpy_new_arg[of newhd targs] l by (simp add: combound_bvs g'(4) closed_def)
    with conv_cpy(1)[OF tyw \<sigma> len] ds
    show "list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) [combound newhd 0 (length Ts')] [u]"
      by (auto intro: conv_trans)
  qed
qed

text \<open>A projection: the bound variable of the argument applied to new arguments.\<close>

lemma astep_proj:
  assumes po: "proj_ok env rb targs Ts u env' Ts' Us head targ ot"
    and ma: "make_args vname Ts' env' Us = (env1, args)"
    and S: "okW (SIMPL alg' env1 ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (env2, ffs, frs)"
  shows "astepo ot env rb targs Ts [u] dps [list_comb head args] env2 (ffs @ frs)"
proof -
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us"
    and ma': "tenv env1 = tenv env'" "tyenv env1 = tyenv env'" "maxidx env' \<le> maxidx env1"
    and viG: "\<And>\<rho> X. vinv \<rho> env' X \<Longrightarrow> vinv \<rho> env1 (lvars Gs \<union> X)"
    by (rule make_args_props[OF ma]) blast
  have GVar: "\<exists>x U. G = Var x U" if "G \<in> set Gs" for G
  proof -
    from that obtain k where k: "k < length Gs" "G = Gs ! k" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF Gs k(1)] k(2) show ?thesis by blast
  qed
  have hdG: "head_of G = G" if "G \<in> set Gs" for G using GVar[OF that] by auto
  have clG: "closed G" if "G \<in> set Gs" for G using GVar[OF that] by (auto simp: closed_def)
  have hd: "map (\<lambda>arg. list_comb (head_of arg) targs) args = map (\<lambda>G. G \<degree>\<degree> targs) Gs"
    by (auto simp: args list_comb_apps head_of_apps hdG)
  define dp where "dp = (rb, targ \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs, u)"
  have dst: "dstep env1 (dp # dps) env2 (ffs @ frs)"
    by (rule dstep_set[OF SIMPL_sound[OF S[unfolded hd, unfolded list_comb_apps, folded dp_def]]]) auto
  from po obtain j where ext0: "extends env env'" and tenv0: "tenv env' = tenv env" and l: "length Ts' = length targs"
    and hj: "head = Bound j" "0 \<le> j" "j < ilength targs" "targ = targs ! (length targs - 1 - nat_of_integer j)"
    and sem: "\<And>\<rho> e U. tsol (tyenv env') \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      tyok ot \<rho> e [U] \<Longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow>
      \<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb) \<Longrightarrow>
      map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts \<and> e \<turnstile> inst \<rho> targ : map (tsubst \<rho>) Us \<Rrightarrow> U"
    unfolding proj_ok_def by blast
  have ext1: "extends env' env1" by (rule extends_tenv_eq[OF ma'])
  have ext2: "extends env1 env2" by (rule dstepD(1)[OF dst])
  show ?thesis
  proof (rule astepoI)
    show "extends env env2" using extends_trans[OF ext0 extends_trans[OF ext1 ext2]] .
    show "length [list_comb head args] = length [u]" by simp
    fix \<rho> env'' X e Us0
    assume tsol: "tsol (tyenv env'') \<rho>" and ext: "extends env2 env''" and wte: "wt_env \<rho> env"
      and dt: "dtyped \<rho> dps" and bs: "bs_env \<rho> e rb" and tyo: "tyok ot \<rho> e Us0"
      and tys: "e \<tturnstile> map (inst \<rho>) [u] : Us0"
      and tyt: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
      and lb: "\<forall>t\<in>set ([u] @ targs). \<not> loose_bvar t (ilength rb)"
      and vi: "vinv \<rho> env (X \<union> dvars dps \<union> lvars ([u] @ targs))"
    from tys obtain U where Us0: "Us0 = [U]" and tyu: "e \<turnstile> inst \<rho> u : U" by (auto split: list.splits)
    have tsol1: "tsol (tyenv env') \<rho>" by (rule extends_tsol[OF tsol extends_trans[OF ext1 extends_trans[OF ext2 ext]]])
    have lbu: "\<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb)" using lb by simp
    from sem[OF tsol1 bs tyu tyo[unfolded Us0] tyt lbu] have ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
      and tyg: "e \<turnstile> inst \<rho> targ : map (tsubst \<rho>) Us \<Rrightarrow> U" by blast+
    have len: "length Ts = length targs" using typings_nth[OF tyt] by simp
    have n: "length Ts' = length Ts" using l len by simp
    have cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF bs tyt]) (use lb in auto)
    define i where "i = length targs - 1 - nat_of_integer j"
    have jl: "nat_of_integer j < length targs" using hj(2,3) nat_of_integer_less_ilength by blast
    then have i: "i < length targs" by (simp add: i_def)
    have targ_in: "targ \<in> set targs" using hj(4) i by (simp add: i_def)
    have ltarg: "\<not> loose_bvar targ (ilength rb)" using lb targ_in by simp
    have cUs: "\<forall>U'\<in>set Us. cert_typ alg ar (tsubst \<rho> U')"
      using bs_env_cert[OF bs tyg ltarg] by (simp add: cert_typ_funs)
    have tyG: "e' \<turnstile> inst \<rho> G : map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> U'" if "\<exists>x. G = Var x (Ts' \<Rrightarrow> U')" "U' \<in> set Us"
      for e' G U'
      using that cert cUs by (auto simp: tsubst_funs ts cert_typ_funs)
    have lGs: "length Gs = length Us" by (rule list_all2_lengthD[OF Gs])
    have tyGk: "e' \<turnstile> inst \<rho> (Gs ! k) : map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> (Us ! k)" if "k < length Gs" for e' k
      by (rule tyG[OF list_all2_nthD[OF Gs that]]) (use that lGs in simp)
    have tyGs: "e \<tturnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> targs) Gs) : map (tsubst \<rho>) Us"
      unfolding typings_iff
    proof (rule list_all2_all_nthI)
      fix k assume "k < length (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> targs) Gs))"
      then have k: "k < length Gs" by simp
      from list_app_typeI[OF tyGk[OF k] tyt] k lGs
      show "e \<turnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> targs) Gs) ! k : map (tsubst \<rho>) Us ! k"
        by (simp add: inst_apps)
    qed (simp add: lGs)
    show "wt_env \<rho> env2 \<and> dtyped \<rho> (ffs @ frs) \<and> vinv \<rho> env2 (X \<union> dvars (ffs @ frs) \<union> lvars [list_comb head args]) \<and>
        (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) [list_comb head args] : Us0) \<and>
        (\<forall>t\<in>set [list_comb head args]. \<not> loose_bvar t (ilength Ts)) \<and>
        (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> (ffs @ frs) \<longrightarrow>
          list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) [list_comb head args] [u] \<and>
          dsolved \<rho> \<sigma> dps)"
    proof (intro conjI allI impI)
      have wte1: "wt_env \<rho> env1" using wt_env_tenv[of env1 env \<rho>] ma'(1) tenv0 wte by simp
      have "e \<turnstile> inst \<rho> (targ \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) : U"
        using list_app_typeI[OF tyg tyGs] by (simp add: inst_apps)
      then have dt1: "dtyped \<rho> (dp # dps)"
        using dt bs tyu lb ltarg clG by (auto simp: dp_def loose_bvar_apps closed_loose_bvar)
      have "vinv \<rho> env' (X \<union> dvars dps \<union> lvars ([u] @ targs))" by (rule vinv_tenv[OF tenv0 ext0 vi])
      then have "vinv \<rho> env1 (lvars Gs \<union> (X \<union> dvars dps \<union> lvars ([u] @ targs)))" by (rule viG)
      then have vi1: "vinv \<rho> env1 ((X \<union> lvars Gs) \<union> dvars (dp # dps))"
        by (rule vinv_mono) (use targ_in in \<open>auto simp: dp_def vars_apps\<close>)
      note R = dstepD(2)[OF dst tsol ext wte1 dt1 vi1]
      show "wt_env \<rho> env2" "dtyped \<rho> (ffs @ frs)" using R by blast+
      have va: "vars (list_comb head args) = lvars Gs" by (auto simp: list_comb_apps hj(1) args vars_apps)
      show "vinv \<rho> env2 (X \<union> dvars (ffs @ frs) \<union> lvars [list_comb head args])"
        using R by (simp add: va Un_ac)
      have jT: "pushes e' (map (tsubst \<rho>) Ts) j = map (tsubst \<rho>) Us \<Rrightarrow> U" for e'
      proof -
        have "j < ilength (map (tsubst \<rho>) Ts)" using hj(3) len by (simp add: ilength_eq)
        then have "pushes e' (map (tsubst \<rho>) Ts) j = rev (map (tsubst \<rho>) Ts) ! nat_of_integer j"
          using hj(2) by (simp add: pushes_nth)
        also have "\<dots> = tsubst \<rho> (Ts ! i)" using jl len by (simp add: rev_nth i_def)
        also have "\<dots> = map (tsubst \<rho>) Us \<Rrightarrow> U"
        proof -
          have "e \<turnstile> inst \<rho> (targs ! i) : tsubst \<rho> (Ts ! i)" using typings_nth[OF tyt] i len by simp
          with tyg hj(4) show ?thesis by (simp add: i_def typing_unique)
        qed
        finally show ?thesis .
      qed
      have tyargs: "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) args : map (tsubst \<rho>) Us" for e'
        unfolding typings_iff
      proof (rule list_all2_all_nthI)
        fix k assume "k < length (map (inst \<rho>) args)"
        then have k: "k < length Gs" by (simp add: args)
        have "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Gs ! k) \<degree>\<degree> bvs (length (map (tsubst \<rho>) Ts)) : tsubst \<rho> (Us ! k)"
          by (rule list_app_typeI[OF tyGk[OF k] typings_bvs])
        then show "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> map (inst \<rho>) args ! k : map (tsubst \<rho>) Us ! k"
          using k lGs n by (simp add: args inst_apps comp_def)
      qed (simp add: args lGs)
      have tyc: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb head args) : U" for e'
        using list_app_typeI[OF typing.Bound[where e="pushes e' (map (tsubst \<rho>) Ts)", OF hj(2) jT] tyargs[of e']]
        by (simp add: list_comb_apps inst_apps hj(1))
      show "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) [list_comb head args] : Us0" for e'
        using tyc by (simp add: Us0)
      have il: "ilength Ts = ilength targs" using len by (simp add: ilength_eq)
      have lbB: "\<not> loose_bvar (Bound j) (ilength Ts)" using hj(3) il by simp
      have lba: "\<not> loose_bvar a (ilength Ts)" if "a \<in> set args" for a
      proof -
        from that obtain G where G: "G \<in> set Gs" "a = G \<degree>\<degree> bvs (length Ts')" by (auto simp: args)
        then show ?thesis using clG[OF G(1)] loose_bvar_bvs_ilength[OF n[symmetric]]
          by (auto simp: loose_bvar_apps closed_loose_bvar)
      qed
      show "\<forall>t\<in>set [list_comb head args]. \<not> loose_bvar t (ilength Ts)"
        using lbB lba by (simp add: list_comb_apps loose_bvar_apps hj(1))
      fix \<sigma> assume sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> (ffs @ frs)"
      note \<sigma> = solutionD(3)[OF sol]
      have ds1: "dsolved \<rho> \<sigma> (dp # dps)" using R[THEN conjunct2, THEN conjunct2, THEN conjunct2] sol ds by blast
      then show "dsolved \<rho> \<sigma> dps" by (simp add: dp_def)
      have tyw: "e \<turnstile> inst \<rho> (types_abs Ts (list_comb head args) \<degree>\<degree> targs) : U"
        by (rule typing_tabs_app[OF tyc tyt cert])
      have cG: "cpy targs (G \<degree>\<degree> bvs (length Ts')) = G \<degree>\<degree> targs" if "G \<in> set Gs" for G
        by (simp only: l cpy_new_arg[OF clG[OF that]])
      have ma2: "map (cpy targs) args = map (\<lambda>G. G \<degree>\<degree> targs) Gs" using cG by (simp add: args)
      have "cpy targs (list_comb head args) = targ \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs"
        by (simp only: list_comb_apps hj(1) cpy_apps ma2 cpy_Bound[OF hj(2,3)] hj(4))
      with conv_cpy(1)[OF tyw \<sigma> len] ds1
      show "list_all2 (\<lambda>u' u. ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) [list_comb head args] [u]"
        by (auto simp: dp_def intro: conv_trans)
    qed
  qed
qed

subsection \<open>Binding the variable to the abstraction of a copy\<close>

lemma typings_unique: "e \<tturnstile> ts : Ts \<Longrightarrow> e \<tturnstile> ts : Us \<Longrightarrow> Ts = Us"
  by (induction ts arbitrary: Ts Us) (auto split: list.splits dest: typing_unique)

lemma copy_bind_conv:
  assumes "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u')"
    "ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    "wt (ap \<rho> \<sigma> (Var v T \<degree>\<degree> targs))" "wt (ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs))"
  shows "ap \<rho> \<sigma> (Var v T \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
proof -
  have "ap \<rho> \<sigma> (Var v T \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs)"
    unfolding ap_apps
    by (rule conv_apps) (use assms in \<open>simp_all add: ap_apps list_all2_refl\<close>)
  from conv_trans[OF this assms(2)] show ?thesis .
qed

text \<open>
  The step of \<open>new_dset\<close>: a pair with the flexible side \<open>?v targs\<close> is solved by a copy of its
  other side, whatever way the binding of \<open>?v\<close> to the abstraction of the copy is recorded.
\<close>

lemma dstep_copy_bind:
  assumes st: "strip_comb t = (Var v T, targs)" and ta: "targs_ok env1 rb t targs Ts"
    and el: "astepo (Some t) env1 rb targs Ts [u] dps1 [u'] env' dps'" and ext: "extends env' envY"
    and bind: "\<And>\<rho> env'' X. tsol (tyenv env'') \<rho> \<Longrightarrow> extends envY env'' \<Longrightarrow> wt_env \<rho> env' \<Longrightarrow>
      dtyped \<rho> (dps' @ others) \<Longrightarrow>
      (\<And>e. e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T) \<Longrightarrow> closed (types_abs Ts u') \<Longrightarrow>
      vinv \<rho> env' (X \<union> insert (v, T) (dvars (dps' @ others) \<union> vars u')) \<Longrightarrow>
      wt_env \<rho> envY \<and> dtyped \<rho> dpsY \<and> vinv \<rho> envY (X \<union> dvars dpsY) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dpsY \<longrightarrow>
        dsolved \<rho> \<sigma> (dps' @ others) \<and> \<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u'))"
  shows "dstep env1 ((rb, t, u) # dps1 @ others) envY dpsY"
proof (rule dstepI)
  have e1: "extends env1 env'" by (rule astepoD(1)[OF el])
  show "extends env1 envY" by (rule extends_trans[OF e1 ext])
  fix \<rho> env'' X assume tsol: "tsol (tyenv env'') \<rho>" and extY: "extends envY env''" and wte: "wt_env \<rho> env1"
    and dt: "dtyped \<rho> ((rb, t, u) # dps1 @ others)" and vi: "vinv \<rho> env1 (X \<union> dvars ((rb, t, u) # dps1 @ others))"
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  from dt obtain e U where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : U" and tyu: "e \<turnstile> inst \<rho> u : U"
    and lbt: "\<not> loose_bvar t (ilength rb)" and lbu: "\<not> loose_bvar u (ilength rb)" and dt1: "dtyped \<rho> dps1"
    and dto: "dtyped \<rho> others"
    by (auto simp: dtyped_def)
  have ext': "extends env' env''" by (rule extends_trans[OF ext extY])
  have tsol1: "tsol (tyenv env1) \<rho>" by (rule extends_tsol[OF tsol extends_trans[OF e1 ext']])
  have tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" using ta tsol1 bs tyt by (auto simp: targs_ok_def)
  from tyt[unfolded t inst_apps] obtain Us where tyv: "e \<turnstile> inst \<rho> (Var v T) : Us \<Rrightarrow> U"
    and tyas: "e \<tturnstile> map (inst \<rho>) targs : Us"
    by (rule list_app_typeE)
  have Us: "Us = map (tsubst \<rho>) Ts" by (rule typings_unique[OF tyas tya])
  from tyv have T: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> U" by (auto simp: Us)
  have lba: "\<forall>t\<in>set ([u] @ targs). \<not> loose_bvar t (ilength rb)" using lbt lbu by (auto simp: t loose_bvar_apps)
  have vi1: "vinv \<rho> env1 ((X \<union> dvars others \<union> {(v, T)}) \<union> dvars dps1 \<union> lvars ([u] @ targs))"
    using vi by (rule vinv_mono) (auto simp: t vars_apps)
  have tyu1: "e \<tturnstile> map (inst \<rho>) [u] : [U]" using tyu by simp
  have tyo: "tyok (Some t) \<rho> e [U]" using tyt by simp
  note R = astepoD(3)[OF el tsol ext' wte dt1 bs tyo tyu1 tya lba vi1]
  have cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF bs tya]) (use lba in auto)
  have tyc: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> u' : U" for e' using R by auto
  have tyb: "e' \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T" for e'
    using typing_types_abs[OF tyc] cert by (simp add: inst_types_abs T)
  have cl: "closed (types_abs Ts u')" by (rule closed_types_abs) (use R in auto)
  have vi2: "vinv \<rho> env' (X \<union> insert (v, T) (dvars (dps' @ others) \<union> vars u'))" using R by (simp add: Un_ac)
  have dt2: "dtyped \<rho> (dps' @ others)" using R dto by (simp add: dtyped_def ball_Un)
  note B = bind[OF tsol extY R[THEN conjunct1] dt2 tyb cl vi2]
  show "wt_env \<rho> envY \<and> dtyped \<rho> dpsY \<and> vinv \<rho> envY (X \<union> dvars dpsY) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dpsY \<longrightarrow> dsolved \<rho> \<sigma> ((rb, t, u) # dps1 @ others))"
  proof (intro conjI allI impI)
    show "wt_env \<rho> envY" "dtyped \<rho> dpsY" "vinv \<rho> envY (X \<union> dvars dpsY)" using B by blast+
    fix \<sigma> assume sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> dpsY"
    note \<sigma> = solutionD(3)[OF sol]
    from B sol ds have ds2: "dsolved \<rho> \<sigma> (dps' @ others)" and bv: "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u')"
      by blast+
    from ds2 have ds': "dsolved \<rho> \<sigma> dps'" and dso: "dsolved \<rho> \<sigma> others" by (simp_all add: dsolved_def)
    from R sol ds' have cu: "ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" and d1: "dsolved \<rho> \<sigma> dps1"
      by auto
    have w1: "wt (ap \<rho> \<sigma> (Var v T \<degree>\<degree> targs))" using wt_ap[OF tyt \<sigma>] by (simp add: t)
    have w2: "wt (ap \<rho> \<sigma> (types_abs Ts u' \<degree>\<degree> targs))"
      by (rule wt_ap[OF typing_tabs_app[OF tyc tya cert] \<sigma>])
    from copy_bind_conv[OF bv cu w1 w2] d1 dso show "dsolved \<rho> \<sigma> ((rb, t, u) # dps1 @ others)"
      by (simp add: t dsolved_def ball_Un)
  qed
qed

lemma bs_env_Nil: "bs_env \<rho> e []"
  by (simp add: bs_env_def)

text \<open>The two ways in which \<open>new_dset\<close> records the binding:\<close>

lemma new_dset_bind:
  assumes nd: "okW (new_dset (v, T) Ts u' env' dps') y"
  obtains envY dpsY where "y = El_E envY dpsY" "extends env' envY"
    "\<And>\<rho> env'' X. tsol (tyenv env'') \<rho> \<Longrightarrow> extends envY env'' \<Longrightarrow> wt_env \<rho> env' \<Longrightarrow> dtyped \<rho> dps' \<Longrightarrow>
      (\<And>e. e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T) \<Longrightarrow> closed (types_abs Ts u') \<Longrightarrow>
      vinv \<rho> env' (X \<union> insert (v, T) (dvars dps' \<union> vars u')) \<Longrightarrow>
      wt_env \<rho> envY \<and> dtyped \<rho> dpsY \<and> vinv \<rho> envY (X \<union> dvars dpsY) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dpsY \<longrightarrow>
        dsolved \<rho> \<sigma> dps' \<and> \<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u'))"
proof -
  from nd obtain r where lk: "ok (lookup env' v T) r"
    and rest: "okW (case r of
        None \<Rightarrow> do {env'' \<leftarrow> liftM (update (v, T) (types_abs Ts u') env'); returnW (El_E env'' dps')}
      | Some s \<Rightarrow> returnW (El_E env' (([], s, types_abs Ts u') # dps'))) y"
    by (auto simp: new_dset_def)
  show ?thesis
  proof (cases r)
    case None
    with rest obtain env'' where upd: "ok (update (v, T) (types_abs Ts u') env') env''" and y: "y = El_E env'' dps'"
      by auto
    show ?thesis
    proof (rule that[OF y extends_update[OF upd]])
      fix \<rho> env3 X assume tsol: "tsol (tyenv env3) \<rho>" and ext: "extends env'' env3" and wte: "wt_env \<rho> env'"
        and dt: "dtyped \<rho> dps'" and tyb: "\<And>e. e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T"
        and cl: "closed (types_abs Ts u')" and vi: "vinv \<rho> env' (X \<union> insert (v, T) (dvars dps' \<union> vars u'))"
      have "wt_env \<rho> env''" by (rule wt_env_update[OF upd wte cl tyb])
      moreover have "vinv \<rho> env'' (X \<union> dvars dps')"
        by (rule vinv_update[OF upd]) (use vi in \<open>simp add: Un_ac\<close>)
      moreover have "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u')" if "solution \<rho> \<sigma> env3" for \<sigma>
        by (rule solution_update[OF upd solution_extends[OF that ext]])
      ultimately show "wt_env \<rho> env'' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env'' (X \<union> dvars dps') \<and>
          (\<forall>\<sigma>. solution \<rho> \<sigma> env3 \<longrightarrow> dsolved \<rho> \<sigma> dps' \<longrightarrow>
            dsolved \<rho> \<sigma> dps' \<and> \<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u'))"
        using dt by blast
    qed
  next
    case (Some s)
    with rest have y: "y = El_E env' (([], s, types_abs Ts u') # dps')" by simp
    from lk Some obtain S where lS: "vt_lookup (tenv env') v = Some (S, s)" by (auto elim: ok_lookup_Some)
    show ?thesis
    proof (rule that[OF y extends_refl])
      fix \<rho> env3 X assume tsol: "tsol (tyenv env3) \<rho>" and ext: "extends env' env3" and wte: "wt_env \<rho> env'"
        and dt: "dtyped \<rho> dps'" and tyb: "\<And>e. e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T"
        and cl: "closed (types_abs Ts u')" and vi: "vinv \<rho> env' (X \<union> insert (v, T) (dvars dps' \<union> vars u'))"
      have tsol': "tsol (tyenv env') \<rho>" by (rule extends_tsol[OF tsol ext])
      note ls = lookup_sound[OF lk[unfolded Some] tsol' wte]
      have cs: "closed s" by (rule wt_env_closed[OF wte lS])
      have "dtyped \<rho> (([], s, types_abs Ts u') # dps')"
        using ls(2)[of undefined] tyb[of undefined] cs cl dt bs_env_Nil[of \<rho> undefined]
        by (auto simp: closed_def)
      moreover have "vinv \<rho> env' (X \<union> dvars (([], s, types_abs Ts u') # dps'))"
      proof -
        have "vinv \<rho> env' (X \<union> (dvars dps' \<union> vars u'))" using vi by (rule vinv_mono) auto
        then have "vinv \<rho> env' (X \<union> (vars s \<union> vars u' \<union> dvars dps'))"
          by (rule vinv_hn) (use evarsI2[OF lS] in auto)
        then show ?thesis by (simp add: Un_ac)
      qed
      moreover have "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u')"
        if "solution \<rho> \<sigma> env3" "dsolved \<rho> \<sigma> (([], s, types_abs Ts u') # dps')" for \<sigma>
      proof -
        have "ap \<rho> \<sigma> (Var v T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> s" by (rule ls(1)[OF solution_extends[OF that(1) ext]])
        with that(2) show ?thesis by (auto intro: conv_trans)
      qed
      ultimately show "wt_env \<rho> env' \<and> dtyped \<rho> (([], s, types_abs Ts u') # dps') \<and>
          vinv \<rho> env' (X \<union> dvars (([], s, types_abs Ts u') # dps')) \<and>
          (\<forall>\<sigma>. solution \<rho> \<sigma> env3 \<longrightarrow> dsolved \<rho> \<sigma> (([], s, types_abs Ts u') # dps') \<longrightarrow>
            dsolved \<rho> \<sigma> dps' \<and> \<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u'))"
        using wte by auto
    qed
  qed
qed

theorem new_dset_sound:
  assumes nd: "okW (new_dset (v, T) Ts u' env' (dps' @ others)) y"
    and d0: "dstep env0 dps0 env1 ((rb, t, u) # dps1 @ others)" and st: "strip_comb t = (Var v T, targs)"
    and ta: "targs_ok env1 rb t targs Ts" and el: "astepo (Some t) env1 rb targs Ts [u] dps1 [u'] env' dps'"
  shows "elem_ok (GE env0 dps0) y"
proof -
  obtain envY dpsY where y: "y = El_E envY dpsY" and ext: "extends env' envY"
    and bind: "\<And>\<rho> env'' X. tsol (tyenv env'') \<rho> \<Longrightarrow> extends envY env'' \<Longrightarrow> wt_env \<rho> env' \<Longrightarrow>
      dtyped \<rho> (dps' @ others) \<Longrightarrow>
      (\<And>e. e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T) \<Longrightarrow> closed (types_abs Ts u') \<Longrightarrow>
      vinv \<rho> env' (X \<union> insert (v, T) (dvars (dps' @ others) \<union> vars u')) \<Longrightarrow>
      wt_env \<rho> envY \<and> dtyped \<rho> dpsY \<and> vinv \<rho> envY (X \<union> dvars dpsY) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dpsY \<longrightarrow>
        dsolved \<rho> \<sigma> (dps' @ others) \<and> \<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u'))"
    by (rule new_dset_bind[OF nd]) blast
  have "dstep env1 ((rb, t, u) # dps1 @ others) envY dpsY" by (rule dstep_copy_bind[OF st ta el ext bind])
  with d0 y show ?thesis by (simp add: dstep_trans)
qed

text \<open>For a single step of matching, the pair is kept, and the binding is sound by itself.\<close>

lemma typing_vars_cert: "e \<turnstile> inst \<rho> t : U \<Longrightarrow> (v, T) \<in> vars t \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  by (induction t arbitrary: e U) auto

lemma dtyped_vars_cert: "dtyped \<rho> dps \<Longrightarrow> (v, T) \<in> dvars dps \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  unfolding dtyped_def dvars_def by (fastforce intro: typing_vars_cert)

lemma sstepD:
  assumes "mstep1 env0 dps0 Ts T u' env dps"
  shows "extends env0 env"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env env'' \<Longrightarrow> wt_env \<rho> env0 \<Longrightarrow> dtyped \<rho> dps0 \<Longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0) \<Longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> vars u') \<and>
      (\<exists>B. tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> B \<and> (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> u' : B)) \<and>
      \<not> loose_bvar u' (ilength Ts) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow> dsolved \<rho> \<sigma> dps0)"
  using assms unfolding mstep1_def by blast+

theorem new_dset_sound1:
  assumes nd: "okW (new_dset (v, T) Ts u' env' dps') y" and d0: "dstep env0 dps0 env1 dps1"
    and vT: "(v, T) \<in> dvars dps1" and el: "mstep1 env1 dps1 Ts T u' env' dps'"
  shows "elem_ok (GE env0 dps0) y"
proof -
  obtain envY dpsY where y: "y = El_E envY dpsY" and ext: "extends env' envY"
    and bind: "\<And>\<rho> env'' X. tsol (tyenv env'') \<rho> \<Longrightarrow> extends envY env'' \<Longrightarrow> wt_env \<rho> env' \<Longrightarrow> dtyped \<rho> dps' \<Longrightarrow>
      (\<And>e. e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T) \<Longrightarrow> closed (types_abs Ts u') \<Longrightarrow>
      vinv \<rho> env' (X \<union> insert (v, T) (dvars dps' \<union> vars u')) \<Longrightarrow>
      wt_env \<rho> envY \<and> dtyped \<rho> dpsY \<and> vinv \<rho> envY (X \<union> dvars dpsY) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dpsY \<longrightarrow>
        dsolved \<rho> \<sigma> dps' \<and> \<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts u'))"
    by (rule new_dset_bind[OF nd]) blast
  have "dstep env1 dps1 envY dpsY"
  proof (rule dstepI)
    have e1: "extends env1 env'" by (rule sstepD(1)[OF el])
    show "extends env1 envY" by (rule extends_trans[OF e1 ext])
    fix \<rho> env'' X assume tsol: "tsol (tyenv env'') \<rho>" and extY: "extends envY env''" and wte: "wt_env \<rho> env1"
      and dt: "dtyped \<rho> dps1" and vi: "vinv \<rho> env1 (X \<union> dvars dps1)"
    have ext': "extends env' env''" by (rule extends_trans[OF ext extY])
    have vi1: "vinv \<rho> env1 ((X \<union> {(v, T)}) \<union> dvars dps1)" using vi vT by (simp add: insert_absorb Un_ac)
    note R = sstepD(2)[OF el tsol ext' wte dt vi1]
    from R obtain B where T: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> B"
      and tyc: "\<And>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> u' : B" by blast
    have "cert_typ alg ar (tsubst \<rho> T)" by (rule dtyped_vars_cert[OF dt vT])
    then have cert: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (simp add: T cert_typ_funs)
    have tyb: "e' \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T" for e'
      using typing_types_abs[OF tyc] cert by (simp add: inst_types_abs T)
    have cl: "closed (types_abs Ts u')" by (rule closed_types_abs) (use R in auto)
    have vi2: "vinv \<rho> env' (X \<union> insert (v, T) (dvars dps' \<union> vars u'))" using R by (simp add: Un_ac)
    note B = bind[OF tsol extY R[THEN conjunct1] R[THEN conjunct2, THEN conjunct1] tyb cl vi2]
    show "wt_env \<rho> envY \<and> dtyped \<rho> dpsY \<and> vinv \<rho> envY (X \<union> dvars dpsY) \<and>
        (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dpsY \<longrightarrow> dsolved \<rho> \<sigma> dps1)"
      using B R by blast
  qed
  with d0 y show ?thesis by (simp add: dstep_trans)
qed

subsection \<open>Type computations\<close>

lemma mapM_fastype_sound:
  assumes "ok (mapM (fastype env rb) ts) Ts'"
  shows "length Ts' = length ts"
    and "tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<tturnstile> map (inst \<rho>) ts : Us \<Longrightarrow> map (tsubst \<rho>) Ts' = Us"
proof -
  from assms have l: "list_all2 (\<lambda>t T. ok (fastype env rb t) T) ts Ts'" by (simp add: ok_mapM)
  then show "length Ts' = length ts" by (simp add: list_all2_lengthD)
  assume tsol: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e rb" and ty: "e \<tturnstile> map (inst \<rho>) ts : Us"
  from l ty show "map (tsubst \<rho>) Ts' = Us"
  proof (induction ts Ts' arbitrary: Us rule: list_all2_induct)
    case (Cons t ts T Ts')
    from Cons.prems obtain U Us' where Us: "Us = U # Us'" and tt: "e \<turnstile> inst \<rho> t : U"
      and tts: "e \<tturnstile> map (inst \<rho>) ts : Us'"
      by (auto split: list.splits)
    from fastype_sound[OF Cons.hyps(1) tsol bs tt] Cons.IH[OF tts] Us show ?case by simp
  qed simp
qed

lemma body_type_TVar:
  assumes "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> B = TVar v S \<Longrightarrow> vt_lookup (tyenv env) v = None"
  using assms
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where "Ts = [T1, U]" by auto
      with h Type True have "ok (bt env U) B" by simp
      from "1.IH"[OF this refl "1.prems"(2)] show ?thesis .
    next
      case False
      with h Type have "B = T" by (auto split: list.splits if_splits)
      with Type "1.prems"(2) show ?thesis by simp
    qed
  next
    case (TVar v' S')
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v' S') lr"
      and rest: "ok (case lr of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B" by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr have "vt_lookup (tyenv env) v' = None"
        by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)
      with None rest TVar "1.prems"(2) show ?thesis by simp
    next
      case (Some T')
      with rest have "ok (bt env T') B" by simp
      from "1.IH"[OF this refl "1.prems"(2)] show ?thesis .
    qed
  next
    case (TFree a S)
    with h "1.prems"(2) show ?thesis by simp
  qed
qed

lemma devar_nonTVar: "\<not> is_TVar U \<Longrightarrow> devar \<theta> U = return U"
  by (subst devar.simps) (cases U; simp)

lemma devar_unbound: "vt_lookup \<theta> v = None \<Longrightarrow> devar \<theta> (TVar v S) = return (TVar v S)"
  by (subst devar.simps) (simp add: type_lookup_def)

text \<open>Unifying an unbound type variable with another type binds it:\<close>

lemma cunify_types_TVar:
  assumes cu: "okW (cunify_types alg' (TVar v S) U env) env'" and nt: "\<not> is_TVar U"
    and unb: "vt_lookup (tyenv env) v = None" and tsol: "tsol (tyenv env') \<rho>"
  shows "\<rho> v S = tsubst \<rho> U"
proof -
  have nh: False if "ok (case e of TUnify \<Rightarrow> raise (Unif (Typ_Clash (tyenv env) (TVar v S) U)) | _ \<Rightarrow> raise e) y"
    for e and y :: env
    using that by (cases e) auto
  have ne: "TVar v S \<noteq> U" using nt by auto
  from cu[unfolded cunify_types_ok] ne obtain tye' n' where
    tu: "ok (type_unify alg' U (TVar v S) (tyenv env, maxidx env)) (tye', n')"
    and env': "env' = Envir n' (tenv env) tye'"
    by (auto simp: unify_types_def ok_handle split: prod.splits dest: nh)
  have uo: "ok (unify_aux alg' U (TVar v S) (tyenv env, maxidx env)) (tye', n')" using tu by (simp add: type_unify_def)
  obtain tye1 where u: "ok (update_new (v, (S, U)) (tyenv env)) tye1"
    and m: "ok (meet alg' U S (tye1, maxidx env)) (tye', n')"
    using uo nt by (subst (asm) unify_aux.simps) (cases U; auto simp: devar_nonTVar devar_unbound[OF unb] split: if_splits)
  have "textends tye1 tye'" using meet_textends[OF m refl] by simp
  from update_new_sound(2)[OF u this] tsol env' show ?thesis by simp
qed

lemma proj_unify_sound:
  assumes pu: "okW (proj_unify cfg base bary Cs env) env'"
    and tv: "Cs \<noteq> [] \<longrightarrow> is_TVar bary \<and> (\<forall>v S. bary = TVar v S \<longrightarrow> vt_lookup (tyenv env) v = None)"
  shows "tenv env' = tenv env" "extends env env'"
    and "tsol (tyenv env') \<rho> \<Longrightarrow> wft ar (tsubst \<rho> base) \<Longrightarrow> wft ar (tsubst \<rho> bary) \<Longrightarrow>
      tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
proof -
  have "tenv env' = tenv env \<and> extends env env' \<and>
    (tsol (tyenv env') \<rho> \<longrightarrow> wft ar (tsubst \<rho> base) \<longrightarrow> wft ar (tsubst \<rho> bary) \<longrightarrow>
      tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base))"
  proof (cases "Cs = []")
    case True
    then have cu: "okW (cunify_types (cfg_alg cfg) base bary env) env'"
      using pu by (auto simp: proj_unify_def test_unify_types_ok split: if_splits)
    note c = cunify_types_sound[OF cu]
    show ?thesis using c(1,2) c(3)[of \<rho>] True by auto
  next
    case False
    then have cu: "okW (cunify_types (cfg_alg cfg) bary (Cs \<Rrightarrow> base) env) env'"
      using pu by (auto simp: proj_unify_def List.null_iff)
    note c = cunify_types_sound[OF cu]
    from tv False obtain v S where b: "bary = TVar v S" and unb: "vt_lookup (tyenv env) v = None"
      by (cases bary) auto
    from False obtain C Cs' where "Cs = C # Cs'" by (cases Cs) auto
    then have nt: "\<not> is_TVar (Cs \<Rrightarrow> base)" by simp
    show ?thesis using c(1,2) cunify_types_TVar[OF cu[unfolded b] nt unb] b by auto
  qed
  then show "tenv env' = tenv env" "extends env env'"
    and "tsol (tyenv env') \<rho> \<Longrightarrow> wft ar (tsubst \<rho> base) \<Longrightarrow> wft ar (tsubst \<rho> bary) \<Longrightarrow>
      tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
    by blast+
qed

lemma gentvars_props:
  assumes "gentvars p env = (env', Cs)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'" "Cs = [] \<longleftrightarrow> p = 0"
  using assms by (auto simp: gentvars_def integer_arith split: if_splits env.splits)

lemma arity_guesses_TVar: "p \<in> set (arity_guesses cfg T) \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> is_TVar T"
  by (auto simp: arity_guesses_def split: if_splits)

lemma cert_wft: "cert_typ alg ar T \<Longrightarrow> wft ar T"
  by (simp add: cert_typ_def)


subsection \<open>Projections and imitation\<close>

lemma nat_integer_of_nat [simp]: "nat_of_integer (integer_of_nat m) = m"
  by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq)

lemma integer_of_nat_less: "integer_of_nat a < integer_of_nat b \<longleftrightarrow> a < b"
  by (simp add: integer_less_iff integer_of_nat.rep_eq)

lemma integer_of_nat_nonneg: "0 \<le> integer_of_nat a"
  by (simp add: integer_less_eq_iff integer_of_nat.rep_eq)

lemma okW_CANTUNIFY_returnW:
  "okW (case e of CANTUNIFY \<Rightarrow> returnW t | _ \<Rightarrow> raiseW e) s \<Longrightarrow> s = t"
  by (cases e) auto

lemma projenv_sinv:
  assumes pe: "okW (projenv cfg vname rb targs u env dps base Ts' head Usb targ p tail) s"
    and tl: "seqinv (GC env rb targs Ts u dps ot) tail"
    and st: "ok (strip_type env T) Usb" and pg: "p \<in> set (arity_guesses cfg (snd Usb))"
    and hk: "k < length targs" "head = Bound (integer_of_nat (length targs - 1 - k))" "targ = targs ! k"
      "T = Ts' ! k"
    and fty: "\<And>\<rho> e. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow>
      e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> tyok ot \<rho> e [U] \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      U = tsubst \<rho> base"
    and lTs': "length Ts' = length targs"
  shows "seqinv (GC env rb targs Ts u dps ot) s"
proof -
  obtain Us bary where Usb: "Usb = (Us, bary)" by (cases Usb)
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by fastforce
  note g' = gentvars_props[OF g]
  from okW_handle_CANTUNIFY[OF pe[unfolded projenv_def Usb g prod.case]]
  consider (ok) env' where "okW (proj_unify cfg base bary Cs env0) env'"
      "s = S_Proj vname env' Ts' (Us @ Cs) targs rb u dps head targ tail"
    | (cu) "s = tail"
    by auto
  then show ?thesis
  proof cases
    case (ok env')
    have tv: "Cs \<noteq> [] \<longrightarrow> is_TVar bary \<and> (\<forall>v S. bary = TVar v S \<longrightarrow> vt_lookup (tyenv env0) v = None)"
    proof
      assume "Cs \<noteq> []"
      then have "is_TVar bary" using arity_guesses_TVar[OF pg] g'(4) by (simp add: Usb)
      moreover have "ok (body_type env T) bary" using st by (auto simp: strip_type_def Usb)
      ultimately show "is_TVar bary \<and> (\<forall>v S. bary = TVar v S \<longrightarrow> vt_lookup (tyenv env0) v = None)"
        using body_type_TVar[of env T] g'(2) by auto
    qed
    note pu = proj_unify_sound[OF ok(1) tv]
    have ext0: "extends env env0" by (rule extends_tenv_eq) (use g' in simp_all)
    have "proj_ok env rb targs Ts u env' Ts' (Us @ Cs) head targ ot"
      unfolding proj_ok_def
    proof (intro conjI allI impI)
      show "extends env env'" by (rule extends_trans[OF ext0 pu(2)])
      show "tenv env' = tenv env" using pu(1) g'(1) by simp
      show "length Ts' = length targs" by (fact lTs')
      show "\<exists>j. head = Bound j \<and> 0 \<le> j \<and> j < ilength targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j)"
        using hk by (intro exI[of _ "integer_of_nat (length targs - 1 - k)"])
          (auto simp: ilength_eq nat_integer_of_nat integer_of_nat_less integer_of_nat_nonneg)
      fix \<rho> e U assume tsol: "tsol (tyenv env') \<rho>" and bs: "bs_env \<rho> e rb" and tyu: "e \<turnstile> inst \<rho> u : U"
        and tyo: "tyok ot \<rho> e [U]" and tyt: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
        and lb: "\<forall>t\<in>set (u # targs). \<not> loose_bvar t (ilength rb)"
      have tsol0: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol extends_trans[OF ext0 pu(2)]])
      have ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts" by (rule fty[OF tsol0 bs tyt])
      then show "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts" .
      have len: "length Ts = length targs" using typings_nth[OF tyt] by simp
      have tyg: "e \<turnstile> inst \<rho> targ : tsubst \<rho> T"
      proof -
        have "e \<turnstile> inst \<rho> targ : tsubst \<rho> (Ts ! k)" using typings_nth[OF tyt] hk len by simp
        moreover have "tsubst \<rho> (Ts ! k) = tsubst \<rho> T"
          using arg_cong[OF ts, of "\<lambda>xs. xs ! k"] hk len typings_nth[OF tyt]
          by (simp add: map_eq_imp_length_eq[OF ts])
        ultimately show ?thesis by simp
      qed
      have T: "tsubst \<rho> T = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> bary"
        using strip_type_sound[OF st[unfolded Usb] tsol0] .
      have U: "U = tsubst \<rho> base" by (rule bse[OF tsol0 bs tyo tyu])
      have cT: "cert_typ alg ar (tsubst \<rho> T)" by (rule bs_env_cert[OF bs tyg]) (use lb hk in simp)
      have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu]) (use lb in simp)
      have "tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
        using pu(3)[OF tsol] cU cT by (simp add: U T cert_typ_funs cert_wft)
      with tyg T U show "e \<turnstile> inst \<rho> targ : map (tsubst \<rho>) (Us @ Cs) \<Rrightarrow> U"
        by (simp add: tsubst_funs)
    qed
    with tl ok(2) show ?thesis by (auto intro: seqinv.Proj)
  qed (use tl in simp)
qed

lemma copyargs_sinv: "seqinv (GD env rb targs Ts uargs dps) (copyargs vname rb targs env dps uargs)"
proof (induction uargs)
  case Nil
  show ?case by (simp, rule seqinv.Single) (simp add: astep_Nil)
qed (simp add: seqinv.Maps)

lemma make_projs_props:
  "okW (make_projs u targs0 Ts targs) ps \<Longrightarrow> length Ts = length targs \<and>
    (\<forall>q\<in>set ps. \<exists>k<length targs. q = (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k))"
proof (induction u targs0 Ts targs arbitrary: ps rule: make_projs.induct)
  case (1 u targs0 T Ts targ targs)
  from "1.prems" obtain ps' where ps': "okW (make_projs u targs0 Ts targs) ps'"
    and ps: "ps = (Bound (ilength Ts), T, targ) # ps'" by auto
  note IH = "1.IH"[OF ps']
  have "\<exists>k<length (targ # targs). q = (Bound (integer_of_nat (length (targ # targs) - 1 - k)),
      (T # Ts) ! k, (targ # targs) ! k)" if "q \<in> set ps" for q
  proof -
    from that ps consider "q = (Bound (ilength Ts), T, targ)" | "q \<in> set ps'" by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using IH by (intro exI[of _ 0]) (simp add: ilength_eq)
    next
      case 2
      with IH obtain k where "k < length targs"
        "q = (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k)" by blast
      then show ?thesis by (intro exI[of _ "Suc k"]) simp
    qed
  qed
  with IH show ?case by simp
qed auto

lemma matchfun_sinv:
  assumes "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts' projs) s"
    and projs: "\<forall>q\<in>set projs. \<exists>k<length targs. q = (Bound (integer_of_nat (length targs - 1 - k)), Ts' ! k, targs ! k)"
    and u: "u = uhead \<degree>\<degree> uargs"
    and fty: "\<And>\<rho> e. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow>
      e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<Longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> tyok ot \<rho> e [U] \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      U = tsubst \<rho> base"
    and lTs': "length Ts' = length targs"
  shows "seqinv (GC env rb targs Ts u dps ot) s"
  using assms(1,2)
proof (induction projs arbitrary: s)
  case Nil
  then show ?case
    by (cases uhead) (auto simp: u closed_def intro!: seqinv.MapJoin seqinv.Empty copyargs_sinv)
next
  case (Cons q projs)
  obtain bvar T targ where q: "q = (bvar, T, targ)" by (cases q)
  from Cons.prems(2) q obtain k where hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    "T = Ts' ! k" "targ = targs ! k" by auto
  from Cons.prems(1)[unfolded q matchfun.simps] obtain Usb tail where st: "ok (strip_type env T) Usb"
    and mt: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts' projs) tail"
    and fo: "okW (foldrW (projenv cfg vname rb targs u env dps base Ts' bvar Usb targ) (arity_guesses cfg (snd Usb)) tail) s"
    by auto
  have tl: "seqinv (GC env rb targs Ts u dps ot) tail" by (rule Cons.IH[OF mt]) (use Cons.prems(2) in auto)
  have "seqinv (GC env rb targs Ts u dps ot) tail \<longrightarrow> set ps \<subseteq> set (arity_guesses cfg (snd Usb)) \<longrightarrow>
      seqinv (GC env rb targs Ts u dps ot) s'"
    if "okW (foldrW (projenv cfg vname rb targs u env dps base Ts' bvar Usb targ) ps tail) s'" for ps s'
    using that
  proof (induction rule: okW_foldrW_induct)
    case (Cons p ps b b1 b')
    show ?case
    proof (intro impI)
      assume b: "seqinv (GC env rb targs Ts u dps ot) b" and ss: "set (p # ps) \<subseteq> set (arity_guesses cfg (snd Usb))"
      with Cons.IH have b1: "seqinv (GC env rb targs Ts u dps ot) b1" by simp
      show "seqinv (GC env rb targs Ts u dps ot) b'"
        by (rule projenv_sinv[OF Cons.hyps(2) b1 st _ hk(1,2) hk(4,3) fty bse lTs']) (use ss in auto)
    qed
  qed simp
  with fo tl show ?case by blast
qed

subsection \<open>Copies\<close>

text \<open>
  The rigid side is saturated: its abstractions have no arguments, and otherwise its type is the
  body type of the type of its head, for every type instantiation.
\<close>

function satd :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "satd env rb u =
    (case fst (strip_comb u) of
      Abs a T b \<Rightarrow> snd (strip_comb u) = [] \<and> satd env ((a, T) # rb) b
    | _ \<Rightarrow> (\<forall>T0 B \<rho> e U. ok (fastype env rb (fst (strip_comb u))) T0 \<longrightarrow> ok (body_type env T0) B \<longrightarrow>
        tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow> e \<turnstile> inst \<rho> u : U \<longrightarrow> U = tsubst \<rho> B))"
  by auto
termination
  by (relation "measure (\<lambda>(env, rb, u). size u)") (auto dest: strip_comb_Abs_size)

declare satd.simps[simp del]

lemma satd_Abs:
  "fst (strip_comb u) = Abs a T b \<Longrightarrow> satd env rb u \<Longrightarrow> snd (strip_comb u) = [] \<and> satd env ((a, T) # rb) b"
  by (subst (asm) satd.simps) simp

lemma satd_base:
  "\<not> is_Abs (fst (strip_comb u)) \<Longrightarrow> satd env rb u \<Longrightarrow> ok (fastype env rb (fst (strip_comb u))) T0 \<Longrightarrow>
    ok (body_type env T0) B \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
    U = tsubst \<rho> B"
  by (subst (asm) satd.simps) (auto split: pterm.splits)

text \<open>
  The rigid side \<open>u\<close> of a pair with the flexible side \<open>t\<close> is saturated if its type is the body
  type of the type of its head whenever both sides are well-typed with the same type. (Unlike
  \<^const>\<open>satd\<close>, this restricts only the typings of \<open>u\<close> in which \<open>t\<close> has the same type.)
\<close>

definition rsat :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "rsat env rb t u \<longleftrightarrow> (\<forall>T0 B \<rho> e U. ok (fastype env rb (fst (strip_comb u))) T0 \<longrightarrow>
    ok (body_type env T0) B \<longrightarrow> tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow>
    e \<turnstile> inst \<rho> t : U \<longrightarrow> e \<turnstile> inst \<rho> u : U \<longrightarrow> U = tsubst \<rho> B)"

text \<open>The hypothesis of \<^const>\<open>mc\<close> for a goal with or without a flexible side:\<close>

definition msat :: "pterm option \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "msat ot env rb u \<longleftrightarrow> (case ot of None \<Rightarrow> satd env rb u
    | Some t \<Rightarrow> \<not> is_Abs (fst (strip_comb u)) \<and> rsat env rb t u)"

lemma mc_sinv:
  "okW (mc cfg vname rb targs u env dps) s \<Longrightarrow> msat ot env rb u \<Longrightarrow> seqinv (GC env rb targs Ts u dps ot) s"
proof (induction "size u" arbitrary: rb targs u Ts s ot rule: less_induct)
  case less
  define uhead where "uhead = fst (strip_comb u)"
  define uargs where "uargs = snd (strip_comb u)"
  have u: "u = uhead \<degree>\<degree> uargs" by (rule strip_comb_apps) (simp add: uhead_def uargs_def)
  note m = less.prems(1)[unfolded mc.simps[of cfg vname rb targs u env dps] Let_def, folded uhead_def uargs_def]
  have fty: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    if "ok (mapM (fastype env rb) targs) Ts'" "tsol (tyenv env) \<rho>" "bs_env \<rho> e rb"
      "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" for \<rho> e Ts'
    by (rule mapM_fastype_sound(2)[OF that])
  have bse: "U = tsubst \<rho> base"
    if "\<not> is_Abs uhead" "ok (fastype env rb uhead) T0" "ok (body_type env T0) base"
      "tsol (tyenv env) \<rho>" "bs_env \<rho> e rb" "tyok ot \<rho> e [U]" "e \<turnstile> inst \<rho> u : U" for \<rho> e U T0 base
  proof (cases ot)
    case None
    with less.prems(2) have sat: "satd env rb u" by (simp add: msat_def)
    show ?thesis by (rule satd_base[OF _ sat _ that(3)]) (use that in \<open>simp_all add: uhead_def\<close>)
  next
    case (Some t)
    with less.prems(2) have "rsat env rb t u" by (simp add: msat_def)
    from this[unfolded rsat_def] that Some show ?thesis by (simp add: uhead_def)
  qed
  show ?case
  proof (cases uhead)
    case (Abs a T body)
    have sat: "satd env rb u" using less.prems(2) Abs by (cases ot) (simp_all add: msat_def uhead_def)
    from satd_Abs[OF Abs[unfolded uhead_def] sat]
    have na: "uargs = []" and sb: "satd env ((a, T) # rb) body" by (simp_all add: uargs_def)
    have u': "u = Abs a T body" using u na Abs by simp
    from m Abs obtain s' where
      m': "okW (mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps) s'"
      and s: "s = S_MapAbs a T s'" by auto
    have "seqinv (GC env ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) (Ts @ [T]) body dps None) s'"
      by (rule less.hyps[OF _ m']) (simp_all add: u' msat_def sb)
    then show ?thesis by (simp add: s u' seqinv.MapAbs)
  next
    case (Var w W)
    from m Var obtain T0 base Ts' where T0: "ok (fastype env rb uhead) T0"
      and base: "ok (body_type env T0) base"
      and s0: "\<forall>env' newhd. genvar (fst w) env (foldr fun_type Ts' base) = (env', newhd) \<longrightarrow>
        ok (mapM (fastype env rb) targs) Ts' \<and>
        s = S_Single (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u) # dps))"
      by (auto split: prod.splits)
    obtain env' newhd where g: "genvar (fst w) env (foldr fun_type Ts' base) = (env', newhd)" by fastforce
    from s0 g have Ts': "ok (mapM (fastype env rb) targs) Ts'"
      and s: "s = S_Single (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u) # dps))"
      by blast+
    have "astepo ot env rb targs Ts [u] dps [combound newhd 0 (length Ts')] env' ((rb, newhd \<degree>\<degree> targs, u) # dps)"
      by (rule astep_newflex[OF g mapM_fastype_sound(1)[OF Ts']]) (use fty[OF Ts'] bse[OF _ T0 base] Var in auto)
    then show ?thesis by (simp add: s list_comb_apps seqinv.Single)
  next
    case (Const c C)
    from m Const obtain T0 base Ts' projs where T0: "ok (fastype env rb uhead) T0"
      and base: "ok (body_type env T0) base" and Ts': "ok (mapM (fastype env rb) targs) Ts'"
      and mp: "okW (make_projs u targs Ts' targs) projs"
      and mf: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts' (rev projs)) s"
      by auto
    show ?thesis
      by (rule matchfun_sinv[OF mf _ u fty[OF Ts'] bse[OF _ T0 base] mapM_fastype_sound(1)[OF Ts']]) (use make_projs_props[OF mp] Const in auto)
  next
    case (Free c C)
    from m Free obtain T0 base Ts' projs where T0: "ok (fastype env rb uhead) T0"
      and base: "ok (body_type env T0) base" and Ts': "ok (mapM (fastype env rb) targs) Ts'"
      and mp: "okW (make_projs u targs Ts' targs) projs"
      and mf: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts' (rev projs)) s"
      by auto
    show ?thesis
      by (rule matchfun_sinv[OF mf _ u fty[OF Ts'] bse[OF _ T0 base] mapM_fastype_sound(1)[OF Ts']]) (use make_projs_props[OF mp] Free in auto)
  next
    case (Bound i)
    from m Bound obtain T0 base Ts' projs where T0: "ok (fastype env rb uhead) T0"
      and base: "ok (body_type env T0) base" and Ts': "ok (mapM (fastype env rb) targs) Ts'"
      and mp: "okW (make_projs u targs Ts' targs) projs"
      and mf: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts' (rev projs)) s"
      by auto
    show ?thesis
      by (rule matchfun_sinv[OF mf _ u fty[OF Ts'] bse[OF _ T0 base] mapM_fastype_sound(1)[OF Ts']]) (use make_projs_props[OF mp] Bound in auto)
  next
    case (App f x)
    from m App obtain T0 base Ts' projs where T0: "ok (fastype env rb uhead) T0"
      and base: "ok (body_type env T0) base" and Ts': "ok (mapM (fastype env rb) targs) Ts'"
      and mp: "okW (make_projs u targs Ts' targs) projs"
      and mf: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts' (rev projs)) s"
      by auto
    show ?thesis
      by (rule matchfun_sinv[OF mf _ u fty[OF Ts'] bse[OF _ T0 base] mapM_fastype_sound(1)[OF Ts']]) (use make_projs_props[OF mp] App in auto)
  qed
qed

text \<open>The copies of an argument: a deferred argument, or the copies of \<^const>\<open>mc\<close>.\<close>

lemma copycons_sinv:
  assumes cc: "okW (copycons cfg vname rb targs uarg uargs env dps) cs"
    and el: "astep env0 rb targs Ts uargs0 dps0 uargs env dps"
    and sat: "\<And>u1 u2. ok (head_norm env uarg) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow> satd env rb u2"
  shows "seqinv (GD env0 rb targs Ts (uarg # uargs0) dps0) cs"
proof -
  from cc obtain u1 u2 d s where h: "ok (head_norm env uarg) u1" and e: "ok (eta_norm env rb u1) u2"
    and d: "okW (if 0 < cfg_arity_bound cfg then liftM (defer_arg env rb u2) else returnW False) d"
    and s: "okW (if d then do {
          A \<leftarrow> liftM (fastype env rb u2);
          Ts' \<leftarrow> liftM (mapM (fastype env rb) targs);
          (let (env', newhd) = genvar vname env (foldr fun_type Ts' A) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts')) env'
              ((rb, list_comb newhd targs, u2) # dps))))}
         else mc cfg vname rb targs u2 env dps) s"
    and cs: "cs = S_MapCons uargs s"
    by (auto simp: copycons_def)
  have tc: "tconv env rb uarg u2" by (rule tconv_trans[OF head_norm_tconv[OF h] eta_norm_tconv[OF e]])
  have "seqinv (GC env rb targs Ts u2 dps None) s"
  proof (cases d)
    case True
    with s obtain A Ts' where A: "ok (fastype env rb u2) A"
      and s0: "\<forall>env' newhd. genvar vname env (foldr fun_type Ts' A) = (env', newhd) \<longrightarrow>
        ok (mapM (fastype env rb) targs) Ts' \<and>
        s = S_Single (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u2) # dps))"
      by (auto split: prod.splits)
    obtain env' newhd where g: "genvar vname env (foldr fun_type Ts' A) = (env', newhd)" by fastforce
    from s0 g have Ts': "ok (mapM (fastype env rb) targs) Ts'"
      and s': "s = S_Single (El_C (combound newhd 0 (length Ts')) env' ((rb, list_comb newhd targs, u2) # dps))"
      by blast+
    have "astepo None env rb targs Ts [u2] dps [combound newhd 0 (length Ts')] env' ((rb, newhd \<degree>\<degree> targs, u2) # dps)"
      by (rule astep_newflex[OF g mapM_fastype_sound(1)[OF Ts']])
        (use mapM_fastype_sound(2)[OF Ts'] fastype_sound[OF A] in blast)
    then show ?thesis by (simp add: s' list_comb_apps seqinv.Single)
  next
    case False
    with s have "okW (mc cfg vname rb targs u2 env dps) s" by simp
    from mc_sinv[OF this] sat[OF h e] show ?thesis by (simp add: msat_def)
  qed
  then show ?thesis by (simp add: cs seqinv.MapCons[OF el tc])
qed


subsection \<open>The \<open>\<eta>\<close>-expansion of a pair\<close>

lemma binder_types_sound:
  assumes "binder_types env T = Some r"
  shows "r = Ok Ts \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> \<exists>W. tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> W"
  using assms
proof (induction env T r arbitrary: Ts rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Us)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Us = [T1, U])")
      case True
      then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" using Type by auto
      from h T obtain Ts' where r: "ok (bt env U) Ts'" and Ts: "Ts = T1 # Ts'" by auto
      from "1.IH"[OF r refl "1.prems"(2)] Ts T show ?thesis by auto
    next
      case False
      with h Type have "Ts = []" by (auto split: list.splits if_splits)
      then show ?thesis by simp
    qed
  next
    case (TVar v S)
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v S) lr"
      and rest: "ok (case lr of None \<Rightarrow> return [] | Some T' \<Rightarrow> bt env T') Ts"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some T')
      with rest have r: "ok (bt env T') Ts" by simp
      from "1.IH"[OF r refl "1.prems"(2)] ok_type_lookup_sound[OF lr[unfolded Some] "1.prems"(2)] TVar
      show ?thesis by simp
    qed (use rest in simp)
  next
    case (TFree a S)
    with h show ?thesis by simp
  qed
qed

lemma funs_prefix:
  "Us \<Rrightarrow> U = Vs \<Rrightarrow> W \<Longrightarrow> length Us \<le> length Vs \<Longrightarrow> U = drop (length Us) Vs \<Rrightarrow> W"
proof (induction Us arbitrary: Vs)
  case (Cons U' Us)
  then obtain V Vs' where "Vs = V # Vs'" by (cases Vs) auto
  with Cons show ?case by simp
qed simp

lemma bs_env_pushes:
  "bs_env \<rho> e rb \<Longrightarrow> \<forall>T\<in>set Es. cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow>
    bs_env \<rho> (pushes e (map (tsubst \<rho>) Es)) (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb)"
proof (induction Es arbitrary: e rb)
  case (Cons E Es)
  have "bs_env \<rho> (e\<langle>0:tsubst \<rho> E\<rangle>) ((STR '''', E) # rb)" by (rule bs_env_Cons) (use Cons.prems in simp_all)
  from Cons.IH[OF this] Cons.prems(2) show ?case by simp
qed simp

lemma typing_incr_pushes: "e \<turnstile> s : S \<Longrightarrow> pushes e Us \<turnstile> incr_bv (ilength Us) 0 s : S"
proof (induction Us arbitrary: e s)
  case (Cons U Us)
  have "e\<langle>0:U\<rangle> \<turnstile> lift s 0 : S" using Cons.prems by (rule lift_type) simp
  from Cons.IH[OF this] show ?case by (simp add: incr_bv_incr_bv add.commute)
qed simp

lemma loose_bvar_incr_bv:
  "0 \<le> n \<Longrightarrow> 0 \<le> lev \<Longrightarrow> lev \<le> k \<Longrightarrow> loose_bvar (incr_bv n lev t) (k + n) = loose_bvar t k"
  by (induction n lev t arbitrary: k rule: incr_bv.induct) (auto simp: algebra_simps)

lemma conv_types_abs:
  "wt (types_abs Vs s) \<Longrightarrow> wt (types_abs Vs s') \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' \<Longrightarrow> types_abs Vs s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Vs s'"
proof (induction Vs)
  case (Cons V Vs)
  from Cons.prems(1,2) have "wt (types_abs Vs s)" "wt (types_abs Vs s')" by (auto dest: wt_AbsD)
  from Cons.IH[OF this Cons.prems(3)] Cons.prems(1,2) show ?case by (simp add: conv_Abs)
qed simp

lemma bvs_Suc: "bvs (Suc n) = Bound (integer_of_nat n) # bvs n"
  by simp

text \<open>The abstraction of the application to new bound variables is \<open>\<eta>\<close>-equivalent:\<close>

lemma eta_bvs:
  "e \<turnstile> s : Vs \<Rrightarrow> W \<Longrightarrow> \<forall>V\<in>set Vs. cert_typ alg ar V \<Longrightarrow>
    e \<turnstile> types_abs Vs (incr_bv (ilength Vs) 0 s \<degree>\<degree> bvs (length Vs)) : Vs \<Rrightarrow> W \<and>
    types_abs Vs (incr_bv (ilength Vs) 0 s \<degree>\<degree> bvs (length Vs)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
proof (induction Vs arbitrary: e s)
  case (Cons V Vs)
  define s1 where "s1 = lift s 0 $ Bound 0"
  have ty1: "e\<langle>0:V\<rangle> \<turnstile> s1 : Vs \<Rrightarrow> W"
    using Cons.prems(1) by (auto simp: s1_def intro!: typing.App[OF lift_type])
  note IH = Cons.IH[OF ty1] Cons.prems(2)
  have eq: "incr_bv (ilength (V # Vs)) 0 s \<degree>\<degree> bvs (length (V # Vs)) =
      incr_bv (ilength Vs) 0 s1 \<degree>\<degree> bvs (length Vs)"
  proof -
    have i: "integer_of_nat (Suc (length Vs)) = integer_of_nat (length Vs) + 1"
      by (simp add: integer_of_nat_eq_of_nat)
    have "incr_bv (integer_of_nat (length Vs)) 0 (lift s 0) = incr_bv (integer_of_nat (length Vs) + 1) 0 s"
      by (rule incr_bv_incr_bv) (simp_all add: integer_of_nat_nonneg)
    then show ?thesis by (simp only: length_Cons bvs_Suc) (simp add: s1_def ilength_eq i del: upt_Suc)
  qed
  have cV: "cert_typ alg ar V" using Cons.prems(2) by simp
  have t1: "e \<turnstile> Abs STR '''' V (types_abs Vs (incr_bv (ilength Vs) 0 s1 \<degree>\<degree> bvs (length Vs))) : (V # Vs) \<Rrightarrow> W"
    using IH cV by auto
  have t2: "e \<turnstile> Abs STR '''' V s1 : (V # Vs) \<Rrightarrow> W" using ty1 cV by auto
  have "Abs STR '''' V (types_abs Vs (incr_bv (ilength Vs) 0 s1 \<degree>\<degree> bvs (length Vs))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs STR '''' V s1"
    by (rule conv_Abs) (use t1 t2 IH in \<open>auto simp: wt_def\<close>)
  also have "Abs STR '''' V s1 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" unfolding s1_def by (rule conv_eta_lift) (use t2 in \<open>auto simp: wt_def s1_def\<close>)
  finally have c: "Abs STR '''' V (types_abs Vs (incr_bv (ilength Vs) 0 s1 \<degree>\<degree> bvs (length Vs))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" .
  show ?case unfolding eq using t1 c by simp
qed simp

lemma strip_comb_expand:
  "strip_comb t = (Var v T, targs) \<Longrightarrow>
    strip_comb (incr_bv n 0 t \<degree>\<degree> ts) = (Var v T, map (incr_bv n 0) targs @ ts)"
  by (simp add: strip_comb_apps[of t] incr_bv_apps foldl_append[symmetric] strip_comb_atom_apps
      del: foldl_append)

lemma dstep_eta_expand:
  assumes st: "strip_comb t = (Var v T, targs)" and bt: "ok (binder_types env T) Ts"
    and len: "length targs \<le> length Ts"
  shows "dstep env [(rb, t, u)] env [eta_expand_dpair (drop (length targs) Ts) (rb, t, u)]"
proof -
  define Es where "Es = drop (length targs) Ts"
  define j where "j = length Es"
  have ij: "integer_of_nat j = ilength Es" by (simp add: j_def ilength_eq)
  have ed: "eta_expand_dpair Es (rb, t, u) =
      (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
       incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)"
    by (simp add: eta_expand_dpair_def Let_def j_def incr_boundvars_def list_comb_apps ij[unfolded j_def])
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  show ?thesis unfolding Es_def[symmetric] ed
  proof (rule dstepI[OF extends_refl])
    fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext: "extends env env''" and wte: "wt_env \<rho> env"
      and dt: "dtyped \<rho> [(rb, t, u)]" and vi: "vinv \<rho> env (X \<union> dvars [(rb, t, u)])"
    have tsol: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol'' ext])
    from dt obtain e U where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : U" and tyu: "e \<turnstile> inst \<rho> u : U"
      and lbt: "\<not> loose_bvar t (ilength rb)" and lbu: "\<not> loose_bvar u (ilength rb)"
      by auto
    from binder_types_sound[OF bt refl tsol] obtain W where T: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> W" by blast
    from tyt[unfolded t inst_apps] obtain Us where tyv: "e \<turnstile> inst \<rho> (Var v T) : Us \<Rrightarrow> U"
      and tyas: "e \<tturnstile> map (inst \<rho>) targs : Us"
      by (rule list_app_typeE)
    have lUs: "length Us = length targs" using typings_nth[OF tyas] by simp
    from tyv T have "Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> W" by auto
    from funs_prefix[OF this] len lUs have U: "U = map (tsubst \<rho>) Es \<Rrightarrow> W" by (simp add: Es_def drop_map)
    have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu lbu])
    then have cEs: "\<forall>T\<in>set Es. cert_typ alg ar (tsubst \<rho> T)" by (simp add: U cert_typ_funs)
    define e' where "e' = pushes e (map (tsubst \<rho>) Es)"
    have bs': "bs_env \<rho> e' (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb)" unfolding e'_def by (rule bs_env_pushes[OF bs cEs])
    have tyb: "e' \<tturnstile> bvs j : map (tsubst \<rho>) Es" using typings_bvs[of e "map (tsubst \<rho>) Es"] by (simp add: e'_def j_def)
    have tyx: "e' \<turnstile> inst \<rho> (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j) : W" if "e \<turnstile> inst \<rho> x : U" for x
      using list_app_typeI[OF typing_incr_pushes[OF that[unfolded U], of "map (tsubst \<rho>) Es", unfolded ilength_map]
          typings_bvs[of e "map (tsubst \<rho>) Es", unfolded length_map]]
      by (simp add: e'_def j_def inst_apps comp_def)
    have lbx: "\<not> loose_bvar (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j) (ilength (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb))"
      if "\<not> loose_bvar x (ilength rb)" for x
    proof -
      have "\<not> loose_bvar (incr_bv (ilength Es) 0 x) (ilength rb + ilength Es)"
        using loose_bvar_incr_bv[of "ilength Es" 0 "ilength rb" x] that by simp
      moreover have "\<not> loose_bvar b (ilength rb + ilength Es)" if "b \<in> set (bvs j)" for b
      proof -
        from that obtain x where x: "x < length Es" "b = Bound (integer_of_nat x)" by (auto simp: j_def)
        have "integer_of_nat x < ilength Es" using x by (simp add: ilength_eq integer_of_nat_less)
        then have "integer_of_nat x < ilength rb + ilength Es"
          using ilength_nonneg[of rb] by (simp add: integer_less_iff integer_less_eq_iff plus_integer.rep_eq)
        then show ?thesis using x by simp
      qed
      ultimately show ?thesis by (auto simp: loose_bvar_apps add.commute)
    qed
    show "wt_env \<rho> env \<and> dtyped \<rho> [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
        incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)] \<and>
      vinv \<rho> env (X \<union> dvars [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
        incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)]) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb,
        incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j, incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)] \<longrightarrow>
        dsolved \<rho> \<sigma> [(rb, t, u)])"
    proof (intro conjI allI impI)
      show "wt_env \<rho> env" by (fact wte)
      show "dtyped \<rho> [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
          incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)]"
        using bs' tyx[OF tyt] tyx[OF tyu] lbx[OF lbt] lbx[OF lbu] by auto
      show "vinv \<rho> env (X \<union> dvars [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j,
          incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)])"
        using vi by (simp add: vars_apps)
      fix \<sigma> assume sol: "solution \<rho> \<sigma> env''" and ds: "dsolved \<rho> \<sigma> [(rev (map (\<lambda>T. (STR '''', T)) Es) @ rb,
          incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j, incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)]"
      note \<sigma> = solutionD(3)[OF sol]
      have apx: "ap \<rho> \<sigma> (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j) =
          incr_bv (ilength (map (tsubst \<rho>) Es)) 0 (ap \<rho> \<sigma> x) \<degree>\<degree> bvs (length (map (tsubst \<rho>) Es))" for x
        using \<sigma> by (simp add: ap_apps ap_lift j_def comp_def)
      have ex: "types_abs (map (tsubst \<rho>) Es) (ap \<rho> \<sigma> (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> x \<and>
          wt (types_abs (map (tsubst \<rho>) Es) (ap \<rho> \<sigma> (incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j)))"
        if "e \<turnstile> inst \<rho> x : U" for x
        using eta_bvs[OF typing_ap[OF that \<sigma>, unfolded U]] cEs by (auto simp: apx wt_def)
      from ds have "ap \<rho> \<sigma> (incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j)"
        by simp
      then have "types_abs (map (tsubst \<rho>) Es) (ap \<rho> \<sigma> (incr_bv (ilength Es) 0 t \<degree>\<degree> bvs j)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>
          types_abs (map (tsubst \<rho>) Es) (ap \<rho> \<sigma> (incr_bv (ilength Es) 0 u \<degree>\<degree> bvs j))"
        using ex[OF tyt] ex[OF tyu] by (intro conv_types_abs) auto
      with ex[OF tyt] ex[OF tyu] show "dsolved \<rho> \<sigma> [(rb, t, u)]" by (auto intro: conv_trans conv_sym)
    qed
  qed
qed

subsection \<open>Single steps\<close>

text \<open>The kept pair \<open>(rb, t, u)\<close> with \<open>t = ?v targs\<close> fixes the types of a single step:\<close>

lemma pair_typing:
  assumes pr: "(rb, t, u) \<in> set dps" and st: "strip_comb t = (Var v T, targs)" and ta: "targs_ok env rb t targs Ts"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> t : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      U = tsubst \<rho> base"
    and tsol: "tsol (tyenv env) \<rho>" and dt: "dtyped \<rho> dps"
  obtains e where "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> u : tsubst \<rho> base" "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts" "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> base"
    "\<not> loose_bvar u (ilength rb)" "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
proof -
  from dt pr obtain e U where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : U" and tyu: "e \<turnstile> inst \<rho> u : U"
    and lbt: "\<not> loose_bvar t (ilength rb)" and lbu: "\<not> loose_bvar u (ilength rb)"
    unfolding dtyped_def by fastforce
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" using ta tsol bs tyt by (auto simp: targs_ok_def)
  from tyt[unfolded t inst_apps] obtain Us where tyv: "e \<turnstile> inst \<rho> (Var v T) : Us \<Rrightarrow> U"
    and tyas: "e \<tturnstile> map (inst \<rho>) targs : Us"
    by (rule list_app_typeE)
  have Us: "Us = map (tsubst \<rho>) Ts" by (rule typings_unique[OF tyas tya])
  have U: "U = tsubst \<rho> base" by (rule bse[OF tsol bs tyt tyu])
  from tyv have T: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> base" by (auto simp: Us U)
  have "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts" by (rule mapM_fastype_sound(2)[OF Ts' tsol bs tya])
  moreover have "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)" using lbt by (simp add: t loose_bvar_apps)
  ultimately show ?thesis using that bs tyu tya T lbu by (simp add: U)
qed

text \<open>The copy of a projection, typed under the binders of the arguments:\<close>

lemma typing_proj_copy:
  assumes Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us" and ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    and cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" and cUs: "\<forall>U\<in>set Us. cert_typ alg ar (tsubst \<rho> U)"
    and hj: "0 \<le> j" "j < ilength Ts"
    and jT: "tsubst \<rho> (Ts ! (length Ts - 1 - nat_of_integer j)) = map (tsubst \<rho>) Us \<Rrightarrow> W"
    and len: "length Ts' = length Ts"
  shows "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb (Bound j) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs)) : W"
proof -
  have lGs: "length Gs = length Us" by (rule list_all2_lengthD[OF Gs])
  have tyGk: "e'' \<turnstile> inst \<rho> (Gs ! k) : map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> (Us ! k)" if "k < length Gs" for e'' k
  proof -
    from list_all2_nthD[OF Gs that] obtain x where "Gs ! k = Var x (Ts' \<Rrightarrow> (Us ! k))" by blast
    moreover have "Us ! k \<in> set Us" using that lGs by simp
    ultimately show ?thesis using cTs cUs by (auto simp: tsubst_funs ts cert_typ_funs)
  qed
  have tyargs: "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs) : map (tsubst \<rho>) Us"
    unfolding typings_iff
  proof (rule list_all2_all_nthI)
    fix k assume "k < length (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs))"
    then have k: "k < length Gs" by simp
    have "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Gs ! k) \<degree>\<degree> bvs (length (map (tsubst \<rho>) Ts)) : tsubst \<rho> (Us ! k)"
      by (rule list_app_typeI[OF tyGk[OF k] typings_bvs])
    then show "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs) ! k :
        map (tsubst \<rho>) Us ! k"
      using k lGs len by (simp add: inst_apps comp_def)
  qed (simp add: lGs)
  have "pushes e' (map (tsubst \<rho>) Ts) j = map (tsubst \<rho>) Us \<Rrightarrow> W"
  proof -
    have "j < ilength (map (tsubst \<rho>) Ts)" using hj(2) by simp
    then have "pushes e' (map (tsubst \<rho>) Ts) j = rev (map (tsubst \<rho>) Ts) ! nat_of_integer j"
      using hj(1) by (simp add: pushes_nth)
    also have "\<dots> = tsubst \<rho> (Ts ! (length Ts - 1 - nat_of_integer j))"
      using hj nat_of_integer_less_ilength[OF hj] by (simp add: rev_nth)
    finally show ?thesis using jT by simp
  qed
  from list_app_typeI[OF typing.Bound[where e="pushes e' (map (tsubst \<rho>) Ts)", OF hj(1) this] tyargs]
  show ?thesis by (simp add: list_comb_apps inst_apps)
qed

lemma mstep1_proj:
  assumes pr: "(rb, t, u) \<in> set dps" and st: "strip_comb t = (Var v T, targs)" and ta: "targs_ok env rb t targs Ts"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> t : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      U = tsubst \<rho> base"
    and hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    and stT: "ok (strip_type env (Ts' ! k)) (Us, bary)" and pg: "p \<in> set (arity_guesses cfg bary)"
    and g: "gentvars p env = (env0, Cs)" and pu: "okW (proj_unify cfg base bary Cs env0) env'"
    and ma: "make_args vname Ts' env' (Us @ Cs) = (env'', args)"
  shows "mstep1 env dps Ts T (list_comb bvar args) env'' dps"
proof -
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs (Us @ Cs)"
    and ma': "tenv env'' = tenv env'" "tyenv env'' = tyenv env'" "maxidx env' \<le> maxidx env''"
    and viG: "\<And>\<rho> X. vinv \<rho> env' X \<Longrightarrow> vinv \<rho> env'' (lvars Gs \<union> X)"
    by (rule make_args_props[OF ma]) blast
  note g' = gentvars_props[OF g]
  have tv: "Cs \<noteq> [] \<longrightarrow> is_TVar bary \<and> (\<forall>v S. bary = TVar v S \<longrightarrow> vt_lookup (tyenv env0) v = None)"
  proof
    assume "Cs \<noteq> []"
    then have "is_TVar bary" using arity_guesses_TVar[OF pg] g'(4) by simp
    moreover have "ok (body_type env (Ts' ! k)) bary" using stT by (auto simp: strip_type_def)
    ultimately show "is_TVar bary \<and> (\<forall>v S. bary = TVar v S \<longrightarrow> vt_lookup (tyenv env0) v = None)"
      using body_type_TVar[of env "Ts' ! k"] g'(2) by auto
  qed
  note pu' = proj_unify_sound[OF pu tv]
  have ext0: "extends env env0" by (rule extends_tenv_eq) (use g' in simp_all)
  have ext1: "extends env' env''" by (rule extends_tenv_eq[OF ma'])
  have ext: "extends env env''" by (rule extends_trans[OF extends_trans[OF ext0 pu'(2)] ext1])
  have tenv: "tenv env'' = tenv env" using ma'(1) pu'(1) g'(1) by simp
  have lTs': "length Ts' = length targs" by (rule mapM_fastype_sound(1)[OF Ts'])
  show ?thesis
    unfolding mstep1_def
  proof (intro conjI allI impI ext)
    fix \<rho> env3 X assume tsol3: "tsol (tyenv env3) \<rho>" and ext3: "extends env'' env3" and wte: "wt_env \<rho> env"
      and dt: "dtyped \<rho> dps" and vi: "vinv \<rho> env (X \<union> dvars dps)"
    have tsol': "tsol (tyenv env') \<rho>" by (rule extends_tsol[OF tsol3 extends_trans[OF ext1 ext3]])
    have tsol: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol3 extends_trans[OF ext ext3]])
    obtain e where bs: "bs_env \<rho> e rb" and tyu: "e \<turnstile> inst \<rho> u : tsubst \<rho> base"
      and tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" and ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
      and T: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> base"
      and lbu: "\<not> loose_bvar u (ilength rb)" and lba: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
      by (rule pair_typing[OF pr st ta Ts' bse tsol dt])
    have len: "length Ts = length targs" using typings_nth[OF tya] by simp
    have cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF bs tya lba])
    have cb: "cert_typ alg ar (tsubst \<rho> base)" by (rule bs_env_cert[OF bs tyu lbu])
    have Tk: "tsubst \<rho> (Ts ! k) = tsubst \<rho> (Ts' ! k)"
      using arg_cong[OF ts, of "\<lambda>xs. xs ! k"] hk(1) len lTs' by simp
    have Tk': "tsubst \<rho> (Ts' ! k) = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> bary"
      by (rule strip_type_sound[OF stT tsol])
    have cTk: "cert_typ alg ar (tsubst \<rho> (Ts ! k))" using cTs hk(1) len by simp
    have bary: "tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
      using pu'(3)[OF extends_tsol[OF tsol3 ext3, unfolded ma'(2)]] cb cTk
      by (simp add: Tk Tk' cert_typ_funs cert_wft)
    have jT: "tsubst \<rho> (Ts ! k) = map (tsubst \<rho>) (Us @ Cs) \<Rrightarrow> tsubst \<rho> base"
      using Tk Tk' bary by (simp add: tsubst_funs)
    have cUs: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho> U)" using cTk by (auto simp: jT cert_typ_funs)
    have j: "0 \<le> integer_of_nat (length targs - 1 - k)" "integer_of_nat (length targs - 1 - k) < ilength Ts"
      using hk len by (simp_all add: integer_of_nat_nonneg ilength_eq integer_of_nat_less)
    have kk: "length Ts - 1 - nat_of_integer (integer_of_nat (length targs - 1 - k)) = k" using hk len by simp
    have kk2: "length targs - Suc (length targs - Suc k) = k" using hk(1) by simp
    have tyc: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb bvar args) : tsubst \<rho> base" for e'
      unfolding hk(2) args
      by (rule typing_proj_copy[OF Gs ts cTs cUs j _ ]) (simp_all add: kk kk2 jT lTs' len)
    show "wt_env \<rho> env''" using wte by (simp add: wt_env_tenv[OF tenv])
    show "dtyped \<rho> dps" by (fact dt)
    have "vinv \<rho> env' (X \<union> dvars dps)" using vinv_tenv[OF _ extends_trans[OF ext0 pu'(2)] vi] pu'(1) g'(1) by simp
    from viG[OF this] show "vinv \<rho> env'' (X \<union> dvars dps \<union> vars (list_comb bvar args))"
      by (simp add: hk(2) args list_comb_apps vars_apps Un_ac)
    show "\<exists>B. tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> B \<and> (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb bvar args) : B)"
      using T tyc by blast
    show "\<not> loose_bvar (list_comb bvar args) (ilength Ts)"
    proof -
      have "\<not> loose_bvar a (ilength Ts)" if "a \<in> set args" for a
      proof -
        from that obtain G where G: "G \<in> set Gs" "a = G \<degree>\<degree> bvs (length Ts')" by (auto simp: args)
        from G(1) obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
        from list_all2_nthD[OF Gs i(1)] i(2) have "\<exists>x U. G = Var x U" by blast
        then show ?thesis using G(2) loose_bvar_bvs_ilength[of Ts "length Ts'"] lTs' len by (auto simp: loose_bvar_apps)
      qed
      then show ?thesis using j(2) by (simp add: hk(2) list_comb_apps loose_bvar_apps)
    qed
    show "dsolved \<rho> \<sigma> dps" if "dsolved \<rho> \<sigma> dps" for \<sigma> using that .
  qed
qed

lemma typings_new_args:
  assumes Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us" and ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    and cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" and cUs: "\<forall>U\<in>set Us. cert_typ alg ar (tsubst \<rho> U)"
    and len: "length Ts' = length Ts"
  shows "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs) : map (tsubst \<rho>) Us"
  unfolding typings_iff
proof (rule list_all2_all_nthI)
  have lGs: "length Gs = length Us" by (rule list_all2_lengthD[OF Gs])
  then show "length (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs)) = length (map (tsubst \<rho>) Us)" by simp
  fix k assume "k < length (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs))"
  then have k: "k < length Gs" by simp
  from list_all2_nthD[OF Gs k] obtain x where "Gs ! k = Var x (Ts' \<Rrightarrow> (Us ! k))" by blast
  moreover have "Us ! k \<in> set Us" using k lGs by simp
  ultimately have "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Gs ! k) : map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> (Us ! k)"
    using cTs cUs by (auto simp: tsubst_funs ts cert_typ_funs)
  from list_app_typeI[OF this typings_bvs]
  show "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs) ! k :
      map (tsubst \<rho>) Us ! k"
    using k lGs len by (simp add: inst_apps comp_def)
qed

lemma mstep1_imit:
  assumes pr: "(rb, t, u) \<in> set dps" and st: "strip_comb t = (Var v T, targs)" and ta: "targs_ok env rb t targs Ts"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> t : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      U = tsubst \<rho> base"
    and uh: "fst (strip_comb u) = uhead" and cl: "closed uhead" and vh: "vars uhead = {}"
    and T0: "ok (fastype env rb uhead) T0" and base: "ok (body_type env T0) base"
    and bt: "ok (binder_types env T0) Us" and ma: "make_args vname Ts' env Us = (env', args)"
  shows "mstep1 env dps Ts T (list_comb uhead args) env' dps"
proof -
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us"
    and ma': "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    and viG: "\<And>\<rho> X. vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' (lvars Gs \<union> X)"
    by (rule make_args_props[OF ma]) blast
  have ext: "extends env env'" by (rule extends_tenv_eq[OF ma'])
  have lTs': "length Ts' = length targs" by (rule mapM_fastype_sound(1)[OF Ts'])
  define uargs where "uargs = snd (strip_comb u)"
  have u: "u = uhead \<degree>\<degree> uargs" by (rule strip_comb_apps) (simp add: uh[symmetric] uargs_def)
  show ?thesis
    unfolding mstep1_def
  proof (intro conjI allI impI ext)
    fix \<rho> env3 X assume tsol3: "tsol (tyenv env3) \<rho>" and ext3: "extends env' env3" and wte: "wt_env \<rho> env"
      and dt: "dtyped \<rho> dps" and vi: "vinv \<rho> env (X \<union> dvars dps)"
    have tsol: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol3 extends_trans[OF ext ext3]])
    obtain e where bs: "bs_env \<rho> e rb" and tyu: "e \<turnstile> inst \<rho> u : tsubst \<rho> base"
      and tya: "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" and ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
      and T: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> base"
      and lbu: "\<not> loose_bvar u (ilength rb)" and lba: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
      by (rule pair_typing[OF pr st ta Ts' bse tsol dt])
    have len: "length Ts = length targs" using typings_nth[OF tya] by simp
    have cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule cert_targs[OF bs tya lba])
    from tyu[unfolded u inst_apps] obtain Vs where tyh: "e \<turnstile> inst \<rho> uhead : Vs \<Rrightarrow> tsubst \<rho> base"
      by (rule list_app_typeE)
    have T0': "tsubst \<rho> T0 = Vs \<Rrightarrow> tsubst \<rho> base" by (rule fastype_sound[OF T0 tsol bs tyh])
    have T0'': "tsubst \<rho> T0 = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> base"
      by (rule binder_body_type_sound[OF bt refl base tsol])
    have cT0: "cert_typ alg ar (tsubst \<rho> T0)"
      using bs_env_cert[OF bs tyh] closed_loose_bvar[OF cl] by (simp add: T0')
    then have cUs: "\<forall>U\<in>set Us. cert_typ alg ar (tsubst \<rho> U)" by (simp add: T0'' cert_typ_funs)
    have tyh': "e' \<turnstile> inst \<rho> uhead : map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> base" for e'
      using typing_closed[OF tyh closed_inst[OF cl]] T0' T0'' by simp
    have tyc: "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb uhead args) : tsubst \<rho> base" for e'
      using list_app_typeI[OF tyh' typings_new_args[OF Gs ts cTs cUs]] lTs' len
      by (simp add: args list_comb_apps inst_apps)
    show "wt_env \<rho> env'" using wte by (simp add: wt_env_tenv[OF ma'(1)])
    show "dtyped \<rho> dps" by (fact dt)
    from viG[OF vi] show "vinv \<rho> env' (X \<union> dvars dps \<union> vars (list_comb uhead args))"
      by (simp add: args list_comb_apps vars_apps vh Un_ac)
    show "\<exists>B. tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> B \<and> (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb uhead args) : B)"
      using T tyc by blast
    show "\<not> loose_bvar (list_comb uhead args) (ilength Ts)"
    proof -
      have "\<not> loose_bvar a (ilength Ts)" if "a \<in> set args" for a
      proof -
        from that obtain G where G: "G \<in> set Gs" "a = G \<degree>\<degree> bvs (length Ts')" by (auto simp: args)
        from G(1) obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
        from list_all2_nthD[OF Gs i(1)] i(2) have "\<exists>x U. G = Var x U" by blast
        then show ?thesis using G(2) loose_bvar_bvs_ilength[of Ts "length Ts'"] lTs' len by (auto simp: loose_bvar_apps)
      qed
      then show ?thesis using closed_loose_bvar[OF cl] by (simp add: list_comb_apps loose_bvar_apps)
    qed
    show "dsolved \<rho> \<sigma> dps" if "dsolved \<rho> \<sigma> dps" for \<sigma> using that .
  qed
qed

lemma match1_proj_sinv:
  assumes m: "okW (match1_proj cfg vname env dps base Ts' bvar Usb p tail) s" and tl: "seqinv (GS env dps Ts T) tail"
    and pr: "(rb, t, u) \<in> set dps" and st: "strip_comb t = (Var v T, targs)" and ta: "targs_ok env rb t targs Ts"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> t : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      U = tsubst \<rho> base"
    and hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    and stT: "ok (strip_type env (Ts' ! k)) Usb" and pg: "p \<in> set (arity_guesses cfg (snd Usb))"
  shows "seqinv (GS env dps Ts T) s"
proof -
  obtain Us bary where Usb: "Usb = (Us, bary)" by (cases Usb)
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by fastforce
  from okW_handle_CANTUNIFY[OF m[unfolded match1_proj_def Usb g prod.case]]
  consider (ok) env' where "okW (proj_unify cfg base bary Cs env0) env'"
      "okW (case make_args vname Ts' env' (Us @ Cs) of (env'', args) \<Rightarrow>
        returnW (S_Append (S_Single (El_C (list_comb bvar args) env'' dps)) tail)) s"
    | (cu) "s = tail"
    by auto
  then show ?thesis
  proof cases
    case (ok env')
    obtain env'' args where ma: "make_args vname Ts' env' (Us @ Cs) = (env'', args)" by fastforce
    with ok(2) have s: "s = S_Append (S_Single (El_C (list_comb bvar args) env'' dps)) tail" by simp
    have "mstep1 env dps Ts T (list_comb bvar args) env'' dps"
      by (rule mstep1_proj[OF pr st ta Ts' bse hk stT[unfolded Usb] pg[unfolded Usb snd_conv] g ok(1) ma])
    then show ?thesis by (simp add: s tl seqinv.Append seqinv.Single)
  qed (use tl in simp)
qed

lemma match1_projs_sinv:
  assumes "okW (match1_projs cfg vname env dps base Ts' projs tail) s" and tl: "seqinv (GS env dps Ts T) tail"
    and projs: "\<forall>q\<in>set projs. \<exists>k<length targs. q = (Bound (integer_of_nat (length targs - 1 - k)), Ts' ! k, targs ! k)"
    and pr: "(rb, t, u) \<in> set dps" and st: "strip_comb t = (Var v T, targs)" and ta: "targs_ok env rb t targs Ts"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'"
    and bse: "\<And>\<rho> e U. tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> t : U \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
      U = tsubst \<rho> base"
  shows "seqinv (GS env dps Ts T) s"
  using assms(1,3)
proof (induction projs arbitrary: s)
  case Nil
  then show ?case using tl by simp
next
  case (Cons q projs)
  obtain bvar T' targ where q: "q = (bvar, T', targ)" by (cases q)
  from Cons.prems(2) q obtain k where hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    "T' = Ts' ! k" by auto
  from Cons.prems(1)[unfolded q match1_projs.simps] obtain Usb tl' where stT: "ok (strip_type env T') Usb"
    and mt: "okW (match1_projs cfg vname env dps base Ts' projs tail) tl'"
    and fo: "okW (foldrW (match1_proj cfg vname env dps base Ts' bvar Usb) (arity_guesses cfg (snd Usb)) tl') s"
    by auto
  have tl': "seqinv (GS env dps Ts T) tl'" by (rule Cons.IH[OF mt]) (use Cons.prems(2) in auto)
  have "seqinv (GS env dps Ts T) b0 \<longrightarrow> set ps \<subseteq> set (arity_guesses cfg (snd Usb)) \<longrightarrow> seqinv (GS env dps Ts T) s'"
    if "okW (foldrW (match1_proj cfg vname env dps base Ts' bvar Usb) ps b0) s'" for ps b0 s'
    using that
  proof (induction rule: okW_foldrW_induct)
    case (Cons p ps b b1 b')
    show ?case
    proof (intro impI)
      assume b: "seqinv (GS env dps Ts T) b" and ss: "set (p # ps) \<subseteq> set (arity_guesses cfg (snd Usb))"
      with Cons.IH have b1: "seqinv (GS env dps Ts T) b1" by simp
      show "seqinv (GS env dps Ts T) b'"
        by (rule match1_proj_sinv[OF Cons.hyps(2) b1 pr st ta Ts' bse hk(1,2) stT[unfolded hk(3)]]) (use ss in auto)
    qed
  qed simp
  with fo tl' show ?case by blast
qed

lemma match1_sinv:
  assumes m: "okW (match1 cfg vname rb targs u env dps) s"
    and pr: "(rb, t, u) \<in> set dps" and st: "strip_comb t = (Var v T, targs)" and ta: "targs_ok env rb t targs Ts"
    and nab: "\<not> is_Abs (fst (strip_comb u))" and sat: "rsat env rb t u"
  shows "seqinv (GS env dps Ts T) s"
proof -
  from m obtain T0 base Ts' projs imit where T0: "ok (fastype env rb (fst (strip_comb u))) T0"
    and base: "ok (body_type env T0) base" and Ts': "ok (mapM (fastype env rb) targs) Ts'"
    and mp: "okW (make_projs u targs Ts' targs) projs"
    and im: "okW (case fst (strip_comb u) of
          Const _ _ \<Rightarrow> do {
            Us \<leftarrow> liftM (binder_types env T0);
            (case make_args vname Ts' env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb (fst (strip_comb u)) args) env' dps)))}
        | Free _ _ \<Rightarrow> do {
            Us \<leftarrow> liftM (binder_types env T0);
            (case make_args vname Ts' env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb (fst (strip_comb u)) args) env' dps)))}
        | _ \<Rightarrow> returnW S_Empty) imit"
    and m': "okW (match1_projs cfg vname env dps base Ts' (rev projs) imit) s"
    by (auto simp: match1_def Let_def)
  define uhead where "uhead = fst (strip_comb u)"
  note T0 = T0[folded uhead_def] and im = im[folded uhead_def]
  have bse: "U = tsubst \<rho> base"
    if "tsol (tyenv env) \<rho>" "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : U" "e \<turnstile> inst \<rho> u : U" for \<rho> e U
    using sat[unfolded rsat_def] T0 base that by (simp add: uhead_def)
  have imit_ok: "seqinv (GS env dps Ts T) (S_Single (El_C (list_comb uhead args) env' dps))"
    if "closed uhead" "vars uhead = {}" "ok (binder_types env T0) Us" "make_args vname Ts' env Us = (env', args)"
    for Us env' args
    using mstep1_imit[OF pr st ta Ts' bse uhead_def[symmetric] that(1,2) T0 base that(3,4)]
    by (simp add: seqinv.Single)
  have tl: "seqinv (GS env dps Ts T) imit"
  proof (cases uhead)
    case (Const c C)
    from im Const obtain Us where bt: "ok (binder_types env T0) Us"
      and r: "okW (case make_args vname Ts' env Us of (env', args) \<Rightarrow>
        returnW (S_Single (El_C (list_comb uhead args) env' dps))) imit" by auto
    obtain env' args where ma: "make_args vname Ts' env Us = (env', args)" by fastforce
    from r ma have "imit = S_Single (El_C (list_comb uhead args) env' dps)" by simp
    with imit_ok[OF _ _ bt ma] Const show ?thesis by (simp add: closed_def)
  next
    case (Free c C)
    from im Free obtain Us where bt: "ok (binder_types env T0) Us"
      and r: "okW (case make_args vname Ts' env Us of (env', args) \<Rightarrow>
        returnW (S_Single (El_C (list_comb uhead args) env' dps))) imit" by auto
    obtain env' args where ma: "make_args vname Ts' env Us = (env', args)" by fastforce
    from r ma have "imit = S_Single (El_C (list_comb uhead args) env' dps)" by simp
    with imit_ok[OF _ _ bt ma] Free show ?thesis by (simp add: closed_def)
  qed (use im in \<open>auto intro: seqinv.Empty\<close>)
  show ?thesis
    by (rule match1_projs_sinv[OF m' tl _ pr st ta Ts' bse]) (use make_projs_props[OF mp] in auto)
qed

subsection \<open>\<open>MATCH\<close>\<close>

lemma match_pair_sinv:
  assumes m: "okW (match_pair cfg env (rb, t, u) dps) s" and st: "strip_comb t = (Var v T, targs)"
    and ta: "\<And>Ts. ok (binder_types env T) Ts \<Longrightarrow> targs_ok env rb t targs Ts"
    and sat: "rsat env rb t u" and nab: "\<not> is_Abs (fst (strip_comb u))"
  shows "seqinv (GE env ((rb, t, u) # dps)) s"
proof -
  from m st obtain Ts cs os occ s' where bt: "ok (binder_types env T) Ts"
    and co: "ok (connected env (u # targs) dps) (cs, os)"
    and "ok (occ_check env v targs u cs) occ"
    and ms: "okW (if occ then match1 cfg (fst v) rb targs u env ((rb, t, u) # dps)
      else mc cfg (fst v) rb targs u env cs) s'"
    and s: "s = S_MapNewDset (v, T) Ts (if occ then [] else os) s'"
    by (auto simp: match_pair_def split: prod.splits)
  note ta' = ta[OF bt]
  have vT: "(v, T) \<in> dvars ((rb, t, u) # dps)" by (simp add: strip_comb_apps[OF st] vars_apps)
  show ?thesis
  proof (cases occ)
    case True
    with ms have "okW (match1 cfg (fst v) rb targs u env ((rb, t, u) # dps)) s'" by simp
    from match1_sinv[OF this _ st ta' nab sat]
    have "seqinv (GS env ((rb, t, u) # dps) Ts T) s'" by simp
    from seqinv.NewDset1[OF dstep_refl vT this] show ?thesis by (simp add: s True)
  next
    case False
    with ms have "okW (mc cfg (fst v) rb targs u env cs) s'" by simp
    from mc_sinv[OF this] sat nab have "seqinv (GC env rb targs Ts u cs (Some t)) s'" by (simp add: msat_def)
    moreover have "dstep env ((rb, t, u) # dps) env ((rb, t, u) # cs @ os)"
      by (rule dstep_set[OF dstep_refl[of env "(rb, t, u) # dps"] refl]) (use connected_set[OF co] in auto)
    ultimately show ?thesis by (simp add: s False seqinv.NewDset[OF _ st ta'])
  qed
qed

text \<open>
  The saturation of a pair: in the type environment of \<^const>\<open>match_sat\<close>, the variable of the
  flexible side has at least as many binder types as arguments, and after the \<open>\<eta>\<close>-expansion
  the rigid side is saturated (\<^const>\<open>rsat\<close>) and not an abstraction.
\<close>

definition msat_ok :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "msat_ok env dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow> \<forall>v T targs Ts. strip_comb t = (Var v T, targs) \<longrightarrow>
    ok (binder_types env T) Ts \<longrightarrow> length targs \<le> length Ts \<and>
    (case eta_expand_dpair (drop (length targs) Ts) dp of (rb', t', u') \<Rightarrow>
      rsat env rb' t' u' \<and> \<not> is_Abs (fst (strip_comb u'))))"

lemma eta_expand_dpair_eq:
  "eta_expand_dpair Es (rb, t, u) =
    (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> bvs (length Es),
     incr_bv (ilength Es) 0 u \<degree>\<degree> bvs (length Es))"
  by (simp add: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq)

lemma match_sat_sinv:
  assumes m: "okW (match_sat cfg env dp dps) s" and ms: "msat_ok env dp"
  shows "seqinv (GE env (dp # dps)) s"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain h targs where st0: "strip_comb t = (h, targs)" by fastforce
  from m st0 obtain v T where h: "h = Var v T" by (cases h) (auto simp: match_sat_def dp)
  note st = st0[unfolded h]
  from m st obtain Ts where bt: "ok (binder_types env T) Ts"
    and mp: "okW (match_pair cfg env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u)) dps) s"
    by (auto simp: match_sat_def dp)
  from ms[unfolded msat_ok_def dp prod.case, rule_format, OF st bt]
  have len: "length targs \<le> length Ts"
    and sat: "case eta_expand_dpair (drop (length targs) Ts) (rb, t, u) of (rb', t', u') \<Rightarrow>
      rsat env rb' t' u' \<and> \<not> is_Abs (fst (strip_comb u'))"
    by (simp_all add: dp)
  define Es where "Es = drop (length targs) Ts"
  define targs' where "targs' = map (incr_bv (ilength Es) 0) targs @ bvs (length Es)"
  define rb' where "rb' = rev (map (\<lambda>T. (STR '''', T)) Es) @ rb"
  define t' where "t' = incr_bv (ilength Es) 0 t \<degree>\<degree> bvs (length Es)"
  define u' where "u' = incr_bv (ilength Es) 0 u \<degree>\<degree> bvs (length Es)"
  have ed: "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
    by (simp add: eta_expand_dpair_eq rb'_def t'_def u'_def)
  have st': "strip_comb t' = (Var v T, targs')" by (simp add: t'_def targs'_def strip_comb_expand[OF st])
  have lt': "length targs' = length Ts" using len by (simp add: targs'_def Es_def)
  have ta: "targs_ok env rb' t' targs' Ts'" if "ok (binder_types env T) Ts'" for Ts'
  proof -
    from that bt have Ts': "Ts' = Ts" by simp
    show ?thesis
      unfolding targs_ok_def Ts'
    proof (intro allI impI)
      fix \<rho> e U assume tsol: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e rb'" and tyt: "e \<turnstile> inst \<rho> t' : U"
      from binder_types_sound[OF bt refl tsol] obtain W where T: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> W" by blast
      from tyt[unfolded strip_comb_apps[OF st'] inst_apps] obtain Us where tyv: "e \<turnstile> inst \<rho> (Var v T) : Us \<Rrightarrow> U"
        and tyas: "e \<tturnstile> map (inst \<rho>) targs' : Us"
        by (rule list_app_typeE)
      have l: "length Us = length (map (tsubst \<rho>) Ts)" using typings_nth[OF tyas] lt' by simp
      from tyv T have "Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> W" by auto
      with funs_eq[OF l] have "Us = map (tsubst \<rho>) Ts" by simp
      with tyas show "e \<tturnstile> map (inst \<rho>) targs' : map (tsubst \<rho>) Ts" by simp
    qed
  qed
  from sat ed have sat': "rsat env rb' t' u'" and nab: "\<not> is_Abs (fst (strip_comb u'))" by (simp_all add: Es_def)
  have "seqinv (GE env ((rb', t', u') # dps)) s"
    by (rule match_pair_sinv[OF mp[folded Es_def, unfolded ed] st' ta sat' nab])
  moreover have "dstep env (dp # dps) env ((rb', t', u') # dps)"
    using dstep_frame[OF dstep_eta_expand[OF st bt len, of rb u], of dps] ed by (simp add: dp Es_def)
  ultimately show ?thesis by (rule seqinv_GE_dstep[OF _ refl])
qed

lemma match_eta_sinv:
  assumes m: "okW (match_eta cfg env dp dps B j tail) s" and tl: "seqinv (GE env (dp # dps)) tail"
    and ms: "\<And>env'. extends env env' \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> msat_ok env' dp"
  shows "seqinv (GE env (dp # dps)) s"
proof (cases "j = 0")
  case True
  with m obtain s' where "okW (match_sat cfg env dp dps) s'" and s: "s = S_Append s' tail"
    by (auto simp: match_eta_def)
  from match_sat_sinv[OF this(1) ms[OF extends_refl refl]] tl show ?thesis by (simp add: s seqinv.Append)
next
  case False
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by fastforce
  note g' = gentvars_props[OF g]
  from okW_handle_CANTUNIFY[OF m[unfolded match_eta_def, simplified False if_False g prod.case]]
  consider (ok) env2 s' where "okW (cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1) env2"
      "okW (match_sat cfg env2 dp dps) s'" "s = S_Append s' tail"
    | (cu) "s = tail"
    by auto
  then show ?thesis
  proof cases
    case (ok env2 s')
    note c = cunify_types_sound[OF ok(1)]
    have ext1: "extends env env1" by (rule extends_tenv_eq) (use g' in simp_all)
    have ext: "extends env env2" by (rule extends_trans[OF ext1 c(2)])
    have te: "tenv env2 = tenv env" using c(1) g'(1) by simp
    have "seqinv (GE env2 (dp # dps)) s'" by (rule match_sat_sinv[OF ok(2) ms[OF ext te]])
    from seqinv_GE_dstep[OF this refl dstep_tenv[OF te ext]] tl show ?thesis by (simp add: ok(3) seqinv.Append)
  qed (use tl in simp)
qed

text \<open>
  The hypothesis of \<open>MATCH\<close>: in every extension of the type environment (by the guesses of
  \<^const>\<open>match_eta\<close>), the pair is saturated in the sense of \<^const>\<open>msat_ok\<close>.
\<close>

definition MATCH_ok :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "MATCH_ok env dp \<longleftrightarrow> (\<forall>env'. extends env env' \<longrightarrow> tenv env' = tenv env \<longrightarrow> msat_ok env' dp)"

theorem MATCH_sound:
  assumes m: "okW (MATCH cfg env dp dps) s" and mo: "MATCH_ok env dp"
  shows "seqinv (GE env (dp # dps)) s"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain h targs where st0: "strip_comb t = (h, targs)" by fastforce
  from m st0 obtain v T where h: "h = Var v T" by (cases h) (auto simp: MATCH_def dp)
  note st = st0[unfolded h]
  from m[unfolded dp] st obtain B where B: "ok (body_type env T) B"
    and r: "okW (if is_TVar B then foldrW (match_eta cfg env (rb, t, u) dps B) (arity_guesses cfg B) S_Empty
      else match_sat cfg env (rb, t, u) dps) s"
    by (auto simp: MATCH_def)
  note r = r[folded dp]
  have ms: "msat_ok env' dp" if "extends env env'" "tenv env' = tenv env" for env'
    using mo that unfolding MATCH_ok_def by blast
  show ?thesis
  proof (cases "is_TVar B")
    case True
    with r have f: "okW (foldrW (match_eta cfg env dp dps B) (arity_guesses cfg B) S_Empty) s" by simp
    have "seqinv (GE env (dp # dps)) b \<longrightarrow> seqinv (GE env (dp # dps)) s'"
      if "okW (foldrW (match_eta cfg env dp dps B) js b) s'" for js b s'
      using that
    proof (induction rule: okW_foldrW_induct)
      case (Cons j js b b1 b')
      show ?case
      proof
        assume "seqinv (GE env (dp # dps)) b"
        with Cons.IH have "seqinv (GE env (dp # dps)) b1" by simp
        from match_eta_sinv[OF Cons.hyps(2) this ms] show "seqinv (GE env (dp # dps)) b'" .
      qed
    qed simp
    with f show ?thesis by (blast intro: seqinv.Empty)
  next
    case False
    with r have "okW (match_sat cfg env dp dps) s" by simp
    from match_sat_sinv[OF this ms[OF extends_refl refl]] show ?thesis .
  qed
qed

end

end
