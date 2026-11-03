section \<open>Soundness of \<open>MATCH\<close>\<close>

theory Unify_Match_Sound
  imports Unify_Simpl_Sound
begin

text \<open>
  The goals of the elements of the sequences (as in the old development): unifiers
  (\<open>GR env0 dps0\<close>), reduced problems (\<open>GE env0 dps0\<close>), copies of a term \<open>u\<close> into a variable
  applied to \<open>targs\<close> of types \<open>Ts\<close> under the binders \<open>rb\<close> (\<open>GC env0 rb targs Ts u dps0\<close>), copies
  of argument lists (\<open>GD\<close>), and single steps of matching (\<open>GS env0 dps0 Ts B\<close>), whose copies
  have type \<open>B\<close> under binders of types \<open>Ts\<close>.
\<close>

datatype goal =
  GR env "dpair list"
| GE env "dpair list"
| GC env binders "pterm list" "ptyp list" pterm "dpair list"
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
  A single step of matching keeps the pairs: the term \<open>u'\<close>, abstracted over \<open>Ts\<close>, has the type
  of the variable of type \<open>T\<close>.
\<close>

definition sstep :: "env \<Rightarrow> dpair list \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "sstep env0 dps0 Ts T u' env dps \<longleftrightarrow> extends env0 env \<and>
    (\<forall>\<rho> env'' X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env env'' \<longrightarrow> wt_env \<rho> env0 \<longrightarrow> dtyped \<rho> dps0 \<longrightarrow>
      vinv \<rho> env0 (X \<union> dvars dps0) \<longrightarrow>
      wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (X \<union> dvars dps \<union> vars u') \<and>
      (\<exists>B. tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> B \<and> (\<forall>e'. pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> u' : B)) \<and>
      \<not> loose_bvar u' (ilength Ts) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow> dsolved \<rho> \<sigma> dps0))"

fun elem_ok :: "goal \<Rightarrow> elem \<Rightarrow> bool" where
  "elem_ok (GR env0 dps0) (El_R env tps) \<longleftrightarrow> dstep env0 dps0 env (tps_dps tps)"
| "elem_ok (GE env0 dps0) (El_E env dps) \<longleftrightarrow> dstep env0 dps0 env dps"
| "elem_ok (GC env0 rb targs Ts u dps0) (El_C u' env dps) \<longleftrightarrow> astep env0 rb targs Ts [u] dps0 [u'] env dps"
| "elem_ok (GD env0 rb targs Ts us dps0) (El_D us' env dps) \<longleftrightarrow> astep env0 rb targs Ts us dps0 us' env dps"
| "elem_ok (GS env0 dps0 Ts T) (El_C u' env dps) \<longleftrightarrow> sstep env0 dps0 Ts T u' env dps"
| "elem_ok _ _ \<longleftrightarrow> False"

text \<open>The arguments of the flexible side have the types \<open>Ts\<close>:\<close>

definition targs_ok :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "targs_ok env rb t targs Ts \<longleftrightarrow> (\<forall>\<rho> e U. tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow>
    e \<turnstile> inst \<rho> t : U \<longrightarrow> e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts)"

text \<open>A projection on the argument \<open>targ\<close> of the copy goal, after the type unification:\<close>

definition proj_ok :: "env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> ptyp list \<Rightarrow>
    ptyp list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "proj_ok env rb targs Ts u env' Ts' Us head targ \<longleftrightarrow> extends env env' \<and> tenv env' = tenv env \<and>
    (\<exists>j. head = Bound j \<and> 0 \<le> j \<and> j < ilength targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j)) \<and>
    (\<forall>\<rho> e U. tsol (tyenv env') \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow> e \<turnstile> inst \<rho> u : U \<longrightarrow>
      e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts \<longrightarrow>
      map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts \<and> e \<turnstile> inst \<rho> targ : map (tsubst \<rho>) Us \<Rrightarrow> U)"

inductive sinv :: "goal \<Rightarrow> seq \<Rightarrow> bool" where
  Empty: "sinv G S_Empty"
| Single: "elem_ok G x \<Longrightarrow> sinv G (S_Single x)"
| Append: "sinv G xq \<Longrightarrow> sinv G yq \<Longrightarrow> sinv G (S_Append xq yq)"
| AddUnify: "dstep env0 dps0 env dps \<Longrightarrow> sinv (GR env0 dps0) reseq \<Longrightarrow>
    sinv (GR env0 dps0) (S_AddUnify td env dps reseq)"
| ItRight: "sinv (GE env0 dps0) xq \<Longrightarrow> sinv (GR env0 dps0) yq \<Longrightarrow> sinv (GR env0 dps0) (S_ItRight td xq yq)"
| NewDset: "dstep env0 dps0 env1 ((rb, t, u) # dps1) \<Longrightarrow> strip_comb t = (Var v T, targs) \<Longrightarrow>
    targs_ok env1 rb t targs Ts \<Longrightarrow> sinv (GC env1 rb targs Ts u dps1) xq \<Longrightarrow>
    sinv (GE env0 dps0) (S_MapNewDset (v, T) Ts xq)"
| NewDset1: "dstep env0 dps0 env1 dps1 \<Longrightarrow> (v, T) \<in> dvars dps1 \<Longrightarrow> sinv (GS env1 dps1 Ts T) xq \<Longrightarrow>
    sinv (GE env0 dps0) (S_MapNewDset (v, T) Ts xq)"
| MapAbs: "sinv (GC env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) (Ts @ [T]) body dps0) xq \<Longrightarrow>
    sinv (GC env0 rb targs Ts (Abs a T body) dps0) (S_MapAbs a T xq)"
| Proj: "proj_ok env rb targs Ts u env' Ts' Us head targ \<Longrightarrow> sinv (GC env rb targs Ts u dps) tail \<Longrightarrow>
    sinv (GC env rb targs Ts u dps) (S_Proj vname env' Ts' Us targs rb u dps head targ tail)"
| MapJoin: "closed uhead \<Longrightarrow> vars uhead = {} \<Longrightarrow> sinv (GD env0 rb targs Ts uargs dps0) xq \<Longrightarrow>
    sinv (GC env0 rb targs Ts (uhead \<degree>\<degree> uargs) dps0) (S_MapJoin uhead xq)"
| Maps: "sinv (GD env0 rb targs Ts uargs dps0) xq \<Longrightarrow>
    sinv (GD env0 rb targs Ts (uarg # uargs) dps0) (S_Maps vname rb targs uarg xq)"
| MapCons: "astep env0 rb targs Ts uargs dps0 uargs' env dps \<Longrightarrow> tconv env rb uarg u2 \<Longrightarrow>
    sinv (GC env rb targs Ts u2 dps) xq \<Longrightarrow> sinv (GD env0 rb targs Ts (uarg # uargs) dps0) (S_MapCons uargs' xq)"

text \<open>Reduced problems compose with steps before them:\<close>

lemma sinv_GE_dstep: "sinv G s \<Longrightarrow> G = GE env1 dps1 \<Longrightarrow> dstep env0 dps0 env1 dps1 \<Longrightarrow> sinv (GE env0 dps0) s"
proof (induction arbitrary: env1 dps1 rule: sinv.induct)
  case (Single G x)
  then show ?case by (cases x) (auto intro!: sinv.Single intro: dstep_trans)
qed (auto intro: sinv.intros dstep_trans)


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

end

end
