section \<open>Problems with Type Variables: Soundness of \<open>MATCH\<close>\<close>

theory Unify_Poly_Match
  imports Unify_Poly_Shape
begin

context csig
begin

text \<open>
  The invariant of sequences of theory \<^theory>\<open>Pure_Unify_Correctness.Unify_Match\<close>, for problems
  whose types contain type variables. Terms are well-formed in the sense of
  \<^theory>\<open>Pure_Unify_Correctness.Unify_Poly_Simpl\<close>, the environments only grow, together with
  their type environments (\<^const>\<open>pextends\<close>), and the semantics ranges over the substitutions that
  satisfy an environment and respect its type environment (\<^const>\<open>psat\<close>).

  The guesses of arities are sound because they only extend the type environment: a substitution
  that respects the extended type environment respects the original one. The copies are
  semantically the same as in the monomorphic case; the types only enter through the
  well-formedness of the new terms.
\<close>


subsection \<open>Elements\<close>

definition swf_cp :: "(name \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pterm \<Rightarrow> bool" where
  "swf_cp ar k u' \<longleftrightarrow> proper u' \<and> twft ar u' \<and> no_loose_bound (tr u') k"

definition pwf_state :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "pwf_state ar env0 env dps \<longleftrightarrow> pextends env0 env \<and> swf_env ar env \<and> (\<forall>dp\<in>set dps. swf_dp ar dp)"

definition preduces :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "preduces ar env0 dps0 env dps \<longleftrightarrow> pwf_state ar env0 env dps \<and>
    (\<forall>\<sigma>. psat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow> dsolved_all \<sigma> dps0)"

definition punifier :: "env \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "punifier env0 dps0 env tps \<longleftrightarrow> pextends env0 env \<and>
    (\<forall>\<sigma>. psat \<sigma> env \<longrightarrow>
      (\<forall>(t, u)\<in>set tps. mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)) \<longrightarrow> dsolved_all \<sigma> dps0)"

definition pcopy_ok :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> dpair list \<Rightarrow>
    pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "pcopy_ok ar env0 rb targs u dps0 u' env dps \<longleftrightarrow> pwf_state ar env0 env dps \<and>
    swf_cp ar (length targs) u' \<and>
    (\<forall>\<sigma>. psat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow>
      dsolvedB \<sigma> rb (cpy targs u') (tr u) \<and> dsolved_all \<sigma> dps0)"

definition pargs_ok :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> dpair list \<Rightarrow>
    pterm list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "pargs_ok ar env0 rb targs uargs dps0 uargs' env dps \<longleftrightarrow> pwf_state ar env0 env dps \<and>
    length uargs' = length uargs \<and> (\<forall>a'\<in>set uargs'. swf_cp ar (length targs) a') \<and>
    (\<forall>\<sigma>. psat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow>
      list_all2 (\<lambda>a' a. dsolvedB \<sigma> rb (cpy targs a') (tr a)) uargs' uargs \<and> dsolved_all \<sigma> dps0)"

fun pelem_ok :: "(name \<Rightarrow> nat) \<Rightarrow> goal \<Rightarrow> elem \<Rightarrow> bool" where
  "pelem_ok ar (GR env0 dps0) (El_R env tps) \<longleftrightarrow> punifier env0 dps0 env tps"
| "pelem_ok ar (GE env0 dps0) (El_E env dps) \<longleftrightarrow> preduces ar env0 dps0 env dps"
| "pelem_ok ar (GC env0 rb targs u dps0) (El_C u' env dps) \<longleftrightarrow> pcopy_ok ar env0 rb targs u dps0 u' env dps"
| "pelem_ok ar (GD env0 rb targs uargs dps0) (El_D uargs' env dps) \<longleftrightarrow>
    pargs_ok ar env0 rb targs uargs dps0 uargs' env dps"
| "pelem_ok ar (GS env0 dps0 k) (El_C u' env dps) \<longleftrightarrow> pwf_state ar env0 env dps \<and> swf_cp ar k u' \<and>
    (\<forall>\<sigma>. psat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow> dsolved_all \<sigma> dps0)"
| "pelem_ok ar _ _ \<longleftrightarrow> False"


subsection \<open>The invariant of sequences\<close>

text \<open>
  The rules follow those of \<^const>\<open>sinv\<close>. A projection (\<^const>\<open>S_Proj\<close>) carries the environment
  after the unification of the types, which extends the environment of the goal.
\<close>

inductive psinv :: "(name \<Rightarrow> nat) \<Rightarrow> goal \<Rightarrow> seq \<Rightarrow> bool" for ar where
  Empty: "psinv ar G S_Empty"
| Single: "pelem_ok ar G x \<Longrightarrow> psinv ar G (S_Single x)"
| AddUnify: "preduces ar env0 dps0 env dps \<Longrightarrow> psinv ar (GR env0 dps0) reseq \<Longrightarrow>
    psinv ar (GR env0 dps0) (S_AddUnify td env dps reseq)"
| ItRight: "psinv ar (GE env0 dps0) xq \<Longrightarrow> psinv ar (GR env0 dps0) yq \<Longrightarrow>
    psinv ar (GR env0 dps0) (S_ItRight td xq yq)"
| MapNewDset: "preduces ar env0 dps0 env1 ((rb, t, u) # dps1) \<Longrightarrow>
    strip_comb t = (Var v T, targs) \<Longrightarrow> length Ts = length targs \<Longrightarrow> \<forall>U\<in>set Ts. wft ar U \<Longrightarrow>
    psinv ar (GC env1 rb targs u dps1) xq \<Longrightarrow> psinv ar (GE env0 dps0) (S_MapNewDset (v, T) Ts xq)"
| MapNewDset1: "preduces ar env0 dps0 env1 dps1 \<Longrightarrow> wft ar T \<Longrightarrow> \<forall>U\<in>set Ts. wft ar U \<Longrightarrow>
    psinv ar (GS env1 dps1 (length Ts)) xq \<Longrightarrow> psinv ar (GE env0 dps0) (S_MapNewDset (v, T) Ts xq)"
| MapAbs: "psinv ar (GC env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body dps0) xq \<Longrightarrow>
    wft ar T \<Longrightarrow> \<forall>t\<in>set targs. proper t \<Longrightarrow>
    psinv ar (GC env0 rb targs (Abs b T' body) dps0) (S_MapAbs a T xq)"
| Proj: "pextends env env' \<Longrightarrow> swf_env ar env' \<Longrightarrow> \<forall>dp\<in>set dps. swf_dp ar dp \<Longrightarrow> sbinders ar rb \<Longrightarrow>
    swf_tm ar rb u \<Longrightarrow> \<forall>t\<in>set targs. swf_tm ar rb t \<Longrightarrow> 0 \<le> j \<Longrightarrow> nat_of_integer j < length targs \<Longrightarrow>
    targ = targs ! (length targs - 1 - nat_of_integer j) \<Longrightarrow> length Ts = length targs \<Longrightarrow>
    \<forall>U\<in>set Ts. wft ar U \<Longrightarrow> \<forall>U\<in>set Us. wft ar U \<Longrightarrow>
    psinv ar (GC env rb targs u dps) tail \<Longrightarrow>
    psinv ar (GC env rb targs u dps) (S_Proj vname env' Ts Us targs rb u dps (Bound j) targ tail)"
| MapJoin: "strip_comb u = (uhead, uargs) \<Longrightarrow> no_loose_bound (tr uhead) 0 \<Longrightarrow> twft ar uhead \<Longrightarrow>
    proper uhead \<Longrightarrow> psinv ar (GD env0 rb targs uargs dps0) xq \<Longrightarrow> psinv ar (GC env0 rb targs u dps0) (S_MapJoin uhead xq)"
| Maps: "psinv ar (GD env0 rb targs uargs dps0) xq \<Longrightarrow> sbinders ar rb \<Longrightarrow> swf_tm ar rb uarg \<Longrightarrow>
    \<forall>t\<in>set targs. swf_tm ar rb t \<Longrightarrow>
    psinv ar (GD env0 rb targs (uarg # uargs) dps0) (S_Maps vname rb targs uarg xq)"
| MapCons: "pargs_ok ar env0 rb targs uargs dps0 uargs' env dps \<Longrightarrow>
    psinv ar (GC env rb targs u2 dps) xq \<Longrightarrow> env \<Turnstile>\<^sub>p rlist_abs rb uarg \<approx> rlist_abs rb u2 \<Longrightarrow>
    psinv ar (GD env0 rb targs (uarg # uargs) dps0) (S_MapCons uargs' xq)"
| Append: "psinv ar G xq \<Longrightarrow> psinv ar G yq \<Longrightarrow> psinv ar G (S_Append xq yq)"


subsection \<open>Well-formedness\<close>

lemma swf_tm_incr:
  assumes "swf_tm ar rb t"
  shows "swf_tm ar ((a, T) # rb) (incr_boundvars 1 t)"
proof -
  from assms have p: "proper t" by (simp add: swf_tm_def)
  have "tr (incr_boundvars 1 t) = lift (tr t) 0" by (rule tr_incr_boundvars1[OF p])
  with assms show ?thesis
    by (auto simp: swf_tm_def incr_boundvars_def proper_incr_bv twft_incr_bv integer_reps
        intro: no_loose_bound_lift)
qed

lemma swf_tm_Bound0: "swf_tm ar ((a, T) # rb) (Bound 0)"
  by (simp add: swf_tm_def)

lemma swf_tm_list_comb:
  "swf_tm ar rb (list_comb h ts) \<longleftrightarrow> swf_tm ar rb h \<and> (\<forall>t\<in>set ts. swf_tm ar rb t)"
  by (auto simp: swf_tm_def proper_list_comb twft_list_comb tr_list_comb no_loose_bound_list_app)

lemma swf_tm_strip_comb:
  "strip_comb u = (h, us) \<Longrightarrow> swf_tm ar rb u \<Longrightarrow> swf_tm ar rb h \<and> (\<forall>t\<in>set us. swf_tm ar rb t)"
  using strip_comb_list_comb swf_tm_list_comb by metis

lemma twft_combound: "twft ar (combound t n k) \<longleftrightarrow> twft ar t"
  by (induction k arbitrary: n) simp_all

lemma swf_cp_combound:
  "twft ar G \<Longrightarrow> no_loose_bound (tr G) 0 \<Longrightarrow> proper G \<Longrightarrow> swf_cp ar k (combound G 0 k)"
  by (auto simp: swf_cp_def proper_combound twft_combound no_loose_bound_tr_combound
      intro: no_loose_bound_mono)

lemma swf_cp_list_comb: "swf_cp ar k (list_comb h ts) \<longleftrightarrow> swf_cp ar k h \<and> (\<forall>t\<in>set ts. swf_cp ar k t)"
  by (auto simp: swf_cp_def proper_list_comb twft_list_comb tr_list_comb no_loose_bound_list_app)

lemma wft_foldr_fun_type:
  "\<forall>U\<in>set Ts. wft ar U \<Longrightarrow> wft ar B \<Longrightarrow> wft ar (foldr fun_type Ts B)"
  by (induction Ts) (simp_all add: tarity_def)

lemma pwf_stateD:
  "pwf_state ar env0 env dps \<Longrightarrow> pextends env0 env"
  "pwf_state ar env0 env dps \<Longrightarrow> swf_env ar env"
  "pwf_state ar env0 env dps \<Longrightarrow> dp \<in> set dps \<Longrightarrow> swf_dp ar dp"
  by (simp_all add: pwf_state_def)

lemma pwf_state_pextends:
  "pwf_state ar env1 env dps \<Longrightarrow> pextends env0 env1 \<Longrightarrow> pwf_state ar env0 env dps"
  by (auto simp: pwf_state_def intro: pextends_trans)

lemma genvar_pextends: "genvar a env T = (env', G) \<Longrightarrow> pextends env env'"
  by (simp add: pextends_def genvar_extends genvar_simps)

lemma genvar_swf_env: "genvar a env T = (env', G) \<Longrightarrow> swf_env ar env \<Longrightarrow> swf_env ar env'"
  by (simp add: swf_env_def genvar_simps)

lemma make_args_pextends: "make_args name Ts env Us = (env', args) \<Longrightarrow> pextends env env'"
  using make_args_props(1,2) by (simp add: pextends_def extends_def)

lemma make_args_swf_env: "make_args name Ts env Us = (env', args) \<Longrightarrow> swf_env ar env \<Longrightarrow> swf_env ar env'"
  using make_args_props(1,2) by (simp add: swf_env_def)

lemma make_args_swf_cp:
  assumes "make_args name Ts env Us = (env', args)" "\<forall>U\<in>set Ts. wft ar U" "\<forall>U\<in>set Us. wft ar U"
  shows "\<forall>a\<in>set args. swf_cp ar (length Ts) a"
proof
  fix a assume "a \<in> set args"
  then obtain i where i: "i < length args" "a = args ! i" by (auto simp: in_set_conv_nth)
  from make_args_props(3)[OF assms(1)] i have l: "length args = length Us"
    and "\<exists>x. a = combound (Var x (foldr fun_type Ts (Us ! i))) 0 (length Ts)"
    by (auto simp: list_all2_conv_all_nth)
  then obtain x where a: "a = combound (Var x (foldr fun_type Ts (Us ! i))) 0 (length Ts)" by blast
  have "Us ! i \<in> set Us" using i l by simp
  with wft_foldr_fun_type[of Ts ar "Us ! i"] assms(2,3) a show "swf_cp ar (length Ts) a"
    by (auto intro: swf_cp_combound)
qed

lemma gentvars_simps:
  assumes "gentvars p env = (env', Cs)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "length Cs = p" "\<forall>C\<in>set Cs. wft ar C"
  using assms by (auto simp: gentvars_def split: if_splits env.splits)

lemma gentvars_pextends: "gentvars p env = (env', Cs) \<Longrightarrow> pextends env env'"
  using gentvars_simps(1,2) by (simp add: pextends_def extends_def)

lemma gentvars_swf_env: "gentvars p env = (env', Cs) \<Longrightarrow> swf_env ar env \<Longrightarrow> swf_env ar env'"
  using gentvars_simps(1,2) by (simp add: swf_env_def)

text \<open>Copies of argument lists.\<close>

lemma copyargs_psound:
  "swf_env ar env \<Longrightarrow> \<forall>dp\<in>set dps. swf_dp ar dp \<Longrightarrow> sbinders ar rb \<Longrightarrow>
    \<forall>t\<in>set uargs. swf_tm ar rb t \<Longrightarrow> \<forall>t\<in>set targs. swf_tm ar rb t \<Longrightarrow>
    psinv ar (GD env rb targs uargs dps) (copyargs vname rb targs env dps uargs)"
proof (induction uargs)
  case Nil
  then show ?case
    by (auto intro!: psinv.Single simp: pargs_ok_def pwf_state_def)
next
  case (Cons uarg uargs)
  then show ?case by (auto intro!: psinv.Maps)
qed


subsection \<open>Saturation of pairs\<close>

text \<open>The \<open>\<eta>\<close>-expansion of a pair by bound variables is semantically the identity.\<close>

lemma lift_list_apps: "lift (h \<degree>\<degree> A) k = lift h k \<degree>\<degree> map (\<lambda>t. lift t k) A"
  by (induction A arbitrary: h) simp_all

lemma Abs_m_eta_liftn: "Abs_m j (liftn j s 0 \<degree>\<degree> map BVar (downs j)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
proof (induction j)
  case (Suc j)
  have "liftn (Suc j) s 0 \<degree>\<degree> map BVar (downs (Suc j)) =
      lift (liftn j s 0 \<degree>\<degree> map BVar (downs j)) 0 \<degree> BVar 0"
    unfolding downs_Suc by (simp add: lift_list_apps comp_def)
  then have "Abs_m (Suc j) (liftn (Suc j) s 0 \<degree>\<degree> map BVar (downs (Suc j))) =
      Abs_m j (dB.Abs (lift (liftn j s 0 \<degree>\<degree> map BVar (downs j)) 0 \<degree> BVar 0))"
    by (simp add: Abs_m)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m j (liftn j s 0 \<degree>\<degree> map BVar (downs j))"
    by (rule equiv_Abs_m[OF eta_into_equiv[OF eta_Abs_lift]])
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" by (rule Suc.IH)
  finally show ?case .
qed simp

lemma rlist_abs_append: "rlist_abs (xs @ rb) t = rlist_abs rb (rlist_abs xs t)"
  by (induction xs t rule: rlist_abs.induct) simp_all

lemma tr_incr_boundvars_nat:
  "proper t \<Longrightarrow> tr (incr_boundvars (integer_of_nat j) t) = liftn j (tr t) 0"
  by (auto simp: incr_boundvars_def tr_incr_bv integer_reps)

abbreviation eta_bvs :: "nat \<Rightarrow> pterm list" where
  "eta_bvs j \<equiv> map (\<lambda>i. Bound (integer_of_nat i)) (downs j)"

abbreviation eta_binder :: "ptyp list \<Rightarrow> binders" where
  "eta_binder Es \<equiv> rev (map (\<lambda>T. (STR '''', T)) Es)"

lemma eta_expand_dpair_simp:
  "eta_expand_dpair Es (rb, t, u) =
    (eta_binder Es @ rb,
     list_comb (incr_boundvars (integer_of_nat (length Es)) t) (eta_bvs (length Es)),
     list_comb (incr_boundvars (integer_of_nat (length Es)) u) (eta_bvs (length Es)))"
  by (simp add: eta_expand_dpair_def Let_def)

lemma tr_eta_expand:
  assumes "proper t"
  shows "tr (rlist_abs (eta_binder Es @ rb)
      (list_comb (incr_boundvars (integer_of_nat (length Es)) t) (eta_bvs (length Es))))
    \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (rlist_abs rb t)"
proof -
  have "tr (list_comb (incr_boundvars (integer_of_nat (length Es)) t) (eta_bvs (length Es))) =
    liftn (length Es) (tr t) 0 \<degree>\<degree> map BVar (downs (length Es))"
    by (simp add: tr_list_comb tr_incr_boundvars_nat[OF assms] comp_def)
  then show ?thesis
    by (simp add: rlist_abs_append tr_rlist_abs equiv_Abs_m[OF Abs_m_eta_liftn])
qed

lemma dsolved_eta_expand_dpair:
  assumes "proper t" "proper u" "closed_on UNIV \<sigma>"
  shows "dsolved \<sigma> (eta_expand_dpair Es (rb, t, u)) \<longleftrightarrow> dsolved \<sigma> (rb, t, u)"
proof -
  note et = mk_subst_equiv[OF tr_eta_expand[OF assms(1), of Es rb] assms(3)]
  note eu = mk_subst_equiv[OF tr_eta_expand[OF assms(2), of Es rb] assms(3)]
  show ?thesis
    unfolding eta_expand_dpair_simp dsolved_def prod.case
    using et eu by (blast intro: equiv_trans equiv_sym)
qed

text \<open>Well-formedness and shape of the expanded pair:\<close>

lemma incr_bv_list_comb:
  "incr_bv inc lev (list_comb h ts) = list_comb (incr_bv inc lev h) (map (incr_bv inc lev) ts)"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma incr_boundvars_list_comb:
  "incr_boundvars inc (list_comb h ts) = list_comb (incr_boundvars inc h) (map (incr_boundvars inc) ts)"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def incr_boundvars_def)

lemma list_comb_append: "list_comb h (ts @ us) = list_comb (list_comb h ts) us"
  by (simp add: list_comb_def)

lemma strip_comb_Var_list_comb: "strip_comb (list_comb (Var v T) ts) = (Var v T, ts)"
  by (rule strip_comb_list_comb_eq) simp

lemma head_of_list_comb_eq: "head_of (list_comb h ts) = head_of h"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma head_of_incr_bv_eq: "head_of (incr_bv inc lev t) = incr_bv inc lev (head_of t)"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma no_loose_bound_liftn: "no_loose_bound t n \<Longrightarrow> no_loose_bound (liftn j t 0) (n + j)"
  by (induction j) (simp_all add: no_loose_bound_lift)

lemma swf_tm_eta_expand:
  assumes "swf_tm ar rb t"
  shows "swf_tm ar (eta_binder Es @ rb)
    (list_comb (incr_boundvars (integer_of_nat (length Es)) t) (eta_bvs (length Es)))"
proof -
  from assms have p: "proper t" "twft ar t" "no_loose_bound (tr t) (length rb)" by (simp_all add: swf_tm_def)
  have "proper (incr_boundvars (integer_of_nat (length Es)) t)"
    using p(1) by (simp add: incr_boundvars_def proper_incr_bv integer_reps)
  moreover have "no_loose_bound (tr (incr_boundvars (integer_of_nat (length Es)) t)) (length rb + length Es)"
    using no_loose_bound_liftn[OF p(3)] by (simp add: tr_incr_boundvars_nat[OF p(1)])
  ultimately show ?thesis
    using p(2) by (auto simp: swf_tm_def proper_list_comb twft_list_comb twft_incr_boundvars tr_list_comb
        no_loose_bound_list_app integer_reps add.commute)
qed

lemma swf_dp_eta_expand:
  "swf_dp ar (rb, t, u) \<Longrightarrow> \<forall>E\<in>set Es. wft ar E \<Longrightarrow> swf_dp ar (eta_expand_dpair Es (rb, t, u))"
  by (auto simp: eta_expand_dpair_simp sbinders_def intro: swf_tm_eta_expand)

lemma eta_expand_dpair_shape:
  assumes "strip_comb t = (Var v T, targs)" "hnf u" "\<not> is_Abs u"
    "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
  shows "strip_comb t' = (Var v T, map (incr_boundvars (integer_of_nat (length Es))) targs @
      eta_bvs (length Es))" "hnf u'" "\<not> is_Abs u'"
proof -
  let ?j = "integer_of_nat (length Es)"
  have t: "t = list_comb (Var v T) targs" by (rule strip_comb_list_comb[OF assms(1)])
  have "incr_boundvars ?j (Var v T) = Var v T" by (simp add: incr_boundvars_def)
  then have "t' = list_comb (Var v T) (map (incr_boundvars ?j) targs @ eta_bvs (length Es))"
    using assms(4) t by (simp add: eta_expand_dpair_simp incr_boundvars_list_comb list_comb_append)
  then show "strip_comb t' = (Var v T, map (incr_boundvars ?j) targs @ eta_bvs (length Es))"
    by (simp add: strip_comb_Var_list_comb)
  have u': "u' = list_comb (incr_boundvars ?j u) (eta_bvs (length Es))"
    using assms(4) by (simp add: eta_expand_dpair_simp)
  have nAbs: "\<not> is_Abs (head_of u)" using assms(2,3) by (cases u) simp_all
  have hd: "head_of u' = incr_boundvars ?j (head_of u)"
    unfolding u' head_of_list_comb_eq by (simp add: incr_boundvars_def head_of_incr_bv_eq)
  have "\<not> is_Abs (head_of u')" unfolding hd using nAbs
    by (cases "head_of u") (simp_all add: incr_boundvars_def)
  then show "hnf u'" "\<not> is_Abs u'"
    by (cases u'; simp)+
qed


subsection \<open>Projections and imitation\<close>

lemma foldrW_inv:
  "okW (foldrW f xs b) s \<Longrightarrow> P b \<Longrightarrow> (\<And>x t s. x \<in> set xs \<Longrightarrow> okW (f x t) s \<Longrightarrow> P t \<Longrightarrow> P s) \<Longrightarrow> P s"
proof (induction xs arbitrary: s)
  case (Cons x xs)
  from Cons.prems(1) obtain t where f: "okW (foldrW f xs b) t" and s: "okW (f x t) s" by auto
  have "P t" by (rule Cons.IH[OF f Cons.prems(2)], rule Cons.prems(3)) simp_all
  from Cons.prems(3)[OF _ s this] show ?case by simp
qed simp

lemma swf_env_types:
  "swf_env ar env \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> twf ar (tyenv env') \<Longrightarrow> swf_env ar env'"
  by (simp add: swf_env_def)

lemma cunify_types_swf:
  assumes "okW (cunify_types alg T U env) env'" "swf_env ar env" "wft ar T" "wft ar U"
  shows "pextends env env'" "swf_env ar env'"
    "tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
  using cunify_types_psound[OF assms(1) swf_envD(1)[OF assms(2)] assms(3,4)] assms(2)
  by (auto intro: swf_env_types)

lemma proj_unify_swf:
  assumes "okW (proj_unify cfg base bary Cs env) env'" "swf_env ar env" "wft ar base" "wft ar bary"
    "\<forall>C\<in>set Cs. wft ar C"
  shows "pextends env env'" "swf_env ar env'"
proof -
  have tw: "twf ar (tyenv env)" by (rule swf_envD(1)[OF assms(2)])
  have "pextends env env' \<and> tenv env' = tenv env \<and> twf ar (tyenv env')"
  proof (cases "Cs = []")
    case True
    show ?thesis
    proof (cases "cfg_trace_types cfg")
      case tt: True
      with True assms(1) have "okW (test_unify_types (cfg_alg cfg) base bary env) env'"
        by (simp add: proj_unify_def)
      from test_unify_types_psound[OF this tw assms(3,4)] show ?thesis by simp
    next
      case False
      with True assms(1) have "okW (cunify_types (cfg_alg cfg) base bary env) env'"
        by (simp add: proj_unify_def)
      from cunify_types_psound[OF this tw assms(3,4)] show ?thesis by simp
    qed
  next
    case False
    with assms(1) have "okW (cunify_types (cfg_alg cfg) bary (foldr fun_type Cs base) env) env'"
      by (simp add: proj_unify_def)
    from cunify_types_psound[OF this tw assms(4) wft_foldr_fun_type[OF assms(5,3)]] show ?thesis by simp
  qed
  with assms(2) show "pextends env env'" "swf_env ar env'" by (auto intro: swf_env_types)
qed

lemma okW_CANTUNIFY_returnW:
  "okW (case e of CANTUNIFY \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> y = x"
  by (cases e) auto

lemma projenv_psound:
  assumes "okW (projenv cfg vname rb targs u env dps base Ts (Bound j) (Us, bary) targ p tail) s"
    "psinv ar (GC env rb targs u dps) tail" "wft ar base" "wft ar bary"
    "swf_env ar env" "\<forall>dp\<in>set dps. swf_dp ar dp" "sbinders ar rb" "swf_tm ar rb u"
    "\<forall>t\<in>set targs. swf_tm ar rb t" "0 \<le> j" "nat_of_integer j < length targs"
    "targ = targs ! (length targs - 1 - nat_of_integer j)" "length Ts = length targs"
    "\<forall>U\<in>set Ts. wft ar U" "\<forall>U\<in>set Us. wft ar U"
  shows "psinv ar (GC env rb targs u dps) s"
proof -
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  have wC: "\<forall>C\<in>set Cs. wft ar C" by (rule gentvars_simps(4)[OF g])
  have w0: "swf_env ar env0" by (rule gentvars_swf_env[OF g assms(5)])
  let ?m = "proj_unify cfg base bary Cs env0"
  let ?r = "\<lambda>env'. S_Proj vname env' Ts (Us @ Cs) targs rb u dps (Bound j) targ tail"
  have "okW (handleW (do {env' \<leftarrow> ?m; returnW (?r env')})
      (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)) s"
    using assms(1) g by (simp add: projenv_def)
  then have "okW (do {env' \<leftarrow> ?m; returnW (?r env')}) s \<or>
    (\<exists>e. okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s)"
    unfolding okW_handleW by blast
  then show ?thesis
  proof
    assume "okW (do {env' \<leftarrow> ?m; returnW (?r env')}) s"
    then obtain env' where m: "okW ?m env'" and s: "s = ?r env'" by auto
    note pu = proj_unify_swf[OF m w0 assms(3,4) wC]
    have ext: "pextends env env'" by (rule pextends_trans[OF gentvars_pextends[OF g] pu(1)])
    have "\<forall>U\<in>set (Us @ Cs). wft ar U" using assms(15) wC by auto
    with s ext pu(2) assms show ?thesis by (auto intro: psinv.Proj)
  next
    assume "\<exists>e. okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s"
    then obtain e where "okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s" by blast
    from okW_CANTUNIFY_returnW[OF this] assms(2) show ?thesis by simp
  qed
qed

lemma matchfun_psound:
  "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) s \<Longrightarrow>
    \<forall>(bv, T, targ)\<in>set projs. \<exists>j. bv = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length targs \<and>
      targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T \<in> set Ts \<Longrightarrow>
    wft ar base \<Longrightarrow> \<forall>U\<in>set Ts. wft ar U \<Longrightarrow> length Ts = length targs \<Longrightarrow>
    swf_env ar env \<Longrightarrow> \<forall>dp\<in>set dps. swf_dp ar dp \<Longrightarrow> sbinders ar rb \<Longrightarrow> swf_tm ar rb u \<Longrightarrow>
    \<forall>t\<in>set targs. swf_tm ar rb t \<Longrightarrow> strip_comb u = (uhead, uargs) \<Longrightarrow>
    psinv ar (GC env rb targs u dps) s"
proof (induction projs arbitrary: s)
  case Nil
  from swf_tm_strip_comb[OF Nil.prems(11,9)]
  have hd: "swf_tm ar rb uhead" and as: "\<forall>t\<in>set uargs. swf_tm ar rb t" by simp_all
  note ca = copyargs_psound[OF Nil.prems(6,7,8) as Nil.prems(10), of vname]
  show ?case
  proof (cases uhead)
    case (Const a T)
    with Nil.prems(1) have "s = S_MapJoin uhead (copyargs vname rb targs env dps uargs)" by simp
    with Const hd ca Nil.prems(11) show ?thesis by (auto simp: swf_tm_def intro: psinv.MapJoin)
  next
    case (Free a T)
    with Nil.prems(1) have "s = S_MapJoin uhead (copyargs vname rb targs env dps uargs)" by simp
    with Free hd ca Nil.prems(11) show ?thesis by (auto simp: swf_tm_def intro: psinv.MapJoin)
  qed (use Nil.prems(1) in \<open>auto intro: psinv.Empty\<close>)
next
  case (Cons p projs)
  obtain bv T targ where p: "p = (bv, T, targ)" by (cases p)
  with Cons.prems(2) obtain j where j: "bv = Bound j" "0 \<le> j" "nat_of_integer j < length targs"
    "targ = targs ! (length targs - 1 - nat_of_integer j)" "T \<in> set Ts" by auto
  from Cons.prems(1) p obtain Usb tail where st: "ok (strip_type env T) Usb"
    and tl: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) tail"
    and pe: "okW (foldrW (projenv cfg vname rb targs u env dps base Ts bv Usb targ) (arity_guesses cfg (snd Usb)) tail) s"
    by auto
  obtain Us bary where Usb: "Usb = (Us, bary)" by (cases Usb)
  have wT: "wft ar T" using Cons.prems(4) j(5) by blast
  have sw: "\<forall>U\<in>set Us. wft ar U" "wft ar bary"
    using strip_type_wft[OF st[unfolded Usb] swf_envD(1)[OF Cons.prems(6)] wT] by simp_all
  have "psinv ar (GC env rb targs u dps) tail"
    using Cons.IH[OF tl] Cons.prems(2-11) by simp
  then show ?case
  proof (rule foldrW_inv[OF pe])
    fix p' t s'
    assume "okW (projenv cfg vname rb targs u env dps base Ts bv Usb targ p' t) s'"
      "psinv ar (GC env rb targs u dps) t"
    from projenv_psound[OF this(1)[unfolded Usb j(1)] this(2) Cons.prems(3) sw(2) Cons.prems(6-10) j(2-4)
        Cons.prems(5,4) sw(1)]
    show "psinv ar (GC env rb targs u dps) s'" .
  qed
qed


subsection \<open>Copies\<close>

lemma mapM_fastype_wft:
  assumes "okW (liftM (mapM (fastype env rb) targs)) Ts" "twf ar (tyenv env)" "sbinders ar rb"
    "\<forall>t\<in>set targs. swf_tm ar rb t"
  shows "length Ts = length targs" "\<forall>U\<in>set Ts. wft ar U"
proof -
  from assms(1) have l2: "list_all2 (\<lambda>x y. ok (fastype env rb x) y) targs Ts" by (simp add: ok_mapM)
  then show lTs: "length Ts = length targs" by (simp add: list_all2_conv_all_nth)
  show "\<forall>U\<in>set Ts. wft ar U"
  proof
    fix U assume "U \<in> set Ts"
    then obtain i where i: "i < length Ts" "U = Ts ! i" by (auto simp: in_set_conv_nth)
    with l2 have "ok (fastype env rb (targs ! i)) U" by (simp add: list_all2_conv_all_nth)
    moreover have "twft ar (targs ! i)" using assms(4) i lTs by (simp add: swf_tm_def)
    ultimately show "wft ar U" by (rule fastype_wft[OF _ assms(2,3)])
  qed
qed

text \<open>A new variable applied to the arguments, with a new pair for the rigid term:\<close>

lemma new_flex_copy:
  assumes "genvar a env (foldr fun_type Ts A) = (env', newhd)" "\<forall>U\<in>set Ts. wft ar U" "wft ar A"
    "length Ts = length targs" "swf_env ar env" "\<forall>dp\<in>set dps. swf_dp ar dp" "sbinders ar rb"
    "swf_tm ar rb u" "\<forall>t\<in>set targs. swf_tm ar rb t"
  shows "pcopy_ok ar env rb targs u dps (combound newhd 0 (length Ts)) env'
    ((rb, list_comb newhd targs, u) # dps)"
proof -
  note gs = genvar_simps[OF assms(1)]
  have gty: "wft ar (foldr fun_type Ts A)" by (rule wft_foldr_fun_type[OF assms(2,3)])
  have whd': "swf_tm ar rb newhd" "no_loose_bound (tr newhd) 0" "twft ar newhd" "proper newhd"
    using gs(4) gty by (simp_all add: swf_tm_def)
  have ws: "pwf_state ar env env' ((rb, list_comb newhd targs, u) # dps)"
    using genvar_pextends[OF assms(1)] genvar_swf_env[OF assms(1,5)] assms(6-9) whd'(1)
    by (auto simp: pwf_state_def swf_tm_list_comb)
  have wc: "swf_cp ar (length targs) (combound newhd 0 (length Ts))"
    using swf_cp_combound[OF whd'(3,2,4)] assms(4) by simp
  show ?thesis
    unfolding pcopy_ok_def
  proof (intro conjI allI impI ws wc)
    fix \<sigma> assume \<sigma>: "psat \<sigma> env'"
      and sol: "dsolved_all \<sigma> ((rb, list_comb newhd targs, u) # dps)"
    have "dsolvedB \<sigma> rb (tr (list_comb newhd targs)) (tr u)"
      using sol by (simp add: dsolved_dsolvedB)
    moreover have "dsolvedB \<sigma> rb (cpy targs (combound newhd 0 (length Ts))) (tr (list_comb newhd targs))"
      using dsolvedB_equiv[OF psatD(1)[OF \<sigma>] cpy_combound[OF whd'(2)]] assms(4) by simp
    ultimately show "dsolvedB \<sigma> rb (cpy targs (combound newhd 0 (length Ts))) (tr u)"
      by (rule dsolvedB_trans[rotated])
    show "dsolved_all \<sigma> dps" using sol by simp
  qed
qed

lemma mc_psound:
  "okW (mc cfg vname rb targs u env dps) s \<Longrightarrow> swf_env ar env \<Longrightarrow> \<forall>dp\<in>set dps. swf_dp ar dp \<Longrightarrow>
    sbinders ar rb \<Longrightarrow> swf_tm ar rb u \<Longrightarrow> hnf u \<Longrightarrow> \<forall>t\<in>set targs. swf_tm ar rb t \<Longrightarrow>
    psinv ar (GC env rb targs u dps) s"
proof (induction cfg vname rb targs u env dps arbitrary: s rule: mc.induct)
  case (1 cfg vname rb targs u env dps)
  note mc = "1.prems"(1) and wenv = "1.prems"(2) and wdps = "1.prems"(3) and bok = "1.prems"(4)
    and wu = "1.prems"(5) and hu = "1.prems"(6) and wtargs = "1.prems"(7)
  define uhead where "uhead = fst (strip_comb u)"
  define uargs where "uargs = snd (strip_comb u)"
  have sc: "strip_comb u = (uhead, uargs)" by (simp add: uhead_def uargs_def)
  have tw: "twf ar (tyenv env)" by (rule swf_envD(1)[OF wenv])
  from swf_tm_strip_comb[OF sc wu] have whd: "swf_tm ar rb uhead" and wargs: "\<forall>t\<in>set uargs. swf_tm ar rb t"
    by simp_all
  from mc obtain T0 base Ts where f0: "okW (liftM (fastype env rb uhead)) T0"
    and b: "okW (liftM (body_type env T0)) base"
    and tsf: "okW (liftM (mapM (fastype env rb) targs)) Ts"
    and rest: "okW (case uhead of
        Abs a T body \<Rightarrow> do {
          s \<leftarrow> mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps;
          returnW (S_MapAbs a T s)}
      | Var w _ \<Rightarrow>
          (case genvar (fst w) env (foldr fun_type Ts base) of (env', newhd) \<Rightarrow>
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rb, list_comb newhd targs, u) # dps))))
      | _ \<Rightarrow> do {
          projs \<leftarrow> make_projs u targs Ts targs;
          matchfun cfg vname rb targs u env dps uhead uargs base Ts (rev projs)}) s"
    using mc[unfolded mc.simps[of cfg vname rb targs u env dps] Let_def, folded uhead_def uargs_def]
    by (simp only: okW_bindW okW_liftM) blast
  have wT0: "wft ar T0" using fastype_wft[OF f0[unfolded okW_liftM] tw bok] whd
    by (simp add: swf_tm_def)
  have wbase: "wft ar base" using body_type_wft[OF _ refl tw wT0] b by (simp add: okW_liftM)
  note mw = mapM_fastype_wft[OF tsf tw bok wtargs]
  have lTs: "length Ts = length targs" and wTs: "\<forall>U\<in>set Ts. wft ar U" using mw by simp_all
  have proj: "psinv ar (GC env rb targs u dps) s"
    if "okW (do {projs \<leftarrow> make_projs u targs Ts targs;
          matchfun cfg vname rb targs u env dps uhead uargs base Ts (rev projs)}) s"
  proof -
    from that obtain projs where pr: "okW (make_projs u targs Ts targs) projs"
      and m: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (rev projs)) s" by auto
    from make_projs_ok[OF pr] have "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
        nat_of_integer j < length targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T \<in> set Ts"
      by simp
    from matchfun_psound[OF m this wbase wTs lTs wenv wdps bok wu wtargs sc] show ?thesis .
  qed
  show ?case
  proof (cases uhead)
    case (Abs a T body)
    have u: "u = Abs a T body" using hnf_Abs_head[OF hu] Abs by (simp add: uhead_def)
    from rest Abs obtain s' where s': "okW (mc cfg vname ((a, T) # rb)
        (map (incr_boundvars 1) targs @ [Bound 0]) body env dps) s'" and s: "s = S_MapAbs a T s'"
      by auto
    have wT: "wft ar T" using wu u by (simp add: swf_tm_def)
    have bok': "sbinders ar ((a, T) # rb)" using bok wT by simp
    have wb: "swf_tm ar ((a, T) # rb) body" using wu u by (simp add: swf_tm_def)
    have hb: "hnf body" using hu u by simp
    have wt': "\<forall>t\<in>set (map (incr_boundvars 1) targs @ [Bound 0]). swf_tm ar ((a, T) # rb) t"
      using wtargs by (auto intro: swf_tm_incr swf_tm_Bound0)
    from "1.IH"[OF uhead_def uargs_def f0 b tsf Abs s' wenv wdps bok' wb hb wt']
    have "psinv ar (GC env ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body dps) s'" .
    moreover have "\<forall>t\<in>set targs. proper t" using wtargs by (simp add: swf_tm_def)
    ultimately show ?thesis using s u wT by (auto intro: psinv.MapAbs)
  next
    case (Var w W)
    obtain env' newhd where g: "genvar (fst w) env (foldr fun_type Ts base) = (env', newhd)"
      by (cases "genvar (fst w) env (foldr fun_type Ts base)")
    with rest Var have s: "s = S_Single (El_C (combound newhd 0 (length Ts)) env'
        ((rb, list_comb newhd targs, u) # dps))" by simp
    from new_flex_copy[OF g wTs wbase lTs wenv wdps bok wu wtargs] s show ?thesis
      by (auto intro: psinv.Single)
  qed (use rest proj in auto)
qed


subsection \<open>Single steps\<close>

lemma single_step_pok:
  assumes "make_args name Ts env Us = (env', args)" "\<forall>U\<in>set Ts. wft ar U" "\<forall>U\<in>set Us. wft ar U"
    "swf_env ar env" "\<forall>dp\<in>set dps. swf_dp ar dp" "swf_cp ar (length Ts) h"
  shows "pelem_ok ar (GS env dps (length Ts)) (El_C (list_comb h args) env' dps)"
  using make_args_swf_cp[OF assms(1-3)] make_args_pextends[OF assms(1)] make_args_swf_env[OF assms(1,4)]
    assms(5,6) psat_pextends[OF _ make_args_pextends[OF assms(1)]]
  by (auto simp: pwf_state_def swf_cp_list_comb)

lemma match1_proj_psound:
  assumes "okW (match1_proj cfg vname env dps base Ts bv (Us, bary) p tail) s"
    "psinv ar (GS env dps (length Ts)) tail" "wft ar base" "wft ar bary"
    "\<forall>U\<in>set Ts. wft ar U" "\<forall>U\<in>set Us. wft ar U" "swf_env ar env" "\<forall>dp\<in>set dps. swf_dp ar dp"
    "swf_cp ar (length Ts) bv"
  shows "psinv ar (GS env dps (length Ts)) s"
proof -
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  have wC: "\<forall>C\<in>set Cs. wft ar C" by (rule gentvars_simps(4)[OF g])
  have w0: "swf_env ar env0" by (rule gentvars_swf_env[OF g assms(7)])
  let ?m = "proj_unify cfg base bary Cs env0"
  let ?r = "\<lambda>env'. (case make_args vname Ts env' (Us @ Cs) of (env'', args) \<Rightarrow>
    returnW (S_Append (S_Single (El_C (list_comb bv args) env'' dps)) tail))"
  have "okW (handleW (do {env' \<leftarrow> ?m; ?r env'})
      (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)) s"
    using assms(1) g by (simp add: match1_proj_def)
  then have "okW (do {env' \<leftarrow> ?m; ?r env'}) s \<or>
    (\<exists>e. okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s)"
    unfolding okW_handleW by blast
  then show ?thesis
  proof
    assume "okW (do {env' \<leftarrow> ?m; ?r env'}) s"
    then obtain env' where m: "okW ?m env'" and r: "okW (?r env') s" by auto
    note pu = proj_unify_swf[OF m w0 assms(3,4) wC]
    have ext: "pextends env env'" by (rule pextends_trans[OF gentvars_pextends[OF g] pu(1)])
    obtain env'' args where ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)"
      by (cases "make_args vname Ts env' (Us @ Cs)")
    have wUC: "\<forall>U\<in>set (Us @ Cs). wft ar U" using assms(6) wC by auto
    have dps': "\<forall>dp\<in>set dps. swf_dp ar dp" by (rule assms(8))
    note eo = single_step_pok[OF ma assms(5) wUC pu(2) dps' assms(9)]
    have eo': "pelem_ok ar (GS env dps (length Ts)) (El_C (list_comb bv args) env'' dps)"
      using eo ext psat_pextends[of _ env'' env'] make_args_pextends[OF ma]
      by (auto simp: pwf_state_def intro: pextends_trans)
    from r ma have "s = S_Append (S_Single (El_C (list_comb bv args) env'' dps)) tail" by simp
    with psinv.Append[OF psinv.Single[OF eo'] assms(2)] show ?thesis by simp
  next
    assume "\<exists>e. okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s"
    then obtain e where "okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s" by blast
    from okW_CANTUNIFY_returnW[OF this] assms(2) show ?thesis by simp
  qed
qed

lemma match1_projs_psound:
  "okW (match1_projs cfg vname env dps base Ts projs tail) s \<Longrightarrow>
    \<forall>(bv, T, targ)\<in>set projs. \<exists>j. bv = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length Ts \<and> T \<in> set Ts \<Longrightarrow>
    wft ar base \<Longrightarrow> \<forall>U\<in>set Ts. wft ar U \<Longrightarrow> swf_env ar env \<Longrightarrow> \<forall>dp\<in>set dps. swf_dp ar dp \<Longrightarrow>
    psinv ar (GS env dps (length Ts)) tail \<Longrightarrow> psinv ar (GS env dps (length Ts)) s"
proof (induction projs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons p projs)
  obtain bv T targ where p: "p = (bv, T, targ)" by (cases p)
  with Cons.prems(2) obtain j where j: "bv = Bound j" "0 \<le> j" "nat_of_integer j < length Ts" "T \<in> set Ts"
    by auto
  from Cons.prems(1) p obtain Usb tl where st: "ok (strip_type env T) Usb"
    and tl: "okW (match1_projs cfg vname env dps base Ts projs tail) tl"
    and h0: "okW (foldrW (match1_proj cfg vname env dps base Ts bv Usb) (arity_guesses cfg (snd Usb)) tl) s"
    by auto
  obtain Us bary where Usb: "Usb = (Us, bary)" by (cases Usb)
  have wT: "wft ar T" using Cons.prems(4) j(4) by blast
  have sw: "\<forall>U\<in>set Us. wft ar U" "wft ar bary"
    using strip_type_wft[OF st[unfolded Usb] swf_envD(1)[OF Cons.prems(5)] wT] by simp_all
  have stl: "psinv ar (GS env dps (length Ts)) tl" using Cons.IH[OF tl] Cons.prems(2-7) by simp
  have wbv: "swf_cp ar (length Ts) bv" using j by (simp add: swf_cp_def)
  from stl show ?case
  proof (rule foldrW_inv[OF h0])
    fix p' t s'
    assume "okW (match1_proj cfg vname env dps base Ts bv Usb p' t) s'"
      "psinv ar (GS env dps (length Ts)) t"
    from match1_proj_psound[OF this(1)[unfolded Usb] this(2) Cons.prems(3) sw(2) Cons.prems(4) sw(1)
        Cons.prems(5,6) wbv]
    show "psinv ar (GS env dps (length Ts)) s'" .
  qed
qed

lemma match1_psound:
  assumes "okW (match1 cfg vname rb targs u env dps) s" "swf_env ar env" "\<forall>dp\<in>set dps. swf_dp ar dp"
    "sbinders ar rb" "swf_tm ar rb u" "\<forall>t\<in>set targs. swf_tm ar rb t"
  shows "psinv ar (GS env dps (length targs)) s"
proof -
  define uhead where "uhead = fst (strip_comb u)"
  have sc: "strip_comb u = (uhead, snd (strip_comb u))" by (simp add: uhead_def)
  have tw: "twf ar (tyenv env)" by (rule swf_envD(1)[OF assms(2)])
  from swf_tm_strip_comb[OF sc assms(5)] have whd: "swf_tm ar rb uhead" by simp
  from assms(1) obtain T0 base Ts projs imit where f0: "okW (liftM (fastype env rb uhead)) T0"
    and b: "okW (liftM (body_type env T0)) base"
    and tsf: "okW (liftM (mapM (fastype env rb) targs)) Ts"
    and pr: "okW (make_projs u targs Ts targs) projs"
    and im: "okW (case uhead of
          Const _ _ \<Rightarrow> do {
            Us \<leftarrow> liftM (binder_types env T0);
            (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb uhead args) env' dps)))}
        | Free _ _ \<Rightarrow> do {
            Us \<leftarrow> liftM (binder_types env T0);
            (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb uhead args) env' dps)))}
        | _ \<Rightarrow> returnW S_Empty) imit"
    and m: "okW (match1_projs cfg vname env dps base Ts (rev projs) imit) s"
    using assms(1)[unfolded match1_def Let_def, folded uhead_def]
    by (simp only: okW_bindW) blast
  have wT0: "wft ar T0" using fastype_wft[OF f0[unfolded okW_liftM] tw assms(4)] whd
    by (simp add: swf_tm_def)
  have wbase: "wft ar base" using body_type_wft[OF _ refl tw wT0] b by (simp add: okW_liftM)
  note mw = mapM_fastype_wft[OF tsf tw assms(4,6)]
  have lTs: "length Ts = length targs" and wTs: "\<forall>U\<in>set Ts. wft ar U" using mw by simp_all
  have imit: "psinv ar (GS env dps (length Ts)) imit"
  proof -
    have "psinv ar (GS env dps (length Ts)) imit" if "uhead = Const a T \<or> uhead = Free a T" for a T
    proof -
      have "okW (do {
            Us \<leftarrow> liftM (binder_types env T0);
            (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb uhead args) env' dps)))}) imit"
        using im that by (elim disjE) simp_all
      then obtain Us where bt: "ok (binder_types env T0) Us"
        and imit0: "okW (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb uhead args) env' dps))) imit"
        by (simp only: okW_bindW okW_liftM) blast
      then have imit: "imit = (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              S_Single (El_C (list_comb uhead args) env' dps))"
        by (simp split: prod.splits)
      have wUs: "\<forall>U\<in>set Us. wft ar U" using binder_types_wft[OF _ refl tw wT0] bt by simp
      obtain env' args where ma: "make_args vname Ts env Us = (env', args)"
        by (cases "make_args vname Ts env Us")
      have "swf_cp ar (length Ts) uhead" using whd that by (auto simp: swf_tm_def swf_cp_def)
      from single_step_pok[OF ma wTs wUs assms(2,3) this] imit ma show ?thesis by (auto intro: psinv.Single)
    qed
    moreover have "imit = S_Empty" if "\<forall>a T. uhead \<noteq> Const a T \<and> uhead \<noteq> Free a T"
      using im that by (cases uhead) auto
    ultimately show ?thesis by (metis psinv.Empty)
  qed
  from make_projs_ok[OF pr] lTs have "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
      nat_of_integer j < length Ts \<and> T \<in> set Ts"
    by fastforce
  from match1_projs_psound[OF m this wbase wTs assms(2,3) imit] lTs show ?thesis by simp
qed


subsection \<open>\<open>MATCH\<close>\<close>

lemma preducesD:
  "preduces ar env0 dps0 env dps \<Longrightarrow> pwf_state ar env0 env dps"
  "preduces ar env0 dps0 env dps \<Longrightarrow> psat \<sigma> env \<Longrightarrow> dsolved_all \<sigma> dps \<Longrightarrow> dsolved_all \<sigma> dps0"
  by (simp_all add: preduces_def)

lemma match_pair_psound:
  assumes "okW (match_pair cfg env (rb, t, u) dpairs) s" "preduces ar env0 dps0 env ((rb, t, u) # dpairs)"
    "strip_comb t = (Var v T, targs)" "ok (binder_types env T) Ts" "length Ts = length targs" "hnf u"
  shows "psinv ar (GE env0 dps0) s"
proof -
  let ?dp = "(rb, t, u)"
  have ws: "pwf_state ar env0 env (?dp # dpairs)" by (rule preducesD(1)[OF assms(2)])
  then have wenv: "swf_env ar env" and wdp: "swf_dp ar ?dp" and wdps: "\<forall>dp\<in>set dpairs. swf_dp ar dp"
    by (simp_all add: pwf_state_def)
  from assms(1,3) obtain Ts' occ s' where bt: "ok (binder_types env T) Ts'"
    and m: "okW (if occ then match1 cfg (fst v) rb targs u env (?dp # dpairs)
      else mc cfg (fst v) rb targs u env dpairs) s'" and s: "s = S_MapNewDset (v, T) Ts' s'"
    by (auto simp: match_pair_def)
  from bt assms(4) have Ts': "Ts' = Ts" by (simp add: return_def)
  from wdp have bok: "sbinders ar rb" and wt: "swf_tm ar rb t" and wu: "swf_tm ar rb u" by simp_all
  from swf_tm_strip_comb[OF assms(3) wt] have wv: "swf_tm ar rb (Var v T)"
    and wtargs: "\<forall>t\<in>set targs. swf_tm ar rb t" by simp_all
  have wT: "wft ar T" using wv by (simp add: swf_tm_def)
  have wTs: "\<forall>U\<in>set Ts. wft ar U"
    using binder_types_wft[OF _ refl swf_envD(1)[OF wenv] wT] assms(4) by simp
  show ?thesis
  proof (cases occ)
    case True
    with m have m1: "okW (match1 cfg (fst v) rb targs u env (?dp # dpairs)) s'" by simp
    have "\<forall>dp'\<in>set (?dp # dpairs). swf_dp ar dp'" using wdp wdps by simp
    from match1_psound[OF m1 wenv this bok wu wtargs] assms(5)
    have "psinv ar (GS env (?dp # dpairs) (length Ts)) s'" by simp
    with assms(2) wT wTs show ?thesis unfolding s Ts' by (rule psinv.MapNewDset1)
  next
    case False
    with m have m0: "okW (mc cfg (fst v) rb targs u env dpairs) s'" by simp
    have "psinv ar (GC env rb targs u dpairs) s'" by (rule mc_psound[OF m0 wenv wdps bok wu assms(6) wtargs])
    with assms(2,3,5) wTs show ?thesis unfolding s Ts' by (auto intro: psinv.MapNewDset)
  qed
qed

text \<open>
  Saturation: by \<^const>\<open>fsat\<close>, the flexible side has at most as many arguments as its type has
  argument types; the expanded pair has exactly as many.
\<close>

lemma match_sat_psound:
  assumes "okW (match_sat cfg env dp dpairs) s" "preduces ar env0 dps0 env (dp # dpairs)" "pfrs_ok env dp"
  shows "psinv ar (GE env0 dps0) s"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have ws: "pwf_state ar env0 env (dp # dpairs)" by (rule preducesD(1)[OF assms(2)])
  then have wenv: "swf_env ar env" and wdp: "swf_dp ar dp" and wdps: "\<forall>dp\<in>set dpairs. swf_dp ar dp"
    by (simp_all add: pwf_state_def)
  from assms(3) dp have fs: "fsat env [] t" and hu: "hnf u" and nu: "\<not> is_Abs u" by simp_all
  from assms(1) dp obtain v T targs where sc: "strip_comb t = (Var v T, targs)"
    by (auto simp: match_sat_def split: prod.splits pterm.splits)
  with assms(1) dp obtain Ts where bt: "ok (binder_types env T) Ts"
    and mp: "okW (match_pair cfg env (eta_expand_dpair (drop (length targs) Ts) dp) dpairs) s"
    by (auto simp: match_sat_def)
  define Es where "Es = drop (length targs) Ts"
  obtain rb' t' u' where dp': "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
    by (cases "eta_expand_dpair Es (rb, t, u)")
  have le: "length targs \<le> length Ts" by (rule fsat_binder_types[OF fs sc bt])
  from wdp dp have wt: "swf_tm ar rb t" and wu: "swf_tm ar rb u" by simp_all
  from swf_tm_strip_comb[OF sc wt] have wT: "wft ar T" by (simp add: swf_tm_def)
  have wTs: "\<forall>U\<in>set Ts. wft ar U"
    using binder_types_wft[OF _ refl swf_envD(1)[OF wenv] wT] bt by simp
  have wEs: "\<forall>E\<in>set Es. wft ar E" using wTs by (auto simp: Es_def dest: in_set_dropD)
  note sh = eta_expand_dpair_shape[OF sc hu nu dp']
  have len: "length Ts = length (map (incr_boundvars (integer_of_nat (length Es))) targs @ eta_bvs (length Es))"
    using le by (simp add: Es_def)
  have wdp': "swf_dp ar (rb', t', u')" using swf_dp_eta_expand[OF wdp[unfolded dp] wEs] dp' by simp
  have red: "preduces ar env0 dps0 env ((rb', t', u') # dpairs)"
    unfolding preduces_def
  proof (intro conjI allI impI)
    show "pwf_state ar env0 env ((rb', t', u') # dpairs)"
      using ws wdp' by (simp add: pwf_state_def)
  next
    fix \<sigma> assume \<sigma>: "psat \<sigma> env" and sol: "dsolved_all \<sigma> ((rb', t', u') # dpairs)"
    have "proper t" "proper u" using wt wu by (simp_all add: swf_tm_def)
    from dsolved_eta_expand_dpair[OF this psatD(1)[OF \<sigma>], of Es rb] sol dp'
    have "dsolved \<sigma> dp" by (simp add: dp)
    with sol have "dsolved_all \<sigma> (dp # dpairs)" by simp
    with preducesD(2)[OF assms(2) \<sigma>] show "dsolved_all \<sigma> dps0" .
  qed
  from mp dp dp' have mp': "okW (match_pair cfg env (rb', t', u') dpairs) s" by (simp add: Es_def)
  from match_pair_psound[OF mp' red sh(1) bt len sh(2)] show ?thesis .
qed

lemma preduces_pextends:
  "preduces ar env0 dps0 env dps \<Longrightarrow> pextends env env' \<Longrightarrow> swf_env ar env' \<Longrightarrow>
    preduces ar env0 dps0 env' dps"
  by (auto simp: preduces_def pwf_state_def intro: pextends_trans psat_pextends)

lemma match_eta_psound:
  assumes "okW (match_eta cfg env dp dpairs B j tail) s" "preduces ar env0 dps0 env (dp # dpairs)"
    "pfrs_ok env dp" "wft ar B" "psinv ar (GE env0 dps0) tail"
  shows "psinv ar (GE env0 dps0) s"
proof (cases "j = 0")
  case True
  with assms(1) obtain s' where m: "okW (match_sat cfg env dp dpairs) s'" and s: "s = S_Append s' tail"
    by (auto simp: match_eta_def)
  from psinv.Append[OF match_sat_psound[OF m assms(2,3)] assms(5)] s show ?thesis by simp
next
  case False
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by (cases "gentvars (Suc j) env")
  have wenv: "swf_env ar env" using preducesD(1)[OF assms(2)] by (simp add: pwf_state_def)
  have w1: "swf_env ar env1" by (rule gentvars_swf_env[OF g wenv])
  have lR: "length Rs = Suc j" and wR: "\<forall>R\<in>set Rs. wft ar R" using gentvars_simps(3,4)[OF g] by simp_all
  then obtain R0 Rs' where Rs: "Rs = R0 # Rs'" by (cases Rs) auto
  have wF: "wft ar (foldr fun_type (tl Rs) (hd Rs))" using wR Rs by (simp add: wft_foldr_fun_type)
  let ?m = "do {
      env2 \<leftarrow> cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1;
      s \<leftarrow> match_sat cfg env2 dp dpairs;
      returnW (S_Append s tail)}"
  have "okW (handleW ?m (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)) s"
    using assms(1) False g by (simp add: match_eta_def)
  then have "okW ?m s \<or> (\<exists>e. okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s)"
    unfolding okW_handleW by blast
  then show ?thesis
  proof
    assume "okW ?m s"
    then obtain env2 s' where cu: "okW (cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1) env2"
      and m: "okW (match_sat cfg env2 dp dpairs) s'" and s: "s = S_Append s' tail"
      by auto
    note cs = cunify_types_swf[OF cu w1 assms(4) wF]
    have ext: "pextends env env2" by (rule pextends_trans[OF gentvars_pextends[OF g] cs(1)])
    have red: "preduces ar env0 dps0 env2 (dp # dpairs)" by (rule preduces_pextends[OF assms(2) ext cs(2)])
    have "pfrs_ok env2 dp" by (rule pfrs_ok_pextends[OF assms(3) ext])
    from psinv.Append[OF match_sat_psound[OF m red this] assms(5)] s show ?thesis by simp
  next
    assume "\<exists>e. okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s"
    then obtain e where "okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s" by blast
    from okW_CANTUNIFY_returnW[OF this] assms(5) show ?thesis by simp
  qed
qed

theorem MATCH_psound:
  assumes "okW (MATCH cfg env dp dpairs) s" "preduces ar env0 dps0 env (dp # dpairs)" "pfrs_ok env dp"
  shows "psinv ar (GE env0 dps0) s"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have ws: "pwf_state ar env0 env (dp # dpairs)" by (rule preducesD(1)[OF assms(2)])
  then have wenv: "swf_env ar env" and wdp: "swf_dp ar dp" by (simp_all add: pwf_state_def)
  from assms(1) dp obtain v T targs where sc: "strip_comb t = (Var v T, targs)"
    by (auto simp: MATCH_def split: prod.splits pterm.splits)
  with assms(1) dp obtain B where bt: "ok (body_type env T) B"
    and m: "okW (if is_TVar B then foldrW (match_eta cfg env dp dpairs B) (arity_guesses cfg B) S_Empty
      else match_sat cfg env dp dpairs) s"
    by (auto simp: MATCH_def)
  from wdp dp have "swf_tm ar rb t" by simp
  from swf_tm_strip_comb[OF sc this] have wT: "wft ar T" by (simp add: swf_tm_def)
  have wB: "wft ar B" using body_type_wft[OF _ refl swf_envD(1)[OF wenv] wT] bt by simp
  show ?thesis
  proof (cases "is_TVar B")
    case True
    with m have f: "okW (foldrW (match_eta cfg env dp dpairs B) (arity_guesses cfg B) S_Empty) s" by simp
    show ?thesis
    proof (rule foldrW_inv[where P = "psinv ar (GE env0 dps0)", OF f psinv.Empty])
      fix j t' s'
      assume "okW (match_eta cfg env dp dpairs B j t') s'" "psinv ar (GE env0 dps0) t'"
      from match_eta_psound[OF this(1) assms(2,3) wB this(2)] show "psinv ar (GE env0 dps0) s'" .
    qed
  next
    case False
    with m have "okW (match_sat cfg env dp dpairs) s" by simp
    from match_sat_psound[OF this assms(2,3)] show ?thesis .
  qed
qed


subsection \<open>\<open>new_dset\<close>\<close>

lemma swf_tm_types_abs:
  assumes "\<forall>U\<in>set Ts. wft ar U" "swf_cp ar (length Ts) u'"
  shows "swf_tm ar [] (types_abs Ts u')"
proof -
  have "proper u'" "twft ar u'" using assms(2) by (simp_all add: swf_cp_def)
  then have "proper (types_abs Ts u')" "twft ar (types_abs Ts u')"
    using assms(1) by (induction Ts) simp_all
  moreover have "no_loose_bound (tr (types_abs Ts u')) 0"
    using assms(2) by (simp add: swf_cp_def tr_types_abs loose_bound_Abs_m)
  ultimately show ?thesis by (simp add: swf_tm_def)
qed

text \<open>Binding the variable of the flex-rigid pair to the abstraction of a copy solves the pair.\<close>

lemma new_dset_psemantics:
  assumes "preduces ar env0 dps0 env1 ((rb, t, u) # dps1)" "strip_comb t = (Var v T, targs)"
    "length Ts = length targs" "pcopy_ok ar env1 rb targs u dps1 u' env' dpairs'"
    "psat \<sigma> env'" "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
    "dsolved_all \<sigma> dpairs'"
  shows "dsolved_all \<sigma> dps0"
proof -
  from assms(4,5,7) have c: "dsolvedB \<sigma> rb (cpy targs u') (tr u)" and d1: "dsolved_all \<sigma> dps1"
    by (simp_all add: pcopy_ok_def)
  have "dsolvedB \<sigma> rb (tr t) (cpy targs u')"
    by (rule dsolvedB_flex_binding[OF assms(2) psatD(1)[OF assms(5)] assms(6,3)])
  from dsolvedB_trans[OF this c] have "dsolved \<sigma> (rb, t, u)" by (simp add: dsolved_dsolvedB)
  with d1 have d: "dsolved_all \<sigma> ((rb, t, u) # dps1)" by simp
  have "pextends env1 env'" using assms(4) by (simp add: pcopy_ok_def pwf_state_def)
  with assms(5) have s1: "psat \<sigma> env1" by (rule psat_pextends)
  from preducesD(2)[OF assms(1) s1 d] show ?thesis .
qed

lemma new_dset_cases:
  assumes "okW (new_dset (v, T) Ts u' env' dpairs') y" "swf_env ar env'"
    "\<forall>U\<in>set Ts. wft ar U" "swf_cp ar (length Ts) u'" "wft ar T"
  obtains env'' where "y = El_E env'' dpairs'" "pextends env' env''" "swf_env ar env''"
      "\<And>\<sigma>. psat \<sigma> env'' \<Longrightarrow> \<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
  | s where "y = El_E env' (([], s, types_abs Ts u') # dpairs')" "swf_tm ar [] s"
      "\<And>\<sigma>. psat \<sigma> env' \<Longrightarrow> dsolved \<sigma> ([], s, types_abs Ts u') \<Longrightarrow>
        \<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
proof -
  have wa: "swf_tm ar [] (types_abs Ts u')" by (rule swf_tm_types_abs[OF assms(3,4)])
  from assms(1) obtain r where lk: "ok (lookup env' v T) r"
    and rest: "okW (case r of
        None \<Rightarrow> do {env'' \<leftarrow> liftM (update (v, T) (types_abs Ts u') env'); returnW (El_E env'' dpairs')}
      | Some s \<Rightarrow> returnW (El_E env' (([], s, types_abs Ts u') # dpairs'))) y"
    by (auto simp: new_dset_def)
  from ok_lookup_some[OF lk] show ?thesis
  proof (elim disjE exE conjE)
    assume "r = None"
    with rest obtain env'' where upd: "ok (update (v, T) (types_abs Ts u') env') env''"
      and y: "y = El_E env'' dpairs'" by auto
    have ext: "pextends env' env''"
      using ok_update_extends[OF upd] ok_update[OF upd] by (simp add: pextends_def)
    have sw: "swf_env ar env''"
      using ok_update_swf_env[OF upd assms(2) _ _ assms(5)] wa by (simp add: swf_tm_def)
    have sem: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))" if "psat \<sigma> env''" for \<sigma>
      by (rule satD[OF psatD(3)[OF that] ok_update_lookup[OF upd]])
    show ?thesis by (rule that(1)[OF y ext sw sem])
  next
    fix s U assume r: "r = Some s" and lks: "vt_lookup (tenv env') v = Some (U, s)"
    from rest r have y: "y = El_E env' (([], s, types_abs Ts u') # dpairs')" by simp
    have ws: "swf_tm ar [] s" using swf_envD(2)[OF assms(2) lks] by (simp add: swf_tm_def)
    have sem: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
      if "psat \<sigma> env'" "dsolved \<sigma> ([], s, types_abs Ts u')" for \<sigma>
    proof -
      have "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
        using that(2) by (simp add: dsolved_def)
      with satD[OF psatD(3)[OF that(1)] lks] show ?thesis by (rule equiv_trans)
    qed
    show ?thesis by (rule that(2)[OF y ws sem])
  qed
qed

lemma new_dset_psound:
  assumes "okW (new_dset (v, T) Ts u' env' dpairs') y"
    "preduces ar env0 dps0 env1 ((rb, t, u) # dps1)" "strip_comb t = (Var v T, targs)"
    "length Ts = length targs" "\<forall>U\<in>set Ts. wft ar U"
    "pcopy_ok ar env1 rb targs u dps1 u' env' dpairs'"
  shows "pelem_ok ar (GE env0 dps0) y"
proof -
  have ws1: "pwf_state ar env0 env1 ((rb, t, u) # dps1)" by (rule preducesD(1)[OF assms(2)])
  have ws: "pwf_state ar env1 env' dpairs'" and wc: "swf_cp ar (length targs) u'"
    using assms(6) by (simp_all add: pcopy_ok_def)
  have ws': "pwf_state ar env0 env' dpairs'" by (rule pwf_state_pextends[OF ws pwf_stateD(1)[OF ws1]])
  have wenv: "swf_env ar env'" by (rule pwf_stateD(2)[OF ws])
  have "swf_tm ar rb t" using pwf_stateD(3)[OF ws1, of "(rb, t, u)"] by simp
  from swf_tm_strip_comb[OF assms(3) this] have wT: "wft ar T" by (simp add: swf_tm_def)
  have wc': "swf_cp ar (length Ts) u'" using wc assms(4) by simp
  from new_dset_cases[OF assms(1) wenv assms(5) wc' wT] show ?thesis
  proof cases
    case (1 env'')
    have "pwf_state ar env0 env'' dpairs'"
      using ws' 1(2,3) by (auto simp: pwf_state_def intro: pextends_trans)
    moreover have "dsolved_all \<sigma> dps0" if \<sigma>: "psat \<sigma> env''" "dsolved_all \<sigma> dpairs'" for \<sigma>
      by (rule new_dset_psemantics[OF assms(2,3,4,6) psat_pextends[OF \<sigma>(1) 1(2)] 1(4)[OF \<sigma>(1)] \<sigma>(2)])
    ultimately show ?thesis unfolding 1(1) pelem_ok.simps preduces_def by blast
  next
    case (2 s)
    have "pwf_state ar env0 env' (([], s, types_abs Ts u') # dpairs')"
      using ws' 2(2) swf_tm_types_abs[OF assms(5) wc'] by (simp add: pwf_state_def)
    moreover have "dsolved_all \<sigma> dps0"
      if \<sigma>: "psat \<sigma> env'" "dsolved_all \<sigma> (([], s, types_abs Ts u') # dpairs')" for \<sigma>
      using new_dset_psemantics[OF assms(2,3,4,6) \<sigma>(1) 2(3)[OF \<sigma>(1)]] \<sigma>(2) by simp
    ultimately show ?thesis unfolding 2(1) pelem_ok.simps preduces_def by blast
  qed
qed

text \<open>For a single step, the pairs are kept: binding the variable is sound.\<close>

lemma new_dset_psound1:
  assumes "okW (new_dset (v, T) Ts u' env' dpairs') y" "preduces ar env0 dps0 env1 dps1"
    "wft ar T" "\<forall>U\<in>set Ts. wft ar U" "pelem_ok ar (GS env1 dps1 (length Ts)) (El_C u' env' dpairs')"
  shows "pelem_ok ar (GE env0 dps0) y"
proof -
  have ws1: "pwf_state ar env0 env1 dps1" by (rule preducesD(1)[OF assms(2)])
  have ws: "pwf_state ar env1 env' dpairs'" and wc: "swf_cp ar (length Ts) u'"
    and sem: "\<And>\<sigma>. psat \<sigma> env' \<Longrightarrow> dsolved_all \<sigma> dpairs' \<Longrightarrow> dsolved_all \<sigma> dps1"
    using assms(5) by simp_all
  have ws': "pwf_state ar env0 env' dpairs'" by (rule pwf_state_pextends[OF ws pwf_stateD(1)[OF ws1]])
  have e1: "pextends env1 env'" by (rule pwf_stateD(1)[OF ws])
  have wenv: "swf_env ar env'" by (rule pwf_stateD(2)[OF ws])
  have red: "dsolved_all \<sigma> dps0" if "psat \<sigma> env'" "dsolved_all \<sigma> dpairs'" for \<sigma>
    using preducesD(2)[OF assms(2) psat_pextends[OF that(1) e1] sem[OF that]] .
  from new_dset_cases[OF assms(1) wenv assms(4) wc assms(3)] show ?thesis
  proof cases
    case (1 env'')
    have "pwf_state ar env0 env'' dpairs'"
      using ws' 1(2,3) by (auto simp: pwf_state_def intro: pextends_trans)
    moreover have "dsolved_all \<sigma> dps0" if \<sigma>: "psat \<sigma> env''" "dsolved_all \<sigma> dpairs'" for \<sigma>
      by (rule red[OF psat_pextends[OF \<sigma>(1) 1(2)] \<sigma>(2)])
    ultimately show ?thesis unfolding 1(1) pelem_ok.simps preduces_def by blast
  next
    case (2 s)
    have "pwf_state ar env0 env' (([], s, types_abs Ts u') # dpairs')"
      using ws' 2(2) swf_tm_types_abs[OF assms(4) wc] by (simp add: pwf_state_def)
    moreover have "dsolved_all \<sigma> dps0"
      if \<sigma>: "psat \<sigma> env'" "dsolved_all \<sigma> (([], s, types_abs Ts u') # dpairs')" for \<sigma>
      using red[OF \<sigma>(1)] \<sigma>(2) by simp
    ultimately show ?thesis unfolding 2(1) pelem_ok.simps preduces_def by blast
  qed
qed

end

end
