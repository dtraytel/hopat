section \<open>Soundness of \<open>MATCH\<close>\<close>

theory Unify_Match
  imports Unify_Shape
begin

text \<open>
  The search of \<open>unify.ML\<close> is a lazy sequence; we model each of its closures by a constructor
  of \<^typ>\<open>seq\<close>. A sequence enumerates solutions of a \<^emph>\<open>goal\<close>, and we characterize the elements
  it may produce by an invariant on sequences, one rule per closure. The goals are:
  \<^item> \<open>GR env0 dps0\<close>: unifiers \<open>El_R env tps\<close> of the pairs \<open>dps0\<close> in \<open>env0\<close>, with flex-flex pairs
    \<open>tps\<close> left;
  \<^item> \<open>GE env0 dps0\<close>: environments with new pairs \<open>El_E env dps\<close> that reduce \<open>dps0\<close>;
  \<^item> \<open>GC env0 rb targs u dps0\<close>: copies \<open>El_C u' env dps\<close> of \<open>u\<close> relative to the arguments \<open>targs\<close>
    of a flexible head: \<open>(\<lambda>\<dots>. u') targs\<close> is equal to \<open>u\<close> once the new pairs \<open>dps\<close> are solved;
  \<^item> \<open>GD env0 rb targs uargs dps0\<close>: copies \<open>El_D uargs' env dps\<close> of the arguments \<open>uargs\<close>.

  Throughout, the environments only grow and stay well-formed, and the pairs stay well-formed.
\<close>


subsection \<open>Elements\<close>

definition wf_cp :: "(name \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pterm \<Rightarrow> bool" where
  "wf_cp ar k u' \<longleftrightarrow> proper u' \<and> typs_ok ar u' \<and> no_loose_bound (tr u') k"

definition wf_state :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "wf_state ar env0 env dps \<longleftrightarrow> extends env env0 \<and> wf_env ar env \<and> (\<forall>dp\<in>set dps. wf_dp ar dp)"

definition reduces :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "reduces ar env0 dps0 env dps \<longleftrightarrow> wf_state ar env0 env dps \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow> dsolved_all \<sigma> dps0)"

definition unifier :: "env \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "unifier env0 dps0 env tps \<longleftrightarrow> extends env env0 \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env \<longrightarrow>
      (\<forall>(t, u)\<in>set tps. mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)) \<longrightarrow> dsolved_all \<sigma> dps0)"

definition copy_ok :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> dpair list \<Rightarrow>
    pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "copy_ok ar env0 rb targs u dps0 u' env dps \<longleftrightarrow> wf_state ar env0 env dps \<and>
    wf_cp ar (length targs) u' \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow>
      dsolvedB \<sigma> rb (cpy targs u') (tr u) \<and> dsolved_all \<sigma> dps0)"

definition args_ok :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> dpair list \<Rightarrow>
    pterm list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "args_ok ar env0 rb targs uargs dps0 uargs' env dps \<longleftrightarrow> wf_state ar env0 env dps \<and>
    length uargs' = length uargs \<and> (\<forall>a'\<in>set uargs'. wf_cp ar (length targs) a') \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow>
      list_all2 (\<lambda>a' a. dsolvedB \<sigma> rb (cpy targs a') (tr a)) uargs' uargs \<and> dsolved_all \<sigma> dps0)"

datatype goal =
  GR env "dpair list"
| GE env "dpair list"
| GC env binders "pterm list" pterm "dpair list"
| GD env binders "pterm list" "pterm list" "dpair list"

fun elem_ok :: "(name \<Rightarrow> nat) \<Rightarrow> goal \<Rightarrow> elem \<Rightarrow> bool" where
  "elem_ok ar (GR env0 dps0) (El_R env tps) \<longleftrightarrow> unifier env0 dps0 env tps"
| "elem_ok ar (GE env0 dps0) (El_E env dps) \<longleftrightarrow> reduces ar env0 dps0 env dps"
| "elem_ok ar (GC env0 rb targs u dps0) (El_C u' env dps) \<longleftrightarrow> copy_ok ar env0 rb targs u dps0 u' env dps"
| "elem_ok ar (GD env0 rb targs uargs dps0) (El_D uargs' env dps) \<longleftrightarrow>
    args_ok ar env0 rb targs uargs dps0 uargs' env dps"
| "elem_ok ar _ _ \<longleftrightarrow> False"


subsection \<open>The invariant of sequences\<close>

text \<open>
  \<open>sinv ar G s\<close>: every element that pulling \<open>s\<close> may produce satisfies the goal \<open>G\<close>, and so do
  the elements of the remaining sequences. The rules follow the closures: \<^const>\<open>S_MapNewDset\<close>
  is the result of \<open>MATCH\<close> for a flex-rigid pair \<open>(rb, t, u)\<close> with \<open>t = ?v targs\<close>,
  \<^const>\<open>S_MapAbs\<close>, \<^const>\<open>S_Proj\<close> and \<^const>\<open>S_MapJoin\<close> are the copies of an abstraction, by
  projection and by imitation, and \<^const>\<open>S_Maps\<close> and \<^const>\<open>S_MapCons\<close> copy argument lists.
\<close>

inductive sinv :: "(name \<Rightarrow> nat) \<Rightarrow> goal \<Rightarrow> seq \<Rightarrow> bool" for ar where
  Empty: "sinv ar G S_Empty"
| Single: "elem_ok ar G x \<Longrightarrow> sinv ar G (S_Single x)"
| AddUnify: "reduces ar env0 dps0 env dps \<Longrightarrow> sinv ar (GR env0 dps0) reseq \<Longrightarrow>
    sinv ar (GR env0 dps0) (S_AddUnify td env dps reseq)"
| ItRight: "sinv ar (GE env0 dps0) xq \<Longrightarrow> sinv ar (GR env0 dps0) yq \<Longrightarrow>
    sinv ar (GR env0 dps0) (S_ItRight td xq yq)"
| MapNewDset: "reduces ar env0 dps0 env1 ((rb, t, u) # dps1) \<Longrightarrow>
    strip_comb t = (Var v T, targs) \<Longrightarrow> length Ts = length targs \<Longrightarrow> \<forall>U\<in>set Ts. ground ar U \<Longrightarrow>
    sinv ar (GC env1 rb targs u dps1) xq \<Longrightarrow> sinv ar (GE env0 dps0) (S_MapNewDset (v, T) Ts xq)"
| MapAbs: "sinv ar (GC env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body dps0) xq \<Longrightarrow>
    ground ar T \<Longrightarrow> \<forall>t\<in>set targs. proper t \<Longrightarrow>
    sinv ar (GC env0 rb targs (Abs b T' body) dps0) (S_MapAbs a T xq)"
| Proj: "wf_env ar env \<Longrightarrow> \<forall>dp\<in>set dps. wf_dp ar dp \<Longrightarrow> binders_ok ar rb \<Longrightarrow> wf_tm ar rb u \<Longrightarrow>
    \<forall>t\<in>set targs. wf_tm ar rb t \<Longrightarrow> 0 \<le> j \<Longrightarrow> nat_of_integer j < length targs \<Longrightarrow>
    targ = targs ! (length targs - 1 - nat_of_integer j) \<Longrightarrow> length Ts = length targs \<Longrightarrow>
    \<forall>U\<in>set Ts. ground ar U \<Longrightarrow> \<forall>U\<in>set Us. ground ar U \<Longrightarrow>
    sinv ar (GC env rb targs u dps) tail \<Longrightarrow>
    sinv ar (GC env rb targs u dps) (S_Proj vname env Ts Us targs rb u dps (Bound j) targ tail)"
| MapJoin: "strip_comb u = (uhead, uargs) \<Longrightarrow> no_loose_bound (tr uhead) 0 \<Longrightarrow> typs_ok ar uhead \<Longrightarrow>
    sinv ar (GD env0 rb targs uargs dps0) xq \<Longrightarrow> sinv ar (GC env0 rb targs u dps0) (S_MapJoin uhead xq)"
| Maps: "sinv ar (GD env0 rb targs uargs dps0) xq \<Longrightarrow> binders_ok ar rb \<Longrightarrow> wf_tm ar rb uarg \<Longrightarrow>
    \<forall>t\<in>set targs. wf_tm ar rb t \<Longrightarrow>
    sinv ar (GD env0 rb targs (uarg # uargs) dps0) (S_Maps vname rb targs uarg xq)"
| MapCons: "args_ok ar env0 rb targs uargs dps0 uargs' env dps \<Longrightarrow>
    sinv ar (GC env rb targs u2 dps) xq \<Longrightarrow> env \<Turnstile> rlist_abs rb uarg \<approx> rlist_abs rb u2 \<Longrightarrow>
    sinv ar (GD env0 rb targs (uarg # uargs) dps0) (S_MapCons uargs' xq)"
| Append: "sinv ar G xq \<Longrightarrow> sinv ar G yq \<Longrightarrow> sinv ar G (S_Append xq yq)"


subsection \<open>Well-formedness of copies\<close>

lemma wf_tm_incr:
  assumes "wf_tm ar rb t"
  shows "wf_tm ar ((a, T) # rb) (incr_boundvars 1 t)"
proof -
  from assms have p: "proper t" by (simp add: wf_tm_def)
  have "tr (incr_boundvars 1 t) = lift (tr t) 0" by (rule tr_incr_boundvars1[OF p])
  with assms show ?thesis
    by (auto simp: wf_tm_def incr_boundvars_def proper_incr_bv typs_ok_incr_bv integer_reps
        intro: no_loose_bound_lift)
qed

lemma wf_tm_Bound0: "wf_tm ar ((a, T) # rb) (Bound 0)"
  by (simp add: wf_tm_def)

lemma wf_tm_list_comb:
  "wf_tm ar rb (list_comb h ts) \<longleftrightarrow> wf_tm ar rb h \<and> (\<forall>t\<in>set ts. wf_tm ar rb t)"
  by (auto simp: wf_tm_def proper_list_comb typs_ok_list_comb tr_list_comb no_loose_bound_list_app)

lemma wf_tm_strip_comb:
  "strip_comb u = (h, us) \<Longrightarrow> wf_tm ar rb u \<Longrightarrow> wf_tm ar rb h \<and> (\<forall>t\<in>set us. wf_tm ar rb t)"
  using strip_comb_list_comb wf_tm_list_comb by metis

lemma no_loose_bound_tr_combound:
  "no_loose_bound (tr (combound t 0 k)) k \<longleftrightarrow> no_loose_bound (tr t) k"
  by (auto simp: tr_combound0 no_loose_bound_list_app)

lemma proper_combound: "0 \<le> n \<Longrightarrow> proper (combound t n k) \<longleftrightarrow> proper t"
proof (induction k arbitrary: n)
  case (Suc k)
  then show ?case by (simp add: integer_reps)
qed simp

lemma typs_ok_combound: "typs_ok ar (combound t n k) \<longleftrightarrow> typs_ok ar t"
  by (induction k arbitrary: n) simp_all

lemma wf_cp_combound:
  "typs_ok ar G \<Longrightarrow> no_loose_bound (tr G) 0 \<Longrightarrow> proper G \<Longrightarrow> wf_cp ar k (combound G 0 k)"
  by (auto simp: wf_cp_def proper_combound typs_ok_combound no_loose_bound_tr_combound
      intro: no_loose_bound_mono)

lemma ground_foldr_fun_type:
  "\<forall>U\<in>set Ts. ground ar U \<Longrightarrow> ground ar B \<Longrightarrow> ground ar (foldr fun_type Ts B)"
  by (induction Ts) simp_all


subsection \<open>Properties of the elements\<close>

lemma wf_stateD:
  "wf_state ar env0 env dps \<Longrightarrow> extends env env0"
  "wf_state ar env0 env dps \<Longrightarrow> wf_env ar env"
  "wf_state ar env0 env dps \<Longrightarrow> dp \<in> set dps \<Longrightarrow> wf_dp ar dp"
  by (simp_all add: wf_state_def)

lemma wf_state_extends:
  "wf_state ar env1 env dps \<Longrightarrow> extends env1 env0 \<Longrightarrow> wf_state ar env0 env dps"
  by (auto simp: wf_state_def intro: extends_trans)

text \<open>A pair of a flexible term \<open>?v targs\<close> and a copy, if \<open>?v\<close> is bound to the abstraction of the copy.\<close>

lemma dsolvedB_flex_binding:
  assumes "strip_comb t = (Var v T, targs)" "closed_on UNIV \<sigma>"
    "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))" "length Ts = length targs"
  shows "dsolvedB \<sigma> rb (tr t) (cpy targs u')"
proof -
  have t: "tr t = dB.Var (code (AVar v)) \<degree>\<degree> map tr targs"
    using strip_comb_list_comb[OF assms(1)] by (simp add: tr_list_comb)
  have e1: "mk_subst \<sigma> (tr t) = \<sigma> (code (AVar v)) \<degree>\<degree> map (mk_subst \<sigma>) (map tr targs)"
    unfolding t by simp
  have e2: "mk_subst \<sigma> (cpy targs u') =
      mk_subst \<sigma> (tr (types_abs Ts u')) \<degree>\<degree> map (mk_subst \<sigma>) (map tr targs)"
    using assms(4) by (simp add: cpy_def tr_types_abs)
  have "\<sigma> (code (AVar v)) \<degree>\<degree> map (mk_subst \<sigma>) (map tr targs) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      mk_subst \<sigma> (tr (types_abs Ts u')) \<degree>\<degree> map (mk_subst \<sigma>) (map tr targs)"
    by (rule equiv_list_app[OF assms(3)]) (simp add: list_all2_refl)
  then show ?thesis unfolding dsolvedB_unabs e1 e2 .
qed



subsection \<open>Building blocks of copies\<close>

lemma strip_comb_acc_fst: "fst (strip_comb_acc t ts) = head_of t"
  by (induction t ts rule: strip_comb_acc.induct) auto

lemma fst_strip_comb: "fst (strip_comb t) = head_of t"
  by (simp add: strip_comb_def strip_comb_acc_fst)

lemma hnf_Abs_head:
  "hnf u \<Longrightarrow> fst (strip_comb u) = Abs a T body \<Longrightarrow> u = Abs a T body"
  by (cases u) (auto simp: fst_strip_comb)

lemma head_of_combound: "head_of (combound t n k) = head_of t"
  by (induction k arbitrary: n) simp_all

text \<open>The projections: the \<open>i\<close>-th argument is referred to by the bound variable \<open>k - 1 - i\<close>.\<close>

lemma make_projs_ok:
  "okW (make_projs u targs0 Ts targs) ps \<Longrightarrow> length Ts = length targs \<and>
    (\<forall>(bv, T, targ)\<in>set ps. \<exists>j. bv = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length targs \<and>
      targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T \<in> set Ts)"
proof (induction u targs0 Ts targs arbitrary: ps rule: make_projs.induct)
  case (1 u targs0 T Ts targ targs)
  from "1.prems" obtain ps' where ps': "okW (make_projs u targs0 Ts targs) ps'"
    and ps: "ps = (Bound (ilength Ts), T, targ) # ps'" by auto
  note IH = "1.IH"[OF ps']
  have hd: "\<exists>j. Bound (ilength Ts) = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length (targ # targs) \<and>
      targ = (targ # targs) ! (length (targ # targs) - 1 - nat_of_integer j) \<and> T \<in> set (T # Ts)"
    using IH by (intro exI[of _ "ilength Ts"]) simp
  have tl: "\<exists>j. bv = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length (targ # targs) \<and>
      targ' = (targ # targs) ! (length (targ # targs) - 1 - nat_of_integer j) \<and> T' \<in> set (T # Ts)"
    if "(bv, T', targ') \<in> set ps'" for bv T' targ'
  proof -
    from IH that obtain j where j: "bv = Bound j" "0 \<le> j" "nat_of_integer j < length targs"
      "targ' = targs ! (length targs - 1 - nat_of_integer j)" "T' \<in> set Ts"
      by fastforce
    moreover have "(targ # targs) ! (length (targ # targs) - 1 - nat_of_integer j) =
        targs ! (length targs - 1 - nat_of_integer j)"
      using j(3) by (simp add: nth_Cons' Suc_diff_Suc)
    ultimately show ?thesis by (intro exI[of _ j]) simp
  qed
  from IH hd tl ps show ?case by fastforce
qed auto

lemma genvs_vars: "list_all2 (\<lambda>v T. \<exists>x. v = Var x T) (genvs name i n Ts) Ts"
  by (induction name i n Ts rule: genvs.induct) auto

lemma genvars_simps:
  assumes "genvars name env Ts = (env', vs)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "list_all2 (\<lambda>v T. \<exists>x. v = Var x T) vs Ts"
  using assms genvs_vars by (auto simp: genvars_def split: env.splits)

lemma make_args_props:
  assumes "make_args name Ts env Us = (env', args)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env"
    "list_all2 (\<lambda>arg U. \<exists>x. arg = combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) args Us"
proof -
  have "tenv env' = tenv env \<and> tyenv env' = tyenv env \<and>
    list_all2 (\<lambda>arg U. \<exists>x. arg = combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) args Us"
  proof (cases "Us = []")
    case True
    with assms show ?thesis by (simp add: make_args_def)
  next
    case False
    obtain env1 vs where g: "genvars name env (map (\<lambda>T. foldr fun_type Ts T) Us) = (env1, vs)"
      by (cases "genvars name env (map (\<lambda>T. foldr fun_type Ts T) Us)")
    with False assms have e: "env' = env1" "args = map (\<lambda>var. combound var 0 (length Ts)) vs"
      by (simp_all add: make_args_def)
    note gs = genvars_simps[OF g]
    from gs(3) have "list_all2 (\<lambda>v U. \<exists>x. v = Var x (foldr fun_type Ts U)) vs Us"
      by (simp add: list_all2_map2)
    then have "list_all2 (\<lambda>arg U. \<exists>x. arg = combound (Var x (foldr fun_type Ts U)) 0 (length Ts))
        (map (\<lambda>var. combound var 0 (length Ts)) vs) Us"
      by (simp add: list_all2_map1) (erule list_all2_mono; auto)
    with e gs show ?thesis by simp
  qed
  then show "tenv env' = tenv env" "tyenv env' = tyenv env"
    "list_all2 (\<lambda>arg U. \<exists>x. arg = combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) args Us"
    by simp_all
qed

lemma make_args_extends: "make_args name Ts env Us = (env', args) \<Longrightarrow> extends env' env"
  using make_args_props(1) by (simp add: extends_def)

lemma make_args_wf_env: "make_args name Ts env Us = (env', args) \<Longrightarrow> wf_env ar env \<Longrightarrow> wf_env ar env'"
  using make_args_props(1,2) by (simp add: wf_env_def)

text \<open>Copies of argument lists.\<close>

lemma copyargs_sound:
  "wf_env ar env \<Longrightarrow> \<forall>dp\<in>set dps. wf_dp ar dp \<Longrightarrow> binders_ok ar rb \<Longrightarrow>
    \<forall>t\<in>set uargs. wf_tm ar rb t \<Longrightarrow> \<forall>t\<in>set targs. wf_tm ar rb t \<Longrightarrow>
    sinv ar (GD env rb targs uargs dps) (copyargs vname rb targs env dps uargs)"
proof (induction uargs)
  case Nil
  then show ?case
    by (auto intro!: sinv.Single simp: args_ok_def wf_state_def)
next
  case (Cons uarg uargs)
  then show ?case by (auto intro!: sinv.Maps)
qed



subsection \<open>Projections and imitation\<close>

lemma test_unify_types_ground:
  "ground ar T \<Longrightarrow> ground ar U \<Longrightarrow> okW (test_unify_types alg T U env) env' \<Longrightarrow> env' = env"
  by (auto simp: test_unify_types_def okW_whenW dest: cunify_types_ground)

lemma okW_CANTUNIFY_handler:
  "okW (case e of CANTUNIFY \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> y = x"
  by (cases e) auto

lemma projenv_sound:
  assumes "okW (projenv cfg vname rb targs u env dps base Ts (Bound j) (Us, bary) targ tail) s"
    "sinv ar (GC env rb targs u dps) tail" "ground ar base" "ground ar bary"
    "wf_env ar env" "\<forall>dp\<in>set dps. wf_dp ar dp" "binders_ok ar rb" "wf_tm ar rb u"
    "\<forall>t\<in>set targs. wf_tm ar rb t" "0 \<le> j" "nat_of_integer j < length targs"
    "targ = targs ! (length targs - 1 - nat_of_integer j)" "length Ts = length targs"
    "\<forall>U\<in>set Ts. ground ar U" "\<forall>U\<in>set Us. ground ar U"
  shows "sinv ar (GC env rb targs u dps) s"
proof -
  let ?m = "(if cfg_trace_types cfg then test_unify_types (cfg_alg cfg) base bary env
    else cunify_types (cfg_alg cfg) base bary env)"
  have "okW (handleW (do {env' \<leftarrow> ?m; returnW (S_Proj vname env' Ts Us targs rb u dps (Bound j) targ tail)})
      (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)) s"
    using assms(1) by (simp add: projenv_def)
  then have "okW (do {env' \<leftarrow> ?m; returnW (S_Proj vname env' Ts Us targs rb u dps (Bound j) targ tail)}) s \<or>
    (\<exists>e. okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s)"
    unfolding okW_handleW by blast
  then show ?thesis
  proof
    assume "okW (do {env' \<leftarrow> ?m; returnW (S_Proj vname env' Ts Us targs rb u dps (Bound j) targ tail)}) s"
    then obtain env' where m: "okW ?m env'"
      and s: "s = S_Proj vname env' Ts Us targs rb u dps (Bound j) targ tail" by auto
    from m assms(3,4) have "env' = env"
      by (auto split: if_splits dest: test_unify_types_ground cunify_types_ground)
    with s assms show ?thesis by (auto intro: sinv.Proj)
  next
    assume "\<exists>e. okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s"
    then obtain e where "okW (case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e) s" by blast
    from okW_CANTUNIFY_handler[OF this] assms(2) show ?thesis by simp
  qed
qed

lemma strip_type_ground:
  assumes "vt_is_empty (tyenv env)" "ground ar T" "ok (strip_type env T) (Us, bary)"
  shows "\<forall>U\<in>set Us. ground ar U" "ground ar bary"
  using assms binder_types_ground[OF assms(1,2)] body_type_ground[OF assms(1,2)]
  by (auto simp: strip_type_def)

lemma matchfun_sound:
  "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) s \<Longrightarrow>
    \<forall>(bv, T, targ)\<in>set projs. \<exists>j. bv = Bound j \<and> 0 \<le> j \<and> nat_of_integer j < length targs \<and>
      targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T \<in> set Ts \<Longrightarrow>
    ground ar base \<Longrightarrow> \<forall>U\<in>set Ts. ground ar U \<Longrightarrow> length Ts = length targs \<Longrightarrow>
    wf_env ar env \<Longrightarrow> \<forall>dp\<in>set dps. wf_dp ar dp \<Longrightarrow> binders_ok ar rb \<Longrightarrow> wf_tm ar rb u \<Longrightarrow>
    \<forall>t\<in>set targs. wf_tm ar rb t \<Longrightarrow> strip_comb u = (uhead, uargs) \<Longrightarrow>
    sinv ar (GC env rb targs u dps) s"
proof (induction projs arbitrary: s)
  case Nil
  from wf_tm_strip_comb[OF Nil.prems(11,9)]
  have hd: "wf_tm ar rb uhead" and as: "\<forall>t\<in>set uargs. wf_tm ar rb t" by simp_all
  note ca = copyargs_sound[OF Nil.prems(6,7,8) as Nil.prems(10), of vname]
  show ?case
  proof (cases uhead)
    case (Const a T)
    with Nil.prems(1) have "s = S_MapJoin uhead (copyargs vname rb targs env dps uargs)" by simp
    with Const hd ca Nil.prems(11) show ?thesis by (auto simp: wf_tm_def intro: sinv.MapJoin)
  next
    case (Free a T)
    with Nil.prems(1) have "s = S_MapJoin uhead (copyargs vname rb targs env dps uargs)" by simp
    with Free hd ca Nil.prems(11) show ?thesis by (auto simp: wf_tm_def intro: sinv.MapJoin)
  qed (use Nil.prems(1) in \<open>auto intro: sinv.Empty\<close>)
next
  case (Cons p projs)
  obtain bv T targ where p: "p = (bv, T, targ)" by (cases p)
  with Cons.prems(2) obtain j where j: "bv = Bound j" "0 \<le> j" "nat_of_integer j < length targs"
    "targ = targs ! (length targs - 1 - nat_of_integer j)" "T \<in> set Ts" by auto
  from Cons.prems(1) p obtain Usb tail where st: "ok (strip_type env T) Usb"
    and tl: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) tail"
    and pe: "okW (projenv cfg vname rb targs u env dps base Ts bv Usb targ tail) s"
    by auto
  obtain Us bary where Usb: "Usb = (Us, bary)" by (cases Usb)
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF Cons.prems(6)])
  have gT: "ground ar T" using Cons.prems(4) j(5) by blast
  note sg = strip_type_ground[OF e gT st[unfolded Usb]]
  have "sinv ar (GC env rb targs u dps) tail"
    using Cons.IH[OF tl] Cons.prems(2-11) by simp
  from projenv_sound[OF pe[unfolded Usb j(1)] this Cons.prems(3) sg(2) Cons.prems(6-10) j(2-4)
      Cons.prems(5,4) sg(1)]
  show ?case .
qed


subsection \<open>Copies\<close>

lemma mc_sound:
  "okW (mc cfg vname rb targs u env dps) s \<Longrightarrow> wf_env ar env \<Longrightarrow> \<forall>dp\<in>set dps. wf_dp ar dp \<Longrightarrow>
    binders_ok ar rb \<Longrightarrow> wf_tm ar rb u \<Longrightarrow> hnf u \<Longrightarrow> \<forall>t\<in>set targs. wf_tm ar rb t \<Longrightarrow>
    sinv ar (GC env rb targs u dps) s"
proof (induction cfg vname rb targs u env dps arbitrary: s rule: mc.induct)
  case (1 cfg vname rb targs u env dps)
  note mc = "1.prems"(1) and wenv = "1.prems"(2) and wdps = "1.prems"(3) and bok = "1.prems"(4)
    and wu = "1.prems"(5) and hu = "1.prems"(6) and wtargs = "1.prems"(7)
  define uhead where "uhead = fst (strip_comb u)"
  define uargs where "uargs = snd (strip_comb u)"
  have sc: "strip_comb u = (uhead, uargs)" by (simp add: uhead_def uargs_def)
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wenv])
  from wf_tm_strip_comb[OF sc wu] have whd: "wf_tm ar rb uhead" and wargs: "\<forall>t\<in>set uargs. wf_tm ar rb t"
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
  have gT0: "ground ar T0" using fastype_ground[OF e bok _ f0[unfolded okW_liftM]] whd
    by (simp add: wf_tm_def)
  have gbase: "ground ar base" by (rule body_type_ground[OF e gT0 b[unfolded okW_liftM]])
  from tsf have "list_all2 (\<lambda>x y. ok (fastype env rb x) y) targs Ts" by (simp add: ok_mapM)
  then have lTs: "length Ts = length targs" by (simp add: list_all2_conv_all_nth)
  have gTs: "\<forall>U\<in>set Ts. ground ar U"
  proof
    fix U assume "U \<in> set Ts"
    then obtain i where i: "i < length Ts" "U = Ts ! i" by (auto simp: in_set_conv_nth)
    with \<open>list_all2 _ targs Ts\<close> have "ok (fastype env rb (targs ! i)) U"
      by (simp add: list_all2_conv_all_nth)
    moreover have "typs_ok ar (targs ! i)" using wtargs i lTs by (simp add: wf_tm_def)
    ultimately show "ground ar U" by (rule fastype_ground[OF e bok, rotated])
  qed
  show ?case
  proof (cases uhead)
    case (Abs a T body)
    have u: "u = Abs a T body" using hnf_Abs_head[OF hu] Abs by (simp add: uhead_def)
    from rest Abs obtain s' where s': "okW (mc cfg vname ((a, T) # rb)
        (map (incr_boundvars 1) targs @ [Bound 0]) body env dps) s'" and s: "s = S_MapAbs a T s'"
      by auto
    have gT: "ground ar T" using wu u by (simp add: wf_tm_def)
    have bok': "binders_ok ar ((a, T) # rb)" using bok gT by (simp add: binders_ok_def)
    have wb: "wf_tm ar ((a, T) # rb) body" using wu u by (simp add: wf_tm_def)
    have hb: "hnf body" using hu u by simp
    have wt': "\<forall>t\<in>set (map (incr_boundvars 1) targs @ [Bound 0]). wf_tm ar ((a, T) # rb) t"
      using wtargs by (auto intro: wf_tm_incr wf_tm_Bound0)
    from "1.IH"[OF uhead_def uargs_def f0 b tsf Abs s' wenv wdps bok' wb hb wt']
    have "sinv ar (GC env ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body dps) s'" .
    moreover have "\<forall>t\<in>set targs. proper t" using wtargs by (simp add: wf_tm_def)
    ultimately show ?thesis using s u gT by (auto intro: sinv.MapAbs)
  next
    case (Var w W)
    obtain env' newhd where g: "genvar (fst w) env (foldr fun_type Ts base) = (env', newhd)"
      by (cases "genvar (fst w) env (foldr fun_type Ts base)")
    with rest Var have s: "s = S_Single (El_C (combound newhd 0 (length Ts)) env'
        ((rb, list_comb newhd targs, u) # dps))" by simp
    note gs = genvar_simps[OF g]
    have gty: "ground ar (foldr fun_type Ts base)" by (rule ground_foldr_fun_type[OF gTs gbase])
    have whd': "wf_tm ar rb newhd" "no_loose_bound (tr newhd) 0" "typs_ok ar newhd" "proper newhd"
      using gs(4) gty by (simp_all add: wf_tm_def)
    have ws: "wf_state ar env env' ((rb, list_comb newhd targs, u) # dps)"
      using genvar_extends[OF g] genvar_wf_env[OF g wenv] wdps bok wu whd'(1) wtargs
      by (auto simp: wf_state_def wf_tm_list_comb)
    have wc: "wf_cp ar (length targs) (combound newhd 0 (length Ts))"
      using wf_cp_combound[OF whd'(3,2,4)] lTs by simp
    have "copy_ok ar env rb targs u dps (combound newhd 0 (length Ts)) env'
        ((rb, list_comb newhd targs, u) # dps)"
      unfolding copy_ok_def
    proof (intro conjI allI impI ws wc)
      fix \<sigma> assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'"
        and sol: "dsolved_all \<sigma> ((rb, list_comb newhd targs, u) # dps)"
      have "dsolvedB \<sigma> rb (tr (list_comb newhd targs)) (tr u)"
        using sol by (simp add: dsolved_dsolvedB)
      moreover have "dsolvedB \<sigma> rb (cpy targs (combound newhd 0 (length Ts))) (tr (list_comb newhd targs))"
        using dsolvedB_equiv[OF \<sigma>(1) cpy_combound[OF whd'(2)]] lTs by simp
      ultimately show "dsolvedB \<sigma> rb (cpy targs (combound newhd 0 (length Ts))) (tr u)"
        by (rule dsolvedB_trans[rotated])
      show "dsolved_all \<sigma> dps" using sol by simp
    qed
    with s show ?thesis by (auto intro: sinv.Single)
  next
    case (Const a T)
    with rest obtain projs where pr: "okW (make_projs u targs Ts targs) projs"
      and m: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (rev projs)) s" by auto
    from make_projs_ok[OF pr] have "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
        nat_of_integer j < length targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T \<in> set Ts"
      by simp
    from matchfun_sound[OF m this gbase gTs lTs wenv wdps bok wu wtargs sc] show ?thesis .
  next
    case (Free a T)
    with rest obtain projs where pr: "okW (make_projs u targs Ts targs) projs"
      and m: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (rev projs)) s" by auto
    from make_projs_ok[OF pr] have "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
        nat_of_integer j < length targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T \<in> set Ts"
      by simp
    from matchfun_sound[OF m this gbase gTs lTs wenv wdps bok wu wtargs sc] show ?thesis .
  next
    case (Bound i)
    with rest obtain projs where pr: "okW (make_projs u targs Ts targs) projs"
      and m: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (rev projs)) s" by auto
    from make_projs_ok[OF pr] have "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
        nat_of_integer j < length targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T \<in> set Ts"
      by simp
    from matchfun_sound[OF m this gbase gTs lTs wenv wdps bok wu wtargs sc] show ?thesis .
  next
    case (App f x)
    with rest obtain projs where pr: "okW (make_projs u targs Ts targs) projs"
      and m: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (rev projs)) s" by auto
    from make_projs_ok[OF pr] have "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>j. bv = Bound j \<and> 0 \<le> j \<and>
        nat_of_integer j < length targs \<and> targ = targs ! (length targs - 1 - nat_of_integer j) \<and> T \<in> set Ts"
      by simp
    from matchfun_sound[OF m this gbase gTs lTs wenv wdps bok wu wtargs sc] show ?thesis .
  qed
qed


subsection \<open>\<open>MATCH\<close>\<close>

theorem MATCH_sound:
  assumes "okW (MATCH cfg env dp dpairs) s" "reduces ar env0 dps0 env (dp # dpairs)" "frs_ok dp"
  shows "sinv ar (GE env0 dps0) s"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from assms(1) dp obtain v T targs where sc: "strip_comb t = (Var v T, targs)"
    by (auto simp: MATCH_def split: prod.splits pterm.splits)
  with assms(1) dp obtain Ts s' where bt: "ok (binder_types env T) Ts"
    and m: "okW (mc cfg (fst v) rb targs u env dpairs) s'" and s: "s = S_MapNewDset (v, T) Ts s'"
    by (auto simp: MATCH_def)
  have ws: "wf_state ar env0 env (dp # dpairs)" using assms(2) by (simp add: reduces_def)
  then have wenv: "wf_env ar env" and wdp: "wf_dp ar dp" and wdps: "\<forall>dp\<in>set dpairs. wf_dp ar dp"
    by (simp_all add: wf_state_def)
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wenv])
  from wdp dp have bok: "binders_ok ar rb" and wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u" by simp_all
  from wf_tm_strip_comb[OF sc wt] have wv: "wf_tm ar rb (Var v T)" and wtargs: "\<forall>t\<in>set targs. wf_tm ar rb t"
    by simp_all
  have gT: "ground ar T" using wv by (simp add: wf_tm_def)
  have gTs: "\<forall>U\<in>set Ts. ground ar U" by (rule binder_types_ground[OF e gT bt])
  from assms(3) dp have sat0: "satT0 (map snd rb) t" and hu: "hnf u" by simp_all
  have "satT env (map snd rb) t" using sat0 satT_satT0[OF e] by simp
  from satT_binder_types[OF e this sc gT bt] have lTs: "length Ts = length targs" .
  have "sinv ar (GC env rb targs u dpairs) s'" by (rule mc_sound[OF m wenv wdps bok wu hu wtargs])
  with assms(2) dp sc lTs gTs show ?thesis unfolding s by (auto intro: sinv.MapNewDset)
qed


subsection \<open>\<open>new_dset\<close>\<close>

lemma wf_tm_types_abs:
  assumes "\<forall>U\<in>set Ts. ground ar U" "wf_cp ar (length Ts) u'"
  shows "wf_tm ar [] (types_abs Ts u')"
proof -
  have "proper u'" "typs_ok ar u'" using assms(2) by (simp_all add: wf_cp_def)
  then have "proper (types_abs Ts u')" "typs_ok ar (types_abs Ts u')"
    using assms(1) by (induction Ts) simp_all
  moreover have "no_loose_bound (tr (types_abs Ts u')) 0"
    using assms(2) by (simp add: wf_cp_def tr_types_abs loose_bound_Abs_m)
  ultimately show ?thesis by (simp add: wf_tm_def)
qed

text \<open>Binding the variable of the flex-rigid pair to the abstraction of a copy solves the pair.\<close>

lemma new_dset_semantics:
  assumes "reduces ar env0 dps0 env1 ((rb, t, u) # dps1)" "strip_comb t = (Var v T, targs)"
    "length Ts = length targs" "copy_ok ar env1 rb targs u dps1 u' env' dpairs'"
    "closed_on UNIV \<sigma>" "sat \<sigma> env'" "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
    "dsolved_all \<sigma> dpairs'"
  shows "dsolved_all \<sigma> dps0"
proof -
  from assms(4-6,8) have c: "dsolvedB \<sigma> rb (cpy targs u') (tr u)" and d1: "dsolved_all \<sigma> dps1"
    by (simp_all add: copy_ok_def)
  have "dsolvedB \<sigma> rb (tr t) (cpy targs u')" by (rule dsolvedB_flex_binding[OF assms(2,5,7,3)])
  from dsolvedB_trans[OF this c] have "dsolved \<sigma> (rb, t, u)" by (simp add: dsolved_dsolvedB)
  with d1 have d: "dsolved_all \<sigma> ((rb, t, u) # dps1)" by simp
  have "extends env' env1" using assms(4) by (simp add: copy_ok_def wf_state_def)
  with assms(6) have s1: "sat \<sigma> env1" by (rule sat_extends)
  from assms(1) have "closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env1 \<longrightarrow> dsolved_all \<sigma> ((rb, t, u) # dps1) \<longrightarrow>
      dsolved_all \<sigma> dps0" unfolding reduces_def by blast
  with assms(5) s1 d show ?thesis by blast
qed

lemma new_dset_sound:
  assumes "okW (new_dset (v, T) Ts u' env' dpairs') y"
    "reduces ar env0 dps0 env1 ((rb, t, u) # dps1)" "strip_comb t = (Var v T, targs)"
    "length Ts = length targs" "\<forall>U\<in>set Ts. ground ar U"
    "copy_ok ar env1 rb targs u dps1 u' env' dpairs'"
  shows "elem_ok ar (GE env0 dps0) y"
proof -
  have ws1: "wf_state ar env0 env1 ((rb, t, u) # dps1)" using assms(2) by (simp add: reduces_def)
  have ws: "wf_state ar env1 env' dpairs'" and wc: "wf_cp ar (length targs) u'"
    using assms(6) by (simp_all add: copy_ok_def)
  have ws': "wf_state ar env0 env' dpairs'" by (rule wf_state_extends[OF ws wf_stateD(1)[OF ws1]])
  have wenv: "wf_env ar env'" by (rule wf_stateD(2)[OF ws])
  have e: "vt_is_empty (tyenv env')" by (rule wf_envD(1)[OF wenv])
  have "wf_tm ar rb t" using wf_stateD(3)[OF ws1, of "(rb, t, u)"] by simp
  from wf_tm_strip_comb[OF assms(3) this] have gT: "ground ar T" by (simp add: wf_tm_def)
  have wa: "wf_tm ar [] (types_abs Ts u')" by (rule wf_tm_types_abs[OF assms(5)]) (use wc assms(4) in simp)
  from assms(1) obtain r where lk: "ok (lookup env' v T) r"
    and rest: "okW (case r of
        None \<Rightarrow> do {env'' \<leftarrow> liftM (update (v, T) (types_abs Ts u') env'); returnW (El_E env'' dpairs')}
      | Some s \<Rightarrow> returnW (El_E env' (([], s, types_abs Ts u') # dpairs'))) y"
    by (auto simp: new_dset_def)
  from ok_lookup[OF e lk] show ?thesis
  proof (elim disjE exE conjE)
    assume "r = None"
    with rest obtain env'' where upd: "ok (update (v, T) (types_abs Ts u') env') env''"
      and y: "y = El_E env'' dpairs'" by auto
    have ext: "extends env'' env'" by (rule ok_update_extends[OF upd])
    have "wf_env ar env''"
      using ok_update_wf_env[OF upd wenv _ _ gT] wa by (simp add: wf_tm_def)
    then have "wf_state ar env0 env'' dpairs'"
      using ws' ext by (auto simp: wf_state_def intro: extends_trans)
    moreover have "dsolved_all \<sigma> dps0"
      if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env''" "dsolved_all \<sigma> dpairs'" for \<sigma>
    proof (rule new_dset_semantics[OF assms(2,3,4,6) \<sigma>(1) sat_extends[OF \<sigma>(2) ext] _ \<sigma>(3)])
      show "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
        by (rule satD[OF \<sigma>(2) ok_update_lookup[OF upd]])
    qed
    ultimately show ?thesis unfolding y elem_ok.simps reduces_def by blast
  next
    fix s assume r: "r = Some s" and lks: "vt_lookup (tenv env') v = Some (T, s)"
    from rest r have y: "y = El_E env' (([], s, types_abs Ts u') # dpairs')" by simp
    have "wf_tm ar [] s" using wf_envD[OF wenv] lks by (auto simp: wf_env_def wf_tm_def)
    with wa ws' have "wf_state ar env0 env' (([], s, types_abs Ts u') # dpairs')"
      by (simp add: wf_state_def binders_ok_def)
    moreover have "dsolved_all \<sigma> dps0"
      if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'" "dsolved_all \<sigma> (([], s, types_abs Ts u') # dpairs')"
      for \<sigma>
    proof (rule new_dset_semantics[OF assms(2,3,4,6) \<sigma>(1,2) _])
      have "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
        using \<sigma>(3) by (simp add: dsolved_def)
      with satD[OF \<sigma>(2) lks] show "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts u'))"
        by (rule equiv_trans)
      show "dsolved_all \<sigma> dpairs'" using \<sigma>(3) by simp
    qed
    ultimately show ?thesis unfolding y elem_ok.simps reduces_def by blast
  qed
qed

end
