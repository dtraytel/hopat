section \<open>Soundness of \<open>MATCH\<close>\<close>

theory Unify_Match
  imports Unify_Shape
begin

context csig
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
  "wf_state ar env0 env dps \<longleftrightarrow> extends env0 env \<and> wf_env ar env \<and> (\<forall>dp\<in>set dps. wf_dp ar dp)"

definition reduces :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "reduces ar env0 dps0 env dps \<longleftrightarrow> wf_state ar env0 env dps \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow> dsolved_all \<sigma> dps0)"

definition unifier :: "env \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "unifier env0 dps0 env tps \<longleftrightarrow> extends env0 env \<and>
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

end

datatype goal =
  GR env "dpair list"
| GE env "dpair list"
| GC env binders "pterm list" pterm "dpair list"
| GD env binders "pterm list" "pterm list" "dpair list"
| GS env "dpair list" nat

context csig
begin

fun elem_ok :: "(name \<Rightarrow> nat) \<Rightarrow> goal \<Rightarrow> elem \<Rightarrow> bool" where
  "elem_ok ar (GR env0 dps0) (El_R env tps) \<longleftrightarrow> unifier env0 dps0 env tps"
| "elem_ok ar (GE env0 dps0) (El_E env dps) \<longleftrightarrow> reduces ar env0 dps0 env dps"
| "elem_ok ar (GC env0 rb targs u dps0) (El_C u' env dps) \<longleftrightarrow> copy_ok ar env0 rb targs u dps0 u' env dps"
| "elem_ok ar (GD env0 rb targs uargs dps0) (El_D uargs' env dps) \<longleftrightarrow>
    args_ok ar env0 rb targs uargs dps0 uargs' env dps"
| "elem_ok ar (GS env0 dps0 k) (El_C u' env dps) \<longleftrightarrow> wf_state ar env0 env dps \<and> wf_cp ar k u' \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env \<longrightarrow> dsolved_all \<sigma> dps \<longrightarrow> dsolved_all \<sigma> dps0)"
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
| MapNewDset1: "reduces ar env0 dps0 env1 dps1 \<Longrightarrow> ground ar T \<Longrightarrow> \<forall>U\<in>set Ts. ground ar U \<Longrightarrow>
    sinv ar (GS env1 dps1 (length Ts)) xq \<Longrightarrow> sinv ar (GE env0 dps0) (S_MapNewDset (v, T) Ts xq)"
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
    proper uhead \<Longrightarrow> sinv ar (GD env0 rb targs uargs dps0) xq \<Longrightarrow> sinv ar (GC env0 rb targs u dps0) (S_MapJoin uhead xq)"
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

subsection \<open>Ground types\<close>

text \<open>
  On ground types, the guesses of arities for type variables do not apply: \<^const>\<open>MATCH\<close>,
  \<^const>\<open>matchfun\<close>, \<^const>\<open>match1_projs\<close> and \<^const>\<open>copycons\<close> take the steps of
  \<open>unify.ML\<close>.
\<close>

lemma liftM_return: "liftM (return x) = returnW x"
  by (simp add: liftM_def return_def returnW_def)

lemma ground_not_TVar: "ground ar T \<Longrightarrow> \<not> is_TVar T"
  by (cases T) simp_all

lemma arity_guesses_not_TVar: "\<not> is_TVar T \<Longrightarrow> arity_guesses cfg T = [0]"
  by (simp add: arity_guesses_def)

lemma foldrW_arity_guesses_ground: "ground ar T \<Longrightarrow> foldrW f (arity_guesses cfg T) b = f 0 b"
  by (simp add: arity_guesses_not_TVar ground_not_TVar)

lemma gentvars_0[simp]: "gentvars 0 env = (env, [])"
  by (simp add: gentvars_def)

lemma projenv_0:
  "projenv cfg vname rbinder targs u env dpairs base Ts head Usb targ 0 tail =
    (case Usb of (Us, bary) \<Rightarrow>
      handleW
        (do {
          env' \<leftarrow>
            (if cfg_trace_types cfg then test_unify_types (cfg_alg cfg) base bary env
             else cunify_types (cfg_alg cfg) base bary env);
          returnW (S_Proj vname env' Ts Us targs rbinder u dpairs head targ tail)})
        (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e))"
  by (simp add: projenv_def proj_unify_def split: prod.splits)

lemma body_type_ground_ex:
  assumes "vt_is_empty (tyenv env)"
  shows "ground ar T \<Longrightarrow> \<exists>B. body_type env T = return B"
proof (induction T)
  case (Type a Ts)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
    case True
    then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by auto
    have "ground ar U" using Type.prems Ts by simp
    with Type.IH[of U] Ts obtain B where "body_type env U = return B" by auto
    with Ts a show ?thesis by (subst body_type.simps) auto
  next
    case False
    then show ?thesis by (subst body_type.simps) (auto split: list.splits)
  qed
qed (subst body_type.simps, auto)+

lemma eta_expand_dpair_Nil[simp]: "eta_expand_dpair [] dp = dp"
  by (cases dp) (simp add: eta_expand_dpair_def incr_boundvars_def)

subsection \<open>Projections and imitation\<close>

lemma strip_type_ground:
  assumes "vt_is_empty (tyenv env)" "ground ar T" "ok (strip_type env T) (Us, bary)"
  shows "\<forall>U\<in>set Us. ground ar U" "ground ar bary"
  using assms binder_types_ground[OF assms(1,2)] body_type_ground[OF assms(1,2)]
  by (auto simp: strip_type_def)

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

end

end
