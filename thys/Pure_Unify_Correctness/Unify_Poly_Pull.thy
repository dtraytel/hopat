section \<open>Problems with Type Variables: Soundness of the Search\<close>

theory Unify_Poly_Pull
  imports Unify_Poly_Flexflex Unify_Pull
begin

context csig
begin

text \<open>
  The soundness of the search of theory \<^theory>\<open>Pure_Unify_Correctness.Unify_Pull\<close>, for problems
  whose types contain type variables: every unifier that \<open>hounifiers\<close> enumerates solves the
  input pairs, for every type instantiation that solves its type environment and every closed
  substitution that satisfies the type instance of its environment and solves the type instances of
  its flex-flex pairs.
\<close>

subsection \<open>Inversion of the invariant\<close>

inductive_cases psinv_SingleE: "psinv ar G (S_Single x)"
inductive_cases psinv_AddUnifyE: "psinv ar G (S_AddUnify td env dps reseq)"
inductive_cases psinv_ItRightE: "psinv ar G (S_ItRight td xq yq)"
inductive_cases psinv_MapNewDsetE: "psinv ar G (S_MapNewDset vT Ts xq)"
inductive_cases psinv_MapAbsE: "psinv ar G (S_MapAbs a T xq)"
inductive_cases psinv_ProjE: "psinv ar G (S_Proj vname env Ts Us targs rb u dps head targ tail)"
inductive_cases psinv_MapJoinE: "psinv ar G (S_MapJoin uhead xq)"
inductive_cases psinv_MapsE: "psinv ar G (S_Maps vname rb targs uarg xq)"
inductive_cases psinv_AppendE: "psinv ar G (S_Append xq yq)"
inductive_cases psinv_MapConsE: "psinv ar G (S_MapCons uargs xq)"


subsection \<open>The elements of the closures\<close>

lemma mapabs_pcopy:
  assumes "pcopy_ok ar env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body dps0 body' env dps"
    "wft ar T" "\<forall>t\<in>set targs. proper t"
  shows "pcopy_ok ar env0 rb targs (Abs b T' body) dps0 (Abs a T body') env dps"
  unfolding pcopy_ok_def
proof (intro conjI allI impI)
  show "pwf_state ar env0 env dps" using assms(1) by (simp add: pcopy_ok_def)
  have w: "swf_cp ar (Suc (length targs)) body'" using assms(1) by (simp add: pcopy_ok_def)
  then show "swf_cp ar (length targs) (Abs a T body')" using assms(2) by (simp add: swf_cp_def)
  fix \<sigma> assume \<sigma>: "psat \<sigma> env" "dsolved_all \<sigma> dps"
  with assms(1) have c: "dsolvedB \<sigma> ((a, T) # rb) (cpy (map (incr_boundvars 1) targs @ [Bound 0]) body') (tr body)"
    and "dsolved_all \<sigma> dps0" by (simp_all add: pcopy_ok_def)
  then show "dsolved_all \<sigma> dps0" by simp
  from c have "dsolvedB \<sigma> rb (dB.Abs (cpy (map (incr_boundvars 1) targs @ [Bound 0]) body')) (dB.Abs (tr body))"
    by (simp add: dsolvedB_Abs)
  moreover have "dsolvedB \<sigma> rb (cpy targs (Abs a T body')) (dB.Abs (cpy (map (incr_boundvars 1) targs @ [Bound 0]) body'))"
    by (rule dsolvedB_sym[OF dsolvedB_equiv[OF psatD(1)[OF \<sigma>(1)] cpy_Abs]])
      (use w assms(3) in \<open>simp_all add: swf_cp_def\<close>)
  ultimately show "dsolvedB \<sigma> rb (cpy targs (Abs a T body')) (tr (Abs b T' body))"
    by (simp add: dsolvedB_trans)
qed

lemma mapjoin_pcopy:
  assumes "strip_comb u = (uhead, uargs)" "no_loose_bound (tr uhead) 0" "twft ar uhead" "proper uhead"
    "pargs_ok ar env0 rb targs uargs dps0 uargs' env dps"
  shows "pcopy_ok ar env0 rb targs u dps0 (list_comb uhead uargs') env dps"
  unfolding pcopy_ok_def
proof (intro conjI allI impI)
  show "pwf_state ar env0 env dps" using assms(5) by (simp add: pargs_ok_def)
  have "\<forall>a'\<in>set uargs'. swf_cp ar (length targs) a'" using assms(5) by (simp add: pargs_ok_def)
  with assms(2-4) show "swf_cp ar (length targs) (list_comb uhead uargs')"
    by (auto simp: swf_cp_def proper_list_comb twft_list_comb tr_list_comb no_loose_bound_list_app
        intro: no_loose_bound_mono)
  fix \<sigma> assume \<sigma>: "psat \<sigma> env" "dsolved_all \<sigma> dps"
  with assms(5) have l: "list_all2 (\<lambda>a' a. dsolvedB \<sigma> rb (cpy targs a') (tr a)) uargs' uargs"
    and "dsolved_all \<sigma> dps0" by (simp_all add: pargs_ok_def)
  then show "dsolved_all \<sigma> dps0" by simp
  have "dsolvedB \<sigma> rb (tr uhead \<degree>\<degree> map (cpy targs) uargs') (tr uhead \<degree>\<degree> map tr uargs)"
    by (rule dsolvedB_apps) (use l in \<open>simp_all add: list_all2_map1 list_all2_map2\<close>)
  moreover have "tr u = tr uhead \<degree>\<degree> map tr uargs"
    using strip_comb_list_comb[OF assms(1)] by (simp add: tr_list_comb)
  moreover have "dsolvedB \<sigma> rb (cpy targs (list_comb uhead uargs')) (tr uhead \<degree>\<degree> map (cpy targs) uargs')"
    by (rule dsolvedB_equiv[OF psatD(1)[OF \<sigma>(1)] cpy_imitate[OF assms(2)]])
  ultimately show "dsolvedB \<sigma> rb (cpy targs (list_comb uhead uargs')) (tr u)"
    by (auto intro: dsolvedB_trans)
qed

lemma mapcons_pargs:
  assumes "pargs_ok ar env0 rb targs uargs dps0 uargs' env dps"
    "pcopy_ok ar env rb targs u2 dps uarg' env' dps'" "env \<Turnstile>\<^sub>p rlist_abs rb uarg \<approx> rlist_abs rb u2"
  shows "pargs_ok ar env0 rb targs (uarg # uargs) dps0 (uarg' # uargs') env' dps'"
proof -
  have w1: "pwf_state ar env0 env dps" and w2: "pwf_state ar env env' dps'"
    using assms(1,2) by (simp_all add: pargs_ok_def pcopy_ok_def)
  have "list_all2 (\<lambda>a' a. dsolvedB \<sigma> rb (cpy targs a') (tr a)) (uarg' # uargs') (uarg # uargs) \<and>
      dsolved_all \<sigma> dps0"
    if \<sigma>: "psat \<sigma> env'" "dsolved_all \<sigma> dps'" for \<sigma>
  proof -
    from assms(2) \<sigma> have c: "dsolvedB \<sigma> rb (cpy targs uarg') (tr u2)" and d: "dsolved_all \<sigma> dps"
      by (simp_all add: pcopy_ok_def)
    have s: "psat \<sigma> env" by (rule psat_pextends[OF \<sigma>(1) pwf_stateD(1)[OF w2]])
    with assms(1) d have l: "list_all2 (\<lambda>a' a. dsolvedB \<sigma> rb (cpy targs a') (tr a)) uargs' uargs"
      and d0: "dsolved_all \<sigma> dps0" by (simp_all add: pargs_ok_def)
    have "dsolvedB \<sigma> rb (tr uarg) (tr u2)"
      using penv_equiv_dsolved'[OF assms(3) s] by (simp add: dsolved_dsolvedB)
    with c have "dsolvedB \<sigma> rb (cpy targs uarg') (tr uarg)" by (blast intro: dsolvedB_trans dsolvedB_sym)
    with l d0 show ?thesis by simp
  qed
  moreover have "pwf_state ar env0 env' dps'" by (rule pwf_state_pextends[OF w2 pwf_stateD(1)[OF w1]])
  moreover have "length uargs' = length uargs" "\<forall>a'\<in>set uargs'. swf_cp ar (length targs) a'"
    using assms(1) unfolding pargs_ok_def by blast+
  moreover have "swf_cp ar (length targs) uarg'" using assms(2) unfolding pcopy_ok_def by blast
  ultimately show ?thesis unfolding pargs_ok_def by (metis length_Cons set_ConsD)
qed

lemma make_args_pargs:
  assumes "make_args vname Ts env Us = (env', args)" "\<forall>U\<in>set Ts. wft ar U" "\<forall>U\<in>set Us. wft ar U"
    "arg \<in> set args"
  obtains G where "arg = combound G 0 (length Ts)" "head_of G = G" "swf_tm ar rb G" "no_loose_bound (tr G) 0"
    "twft ar G" "proper G"
proof -
  from assms(4) obtain i where i: "i < length args" "arg = args ! i" by (auto simp: in_set_conv_nth)
  have l: "list_all2 (\<lambda>arg U. \<exists>x. arg = combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) args Us"
    by (rule make_args_props(3)[OF assms(1)])
  then have "\<exists>x. args ! i = combound (Var x (foldr fun_type Ts (Us ! i))) 0 (length Ts)" "i < length Us"
    using i(1) by (simp_all add: list_all2_conv_all_nth)
  then obtain x where
    "Us ! i \<in> set Us" "arg = combound (Var x (foldr fun_type Ts (Us ! i))) 0 (length Ts)"
    using i(2) by auto
  then obtain U where "U \<in> set Us" "arg = combound (Var x (foldr fun_type Ts U)) 0 (length Ts)"
    by blast
  moreover from this have "wft ar (foldr fun_type Ts U)"
    using assms(2,3) by (simp add: wft_foldr_fun_type)
  ultimately show ?thesis using that[of "Var x (foldr fun_type Ts U)"] by (simp add: swf_tm_def)
qed

lemma proj_pcopy:
  assumes "make_args vname Ts env' Us = (env'', args)"
    "okW (SIMPL alg env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (env2, frigid, fflex)"
    "pextends env env'" "swf_env ar env'" "\<forall>dp\<in>set dps. swf_dp ar dp" "sbinders ar rb" "swf_tm ar rb u"
    "\<forall>t\<in>set targs. swf_tm ar rb t" "0 \<le> j" "nat_of_integer j < length targs"
    "targ = targs ! (length targs - 1 - nat_of_integer j)" "length Ts = length targs"
    "\<forall>U\<in>set Ts. wft ar U" "\<forall>U\<in>set Us. wft ar U"
  shows "pcopy_ok ar env rb targs u dps (list_comb (Bound j) args) env2 (frigid @ fflex)"
proof -
  let ?dp = "(rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u)"
  note margs = make_args_pargs[OF assms(1,13,14)]
  have wenv'': "swf_env ar env''" by (rule make_args_swf_env[OF assms(1,4)])
  have wtarg: "swf_tm ar rb targ" using assms(8,10,11) by simp
  have "swf_tm ar rb (list_comb (head_of arg) targs)" if a: "arg \<in> set args" for arg
  proof -
    obtain G where "arg = combound G 0 (length Ts)" "head_of G = G" "swf_tm ar rb G"
      using margs[OF a] by metis
    with assms(8) show ?thesis by (simp add: head_of_combound swf_tm_list_comb)
  qed
  with wtarg assms(6,7) have wdp: "swf_dp ar ?dp" by (auto simp: swf_tm_list_comb)
  from assms(2) obtain evs where "SIMPL alg env'' (?dp # dps) = Some (evs, UOk (env2, frigid, fflex))"
    by blast
  from SIMPL_ssound[OF this _ wenv'', of "(env2, frigid, fflex)"] wdp assms(5)
  have ws: "swf_st ar (env2, frigid, fflex)" and sr: "psimp_rel (?dp # dps) (env'', [], []) (env2, frigid, fflex)"
    by auto
  have ext: "pextends env env2"
    using psimp_relD(1)[OF sr] make_args_pextends[OF assms(1)] assms(3) by (auto intro: pextends_trans)
  have wst: "pwf_state ar env env2 (frigid @ fflex)" using ws ext by (auto simp: pwf_state_def)
  have wca: "swf_cp ar (length targs) arg" if a: "arg \<in> set args" for arg
  proof -
    obtain G where "arg = combound G 0 (length Ts)" "no_loose_bound (tr G) 0" "twft ar G" "proper G"
      using margs[OF a] by metis
    with swf_cp_combound[of ar G "length Ts"] assms(12) show ?thesis by simp
  qed
  have wc: "swf_cp ar (length targs) (list_comb (Bound j) args)"
    using wca assms(9,10)
    by (auto simp: swf_cp_def proper_list_comb twft_list_comb tr_list_comb no_loose_bound_list_app)
  have "dsolvedB \<sigma> rb (cpy targs (list_comb (Bound j) args)) (tr u) \<and> dsolved_all \<sigma> dps"
    if \<sigma>: "psat \<sigma> env2" "dsolved_all \<sigma> (frigid @ fflex)" for \<sigma>
  proof -
    from psimp_relD(2)[OF sr] \<sigma>(1,2) have d: "dsolved \<sigma> ?dp" "dsolved_all \<sigma> dps" by auto
    have "cpy targs arg \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (list_comb (head_of arg) targs)" if a: "arg \<in> set args" for arg
    proof -
      obtain G where "arg = combound G 0 (length Ts)" "no_loose_bound (tr G) 0" "head_of G = G"
        using margs[OF a] by metis
      with cpy_combound[of G targs] assms(12) show ?thesis by (simp add: head_of_combound)
    qed
    then have "tr targ \<degree>\<degree> map (cpy targs) args \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        tr targ \<degree>\<degree> map (\<lambda>arg. tr (list_comb (head_of arg) targs)) args"
      by (rule equiv_apps_args)
    with cpy_project[OF assms(9,10), of args] assms(11)
    have "cpy targs (list_comb (Bound j) args) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        tr (list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args))"
      by (auto simp: tr_list_comb comp_def intro: equiv_trans)
    from dsolvedB_trans[OF dsolvedB_equiv[OF psatD(1)[OF \<sigma>(1)] this]] d
    show ?thesis by (simp add: dsolved_dsolvedB)
  qed
  with wst wc show ?thesis by (simp add: pcopy_ok_def)
qed

text \<open>\<open>copycons\<close>: a copy of the argument, or a new flexible argument with a new pair.\<close>

lemma copycons_psound:
  assumes "okW (copycons cfg vname rb targs uarg uargs' env dps) cs"
    "pargs_ok ar env0 rb targs uargs dps0 uargs' env dps" "sbinders ar rb" "swf_tm ar rb uarg"
    "\<forall>t\<in>set targs. swf_tm ar rb t"
  shows "psinv ar (GD env0 rb targs (uarg # uargs) dps0) cs"
proof -
  have ws: "pwf_state ar env0 env dps" using assms(2) by (simp add: pargs_ok_def)
  then have wenv: "swf_env ar env" and wdps: "\<forall>dp\<in>set dps. swf_dp ar dp" by (simp_all add: pwf_state_def)
  have tw: "twf ar (tyenv env)" by (rule swf_envD(1)[OF wenv])
  from assms(1)[unfolded copycons_def okW_bindW okW_liftM okW_returnW] obtain u1 u2 d s where
    h: "ok (head_norm env uarg) u1" and e: "ok (eta_norm env rb u1) u2"
    and m: "okW (if d then do {
          A \<leftarrow> liftM (fastype env rb u2);
          Ts \<leftarrow> liftM (mapM (fastype env rb) targs);
          (let (env', newhd) = genvar vname env (foldr fun_type Ts A) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rb, list_comb newhd targs, u2) # dps))))}
         else mc cfg vname rb targs u2 env dps) s" and cs: "cs = S_MapCons uargs' s"
    by blast
  note h1 = head_norm_swf_tm[OF h wenv assms(4)]
  note e1 = eta_norm_swf_tm[OF e wenv assms(3) conjunct1[OF h1]]
  have wu2: "swf_tm ar rb u2" using e1 by simp
  have hu2: "hnf u2" by (rule eta_norm_phnf[OF e head_norm_hnf[OF h refl]])
  have "psinv ar (GC env rb targs u2 dps) s"
  proof (cases d)
    case True
    with m obtain A Ts where A: "ok (fastype env rb u2) A"
      and tsf: "okW (liftM (mapM (fastype env rb) targs)) Ts"
      and s: "okW (case genvar vname env (foldr fun_type Ts A) of (env', newhd) \<Rightarrow>
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rb, list_comb newhd targs, u2) # dps)))) s"
      by (auto simp: Let_def)
    obtain env' newhd where g: "genvar vname env (foldr fun_type Ts A) = (env', newhd)"
      by (cases "genvar vname env (foldr fun_type Ts A)")
    have wA: "wft ar A" using fastype_wft[OF A tw assms(3)] wu2 by (simp add: swf_tm_def)
    note mw = mapM_fastype_wft[OF tsf tw assms(3,5)]
    from new_flex_copy[OF g mw(2) wA mw(1) wenv wdps assms(3) wu2 assms(5)] s g show ?thesis
      by (auto intro: psinv.Single)
  next
    case False
    with m have "okW (mc cfg vname rb targs u2 env dps) s" by simp
    from mc_psound[OF this wenv wdps assms(3) wu2 hu2 assms(5)] show ?thesis .
  qed
  moreover have "env \<Turnstile>\<^sub>p rlist_abs rb uarg \<approx> rlist_abs rb u2"
    using h1 e1 by (blast intro: env_equiv_penv env_equiv_rlist_abs env_equiv_trans)
  ultimately show ?thesis unfolding cs by (rule psinv.MapCons[OF assms(2)])
qed


text \<open>\<open>add_unify\<close>: without flex-rigid pairs, the flex-flex pairs give a unifier.\<close>

lemma punifier_tsolved: "punifier env0 dps0 env tps \<longleftrightarrow> pextends env0 env \<and>
    (\<forall>\<sigma>. psat \<sigma> env \<longrightarrow> tsolved \<sigma> tps \<longrightarrow> dsolved_all \<sigma> dps0)"
  by (simp add: punifier_def tsolved_def)

lemma addunify_punifier:
  assumes "preduces ar env0 dps0 env dps" "okW (SIMPL alg env dps) (env', ffs, [])"
    "okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps)"
  shows "punifier env0 dps0 env'' tps"
proof -
  have ws: "pwf_state ar env0 env dps" by (rule preducesD(1)[OF assms(1)])
  then have wenv: "swf_env ar env" and wdps: "\<forall>dp\<in>set dps. swf_dp ar dp" by (simp_all add: pwf_state_def)
  from assms(2) obtain evs where "SIMPL alg env dps = Some (evs, UOk (env', ffs, []))" by blast
  from SIMPL_ssound[OF this _ wenv wdps, of "(env', ffs, [])"]
  have wst: "swf_st ar (env', ffs, [])" and sr: "psimp_rel dps (env, [], []) (env', ffs, [])" by simp_all
  from wst have "swf_env ar env'" "\<forall>dp\<in>set ffs. swf_dp ar dp" by simp_all
  note fa = foldrW_add_ffpair_psound[OF assms(3) this]
  have e1: "pextends env env'" using psimp_relD(1)[OF sr] by simp
  have ext: "pextends env0 env''" using fa e1 pwf_stateD(1)[OF ws] by (blast intro: pextends_trans)
  have "dsolved_all \<sigma> dps0" if \<sigma>: "psat \<sigma> env''" "tsolved \<sigma> tps" for \<sigma>
  proof -
    have s1: "psat \<sigma> env'" using psat_pextends[OF \<sigma>(1)] fa by blast
    have "dsolved_all \<sigma> ffs" using fa \<sigma> by blast
    with psimp_relD(2)[OF sr] s1 have "dsolved_all \<sigma> dps" by simp
    moreover have "psat \<sigma> env" by (rule psat_pextends[OF s1 e1])
    ultimately show ?thesis by (rule preducesD(2)[OF assms(1), rotated])
  qed
  with ext show ?thesis by (simp add: punifier_tsolved)
qed

text \<open>\<open>add_unify\<close>: the assignments of \<open>MATCH\<close> for the first flex-rigid pair.\<close>

lemma addunify_pmatch:
  assumes "preduces ar env0 dps0 env dps" "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frigid')"
    "okW (MATCH cfg env' dp (frigid' @ ffs)) ms"
  shows "psinv ar (GE env0 dps0) ms"
proof (rule MATCH_psound[OF assms(3)])
  have ws: "pwf_state ar env0 env dps" by (rule preducesD(1)[OF assms(1)])
  then have wenv: "swf_env ar env" and wdps: "\<forall>dp\<in>set dps. swf_dp ar dp" by (simp_all add: pwf_state_def)
  from assms(2) obtain evs where S: "SIMPL (cfg_alg cfg) env dps = Some (evs, UOk (env', ffs, dp # frigid'))"
    by blast
  from SIMPL_ssound[OF S _ wenv wdps, of "(env', ffs, dp # frigid')"]
  have wst: "swf_st ar (env', ffs, dp # frigid')" and sr: "psimp_rel dps (env, [], []) (env', ffs, dp # frigid')"
    by simp_all
  from SIMPL_pfrs[OF S _ wenv wdps, of "(env', ffs, dp # frigid')"] show "pfrs_ok env' dp" by simp
  have e1: "pextends env env'" using psimp_relD(1)[OF sr] by simp
  have "pwf_state ar env0 env' (dp # frigid' @ ffs)"
    using wst e1 pwf_stateD(1)[OF ws] by (auto simp: pwf_state_def intro: pextends_trans)
  moreover have "dsolved_all \<sigma> dps0"
    if \<sigma>: "psat \<sigma> env'" "dsolved_all \<sigma> (dp # frigid' @ ffs)" for \<sigma>
  proof -
    from \<sigma>(2) have "dsolved_all \<sigma> (st_pairs (env', ffs, dp # frigid'))" by auto
    with psimp_relD(2)[OF sr, of \<sigma>] \<sigma>(1) have "dsolved_all \<sigma> dps" by simp
    moreover have "psat \<sigma> env" by (rule psat_pextends[OF \<sigma>(1) e1])
    ultimately show ?thesis by (rule preducesD(2)[OF assms(1), rotated])
  qed
  ultimately show "preduces ar env0 dps0 env' (dp # frigid' @ ffs)" unfolding preduces_def by blast
qed



subsection \<open>Pulling sequences\<close>

theorem pull_psound:
  assumes "pull cfg s = Some r"
  shows "snd r = UOk (Some (x, s')) \<Longrightarrow> psinv ar G s \<Longrightarrow> pelem_ok ar G x \<and> psinv ar G s'"
  using assms
proof (induction cfg s r arbitrary: G x s' rule: pull.raw_induct[rotated, consumes 1])
  case (1 P cfg s r)
  have IH: "pelem_ok ar G y \<and> psinv ar G s1'"
    if "okW (P cfg s1) (Some (y, s1'))" "psinv ar G s1" for s1 G y s1'
  proof -
    from that(1) obtain evs where "P cfg s1 = Some (evs, UOk (Some (y, s1')))" by blast
    from "1.IH"[OF this _ that(2)] show ?thesis by simp
  qed
  note hyps = okW_of[OF "1.hyps" "1.prems"(1)]
  note si = "1.prems"(2)
  show ?case
  proof (cases s)
    case S_Empty
    with hyps show ?thesis by simp
  next
    case (S_Single y)
    with hyps si show ?thesis by (auto elim: psinv_SingleE intro: psinv.Empty)
  next
    case (S_AddUnify td env dps reseq)
    from si S_AddUnify obtain env0 dps0 where G: "G = GR env0 dps0"
      and red: "preduces ar env0 dps0 env dps" and sr: "psinv ar (GR env0 dps0) reseq"
      by (auto elim: psinv_AddUnifyE)
    from addunify_cases[OF hyps[unfolded S_AddUnify seq.case]]
    consider (fail) "okW (P cfg reseq) (Some (x, s'))"
      | (fin) env' ffs env'' tps where "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, [])"
        "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) (env'', tps)"
        "x = El_R env'' tps" "s' = reseq"
      | (mtch) env' ffs dp frigid' ms where "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frigid')"
        "okW (MATCH cfg env' dp (frigid' @ ffs)) ms"
        "okW (P cfg (S_ItRight (td + 1) ms reseq)) (Some (x, s'))"
      by blast
    then show ?thesis
    proof cases
      case fail
      from IH[OF this sr] G show ?thesis by simp
    next
      case (fin env' ffs env'' tps)
      from addunify_punifier[OF red fin(1,2)] fin(3,4) sr G show ?thesis by simp
    next
      case (mtch env' ffs dp frigid' ms)
      have "psinv ar (GR env0 dps0) (S_ItRight (td + 1) ms reseq)"
        by (rule psinv.ItRight[OF addunify_pmatch[OF red mtch(1,2)] sr])
      from IH[OF mtch(3) this] G show ?thesis by simp
    qed
  next
    case (S_ItRight td xq yq)
    from si S_ItRight obtain env0 dps0 where G: "G = GR env0 dps0"
      and sx: "psinv ar (GE env0 dps0) xq" and sy: "psinv ar (GR env0 dps0) yq"
      by (auto elim: psinv_ItRightE)
    from okW_bind_E[OF hyps[unfolded S_ItRight seq.case]] consider (none) "okW (P cfg xq) None" "okW (P cfg yq) (Some (x, s'))"
      | (some) env dps xq' where "okW (P cfg xq) (Some (El_E env dps, xq'))"
        "okW (P cfg (S_AddUnify td env dps (S_ItRight td xq' yq))) (Some (x, s'))"
      by blast
    then show ?thesis
    proof cases
      case none
      from IH[OF none(2) sy] G show ?thesis by simp
    next
      case (some env dps xq')
      from IH[OF some(1) sx] have "preduces ar env0 dps0 env dps" "psinv ar (GE env0 dps0) xq'" by simp_all
      then have "psinv ar (GR env0 dps0) (S_AddUnify td env dps (S_ItRight td xq' yq))"
        by (intro psinv.AddUnify psinv.ItRight sy)
      from IH[OF some(2) this] G show ?thesis by simp
    qed
  next
    case (S_MapNewDset vT Ts xq)
    from okW_map_C[OF hyps[unfolded S_MapNewDset seq.case]] obtain u' env' dpairs' xq' where
      px: "okW (P cfg xq) (Some (El_C u' env' dpairs', xq'))"
      and nd: "okW (new_dset vT Ts u' env' dpairs') x" and s': "s' = S_MapNewDset vT Ts xq'"
      by auto
    from si S_MapNewDset consider
      (copy) env0 dps0 env1 rb t u dps1 v T targs where "G = GE env0 dps0"
        "vT = (v, T)" "preduces ar env0 dps0 env1 ((rb, t, u) # dps1)"
        "strip_comb t = (Var v T, targs)" "length Ts = length targs"
        "\<forall>U\<in>set Ts. wft ar U" "psinv ar (GC env1 rb targs u dps1) xq"
    | (single) env0 dps0 env1 dps1 v T where "G = GE env0 dps0" "vT = (v, T)"
        "preduces ar env0 dps0 env1 dps1" "wft ar T" "\<forall>U\<in>set Ts. wft ar U"
        "psinv ar (GS env1 dps1 (length Ts)) xq"
      by (auto elim: psinv_MapNewDsetE)
    then show ?thesis
    proof cases
      case copy
      note G = copy(1) and vT = copy(2) and red = copy(3) and sc = copy(4) and l = copy(5)
        and g = copy(6) and sx = copy(7)
      from IH[OF px sx] have c: "pcopy_ok ar env1 rb targs u dps1 u' env' dpairs'"
        and sx': "psinv ar (GC env1 rb targs u dps1) xq'" by simp_all
      have "pelem_ok ar (GE env0 dps0) x" by (rule new_dset_psound[OF nd[unfolded vT] red sc l g c])
      moreover have "psinv ar (GE env0 dps0) s'" unfolding s' vT by (rule psinv.MapNewDset[OF red sc l g sx'])
      ultimately show ?thesis using G by simp
    next
      case single
      note G = single(1) and vT = single(2) and red = single(3) and gT = single(4) and g = single(5)
        and sx = single(6)
      from IH[OF px sx] have c: "pelem_ok ar (GS env1 dps1 (length Ts)) (El_C u' env' dpairs')"
        and sx': "psinv ar (GS env1 dps1 (length Ts)) xq'" by simp_all
      have "pelem_ok ar (GE env0 dps0) x" by (rule new_dset_psound1[OF nd[unfolded vT] red gT g c])
      moreover have "psinv ar (GE env0 dps0) s'" unfolding s' vT by (rule psinv.MapNewDset1[OF red gT g sx'])
      ultimately show ?thesis using G by simp
    qed
  next
    case (S_MapAbs a T xq)
    from si S_MapAbs obtain env0 rb targs b T' body dps0 where
      G: "G = GC env0 rb targs (Abs b T' body) dps0"
      and sx: "psinv ar (GC env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body dps0) xq"
      and gT: "wft ar T" and pt: "\<forall>t\<in>set targs. proper t"
      by (auto elim: psinv_MapAbsE)
    from okW_map_C[OF hyps[unfolded S_MapAbs seq.case]] obtain body' env' dpairs' xq' where
      px: "okW (P cfg xq) (Some (El_C body' env' dpairs', xq'))"
      and x: "x = El_C (Abs a T body') env' dpairs'" and s': "s' = S_MapAbs a T xq'"
      by auto
    from IH[OF px sx] mapabs_pcopy[OF _ gT pt] psinv.MapAbs[OF _ gT pt] show ?thesis
      by (simp add: G x s')
  next
    case (S_Proj vname env' Ts Us targs rb u dps head targ tail)
    from si S_Proj obtain env j where G: "G = GC env rb targs u dps" and hd: "head = Bound j"
      and prem: "pextends env env'" "swf_env ar env'" "\<forall>dp\<in>set dps. swf_dp ar dp" "sbinders ar rb"
        "swf_tm ar rb u" "\<forall>t\<in>set targs. swf_tm ar rb t" "0 \<le> j" "nat_of_integer j < length targs"
        "targ = targs ! (length targs - 1 - nat_of_integer j)" "length Ts = length targs"
        "\<forall>U\<in>set Ts. wft ar U" "\<forall>U\<in>set Us. wft ar U"
      and st: "psinv ar (GC env rb targs u dps) tail"
      by (auto elim: psinv_ProjE)
    from hyps S_Proj consider (fail) "okW (P cfg tail) (Some (x, s'))"
      | (ok) env'' args env2 frigid fflex where "make_args vname Ts env' Us = (env'', args)"
        "okW (SIMPL (cfg_alg cfg) env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u)
          # dps)) (env2, frigid, fflex)"
        "x = El_C (list_comb head args) env2 (frigid @ fflex)" "s' = tail"
      by (auto simp: okW_handleW Let_def split: prod.splits dest!: okW_CANTUNIFY_handler')
    then show ?thesis
    proof cases
      case fail
      from IH[OF this st] G show ?thesis by simp
    next
      case (ok env'' args env2 frigid fflex)
      from proj_pcopy[OF ok(1,2) prem] ok(3,4) st G hd show ?thesis by simp
    qed
  next
    case (S_MapJoin uhead xq)
    from si S_MapJoin obtain env0 rb targs u dps0 uargs where G: "G = GC env0 rb targs u dps0"
      and sc: "strip_comb u = (uhead, uargs)" and cl: "no_loose_bound (tr uhead) 0"
      and ty: "twft ar uhead" and pr: "proper uhead"
      and sx: "psinv ar (GD env0 rb targs uargs dps0) xq"
      by (auto elim: psinv_MapJoinE)
    from okW_map_D[OF hyps[unfolded S_MapJoin seq.case]] obtain uargs' env' dpairs' xq' where
      px: "okW (P cfg xq) (Some (El_D uargs' env' dpairs', xq'))"
      and x: "x = El_C (list_comb uhead uargs') env' dpairs'" and s': "s' = S_MapJoin uhead xq'"
      by auto
    from IH[OF px sx] mapjoin_pcopy[OF sc cl ty pr] psinv.MapJoin[OF sc cl ty pr] show ?thesis
      by (simp add: G x s')
  next
    case (S_Maps vname rb targs uarg xq)
    from si S_Maps obtain env0 uargs dps0 where G: "G = GD env0 rb targs (uarg # uargs) dps0"
      and sx: "psinv ar (GD env0 rb targs uargs dps0) xq" and bok: "sbinders ar rb"
      and wu: "swf_tm ar rb uarg" and wt: "\<forall>t\<in>set targs. swf_tm ar rb t"
      by (auto elim: psinv_MapsE)
    from okW_map_D[OF hyps[unfolded S_Maps seq.case]] obtain uargs' env dps xq' cs where
      px: "okW (P cfg xq) (Some (El_D uargs' env dps, xq'))"
      and cc: "okW (copycons cfg vname rb targs uarg uargs' env dps) cs"
      and pa: "okW (P cfg (S_Append cs (S_Maps vname rb targs uarg xq'))) (Some (x, s'))"
      by auto
    from IH[OF px sx] have a: "pargs_ok ar env0 rb targs uargs dps0 uargs' env dps"
      and sx': "psinv ar (GD env0 rb targs uargs dps0) xq'" by simp_all
    have "psinv ar (GD env0 rb targs (uarg # uargs) dps0) (S_Append cs (S_Maps vname rb targs uarg xq'))"
      by (intro psinv.Append copycons_psound[OF cc a bok wu wt] psinv.Maps[OF sx' bok wu wt])
    from IH[OF pa this] G show ?thesis by simp
  next
    case (S_Append xq yq)
    from si S_Append have sx: "psinv ar G xq" and sy: "psinv ar G yq" by (auto elim: psinv_AppendE)
    from okW_bind_opt[OF hyps[unfolded S_Append seq.case]] consider (none) "okW (P cfg yq) (Some (x, s'))"
      | (some) xq' where "okW (P cfg xq) (Some (x, xq'))" "s' = S_Append xq' yq"
      by auto
    then show ?thesis
    proof cases
      case none
      from IH[OF this sy] show ?thesis .
    next
      case (some xq')
      from IH[OF some(1) sx] some(2) sy show ?thesis by (simp add: psinv.Append)
    qed
  next
    case (S_MapCons uargs' xq)
    from si S_MapCons obtain env0 rb targs uarg uargs dps0 env dps u2 where
      G: "G = GD env0 rb targs (uarg # uargs) dps0"
      and a: "pargs_ok ar env0 rb targs uargs dps0 uargs' env dps"
      and sx: "psinv ar (GC env rb targs u2 dps) xq" and eq: "env \<Turnstile>\<^sub>p rlist_abs rb uarg \<approx> rlist_abs rb u2"
      by (auto elim: psinv_MapConsE)
    from okW_map_C[OF hyps[unfolded S_MapCons seq.case]] obtain uarg' env' dpairs' xq' where
      px: "okW (P cfg xq) (Some (El_C uarg' env' dpairs', xq'))"
      and x: "x = El_D (uarg' # uargs') env' dpairs'" and s': "s' = S_MapCons uargs' xq'"
      by auto
    from IH[OF px sx] mapcons_pargs[OF a _ eq] psinv.MapCons[OF a _ eq] show ?thesis
      by (simp add: G x s')
  qed
qed


subsection \<open>Unifiers\<close>

theorem hounifiers_psinv:
  assumes "swf_env ar env" "sbinders ar rb" "\<forall>(t, u)\<in>set tus. swf_tm ar rb t \<and> swf_tm ar rb u"
  shows "psinv ar (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) (hounifiers rb env tus)"
proof -
  have "preduces ar env (map (\<lambda>(t, u). (rb, t, u)) tus) env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    using assms by (auto simp: preduces_def pwf_state_def)
  then show ?thesis unfolding hounifiers_def by (rule psinv.AddUnify[OF _ psinv.Empty])
qed

theorem pull_punifier:
  assumes "psinv ar (GR env0 dps0) s" "pull cfg s = Some r" "snd r = UOk (Some (x, s'))"
  obtains env tps where "x = El_R env tps" "punifier env0 dps0 env tps" "psinv ar (GR env0 dps0) s'"
proof -
  from pull_psound[OF assms(2,3,1)] have "pelem_ok ar (GR env0 dps0) x" "psinv ar (GR env0 dps0) s'"
    by simp_all
  with that show ?thesis by (cases x) auto
qed

text \<open>
  In terms of the input and of type instances: let \<open>El_R env tps\<close> be a unifier of the sequence
  \<open>hounifiers rb env0 tus\<close>. For every type instantiation \<open>\<rho>\<close> that solves the type environment
  of \<open>env\<close> and every closed substitution \<open>\<sigma>\<close> that satisfies the type instance of \<open>env\<close> and solves
  the type instances of the flex-flex pairs \<open>tps\<close>, \<open>\<sigma>\<close> solves the type instance of each input pair.
\<close>

corollary hounifiers_punifier:
  assumes "punifier env0 (map (\<lambda>(t, u). (rb, t, u)) tus) env tps"
    "tsol (tyenv env) \<rho>" "closed_on UNIV \<sigma>" "sat \<sigma> (instE \<rho> env)"
    "\<forall>(t', u')\<in>set tps. mk_subst \<sigma> (tr (inst \<rho> t')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u'))"
    "(t, u) \<in> set tus"
  shows "pextends env0 env"
    "mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb t))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb u)))"
proof -
  show "pextends env0 env" using assms(1) by (simp add: punifier_def)
  have ps: "psat (\<sigma> \<circ> cren \<rho>) env" by (rule psat_instE[OF assms(2-4)])
  have "\<forall>(t', u')\<in>set tps. mk_subst (\<sigma> \<circ> cren \<rho>) (tr t') \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma> \<circ> cren \<rho>) (tr u')"
    using assms(5) by (auto simp: mk_subst_inst)
  with assms(1) ps have "dsolved_all (\<sigma> \<circ> cren \<rho>) (map (\<lambda>(t, u). (rb, t, u)) tus)"
    unfolding punifier_def by blast
  with assms(6) have "dsolved (\<sigma> \<circ> cren \<rho>) (rb, t, u)" by auto
  then show "mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb t))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb u)))"
    by (simp add: dsolved_def mk_subst_inst)
qed

end

end
