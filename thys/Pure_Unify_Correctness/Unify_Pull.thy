section \<open>Soundness of the Search\<close>

theory Unify_Pull
  imports Unify_Flexflex
begin

text \<open>
  Pulling a sequence that satisfies the invariant \<^const>\<open>sinv\<close> of its goal produces an
  element that satisfies the goal and a rest that satisfies the invariant again. For the
  sequences of \<open>hounifiers\<close>, the elements are unifiers.
\<close>


subsection \<open>Inversion of the invariant\<close>

context csig
begin

inductive_cases sinv_SingleE: "sinv ar G (S_Single x)"
inductive_cases sinv_AddUnifyE: "sinv ar G (S_AddUnify td env dps reseq)"
inductive_cases sinv_ItRightE: "sinv ar G (S_ItRight td xq yq)"
inductive_cases sinv_MapNewDsetE: "sinv ar G (S_MapNewDset vT Ts xq)"
inductive_cases sinv_MapAbsE: "sinv ar G (S_MapAbs a T xq)"
inductive_cases sinv_ProjE: "sinv ar G (S_Proj vname env Ts Us targs rb u dps head targ tail)"
inductive_cases sinv_MapJoinE: "sinv ar G (S_MapJoin uhead xq)"
inductive_cases sinv_MapsE: "sinv ar G (S_Maps vname rb targs uarg xq)"
inductive_cases sinv_AppendE: "sinv ar G (S_Append xq yq)"
inductive_cases sinv_MapConsE: "sinv ar G (S_MapCons uargs xq)"


subsection \<open>The elements of the closures\<close>

text \<open>The copy of an abstraction is the abstraction of a copy of its body.\<close>

lemma mapabs_copy:
  assumes "copy_ok ar env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body dps0 body' env dps"
    "ground ar T" "\<forall>t\<in>set targs. proper t"
  shows "copy_ok ar env0 rb targs (Abs b T' body) dps0 (Abs a T body') env dps"
  unfolding copy_ok_def
proof (intro conjI allI impI)
  show "wf_state ar env0 env dps" using assms(1) by (simp add: copy_ok_def)
  have w: "wf_cp ar (Suc (length targs)) body'" using assms(1) by (simp add: copy_ok_def)
  then show "wf_cp ar (length targs) (Abs a T body')" using assms(2) by (simp add: wf_cp_def)
  fix \<sigma> assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env" "dsolved_all \<sigma> dps"
  with assms(1) have c: "dsolvedB \<sigma> ((a, T) # rb) (cpy (map (incr_boundvars 1) targs @ [Bound 0]) body') (tr body)"
    and "dsolved_all \<sigma> dps0" by (simp_all add: copy_ok_def)
  then show "dsolved_all \<sigma> dps0" by simp
  from c have "dsolvedB \<sigma> rb (dB.Abs (cpy (map (incr_boundvars 1) targs @ [Bound 0]) body')) (dB.Abs (tr body))"
    by (simp add: dsolvedB_Abs)
  moreover have "dsolvedB \<sigma> rb (cpy targs (Abs a T body')) (dB.Abs (cpy (map (incr_boundvars 1) targs @ [Bound 0]) body'))"
    by (rule dsolvedB_sym[OF dsolvedB_equiv[OF \<sigma>(1) cpy_Abs]]) (use w assms(3) in \<open>simp_all add: wf_cp_def\<close>)
  ultimately show "dsolvedB \<sigma> rb (cpy targs (Abs a T body')) (tr (Abs b T' body))"
    by (simp add: dsolvedB_trans)
qed

text \<open>Imitation: the head applied to copies of the arguments.\<close>

lemma mapjoin_copy:
  assumes "strip_comb u = (uhead, uargs)" "no_loose_bound (tr uhead) 0" "typs_ok ar uhead" "proper uhead"
    "args_ok ar env0 rb targs uargs dps0 uargs' env dps"
  shows "copy_ok ar env0 rb targs u dps0 (list_comb uhead uargs') env dps"
  unfolding copy_ok_def
proof (intro conjI allI impI)
  show "wf_state ar env0 env dps" using assms(5) by (simp add: args_ok_def)
  have "\<forall>a'\<in>set uargs'. wf_cp ar (length targs) a'" using assms(5) by (simp add: args_ok_def)
  with assms(2-4) show "wf_cp ar (length targs) (list_comb uhead uargs')"
    by (auto simp: wf_cp_def proper_list_comb typs_ok_list_comb tr_list_comb no_loose_bound_list_app
        intro: no_loose_bound_mono)
  fix \<sigma> assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env" "dsolved_all \<sigma> dps"
  with assms(5) have l: "list_all2 (\<lambda>a' a. dsolvedB \<sigma> rb (cpy targs a') (tr a)) uargs' uargs"
    and "dsolved_all \<sigma> dps0" by (simp_all add: args_ok_def)
  then show "dsolved_all \<sigma> dps0" by simp
  have "dsolvedB \<sigma> rb (tr uhead \<degree>\<degree> map (cpy targs) uargs') (tr uhead \<degree>\<degree> map tr uargs)"
    by (rule dsolvedB_apps) (use l in \<open>simp_all add: list_all2_map1 list_all2_map2\<close>)
  moreover have "tr u = tr uhead \<degree>\<degree> map tr uargs"
    using strip_comb_list_comb[OF assms(1)] by (simp add: tr_list_comb)
  moreover have "dsolvedB \<sigma> rb (cpy targs (list_comb uhead uargs')) (tr uhead \<degree>\<degree> map (cpy targs) uargs')"
    by (rule dsolvedB_equiv[OF \<sigma>(1) cpy_imitate[OF assms(2)]])
  ultimately show "dsolvedB \<sigma> rb (cpy targs (list_comb uhead uargs')) (tr u)"
    by (auto intro: dsolvedB_trans)
qed

text \<open>A copy of an argument in front of copies of the other arguments.\<close>

lemma mapcons_args:
  assumes "args_ok ar env0 rb targs uargs dps0 uargs' env dps"
    "copy_ok ar env rb targs u2 dps uarg' env' dps'" "env \<Turnstile> rlist_abs rb uarg \<approx> rlist_abs rb u2"
  shows "args_ok ar env0 rb targs (uarg # uargs) dps0 (uarg' # uargs') env' dps'"
proof -
  have w1: "wf_state ar env0 env dps" and w2: "wf_state ar env env' dps'"
    using assms(1,2) by (simp_all add: args_ok_def copy_ok_def)
  have "list_all2 (\<lambda>a' a. dsolvedB \<sigma> rb (cpy targs a') (tr a)) (uarg' # uargs') (uarg # uargs) \<and>
      dsolved_all \<sigma> dps0"
    if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'" "dsolved_all \<sigma> dps'" for \<sigma>
  proof -
    from assms(2) \<sigma> have c: "dsolvedB \<sigma> rb (cpy targs uarg') (tr u2)" and d: "dsolved_all \<sigma> dps"
      by (simp_all add: copy_ok_def)
    have s: "sat \<sigma> env" by (rule sat_extends[OF \<sigma>(2) wf_stateD(1)[OF w2]])
    with assms(1) \<sigma>(1) d have l: "list_all2 (\<lambda>a' a. dsolvedB \<sigma> rb (cpy targs a') (tr a)) uargs' uargs"
      and d0: "dsolved_all \<sigma> dps0" by (simp_all add: args_ok_def)
    have "dsolvedB \<sigma> rb (tr uarg) (tr u2)"
      using env_equiv_dsolved[OF assms(3) \<sigma>(1) s] by (simp add: dsolved_dsolvedB)
    with c have "dsolvedB \<sigma> rb (cpy targs uarg') (tr uarg)" by (blast intro: dsolvedB_trans dsolvedB_sym)
    with l d0 show ?thesis by simp
  qed
  moreover have "wf_state ar env0 env' dps'" by (rule wf_state_extends[OF w2 wf_stateD(1)[OF w1]])
  moreover have "length uargs' = length uargs" "\<forall>a'\<in>set uargs'. wf_cp ar (length targs) a'"
    using assms(1) unfolding args_ok_def by blast+
  moreover have "wf_cp ar (length targs) uarg'" using assms(2) unfolding copy_ok_def by blast
  ultimately show ?thesis unfolding args_ok_def by (metis length_Cons set_ConsD)
qed


text \<open>Projection: the bound variable applied to new variables.\<close>

lemma make_args_args:
  assumes "make_args vname Ts env Us = (env', args)" "\<forall>U\<in>set Ts. ground ar U" "\<forall>U\<in>set Us. ground ar U"
    "arg \<in> set args"
  obtains G where "arg = combound G 0 (length Ts)" "head_of G = G" "wf_tm ar rb G" "no_loose_bound (tr G) 0"
    "typs_ok ar G" "proper G"
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
  moreover from this have "ground ar (foldr fun_type Ts U)"
    using assms(2,3) by (simp add: ground_foldr_fun_type)
  ultimately show ?thesis using that[of "Var x (foldr fun_type Ts U)"] by (simp add: wf_tm_def)
qed

lemma proj_copy:
  assumes "make_args vname Ts env Us = (env', args)"
    "okW (SIMPL alg env' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (env2, frigid, fflex)"
    "wf_env ar env" "\<forall>dp\<in>set dps. wf_dp ar dp" "binders_ok ar rb" "wf_tm ar rb u"
    "\<forall>t\<in>set targs. wf_tm ar rb t" "0 \<le> j" "nat_of_integer j < length targs"
    "targ = targs ! (length targs - 1 - nat_of_integer j)" "length Ts = length targs"
    "\<forall>U\<in>set Ts. ground ar U" "\<forall>U\<in>set Us. ground ar U"
  shows "copy_ok ar env rb targs u dps (list_comb (Bound j) args) env2 (frigid @ fflex)"
proof -
  let ?dp = "(rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u)"
  note margs = make_args_args[OF assms(1,12,13)]
  have wenv': "wf_env ar env'" by (rule make_args_wf_env[OF assms(1,3)])
  have wtarg: "wf_tm ar rb targ" using assms(7,9,10) by simp
  have "wf_tm ar rb (list_comb (head_of arg) targs)" if a: "arg \<in> set args" for arg
  proof -
    obtain G where "arg = combound G 0 (length Ts)" "head_of G = G" "wf_tm ar rb G"
      using margs[OF a] by metis
    with assms(7) show ?thesis by (simp add: head_of_combound wf_tm_list_comb)
  qed
  with wtarg assms(5,6) have wdp: "wf_dp ar ?dp" by (auto simp: wf_tm_list_comb)
  from assms(2) obtain evs where "SIMPL alg env' (?dp # dps) = Some (evs, UOk (env2, frigid, fflex))"
    by blast
  from SIMPL_sound[OF this _ wenv', of "(env2, frigid, fflex)"] wdp assms(4)
  have ws: "wf_st ar (env2, frigid, fflex)" and sr: "simp_rel (?dp # dps) (env', [], []) (env2, frigid, fflex)"
    by auto
  have ext: "extends env2 env"
    using simp_relD(1)[OF sr] make_args_extends[OF assms(1)] by (auto intro: extends_trans)
  have wst: "wf_state ar env env2 (frigid @ fflex)" using ws ext by (simp add: wf_state_def wf_st_def)
  have wca: "wf_cp ar (length targs) arg" if a: "arg \<in> set args" for arg
  proof -
    obtain G where "arg = combound G 0 (length Ts)" "no_loose_bound (tr G) 0" "typs_ok ar G" "proper G"
      using margs[OF a] by metis
    with wf_cp_combound[of ar G "length Ts"] assms(11) show ?thesis by simp
  qed
  have wc: "wf_cp ar (length targs) (list_comb (Bound j) args)"
    using wca assms(8,9)
    by (auto simp: wf_cp_def proper_list_comb typs_ok_list_comb tr_list_comb no_loose_bound_list_app)
  have "dsolvedB \<sigma> rb (cpy targs (list_comb (Bound j) args)) (tr u) \<and> dsolved_all \<sigma> dps"
    if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env2" "dsolved_all \<sigma> (frigid @ fflex)" for \<sigma>
  proof -
    from simp_relD(2)[OF sr \<sigma>(1)] \<sigma>(2,3) have d: "dsolved \<sigma> ?dp" "dsolved_all \<sigma> dps" by simp_all
    have "cpy targs arg \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (list_comb (head_of arg) targs)" if a: "arg \<in> set args" for arg
    proof -
      obtain G where "arg = combound G 0 (length Ts)" "no_loose_bound (tr G) 0" "head_of G = G"
        using margs[OF a] by metis
      with cpy_combound[of G targs] assms(11) show ?thesis by (simp add: head_of_combound)
    qed
    then have "tr targ \<degree>\<degree> map (cpy targs) args \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        tr targ \<degree>\<degree> map (\<lambda>arg. tr (list_comb (head_of arg) targs)) args"
      by (rule equiv_apps_args)
    with cpy_project[OF assms(8,9), of args] assms(10)
    have "cpy targs (list_comb (Bound j) args) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        tr (list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args))"
      by (auto simp: tr_list_comb comp_def intro: equiv_trans)
    from dsolvedB_trans[OF dsolvedB_equiv[OF \<sigma>(1) this]] d
    show ?thesis by (simp add: dsolved_dsolvedB)
  qed
  with wst wc show ?thesis by (simp add: copy_ok_def)
qed

text \<open>\<open>copycons\<close>: the copies of an argument, consed to copies of the other arguments.\<close>

lemma copycons_sound:
  assumes "okW (copycons cfg vname rb targs uarg uargs' env dps) cs"
    "args_ok ar env0 rb targs uargs dps0 uargs' env dps" "binders_ok ar rb" "wf_tm ar rb uarg"
    "\<forall>t\<in>set targs. wf_tm ar rb t"
  shows "sinv ar (GD env0 rb targs (uarg # uargs) dps0) cs"
proof -
  have ws: "wf_state ar env0 env dps" using assms(2) by (simp add: args_ok_def)
  then have wenv: "wf_env ar env" and wdps: "\<forall>dp\<in>set dps. wf_dp ar dp" by (simp_all add: wf_state_def)
  have "typs_ok ar u2" if "ok (head_norm env uarg) u1" "ok (eta_norm env rb u1) u2" for u1 u2
    using eta_norm_wf_tm[OF that(2) wenv assms(3) conjunct1[OF head_norm_wf_tm[OF that(1) wenv assms(4)]]]
    by (simp add: wf_tm_def)
  from copycons_ground[OF assms(1) this wf_envD(1)[OF wenv] assms(3)] obtain u1 u2 s
    where h: "ok (head_norm env uarg) u1" and e: "ok (eta_norm env rb u1) u2"
      and m: "okW (mc cfg vname rb targs u2 env dps) s" and cs: "cs = S_MapCons uargs' s" .
  note h1 = head_norm_wf_tm[OF h wenv assms(4)]
  note e1 = eta_norm_wf_tm[OF e wenv assms(3) conjunct1[OF h1]]
  have hu2: "hnf u2" by (rule eta_norm_hnf[OF wf_envD(1)[OF wenv] e head_norm_hnf[OF h refl]])
  have "sinv ar (GC env rb targs u2 dps) s" by (rule mc_sound[OF m wenv wdps assms(3) conjunct1[OF e1] hu2 assms(5)])
  moreover have "env \<Turnstile> rlist_abs rb uarg \<approx> rlist_abs rb u2"
    using h1 e1 by (blast intro: env_equiv_rlist_abs env_equiv_trans)
  ultimately show ?thesis unfolding cs by (rule sinv.MapCons[OF assms(2)])
qed


text \<open>\<open>add_unify\<close>: without flex-rigid pairs, the flex-flex pairs give a unifier.\<close>

lemma unifier_tsolved: "unifier env0 dps0 env tps \<longleftrightarrow> extends env env0 \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env \<longrightarrow> tsolved \<sigma> tps \<longrightarrow> dsolved_all \<sigma> dps0)"
  by (simp add: unifier_def tsolved_def)

lemma addunify_unifier:
  assumes "reduces ar env0 dps0 env dps" "okW (SIMPL alg env dps) (env', ffs, [])"
    "okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps)"
  shows "unifier env0 dps0 env'' tps"
proof -
  have ws: "wf_state ar env0 env dps" using assms(1) by (simp add: reduces_def)
  then have wenv: "wf_env ar env" and wdps: "\<forall>dp\<in>set dps. wf_dp ar dp" by (simp_all add: wf_state_def)
  from assms(2) obtain evs where "SIMPL alg env dps = Some (evs, UOk (env', ffs, []))" by blast
  from SIMPL_sound[OF this _ wenv wdps, of "(env', ffs, [])"]
  have wst: "wf_st ar (env', ffs, [])" and sr: "simp_rel dps (env, [], []) (env', ffs, [])" by simp_all
  from wst have "wf_env ar env'" "\<forall>dp\<in>set ffs. wf_dp ar dp" by (simp_all add: wf_st_def)
  note fa = foldrW_add_ffpair_sound[OF assms(3) this]
  have e1: "extends env' env" using simp_relD(1)[OF sr] by simp
  have ext: "extends env'' env0" using fa e1 wf_stateD(1)[OF ws] by (blast intro: extends_trans)
  have "dsolved_all \<sigma> dps0" if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env''" "tsolved \<sigma> tps" for \<sigma>
  proof -
    have s1: "sat \<sigma> env'" using sat_extends[OF \<sigma>(2)] fa by blast
    have "dsolved_all \<sigma> ffs" using fa \<sigma> by blast
    with simp_relD(2)[OF sr \<sigma>(1)] s1 have "dsolved_all \<sigma> dps" by simp
    moreover have "sat \<sigma> env" by (rule sat_extends[OF s1 e1])
    ultimately show ?thesis using assms(1) \<sigma>(1) unfolding reduces_def by blast
  qed
  with ext show ?thesis by (simp add: unifier_tsolved)
qed

text \<open>\<open>add_unify\<close>: the assignments of \<open>MATCH\<close> for the first flex-rigid pair.\<close>

lemma addunify_match:
  assumes "reduces ar env0 dps0 env dps" "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frigid')"
    "okW (MATCH cfg env' dp (frigid' @ ffs)) ms"
  shows "sinv ar (GE env0 dps0) ms"
proof (rule MATCH_sound[OF assms(3)])
  have ws: "wf_state ar env0 env dps" using assms(1) by (simp add: reduces_def)
  then have wenv: "wf_env ar env" and wdps: "\<forall>dp\<in>set dps. wf_dp ar dp" by (simp_all add: wf_state_def)
  from assms(2) obtain evs where S: "SIMPL (cfg_alg cfg) env dps = Some (evs, UOk (env', ffs, dp # frigid'))"
    by blast
  from SIMPL_sound[OF S _ wenv wdps, of "(env', ffs, dp # frigid')"]
  have wst: "wf_st ar (env', ffs, dp # frigid')" and sr: "simp_rel dps (env, [], []) (env', ffs, dp # frigid')"
    by simp_all
  from SIMPL_frs[OF S _ wenv wdps, of "(env', ffs, dp # frigid')"] show "frs_ok dp" by simp
  have e1: "extends env' env" using simp_relD(1)[OF sr] by simp
  have "wf_state ar env0 env' (dp # frigid' @ ffs)"
    using wst e1 wf_stateD(1)[OF ws] by (auto simp: wf_state_def wf_st_def intro: extends_trans)
  moreover have "dsolved_all \<sigma> dps0"
    if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'" "dsolved_all \<sigma> (dp # frigid' @ ffs)" for \<sigma>
  proof -
    from \<sigma>(3) have "dsolved_all \<sigma> (st_pairs (env', ffs, dp # frigid'))" by auto
    with simp_relD(2)[OF sr \<sigma>(1)] \<sigma>(2) have "dsolved_all \<sigma> dps" by simp
    moreover have "sat \<sigma> env" by (rule sat_extends[OF \<sigma>(2) e1])
    ultimately show ?thesis using assms(1) \<sigma>(1) unfolding reduces_def by blast
  qed
  ultimately show "reduces ar env0 dps0 env' (dp # frigid' @ ffs)" unfolding reduces_def by blast
qed



subsection \<open>Pulling sequences\<close>

lemma not_okW_pull_fail[simp]: "\<not> okW pull_fail y"
  by (simp add: pull_fail_def)

lemma okW_CANTUNIFY_handler':
  "okW (case e of CANTUNIFY \<Rightarrow> m | _ \<Rightarrow> raiseW e) y \<Longrightarrow> okW m y"
  by (cases e) auto

text \<open>Decomposing the successful evaluation of the closures.\<close>

lemma okW_bind_opt:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> A | Some (y, q) \<Rightarrow> B y q)) z"
  shows "(okW m None \<and> okW A z) \<or> (\<exists>y q. okW m (Some (y, q)) \<and> okW (B y q) z)"
proof -
  from assms obtain r where r: "okW m r" "okW (case r of None \<Rightarrow> A | Some (y, q) \<Rightarrow> B y q) z"
    unfolding okW_bindW by blast
  show ?thesis
  proof (cases r)
    case None
    with r show ?thesis by simp
  next
    case (Some p)
    with r show ?thesis by (cases p) auto
  qed
qed

lemma okW_map_C:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> returnW None
    | Some (y, q) \<Rightarrow> (case y of El_C a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail))) (Some z)"
  shows "\<exists>a b c q. okW m (Some (El_C a b c, q)) \<and> okW (f a b c q) (Some z)"
proof -
  from okW_bind_opt[OF assms] obtain y q where "okW m (Some (y, q))"
    "okW (case y of El_C a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail) (Some z)" by auto
  then show ?thesis by (cases y) auto
qed

lemma okW_map_D:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> returnW None
    | Some (y, q) \<Rightarrow> (case y of El_D a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail))) (Some z)"
  shows "\<exists>a b c q. okW m (Some (El_D a b c, q)) \<and> okW (f a b c q) (Some z)"
proof -
  from okW_bind_opt[OF assms] obtain y q where "okW m (Some (y, q))"
    "okW (case y of El_D a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail) (Some z)" by auto
  then show ?thesis by (cases y) auto
qed

lemma okW_bind_E:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> A
    | Some (y, q) \<Rightarrow> (case y of El_E a b \<Rightarrow> f a b q | _ \<Rightarrow> pull_fail))) z"
  shows "(okW m None \<and> okW A z) \<or> (\<exists>a b q. okW m (Some (El_E a b, q)) \<and> okW (f a b q) z)"
proof -
  from okW_bind_opt[OF assms] consider (n) "okW m None \<and> okW A z"
    | (s) y q where "okW m (Some (y, q))" "okW (case y of El_E a b \<Rightarrow> f a b q | _ \<Rightarrow> pull_fail) z"
    by blast
  then show ?thesis
  proof cases
    case (s y q)
    then show ?thesis by (cases y) auto
  qed simp
qed

lemma okW_whenW_then: "okW (bindW (whenW b (emit e)) (\<lambda>_. M)) z \<Longrightarrow> okW M z"
  by (auto simp: okW_whenW split: if_splits)

lemma okW_emit_then: "okW (bindW (emit e) (\<lambda>_. M)) z \<Longrightarrow> okW M z"
  by auto

lemma okW_handle_CANTUNIFY:
  assumes "okW (handleW M (\<lambda>e. case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e)) z"
  shows "okW M z \<or> okW N z"
proof -
  from assms have "okW M z \<or> (\<exists>evs e. M = Some (evs, UErr e) \<and>
      okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z)"
    by (simp only: okW_handleW)
  then show ?thesis
  proof (elim disjE)
    assume "\<exists>evs e. M = Some (evs, UErr e) \<and> okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z"
    then obtain e where "okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z" by metis
    from okW_CANTUNIFY_handler'[OF this] show ?thesis ..
  qed (rule disjI1)
qed

lemma okW_bind_triple:
  assumes "okW (bindW m (\<lambda>(a, b, c). f a b c)) z"
  shows "\<exists>a b c. okW m (a, b, c) \<and> okW (f a b c) z"
proof -
  from assms obtain st where "okW m st" "okW ((\<lambda>(a, b, c). f a b c) st) z" unfolding okW_bindW by blast
  then show ?thesis by (cases st) auto
qed

lemma addunify_cases:
  assumes "okW (handleW
    (bindW (whenW b1 (emit e1)) (\<lambda>_. bindW (SIMPL alg env dps) (\<lambda>(env', ffs, frs).
      case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R))))
    (\<lambda>e. case e of CANTUNIFY \<Rightarrow> bindW (whenW b4 (emit e4)) (\<lambda>_. Q) | _ \<Rightarrow> raiseW e)) z"
  shows "okW Q z \<or>
    (\<exists>env' ffs env'' tps. okW (SIMPL alg env dps) (env', ffs, []) \<and>
      okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps) \<and> z = Some (El_R env'' tps, reseq)) \<or>
    (\<exists>env' ffs dp frigid' ms. okW (SIMPL alg env dps) (env', ffs, dp # frigid') \<and>
      okW (MATCH cfg env' dp (frigid' @ ffs)) ms \<and> okW (R ms) z)"
proof -
  from okW_handle_CANTUNIFY[OF assms] show ?thesis
  proof (elim disjE)
    assume "okW (bindW (whenW b1 (emit e1)) (\<lambda>_. bindW (SIMPL alg env dps) (\<lambda>(env', ffs, frs).
      case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)))) z"
    from okW_bind_triple[OF okW_whenW_then[OF this]] obtain env' ffs frs where
      S: "okW (SIMPL alg env dps) (env', ffs, frs)"
      and c: "okW (case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)) z"
      by blast
    show ?thesis
    proof (cases frs)
      case Nil
      with c obtain r where r: "okW (foldrW (add_ffpair alg) ffs (env', [])) r"
        "z = Some (El_R (fst r) (snd r), reseq)" by auto
      obtain env'' tps where "r = (env'', tps)" by (cases r)
      with r have "okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps)"
        "z = Some (El_R env'' tps, reseq)" by simp_all
      with S Nil show ?thesis by blast
    next
      case (Cons dp frigid')
      show ?thesis
      proof (cases b2)
        case True
        with c Cons have "okW Q z" by (auto dest: okW_emit_then)
        then show ?thesis by blast
      next
        case False
        with c Cons have "okW (bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)) z" by simp
        from okW_whenW_then[OF this] obtain ms where "okW (MATCH cfg env' dp (frigid' @ ffs)) ms"
          "okW (R ms) z" unfolding okW_bindW by blast
        with S Cons show ?thesis by blast
      qed
    qed
  next
    assume "okW (bindW (whenW b4 (emit e4)) (\<lambda>_. Q)) z"
    from okW_whenW_then[OF this] show ?thesis by blast
  qed
qed

theorem pull_sound:
  assumes "pull cfg s = Some r"
  shows "snd r = UOk (Some (x, s')) \<Longrightarrow> sinv ar G s \<Longrightarrow> elem_ok ar G x \<and> sinv ar G s'"
  using assms
proof (induction cfg s r arbitrary: G x s' rule: pull.raw_induct[rotated, consumes 1])
  case (1 P cfg s r)
  have IH: "elem_ok ar G y \<and> sinv ar G s1'"
    if "okW (P cfg s1) (Some (y, s1'))" "sinv ar G s1" for s1 G y s1'
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
    with hyps si show ?thesis by (auto elim: sinv_SingleE intro: sinv.Empty)
  next
    case (S_AddUnify td env dps reseq)
    from si S_AddUnify obtain env0 dps0 where G: "G = GR env0 dps0"
      and red: "reduces ar env0 dps0 env dps" and sr: "sinv ar (GR env0 dps0) reseq"
      by (auto elim: sinv_AddUnifyE)
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
      from addunify_unifier[OF red fin(1,2)] fin(3,4) sr G show ?thesis by simp
    next
      case (mtch env' ffs dp frigid' ms)
      have "sinv ar (GR env0 dps0) (S_ItRight (td + 1) ms reseq)"
        by (rule sinv.ItRight[OF addunify_match[OF red mtch(1,2)] sr])
      from IH[OF mtch(3) this] G show ?thesis by simp
    qed
  next
    case (S_ItRight td xq yq)
    from si S_ItRight obtain env0 dps0 where G: "G = GR env0 dps0"
      and sx: "sinv ar (GE env0 dps0) xq" and sy: "sinv ar (GR env0 dps0) yq"
      by (auto elim: sinv_ItRightE)
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
      from IH[OF some(1) sx] have "reduces ar env0 dps0 env dps" "sinv ar (GE env0 dps0) xq'" by simp_all
      then have "sinv ar (GR env0 dps0) (S_AddUnify td env dps (S_ItRight td xq' yq))"
        by (intro sinv.AddUnify sinv.ItRight sy)
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
        "vT = (v, T)" "reduces ar env0 dps0 env1 ((rb, t, u) # dps1)"
        "strip_comb t = (Var v T, targs)" "length Ts = length targs"
        "\<forall>U\<in>set Ts. ground ar U" "sinv ar (GC env1 rb targs u dps1) xq"
    | (single) env0 dps0 env1 dps1 v T where "G = GE env0 dps0" "vT = (v, T)"
        "reduces ar env0 dps0 env1 dps1" "ground ar T" "\<forall>U\<in>set Ts. ground ar U"
        "sinv ar (GS env1 dps1 (length Ts)) xq"
      by (auto elim: sinv_MapNewDsetE)
    then show ?thesis
    proof cases
      case copy
      note G = copy(1) and vT = copy(2) and red = copy(3) and sc = copy(4) and l = copy(5)
        and g = copy(6) and sx = copy(7)
      from IH[OF px sx] have c: "copy_ok ar env1 rb targs u dps1 u' env' dpairs'"
        and sx': "sinv ar (GC env1 rb targs u dps1) xq'" by simp_all
      have "elem_ok ar (GE env0 dps0) x" by (rule new_dset_sound[OF nd[unfolded vT] red sc l g c])
      moreover have "sinv ar (GE env0 dps0) s'" unfolding s' vT by (rule sinv.MapNewDset[OF red sc l g sx'])
      ultimately show ?thesis using G by simp
    next
      case single
      note G = single(1) and vT = single(2) and red = single(3) and gT = single(4) and g = single(5)
        and sx = single(6)
      from IH[OF px sx] have c: "elem_ok ar (GS env1 dps1 (length Ts)) (El_C u' env' dpairs')"
        and sx': "sinv ar (GS env1 dps1 (length Ts)) xq'" by simp_all
      have "elem_ok ar (GE env0 dps0) x" by (rule new_dset_sound1[OF nd[unfolded vT] red gT g c])
      moreover have "sinv ar (GE env0 dps0) s'" unfolding s' vT by (rule sinv.MapNewDset1[OF red gT g sx'])
      ultimately show ?thesis using G by simp
    qed
  next
    case (S_MapAbs a T xq)
    from si S_MapAbs obtain env0 rb targs b T' body dps0 where
      G: "G = GC env0 rb targs (Abs b T' body) dps0"
      and sx: "sinv ar (GC env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body dps0) xq"
      and gT: "ground ar T" and pt: "\<forall>t\<in>set targs. proper t"
      by (auto elim: sinv_MapAbsE)
    from okW_map_C[OF hyps[unfolded S_MapAbs seq.case]] obtain body' env' dpairs' xq' where
      px: "okW (P cfg xq) (Some (El_C body' env' dpairs', xq'))"
      and x: "x = El_C (Abs a T body') env' dpairs'" and s': "s' = S_MapAbs a T xq'"
      by auto
    from IH[OF px sx] mapabs_copy[OF _ gT pt] sinv.MapAbs[OF _ gT pt] show ?thesis
      by (simp add: G x s')
  next
    case (S_Proj vname env Ts Us targs rb u dps head targ tail)
    from si S_Proj obtain j where G: "G = GC env rb targs u dps" and hd: "head = Bound j"
      and prem: "wf_env ar env" "\<forall>dp\<in>set dps. wf_dp ar dp" "binders_ok ar rb" "wf_tm ar rb u"
        "\<forall>t\<in>set targs. wf_tm ar rb t" "0 \<le> j" "nat_of_integer j < length targs"
        "targ = targs ! (length targs - 1 - nat_of_integer j)" "length Ts = length targs"
        "\<forall>U\<in>set Ts. ground ar U" "\<forall>U\<in>set Us. ground ar U"
      and st: "sinv ar (GC env rb targs u dps) tail"
      by (auto elim: sinv_ProjE)
    from hyps S_Proj consider (fail) "okW (P cfg tail) (Some (x, s'))"
      | (ok) env' args env2 frigid fflex where "make_args vname Ts env Us = (env', args)"
        "okW (SIMPL (cfg_alg cfg) env' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u)
          # dps)) (env2, frigid, fflex)"
        "x = El_C (list_comb head args) env2 (frigid @ fflex)" "s' = tail"
      by (auto simp: okW_handleW Let_def split: prod.splits dest!: okW_CANTUNIFY_handler')
    then show ?thesis
    proof cases
      case fail
      from IH[OF this st] G show ?thesis by simp
    next
      case (ok env' args env2 frigid fflex)
      from proj_copy[OF ok(1,2) prem] ok(3,4) st G hd show ?thesis by simp
    qed
  next
    case (S_MapJoin uhead xq)
    from si S_MapJoin obtain env0 rb targs u dps0 uargs where G: "G = GC env0 rb targs u dps0"
      and sc: "strip_comb u = (uhead, uargs)" and cl: "no_loose_bound (tr uhead) 0"
      and ty: "typs_ok ar uhead" and pr: "proper uhead"
      and sx: "sinv ar (GD env0 rb targs uargs dps0) xq"
      by (auto elim: sinv_MapJoinE)
    from okW_map_D[OF hyps[unfolded S_MapJoin seq.case]] obtain uargs' env' dpairs' xq' where
      px: "okW (P cfg xq) (Some (El_D uargs' env' dpairs', xq'))"
      and x: "x = El_C (list_comb uhead uargs') env' dpairs'" and s': "s' = S_MapJoin uhead xq'"
      by auto
    from IH[OF px sx] mapjoin_copy[OF sc cl ty pr] sinv.MapJoin[OF sc cl ty pr] show ?thesis
      by (simp add: G x s')
  next
    case (S_Maps vname rb targs uarg xq)
    from si S_Maps obtain env0 uargs dps0 where G: "G = GD env0 rb targs (uarg # uargs) dps0"
      and sx: "sinv ar (GD env0 rb targs uargs dps0) xq" and bok: "binders_ok ar rb"
      and wu: "wf_tm ar rb uarg" and wt: "\<forall>t\<in>set targs. wf_tm ar rb t"
      by (auto elim: sinv_MapsE)
    from okW_map_D[OF hyps[unfolded S_Maps seq.case]] obtain uargs' env dps xq' cs where
      px: "okW (P cfg xq) (Some (El_D uargs' env dps, xq'))"
      and cc: "okW (copycons cfg vname rb targs uarg uargs' env dps) cs"
      and pa: "okW (P cfg (S_Append cs (S_Maps vname rb targs uarg xq'))) (Some (x, s'))"
      by auto
    from IH[OF px sx] have a: "args_ok ar env0 rb targs uargs dps0 uargs' env dps"
      and sx': "sinv ar (GD env0 rb targs uargs dps0) xq'" by simp_all
    have "sinv ar (GD env0 rb targs (uarg # uargs) dps0) (S_Append cs (S_Maps vname rb targs uarg xq'))"
      by (intro sinv.Append copycons_sound[OF cc a bok wu wt] sinv.Maps[OF sx' bok wu wt])
    from IH[OF pa this] G show ?thesis by simp
  next
    case (S_Append xq yq)
    from si S_Append have sx: "sinv ar G xq" and sy: "sinv ar G yq" by (auto elim: sinv_AppendE)
    from okW_bind_opt[OF hyps[unfolded S_Append seq.case]] consider (none) "okW (P cfg yq) (Some (x, s'))"
      | (some) xq' where "okW (P cfg xq) (Some (x, xq'))" "s' = S_Append xq' yq"
      by auto
    then show ?thesis
    proof cases
      case none
      from IH[OF this sy] show ?thesis .
    next
      case (some xq')
      from IH[OF some(1) sx] some(2) sy show ?thesis by (simp add: sinv.Append)
    qed
  next
    case (S_MapCons uargs' xq)
    from si S_MapCons obtain env0 rb targs uarg uargs dps0 env dps u2 where
      G: "G = GD env0 rb targs (uarg # uargs) dps0"
      and a: "args_ok ar env0 rb targs uargs dps0 uargs' env dps"
      and sx: "sinv ar (GC env rb targs u2 dps) xq" and eq: "env \<Turnstile> rlist_abs rb uarg \<approx> rlist_abs rb u2"
      by (auto elim: sinv_MapConsE)
    from okW_map_C[OF hyps[unfolded S_MapCons seq.case]] obtain uarg' env' dpairs' xq' where
      px: "okW (P cfg xq) (Some (El_C uarg' env' dpairs', xq'))"
      and x: "x = El_D (uarg' # uargs') env' dpairs'" and s': "s' = S_MapCons uargs' xq'"
      by auto
    from IH[OF px sx] mapcons_args[OF a _ eq] sinv.MapCons[OF a _ eq] show ?thesis
      by (simp add: G x s')
  qed
qed



subsection \<open>Unifiers\<close>

text \<open>The sequence of \<open>hounifiers\<close> satisfies the invariant for its pairs.\<close>

theorem hounifiers_sinv:
  assumes "wf_env ar env" "binders_ok ar rb" "\<forall>(t, u)\<in>set tus. wf_tm ar rb t \<and> wf_tm ar rb u"
  shows "sinv ar (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) (hounifiers rb env tus)"
proof -
  have "reduces ar env (map (\<lambda>(t, u). (rb, t, u)) tus) env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    using assms by (auto simp: reduces_def wf_state_def)
  then show ?thesis unfolding hounifiers_def by (rule sinv.AddUnify[OF _ sinv.Empty])
qed

text \<open>Every element that pulling such a sequence produces is a unifier, and the rest of the
  sequence satisfies the invariant again.\<close>

theorem pull_unifier:
  assumes "sinv ar (GR env0 dps0) s" "pull cfg s = Some r" "snd r = UOk (Some (x, s'))"
  obtains env tps where "x = El_R env tps" "unifier env0 dps0 env tps" "sinv ar (GR env0 dps0) s'"
proof -
  from pull_sound[OF assms(2,3,1)] have "elem_ok ar (GR env0 dps0) x" "sinv ar (GR env0 dps0) s'" by simp_all
  with that show ?thesis by (cases x) auto
qed

text \<open>
  In terms of the input: a unifier \<open>El_R env tps\<close> of the sequence \<open>hounifiers rb env0 tus\<close>
  extends \<open>env0\<close>, and every closed substitution that satisfies \<open>env\<close> and solves the remaining
  flex-flex pairs \<open>tps\<close> makes the two sides of each input pair \<open>\<beta>\<eta>\<close>-equal (under the binder).
\<close>

corollary hounifiers_unifier:
  assumes "unifier env0 (map (\<lambda>(t, u). (rb, t, u)) tus) env tps"
    "closed_on UNIV \<sigma>" "sat \<sigma> env" "\<forall>(t', u')\<in>set tps. mk_subst \<sigma> (tr t') \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u')"
    "(t, u) \<in> set tus"
  shows "extends env env0" "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb u))"
proof -
  show "extends env env0" using assms(1) by (simp add: unifier_def)
  from assms(1-4) have "dsolved_all \<sigma> (map (\<lambda>(t, u). (rb, t, u)) tus)" unfolding unifier_def by blast
  with assms(5) have "dsolved \<sigma> (rb, t, u)" by auto
  then show "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb u))"
    by (simp add: dsolved_def)
qed

end

end
