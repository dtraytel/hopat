section \<open>Problems with Type Variables: Completeness of \<open>MATCH\<close>\<close>

theory Unify_Poly_Match_Complete
  imports Unify_Poly_Copy
begin

text \<open>
  Completeness of \<^const>\<open>MATCH\<close> on polymorphic problems, for the arity bound \<open>k\<close>: if the
  solution \<open>\<rho>\<close> of the type environment satisfies the k-condition, some element of the sequence of
  \<^const>\<open>MATCH\<close> is in the invariant for extensions of the solutions, and the measure decreases.
  The guess of the number of arguments \<open>j\<close> of the type of the pair is that of the instance under
  \<open>\<rho>\<close>; the other guesses must not raise an exception, so we first show that the steps of
  \<^const>\<open>MATCH\<close> terminate without an exception on well-typed states, whether they have a
  solution or not.
\<close>


subsection \<open>Extensions of the type environment\<close>

lemma pinv_text:
  assumes pi: "pinv alg ar A W env dps"
    and te: "tenv env' = tenv env" "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'"
    and ti: "tinv ar (maxidx env') (tyenv env') A" "tsorted alg (tyenv env')"
  shows "pinv alg ar A W env' dps"
proof -
  let ?\<theta> = "tyenv env" and ?\<theta>' = "tyenv env'"
  note pi0 = pinvD[OF pi]
  note ei = penv_invD[OF pi0(1)]
  have ac': "tacyc ?\<theta>'" by (rule tinv_tacyc[OF ti(1)])
  have ety: "etys env' = etys env" by (rule etys_same_tenv[OF te(1)])
  have twe: "tyw ar ?\<theta>' A T" if "T \<in> etys env'" for T
    using that ety pi0(3) tyw_textends[OF ac' te(2)] by blast
  have twW: "tyw ar ?\<theta>' A (W x)" for x using pi0(5) tyw_textends[OF ac' te(2)] by blast
  have wc: "wcons W env'"
    using pi0(6) te(1) by (auto simp: wcons_def simp del: split_paired_All dest: arg_cong[of _ _ "tnorm ?\<theta>'"])
      (metis ac' te(2) tnorm_textends)
  have etv: "etvars env' \<subseteq> tvars_env ?\<theta>' \<union> A"
    using pi0(3) tvars_env_textends[OF te(2)] ety by (fastforce simp: etvars_def tyw_def)
  have pe: "penv_inv alg ar W env'"
    unfolding penv_inv_def
  proof (intro conjI)
    show "tinv ar (maxidx env') ?\<theta>' (etvars env')" by (rule tinv_subset[OF ti(1) etv])
    show "tsorted alg ?\<theta>'" by (rule ti(2))
    show "nacyc env'" using ei(3) nacyc_same_tenv[OF te(1)] by simp
    show "pwf_env ar env'" using ei(4) te(1) by (simp add: pwf_env_def)
    show "wt_env W env'"
      using pi0(1) wt_env_textends[OF ac' te(2,1)] by (simp add: penv_inv_def)
    show "fresh_env env'" by (rule fresh_env_same[OF te(1,3) ei(6)])
  qed
  have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar ?\<theta>' A T) \<and> ptyped env' W dp \<and> dp_below (maxidx env') dp"
    if dp: "dp \<in> set dps" for dp
  proof -
    obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
    from pi0(4)[OF dp] dpe obtain T where w: "swf_dp ar dp" and tw: "\<forall>T\<in>dtys dp. tyw ar ?\<theta> A T"
      and ty: "typed env W (map snd rb) t T" "typed env W (map snd rb) u T"
      and bl: "below (maxidx env) t" "below (maxidx env) u"
      by auto
    have "ptyped env' W dp"
      using typed_wcons[OF ac' te(2) pi0(6) wc ty(1)] typed_wcons[OF ac' te(2) pi0(6) wc ty(2)] dpe
      by auto
    moreover have "\<forall>T\<in>dtys dp. tyw ar ?\<theta>' A T" using tw tyw_textends[OF ac' te(2)] by blast
    moreover have "dp_below (maxidx env') dp" using bl below_mono[OF _ te(3)] dpe by simp
    ultimately show ?thesis using w by blast
  qed
  then show ?thesis using pe ti(1) twe twW wc by (auto simp: pinv_def)
qed

lemma foldrW_total:
  "(\<And>x t. x \<in> set xs \<Longrightarrow> \<exists>r. okW (f x t) r) \<Longrightarrow> \<exists>r. okW (foldrW f xs b) r"
proof (induction xs)
  case (Cons x xs)
  then obtain t where "okW (foldrW f xs b) t" by auto
  moreover from Cons.prems[of x t] obtain r where "okW (f x t) r" by auto
  ultimately show ?case by auto
qed simp


subsection \<open>Totality of copying\<close>

text \<open>
  \<open>ptot\<close>: the assumptions under which \<^const>\<open>mc\<close> and \<^const>\<open>match1\<close> terminate without an
  exception: the term \<open>u\<close> and the arguments \<open>targs\<close> are typed modulo the type environment.
\<close>

definition ptot :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> bool" where
  "ptot alg ar A W env rb targs u \<longleftrightarrow> pinv alg ar A W env [] \<and>
    (\<forall>T\<in>snd ` set rb. tyw ar (tyenv env) A T) \<and> (\<forall>t\<in>set targs. \<forall>T\<in>tys t. tyw ar (tyenv env) A T) \<and>
    (\<exists>Ts. list_all2 (typed env W (map snd rb)) targs Ts) \<and> (\<forall>T\<in>tys u. tyw ar (tyenv env) A T) \<and>
    (\<exists>U. typed env W (map snd rb) u U)"

lemma ptot_types:
  assumes "ptot alg ar A W env rb targs u"
  obtains T0 base Ts' where "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "length Ts' = length targs"
    "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T" "tyw ar (tyenv env) A T0" "tyw ar (tyenv env) A base"
    "has_type (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) (head_of u))
      (tnorm (tyenv env) T0)"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  from assms obtain Ts U where pi0: "pinv alg ar A W env []" and twb: "\<forall>T\<in>snd ` set rb. tyw ar ?\<theta> A T"
    and tg: "\<forall>t\<in>set targs. \<forall>T\<in>tys t. tyw ar ?\<theta> A T"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twu: "\<forall>T\<in>tys u. tyw ar ?\<theta> A T"
    and tyu0: "typed env W (map snd rb) u U"
    unfolding ptot_def by blast
  note pi = pinvD[OF pi0]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  have tyu: "has_type ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)" using tyu0 by (simp add: typed_def)
  from has_type_head_of[OF tyu] obtain Th where tyh: "has_type ?V ?Bs (tnormt ?\<theta> (head_of u)) Th" by auto
  have tch: "\<forall>X\<in>set (map snd rb) \<union> tys (head_of u). tcons ?\<theta> X"
    using twb twu tys_head_of[of u] tcU by auto
  from env_fastype_pterm[OF ac tch tyh] obtain T0 where
    f: "ok (fastype env rb (head_of u)) T0" "tnorm ?\<theta> T0 = Th" by (auto simp: fastype_def)
  have twT0: "tyw ar ?\<theta> A T0" using fastype_tyw[OF f(1) pi(2) twb] twu tys_head_of[of u] by blast
  have "tnorm ?\<theta> T0 = foldr fun_type (arg_types (tnorm ?\<theta> T0)) (res_type (tnorm ?\<theta> T0))"
    by (simp add: arg_res_type)
  from body_type_ptnorm[OF ac tcU[OF twT0] this res_type_base] obtain base where
    b: "body_type env T0 = return base" by blast
  have twb0: "tyw ar ?\<theta> A base" using body_type_tyw[OF b[unfolded return_def] refl pi(2) twT0] .
  have tct: "\<forall>t\<in>set targs. \<forall>X\<in>tys t. tcons ?\<theta> X" using tg tcU by blast
  from mapM_fastype_ptnorm[OF ac _ tgty tct] twb tcU obtain Ts' where
    m: "mapM (fastype env rb) targs = return Ts'" "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts" by blast
  have lTs: "length Ts' = length targs"
    using arg_cong[OF m(2), of length] list_all2_lengthD[OF tgty] by simp
  have twTs: "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T" by (rule mapM_fastype_tyw[OF m(1) pi(2) twb]) (use tg in blast)
  show ?thesis using that[OF _ b m(1) lTs twTs twT0 twb0] f tyh by (simp add: return_def)
qed


context wf_algebra
begin

text \<open>The projections of a rigid term with typed arguments raise no exception.\<close>

lemma projs_total:
  assumes cfg: "cfg_alg cfg = alg" and pi0: "pinv alg ar A W env dps"
    and twb: "tyw ar (tyenv env) A base" and twTs: "\<forall>T\<in>set Ts. tyw ar (tyenv env) A T"
    and pT: "\<And>bv T targ. (bv, T, targ) \<in> set projs \<Longrightarrow> T \<in> set Ts"
  shows "\<forall>(bv, T, targ)\<in>set projs. \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
proof (clarify)
  let ?\<theta> = "tyenv env"
  note pi = pinvD[OF pi0]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  fix bv T targ assume "(bv, T, targ) \<in> set projs"
  then have twT: "tyw ar ?\<theta> A T" using pT twTs by blast
  have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
    by (simp add: arg_res_type)
  from strip_type_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Us bary where
    st: "strip_type env T = return (Us, bary)" by blast
  have twb': "tyw ar ?\<theta> A bary" using strip_type_tyw[OF st[unfolded return_def] pi(2) twT] by simp
  have "proj_total cfg env base bary p" for p
    by (rule proj_total_tyw[OF cfg pi(2) ei(2) twb twb'])
  with st show "\<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
    by (auto simp: return_def)
qed

lemma ptot_Abs:
  assumes pt: "ptot alg ar A W env rb targs u" and hA: "head_of u = Abs a T body"
  shows "ptot alg ar A W env ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  from pt obtain Ts where pi0: "pinv alg ar A W env []" and twb: "\<forall>T\<in>snd ` set rb. tyw ar ?\<theta> A T"
    and tg: "\<forall>t\<in>set targs. \<forall>T\<in>tys t. tyw ar ?\<theta> A T"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twu: "\<forall>T\<in>tys u. tyw ar ?\<theta> A T"
    unfolding ptot_def by blast
  note pi = pinvD[OF pi0]
  have ac: "tacyc ?\<theta>" by (rule tinv_tacyc[OF pi(2)])
  obtain T0 base Ts' where
    tyh: "has_type ?V ?Bs (tnormt ?\<theta> (head_of u)) (tnorm ?\<theta> T0)"
    by (rule ptot_types[OF pt])
  from tyh hA obtain U' where tyb: "has_type ?V (tnorm ?\<theta> T # ?Bs) (tnormt ?\<theta> body) U'"
    by (auto elim: has_type_elims)
  have "tnorm ?\<theta> U' = U'" using typed_type_normal[of env W "T # map snd rb" body U'] tyb ac by simp
  with tyb have tyb': "typed env W (map snd ((a, T) # rb)) body U'" by (simp add: typed_def)
  have ths: "tys (head_of u) \<subseteq> tys u" by (rule tys_head_of)
  have twT: "tyw ar ?\<theta> A T" and twbody: "\<forall>X\<in>tys body. tyw ar ?\<theta> A X" using twu ths hA by auto
  have tgty': "list_all2 (typed env W (map snd ((a, T) # rb))) (map (incr_boundvars 1) targs @ [Bound 0]) (Ts @ [T])"
  proof (rule list_all2_appendI)
    show "list_all2 (typed env W (map snd ((a, T) # rb))) (map (incr_boundvars 1) targs) Ts"
      unfolding list_all2_map1 using tgty
      by (rule list_all2_mono) (simp add: typed_def has_type_incr_boundvars1)
  qed (simp add: typed_def has_type_Bound_iff)
  show ?thesis unfolding ptot_def
    using pi0 twb twT tg tgty' twbody tyb' by auto
qed

lemma mc_total:
  assumes cfg: "cfg_alg cfg = alg"
  shows "ptot alg ar A W env rb targs u \<Longrightarrow> \<exists>sq. okW (mc cfg vname rb targs u env dps) sq"
proof (induction "size u" arbitrary: rb targs u rule: less_induct)
  case less
  obtain T0 base Ts' where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "length Ts' = length targs"
    "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T" "tyw ar (tyenv env) A base"
    by (rule ptot_types[OF less.prems]) blast
  note mu = mc_punfold[OF ty0(1-3), of cfg vname dps]
  have pi0: "pinv alg ar A W env []" using less.prems by (simp add: ptot_def)
  have rig: ?case if hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
  proof -
    from make_projs_exact[OF ty0(4), of u targs] obtain projs where
      pr: "make_projs u targs Ts' targs = returnW projs" by blast
    have pT: "T \<in> set Ts'" if "(bv, T, targ) \<in> set (rev projs)" for bv T targ
      using make_projs_ok[of u targs Ts' targs projs] pr that by fastforce
    have pt: "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
        (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
      by (rule projs_total[OF cfg pi0 ty0(6,5)]) (use pT in blast)
    from matchfun_presult[OF pt] obtain sq where
      mf: "okW (matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) base Ts' (rev projs)) sq"
      by blast
    have "okW (mc cfg vname rb targs u env dps) sq" using mu pr mf hA hV by (cases "head_of u") simp_all
    then show ?thesis by blast
  qed
  show ?case
  proof (cases "head_of u")
    case (Abs a T body)
    have "size body < size u" using strip_comb_Abs_size[of u a T body] Abs by (simp add: fst_strip_comb)
    from less.hyps[OF this ptot_Abs[OF less.prems Abs]] obtain s where
      "okW (mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps) s" by blast
    then show ?thesis using mu Abs by auto
  next
    case (Var w Wt)
    then show ?thesis using mu by (simp split: prod.split)
  qed (use rig in simp_all)
qed

end

end
