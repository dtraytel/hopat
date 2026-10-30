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

context csig
begin

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

end


context wf_csig
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


subsection \<open>Single steps of matching\<close>

text \<open>
  The term \<open>hd ?G\<^sub>1(\<dots>) \<dots> ?G\<^sub>m(\<dots>)\<close> built with \<^const>\<open>make_args\<close> is a copy of \<open>h ss\<close> if the new
  variables \<open>?G\<^sub>i\<close> are assigned the abstractions of \<open>ss\<close> (the analogue of
  @{thm [source] make_args_copy}).
\<close>

context csig
begin

lemma pmake_args_copy:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and ma: "make_args vname Ts env Us = (env', args)"
    and tw: "\<forall>X\<in>set Ts \<union> set Us. tyw ar (tyenv env) A X"
    and tyss: "(ibctx \<rho> Ts, \<tau>') \<tturnstile> ss : map trty (map (tsubst \<rho>) Us)"
    and nrss: "\<forall>w\<in>set ss. no_redex w" and nlss: "\<forall>w\<in>set ss. no_loose_bound w (length Ts)"
    and tyhd: "typed env W (rev Ts) hd0 (foldr fun_type Us U)" and vhd: "vps hd0 = {}"
    and twhd: "\<forall>X\<in>tys hd0. tyw ar (tyenv env) A X" and whd: "swf_cp ar (length Ts) hd0"
    and htr: "\<And>\<sigma>'. rigid_subst \<sigma>' \<Longrightarrow> mk_subst \<sigma>' (tr (inst \<rho> hd0)) = h"
    and dD: "ivps \<rho> dps \<subseteq> D"
  obtains W1 \<sigma>1 NV where "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho> env' dps D NV"
    "typed env' W1 (rev Ts) (list_comb hd0 args) U" "swf_cp ar (length Ts) (list_comb hd0 args)"
    "\<forall>X\<in>tys (list_comb hd0 args). tyw ar (tyenv env') A X" "below (maxidx env') (list_comb hd0 args)"
    "vps (inst \<rho> (list_comb hd0 args)) = NV"
    "mk_subst \<sigma>1 (tr (inst \<rho> (list_comb hd0 args))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ss"
    "sum (vsz \<tau>' \<sigma>1) NV = (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (trty (tsubst \<rho> (Us ! i))))"
proof -
  let ?\<theta> = "tyenv env"
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  have lUs: "length Us = length ss" using typings_length[OF tyss] by simp
  define ws where "ws = map (Abs_m (length Ts)) ss"
  have lw: "length ws = length Us" using lUs by (simp add: ws_def)
  have tyssi: "(ibctx \<rho> Ts, \<tau>') \<turnstile> ss ! i : trty (tsubst \<rho> (Us ! i))" if "i < length Us" for i
    using typings_nth[OF tyss, of i] that lUs by simp
  have nri: "no_redex (ss ! i)" "no_loose_bound (ss ! i) (length Ts)" if "i < length ss" for i
    using nrss nlss that by auto
  have wsi: "no_loose_bound (ws ! i) 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> ws ! i : trty (tsubst \<rho> (foldr fun_type Ts (Us ! i))))"
    if i: "i < length Us" for i
  proof -
    have nl: "no_loose_bound (ws ! i) 0" using nlss i lUs by (simp add: ws_def loose_bound_Abs_m)
    have "(\<lambda>_. Atom 0, \<tau>') \<turnstile> Abs_m (length (map trty (map (tsubst \<rho>) Ts))) (ss ! i) :
        map trty (map (tsubst \<rho>) Ts) \<Rrightarrow> trty (tsubst \<rho> (Us ! i))"
      by (rule typing_Abs_m) (use tyssi[OF i] in simp)
    then have "(e, \<tau>') \<turnstile> ws ! i : trty (tsubst \<rho> (foldr fun_type Ts (Us ! i)))" for e
      using typing_closed[OF _ nl] i lUs by (simp add: ws_def tsubst_foldr_fun trty_foldr)
    with nl show ?thesis by blast
  qed
  obtain W1 \<sigma>1 xs where me: "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env' dps" "agree (maxidx env) \<sigma> \<sigma>1"
    "agreeV (maxidx env) W W1" "maxidx env \<le> maxidx env'" "pextends env' env"
    "tenv env' = tenv env" "tyenv env' = tyenv env"
    "length xs = length Us" "distinct xs" "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env'"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. \<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> W1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    by (rule make_args_pextend[OF pc ma tw lw wsi]) blast
  have me12: "\<sigma>1 (code (AVar (xs ! i))) = ws ! i" "W1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    if "i < length Us" for i using me(12) that by blast+
  note pi1 = pinvD[OF pcinvD(1)[OF me(1)]]
  have la: "length args = length Us" using me(8,11) by simp
  have ai: "args ! i = combound (Var (xs ! i) (foldr fun_type Ts (Us ! i))) 0 (length Ts)"
    if "i < length Us" for i using me(8,11) that by simp
  have bxs: "maxidx env < snd (xs ! i) \<and> snd (xs ! i) \<le> maxidx env'" if "i < length Us" for i
  proof -
    have "xs ! i \<in> set xs" using me(8) that by simp
    with me(10) show ?thesis by blast
  qed
  have twG: "tyw ar (tyenv env') A (foldr fun_type Ts (Us ! i))" if "i < length Us" for i
    using tw that me(7) by (simp add: tyw_foldr_fun)
  have tctxi: "tctx env' W1 (xs ! i) = tnorm (tyenv env') (foldr fun_type Ts (Us ! i))" if "i < length Us" for i
    using wcons_tctx[OF pi1(6)] me12(2)[OF that] by simp
  have tyai: "list_all2 (typed env' W1 (rev Ts)) args Us"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length args = length Us" by (rule la)
    fix i assume "i < length args"
    then have i: "i < length Us" using la by simp
    show "typed env' W1 (rev Ts) (args ! i) (Us ! i)"
      using typed_combound_Var[OF tctxi[OF i]] ai[OF i] by simp
  qed
  have bhd: "below (maxidx env) hd0" using vhd by (simp add: below_vps_iff)
  have tyhd': "typed env' W1 (rev Ts) hd0 (foldr fun_type Us U)"
    by (rule typed_pext[OF tyhd me(7) pi(6) pi1(6) me(3) bhd])
  define NV where "NV = set (map2 (\<lambda>x X. (x, tsubst \<rho> (foldr fun_type Ts X))) xs Us)"
  have "map2 (\<lambda>x X. (x, tsubst \<rho> (foldr fun_type Ts X))) xs Us =
      map (\<lambda>i. (xs ! i, tsubst \<rho> (foldr fun_type Ts (Us ! i)))) [0..<length Us]"
    using me(8) by (intro nth_equalityI) auto
  then have NVi: "y \<in> NV \<longleftrightarrow> (\<exists>i<length Us. y = (xs ! i, tsubst \<rho> (foldr fun_type Ts (Us ! i))))" for y
    by (auto simp: NV_def)
  have NVb: "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'" if "y \<in> NV" for y
    using that NVi bxs by auto
  have vai: "vps (inst \<rho> (args ! i)) = {(xs ! i, tsubst \<rho> (foldr fun_type Ts (Us ! i)))}" if "i < length Us" for i
    using ai[OF that] by simp
  have vargs: "\<Union> (vps ` inst \<rho> ` set args) = NV"
  proof
    show "\<Union> (vps ` inst \<rho> ` set args) \<subseteq> NV" using vai la NVi by (force simp: in_set_conv_nth)
    show "NV \<subseteq> \<Union> (vps ` inst \<rho> ` set args)"
    proof
      fix y assume "y \<in> NV"
      then obtain i where i: "i < length Us" "y = (xs ! i, tsubst \<rho> (foldr fun_type Ts (Us ! i)))" using NVi by blast
      then have "y \<in> vps (inst \<rho> (args ! i))" using vai by simp
      with i(1) la show "y \<in> \<Union> (vps ` inst \<rho> ` set args)" by (auto dest: nth_mem[of i args])
    qed
  qed
  have rr: "reach (instE \<rho> env') Z = reach (instE \<rho> env) Z" for Z
    by (rule reach_lookup_eq) (simp add: me(6))
  have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho> env' dps D NV"
  proof (rule psextI[OF me(1) me(3) me(2) _ me(4,5)])
    show "tagree (maxidx env) \<rho> \<rho>" by (simp add: tagree_def)
    show "finite NV" by (simp add: NV_def)
    show "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'" if "y \<in> NV" for y using NVb that by blast
    show "reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> D) \<union> NV" for X
      using rr reach_subset[of X "X \<union> D" "instE \<rho> env"] by auto
    show "ivps \<rho> dps \<subseteq> reach (instE \<rho> env) D \<union> NV" using dD reach_incl[of D "instE \<rho> env"] by blast
  qed
  define u' where "u' = list_comb hd0 args"
  have tyu': "typed env' W1 (rev Ts) u' U" using typed_list_comb[OF tyhd' tyai] by (simp add: u'_def)
  have "\<forall>a\<in>set args. swf_cp ar (length Ts) a"
    by (rule make_args_swf_cp[OF ma]) (use tw in \<open>auto simp: tyw_def\<close>)
  then have wc: "swf_cp ar (length Ts) u'" using whd by (simp add: u'_def swf_cp_list_comb)
  have twu': "\<forall>X\<in>tys u'. tyw ar (tyenv env') A X"
    using twG ai la twhd me(7) by (auto simp: u'_def tys_list_comb in_set_conv_nth)
  have "below (maxidx env') a" if "a \<in> set args" for a
  proof -
    from that obtain i where i: "i < length Us" "a = args ! i" using la by (auto simp: in_set_conv_nth)
    then show ?thesis using ai[OF i(1)] bxs[OF i(1)] by (simp add: below_def)
  qed
  moreover have "below (maxidx env') hd0" using vhd by (simp add: below_vps_iff)
  ultimately have bu': "below (maxidx env') u'" by (simp add: u'_def below_list_comb)
  have vu': "vps (inst \<rho> u') = NV" using vargs vhd by (simp add: u'_def inst_list_comb vps_list_comb vps_inst)
  have rs1: "rigid_subst \<sigma>1" using solutionD(3)[OF pcinvD(3)[OF me(1)]] .
  have eq: "mk_subst \<sigma>1 (tr (inst \<rho> u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ss"
  proof -
    have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho> a))) args) ss"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho> a))) args) = length ss" using la lUs by simp
      fix i assume "i < length (map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho> a))) args)"
      then have i: "i < length Us" using la by simp
      have "mk_subst \<sigma>1 (tr (inst \<rho> (args ! i))) = Abs_m (length Ts) (ss ! i) \<degree>\<degree> map BVar (downs (length Ts))"
        using ai[OF i] me12(1)[OF i] i lUs by (simp add: tr_combound0 ws_def)
      then show "map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho> a))) args ! i \<equiv>\<^sub>\<beta>\<^sub>\<eta> ss ! i"
        using Abs_m_apps_downs[OF nri(2)] i lUs la by simp
    qed
    then have "h \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho> a))) args \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ss"
      by (rule equiv_list_app[OF equiv_refl])
    then show ?thesis using htr[OF rs1] by (simp add: u'_def inst_list_comb tr_list_comb comp_def)
  qed
  have sz: "sum (vsz \<tau>' \<sigma>1) NV = (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (trty (tsubst \<rho> (Us ! i))))"
  proof -
    let ?L = "map2 (\<lambda>x X. (x, tsubst \<rho> (foldr fun_type Ts X))) xs Us"
    have "map fst ?L = xs" using me(8) by (simp add: map_zip_map2 zip_map2 map_map comp_def split_def)
    then have dL: "distinct ?L" using me(9) by (metis distinct_map)
    have "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) = sum_list (map (vsz \<tau>' \<sigma>1) ?L)"
      using sum.distinct_set_conv_list[OF dL] by (simp add: NV_def)
    also have "\<dots> = (\<Sum>i<length Us. vsz \<tau>' \<sigma>1 (xs ! i, tsubst \<rho> (foldr fun_type Ts (Us ! i))))"
      using me(8) by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (trty (tsubst \<rho> (Us ! i))))"
    proof (rule sum.cong)
      show "{..<length Us} = {..<length ss}" using lUs by simp
      fix i assume "i \<in> {..<length ss}"
      then have i: "i < length Us" and i': "i < length ss" using lUs by simp_all
      have "vsz \<tau>' \<sigma>1 (xs ! i, foldr fun_type (map (tsubst \<rho>) Ts) (tsubst \<rho> (Us ! i))) =
          lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (trty (tsubst \<rho> (Us ! i)))"
        by (rule vsz_Abs_m) (use me12(1)[OF i] tyssi[OF i] nri[OF i'] i' in \<open>simp_all add: ws_def\<close>)
      then show "vsz \<tau>' \<sigma>1 (xs ! i, tsubst \<rho> (foldr fun_type Ts (Us ! i))) =
          lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (trty (tsubst \<rho> (Us ! i)))"
        by (simp add: tsubst_foldr_fun)
    qed
    finally show ?thesis .
  qed
  show ?thesis by (rule that[OF sx tyu'[unfolded u'_def] wc[unfolded u'_def] twu'[unfolded u'_def]
    bu'[unfolded u'_def] vu'[unfolded u'_def] eq[unfolded u'_def] sz])
qed

text \<open>An extension of the state by a type unification composes with an extension.\<close>

lemma psext_text:
  assumes sx: "psext alg ar A W \<tau>' \<sigma> \<rho>' env' W1 \<sigma>1 \<rho>1 env1 dps1 D NV"
    and pe: "pextends env' env" and mx: "maxidx env \<le> maxidx env'" and ag: "tagree (maxidx env) \<rho> \<rho>'"
    and rr: "\<And>Z. reach (instE \<rho>' env') Z = reach (instE \<rho> env) Z"
  shows "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho>1 env1 dps1 D NV"
proof -
  note sd = psextD[OF sx]
  show ?thesis
  proof (rule psextI[OF sd(1) agreeV_mono[OF sd(2) mx] agree_mono[OF sd(3) mx]])
    show "tagree (maxidx env) \<rho> \<rho>1" using tagree_trans[OF ag sd(4) mx] .
    show "maxidx env \<le> maxidx env1" using mx sd(5) by simp
    show "pextends env1 env" by (rule pextends_trans[OF sd(6) pe])
    show "finite NV" by (rule sd(7))
    show "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env1" if "y \<in> NV" for y
      using sd(8)[OF that] mx by simp
    show "reach (instE \<rho>1 env1) X \<subseteq> reach (instE \<rho> env) (X \<union> D) \<union> NV" for X
      using sd(9)[of X] rr by simp
    show "ivps \<rho>1 dps1 \<subseteq> reach (instE \<rho> env) D \<union> NV" using sd(10) rr by simp
  qed
qed


text \<open>The elements of a projection of \<^const>\<open>match1\<close> with the guess \<open>p\<close>:\<close>

definition m1_elem :: "cfg \<Rightarrow> name \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> ptyp \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow>
    ptyp list \<Rightarrow> ptyp \<Rightarrow> nat \<Rightarrow> elem \<Rightarrow> bool" where
  "m1_elem cfg vname env dps base Ts bv Us bary p y \<longleftrightarrow>
    (\<exists>env0 Cs env' env'' args. gentvars p env = (env0, Cs) \<and> okW (proj_unify cfg base bary Cs env0) env' \<and>
      make_args vname Ts env' (Us @ Cs) = (env'', args) \<and> y = El_C (list_comb bv args) env'' dps)"

lemma match1_proj_presult:
  assumes "proj_total cfg env base bary p"
  shows "\<exists>r. okW (match1_proj cfg vname env dps base Ts bv (Us, bary) p tail) r \<and>
    (\<forall>y. ev cfg tail y \<longrightarrow> ev cfg r y) \<and>
    (\<forall>y. m1_elem cfg vname env dps base Ts bv Us bary p y \<longrightarrow> ev cfg r y)"
proof -
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  let ?m = "proj_unify cfg base bary Cs env0"
  let ?r = "do {env' \<leftarrow> ?m; (case make_args vname Ts env' (Us @ Cs) of (env'', args) \<Rightarrow>
    returnW (S_Append (S_Single (El_C (list_comb bv args) env'' dps)) tail))}"
  have pe: "match1_proj cfg vname env dps base Ts bv (Us, bary) p tail =
      handleW ?r (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)"
    by (simp add: match1_proj_def g)
  from assms g have "(\<exists>env'. okW ?m env') \<or> (\<exists>evs. ?m = Some (evs, UErr CANTUNIFY))"
    by (simp add: proj_total_def)
  then show ?thesis
  proof
    assume "\<exists>env'. okW ?m env'"
    then obtain env' where e': "okW ?m env'" by blast
    obtain env'' args where ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)"
      by (cases "make_args vname Ts env' (Us @ Cs)")
    let ?R = "S_Append (S_Single (El_C (list_comb bv args) env'' dps)) tail"
    have "okW ?r ?R" using e' ma by auto
    then have ok: "okW (match1_proj cfg vname env dps base Ts bv (Us, bary) p tail) ?R"
      unfolding pe by (rule okW_handleW[THEN iffD2, OF disjI1])
    have "ev cfg ?R y" if "m1_elem cfg vname env dps base Ts bv Us bary p y" for y
    proof -
      from that g obtain env1 env3 args3 where a: "okW ?m env1" "make_args vname Ts env1 (Us @ Cs) = (env3, args3)"
        "y = El_C (list_comb bv args3) env3 dps"
        unfolding m1_elem_def by auto
      have "env1 = env'" using okW_det[OF a(1) e'] .
      with a ma show ?thesis by (auto intro: ev.append_l ev.single)
    qed
    with ok show ?thesis by (blast intro: ev.append_r)
  next
    assume "\<exists>evs. ?m = Some (evs, UErr CANTUNIFY)"
    then obtain evs where c: "?m = Some (evs, UErr CANTUNIFY)" by blast
    then have "?r = Some (evs, UErr CANTUNIFY)" by (simp add: bindW_def)
    then have ok: "okW (match1_proj cfg vname env dps base Ts bv (Us, bary) p tail) tail"
      unfolding pe by (auto simp: okW_handleW)
    have "\<not> m1_elem cfg vname env dps base Ts bv Us bary p y" for y
      using c g by (auto simp: m1_elem_def)
    with ok show ?thesis by blast
  qed
qed

lemma match1_projs_presult:
  assumes "\<forall>(bv, T, targ)\<in>set projs. \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
  shows "\<exists>sq. okW (match1_projs cfg vname env dps base Ts projs tail) sq \<and> (\<forall>x. ev cfg tail x \<longrightarrow> ev cfg sq x) \<and>
    (\<forall>bv T targ Us bary p y. (bv, T, targ) \<in> set projs \<longrightarrow> ok (strip_type env T) (Us, bary) \<longrightarrow>
      p \<in> set (arity_guesses cfg bary) \<longrightarrow> m1_elem cfg vname env dps base Ts bv Us bary p y \<longrightarrow> ev cfg sq y)"
  using assms
proof (induction projs)
  case Nil
  show ?case by (intro exI[of _ tail]) simp
next
  case (Cons pr projs)
  obtain bv T targ where pr: "pr = (bv, T, targ)" by (cases pr)
  from Cons.prems pr obtain Us bary where st: "ok (strip_type env T) (Us, bary)"
    and gs: "\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p" by auto
  from Cons.IH Cons.prems obtain tl where tl: "okW (match1_projs cfg vname env dps base Ts projs tail) tl"
    and tail: "\<forall>x. ev cfg tail x \<longrightarrow> ev cfg tl x"
    and prj: "\<forall>bv T targ Us bary p y. (bv, T, targ) \<in> set projs \<longrightarrow> ok (strip_type env T) (Us, bary) \<longrightarrow>
      p \<in> set (arity_guesses cfg bary) \<longrightarrow> m1_elem cfg vname env dps base Ts bv Us bary p y \<longrightarrow> ev cfg tl y"
    by auto
  have "\<exists>r. okW (foldrW (match1_proj cfg vname env dps base Ts bv (Us, bary)) (arity_guesses cfg bary) tl) r \<and>
      (\<forall>y. ev cfg tl y \<longrightarrow> ev cfg r y) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>y. m1_elem cfg vname env dps base Ts bv Us bary p y \<longrightarrow> ev cfg r y)"
    by (rule ev_foldrW) (use gs match1_proj_presult in blast)
  then obtain r where r: "okW (foldrW (match1_proj cfg vname env dps base Ts bv (Us, bary)) (arity_guesses cfg bary) tl) r"
    "\<forall>y. ev cfg tl y \<longrightarrow> ev cfg r y"
    "\<forall>p\<in>set (arity_guesses cfg bary). \<forall>y. m1_elem cfg vname env dps base Ts bv Us bary p y \<longrightarrow> ev cfg r y"
    by blast
  have "okW (match1_projs cfg vname env dps base Ts (pr # projs) tail) r"
    using tl r(1) st by (auto simp: pr)
  moreover have "ev cfg r y" if "(bv', T', targ') \<in> set (pr # projs)" "ok (strip_type env T') (Us', bary')"
    "p \<in> set (arity_guesses cfg bary')" "m1_elem cfg vname env dps base Ts bv' Us' bary' p y"
    for bv' T' targ' Us' bary' p y
  proof (cases "(bv', T', targ') = pr")
    case True
    with that(2) st pr have "Us' = Us" "bary' = bary" by auto
    with True that(3,4) r(3) pr show ?thesis by auto
  next
    case False
    with that have "(bv', T', targ') \<in> set projs" by simp
    with that(2-4) prj r(2) show ?thesis by blast
  qed
  ultimately show ?case using tail r(2) by blast
qed

lemma match1_punfold:
  assumes "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts" "binder_types env T0 = return Us"
  shows "match1 cfg vname rb targs u env dps = do {
      projs \<leftarrow> make_projs u targs Ts targs;
      imit \<leftarrow>
        (case head_of u of
          Const _ _ \<Rightarrow>
            (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb (head_of u) args) env' dps)))
        | Free _ _ \<Rightarrow>
            (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb (head_of u) args) env' dps)))
        | _ \<Rightarrow> returnW S_Empty);
      match1_projs cfg vname env dps base Ts (rev projs) imit}"
  unfolding match1_def
  by (simp add: assms fst_strip_comb liftM_return Let_def split: pterm.split)

end


context wf_csig
begin

text \<open>
  Completeness of \<^const>\<open>match1\<close>: for a target \<open>s\<close> with a rigid head, the step that copies the
  head of \<open>s\<close> is among the elements, with the guess of the number of arguments of a projection
  from the instance; the pairs are unchanged.
\<close>

lemma pmatch1_complete:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and pre: "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
    and hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
  shows "\<exists>sq. okW (match1 cfg vname rb targs u env dps) sq \<and>
    (\<exists>u' env' W' \<sigma>' \<rho>' NV. ev cfg sq (El_C u' env' dps) \<and>
      pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env (pmc_dom \<rho> u targs dps) Ts U s 1 u' env' dps W' \<sigma>' \<rho>' NV \<and>
      (\<forall>X. reach (instE \<rho>' env') X = reach (instE \<rho> env) X))"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  from pre have pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and kk: "kokA k \<rho> ?\<theta> A" and sb: "sbinders ar rb"
    and twb: "\<forall>T\<in>snd ` set rb. tyw ar ?\<theta> A T"
    and tg: "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar ?\<theta> A T)"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twTs: "\<forall>T\<in>set Ts. tyw ar ?\<theta> A T"
    and wu: "swf_tm ar rb u" and twu: "\<forall>T\<in>tys u. tyw ar ?\<theta> A T"
    and bu: "below (maxidx env) u" and hl: "hlong ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    and twU: "tyw ar ?\<theta> A U" and fU: "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> U)))"
    and tys: "(ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> U)" and nrs: "no_redex s"
    and nls: "no_loose_bound s (length Ts)"
    and eqs: "Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
    unfolding pmc_pre_def by blast+
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  note \<sigma> = solutionD[OF pc0(3)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  obtain T0 base Ts' where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts"
    "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T" "tyw ar ?\<theta> A T0" "tyw ar ?\<theta> A base"
    "has_type ?V ?Bs (tnormt ?\<theta> (head_of u)) (tnorm ?\<theta> T0)"
    "tnorm ?\<theta> base = res_type (tnorm ?\<theta> U)"
    by (rule pmc_types[OF pre])
  have nA: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA])
  then have "\<not> is_Abs (tnormt ?\<theta> u)" by (cases u) auto
  from hlong_nonAbs[OF hl this] have tyu: "has_type ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    and nfU: "\<not> is_funT (tnorm ?\<theta> U)" by auto
  have bU: "tnorm ?\<theta> base = tnorm ?\<theta> U" using ty0(9) arg_res_type_base[OF nfU] by simp
  let ?\<rho>U = "tsubst \<rho> U"
  have iU: "tsubst \<rho> (tnorm ?\<theta> U) = ?\<rho>U" by (rule tsubst_tnorm[OF ac sol tcU[OF twU]])
  have nf\<rho>U: "\<not> is_funT ?\<rho>U" using fU arg_res_type_base[OF nfU] iU by simp
  have ib: "tsubst \<rho> base = ?\<rho>U" by (rule tsubst_tnorm_eq[OF ac sol tcU[OF ty0(7)] tcU[OF twU] bU])
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF tgty] by simp
  have lTs': "length Ts' = length Ts" using arg_cong[OF ty0(4), of length] by simp
  have iTs: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    by (rule map_tsubst_tnorm[OF ac sol _ _ ty0(4)]) (use twTs ty0(5) tcU in blast)+
  \<comment> \<open>The argument types of the head\<close>
  define uargs where "uargs = snd (strip_comb u)"
  have u_eq: "u = list_comb (head_of u) uargs" unfolding uargs_def by (rule head_of_list_comb)
  from res_type_head(2)[OF tyu nfU ty0(8)[folded head_of_tnormt]] obtain As where
    T0: "tnorm ?\<theta> T0 = foldr fun_type As (tnorm ?\<theta> U)"
    and tyas: "list_all2 (has_type ?V ?Bs) (snd (strip_comb (tnormt ?\<theta> u))) As"
    by blast
  from binder_types_ptnorm[OF ac tcU[OF ty0(6)] T0 nfU] obtain Us0 where
    bt: "binder_types env T0 = return Us0" "map (tnorm ?\<theta>) Us0 = As" by blast
  have twUs0: "\<forall>X\<in>set Us0. tyw ar ?\<theta> A X" using binder_types_tyw[OF bt(1)[unfolded return_def] refl pi(2) ty0(6)] .
  \<comment> \<open>The sequence\<close>
  have lTt: "length Ts' = length targs" using lTs lTs' by simp
  from make_projs_exact[OF lTt, of u targs] obtain projs where pr: "make_projs u targs Ts' targs = returnW projs"
    and prs: "\<forall>j<length targs. (Bound (integer_of_nat j), Ts' ! (length targs - Suc j),
      targs ! (length targs - Suc j)) \<in> set projs"
    by blast
  have pT: "T \<in> set Ts'" if "(bv, T, targ) \<in> set (rev projs)" for bv T targ
    using make_projs_ok[of u targs Ts' targs projs] pr that by fastforce
  have pt: "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
    by (rule projs_total[OF cfg(1) pc0(1) ty0(7,5)]) (use pT in blast)
  obtain env0 args0 where ma0: "make_args vname Ts' env Us0 = (env0, args0)"
    by (cases "make_args vname Ts' env Us0")
  define imit where "imit = (case head_of u of
      Const _ _ \<Rightarrow> S_Single (El_C (list_comb (head_of u) args0) env0 dps)
    | Free _ _ \<Rightarrow> S_Single (El_C (list_comb (head_of u) args0) env0 dps)
    | _ \<Rightarrow> S_Empty)"
  have m1: "match1 cfg vname rb targs u env dps = match1_projs cfg vname env dps base Ts' (rev projs) imit"
    using match1_punfold[OF ty0(1-3) bt(1), of cfg vname dps] pr ma0
    by (cases "head_of u") (simp_all add: imit_def)
  from match1_projs_presult[OF pt, where vname = vname and dps = dps and Ts = Ts' and tail = imit] obtain sq where
    mp: "okW (match1_projs cfg vname env dps base Ts' (rev projs) imit) sq"
    and imv: "\<And>x. ev cfg imit x \<Longrightarrow> ev cfg sq x"
    and prj: "\<And>bv T targ Us bary p y. (bv, T, targ) \<in> set (rev projs) \<Longrightarrow> ok (strip_type env T) (Us, bary) \<Longrightarrow>
      p \<in> set (arity_guesses cfg bary) \<Longrightarrow> m1_elem cfg vname env dps base Ts' bv Us bary p y \<Longrightarrow> ev cfg sq y"
    by blast
  \<comment> \<open>The target\<close>
  have nf: "\<not> is_funT (tsubst \<rho> U)" using nf\<rho>U .
  have sA: "\<not> Unif_Occurs.is_Abs s"
  proof
    assume "Unif_Occurs.is_Abs s"
    then obtain s1 where "s = dB.Abs s1" by (cases s) auto
    with tys have "\<exists>X Y. trty (tsubst \<rho> U) = X \<Rightarrow> Y" by auto
    with trty_base[OF nf] show False by auto
  qed
  obtain h ss where h: "is_atom h" "s = h \<degree>\<degree> ss" by (rule no_redex_atom_head[OF nrs sA])
  from tys h(2) obtain Ws where tyh': "(ibctx \<rho> Ts, \<tau>') \<turnstile> h : Ws \<Rrightarrow> trty ?\<rho>U"
    and tyss: "(ibctx \<rho> Ts, \<tau>') \<tturnstile> ss : Ws"
    by (auto elim: list_app_typeE)
  have nrss: "\<forall>w\<in>set ss. no_redex w" using nrs h no_redex_atom_apps by simp
  have nlh: "no_loose_bound h (length Ts)" and nlss: "\<forall>w\<in>set ss. no_loose_bound w (length Ts)"
    using nls h(2) by (simp_all add: no_loose_bound_list_app)
  have lWs: "length Ws = length ss" by (rule typings_length[OF tyss])
  have lsz_s: "lsize (ibctx \<rho> Ts) \<tau>' s (trty ?\<rho>U) =
      Suc (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i)) + (tsize (trty ?\<rho>U) - 1)"
    using lsize_atom_apps[OF h(1) tyh' tyss nrss] h(2) by simp
  \<comment> \<open>The head of the copy: a projection or the imitation\<close>
  have "\<exists>\<rho>' env1 hd0 UC env' args. pcinv alg ar A W \<rho>' \<tau>' \<sigma> env1 dps \<and> tenv env1 = tenv env \<and>
      pextends env1 env \<and> maxidx env \<le> maxidx env1 \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      (\<forall>Z. reach (instE \<rho>' env1) Z = reach (instE \<rho> env) Z) \<and>
      make_args vname Ts' env1 UC = (env', args) \<and> ev cfg sq (El_C (list_comb hd0 args) env' dps) \<and>
      Ws = map trty (map (tsubst \<rho>') UC) \<and> (\<forall>X\<in>set UC. tyw ar (tyenv env1) A X) \<and>
      typed env1 W (rev Ts') hd0 (foldr fun_type UC U) \<and> vps hd0 = {} \<and>
      (\<forall>X\<in>tys hd0. tyw ar (tyenv env1) A X) \<and> swf_cp ar (length Ts') hd0 \<and>
      (\<forall>\<sigma>'. rigid_subst \<sigma>' \<longrightarrow> mk_subst \<sigma>' (tr (inst \<rho>' hd0)) = h)"
  proof (cases "\<exists>j. h = BVar j")
    case True
    then obtain j where hj: "h = BVar j" by blast
    have jn: "j < length Ts" using nlh hj by simp
    define i0 where "i0 = length targs - Suc j"
    have i0: "i0 < length targs" using jn lTs by (simp add: i0_def)
    define T where "T = Ts' ! i0"
    define targ where "targ = targs ! i0"
    have inp: "(Bound (integer_of_nat j), T, targ) \<in> set (rev projs)"
      using prs jn lTs by (simp add: T_def targ_def i0_def)
    have twT: "tyw ar ?\<theta> A T" using ty0(5) i0 lTs lTs' by (simp add: T_def)
    have iT: "tsubst \<rho> T = tsubst \<rho> (Ts ! i0)"
      using arg_cong[OF iTs, of "\<lambda>xs. xs ! i0"] i0 lTs lTs' by (simp add: T_def)
    have bT: "ibctx \<rho> Ts j = trty (tsubst \<rho> T)" using jn lTs iT by (simp add: env_ext_map i0_def)
    from tyh' hj bT have tT: "trty (tsubst \<rho> T) = Ws \<Rrightarrow> trty ?\<rho>U" by auto
    from proj_guess[OF cfg pc kk twT ty0(7) ib nf\<rho>U tT] obtain Us bary p env0' Cs env1 \<rho>' where
      st1: "strip_type env T = return (Us, bary)" and pg: "p \<in> set (arity_guesses cfg bary)"
      and g: "gentvars p env = (env0', Cs)" and pu: "okW (proj_unify cfg base bary Cs env0') env1"
      and pc': "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env1 dps" and te': "tenv env1 = tenv env"
      and pe': "pextends env1 env" and mx: "maxidx env \<le> maxidx env1" and ag': "tagree (maxidx env) \<rho> \<rho>'"
      and rr': "\<And>Z. reach (instE \<rho>' env1) Z = reach (instE \<rho> env) Z"
      and twUC0: "\<forall>X\<in>set (Us @ Cs). tyw ar (tyenv env1) A X"
      and WsUC0: "Ws = map trty (map (tsubst \<rho>') (Us @ Cs))"
      and tT': "tnorm (tyenv env1) T = tnorm (tyenv env1) (foldr fun_type (Us @ Cs) base)"
      by blast
    note pi1 = pinvD[OF pcinvD(1)[OF pc']]
    have ac1: "tacyc (tyenv env1)" by (rule tinv_tacyc[OF pi1(2)])
    have ext1: "textends ?\<theta> (tyenv env1)" using pe' by (simp add: pextends_def)
    obtain env' args where ma: "make_args vname Ts' env1 (Us @ Cs) = (env', args)"
      by (cases "make_args vname Ts' env1 (Us @ Cs)")
    have "m1_elem cfg vname env dps base Ts' (Bound (integer_of_nat j)) Us bary p
        (El_C (list_comb (Bound (integer_of_nat j)) args) env' dps)"
      unfolding m1_elem_def using g pu ma by blast
    from prj[OF inp _ pg this] st1
    have evp: "ev cfg sq (El_C (list_comb (Bound (integer_of_nat j)) args) env' dps)"
      by (simp add: return_def)
    have bU1: "tnorm (tyenv env1) base = tnorm (tyenv env1) U"
      using arg_cong[OF bU, of "tnorm (tyenv env1)"] by (simp add: tnorm_textends[OF ac1 ext1])
    have tUC: "tnorm (tyenv env1) T = tnorm (tyenv env1) (foldr fun_type (Us @ Cs) U)"
      using tT' bU1 by (simp add: tnorm_foldr_fun)
    have jn': "j < length Ts'" using jn lTs' by simp
    have "rev Ts' ! j = T" using jn' lTs' lTs by (simp add: rev_nth T_def i0_def)
    then have "rev (map (tnorm (tyenv env1)) Ts') ! j = tnorm (tyenv env1) T"
      using jn' by (simp add: rev_map)
    then have tyBj: "typed env1 W (rev Ts') (Bound (integer_of_nat j)) (foldr fun_type (Us @ Cs) U)"
      using tUC jn' by (simp add: typed_def has_type_Bound_iff rev_map integer_reps)
    have wBj: "swf_cp ar (length Ts') (Bound (integer_of_nat j))" using jn' by (simp add: swf_cp_def integer_reps)
    have htrj: "\<forall>\<sigma>'. rigid_subst \<sigma>' \<longrightarrow> mk_subst \<sigma>' (tr (inst \<rho>' (Bound (integer_of_nat j)))) = h"
      using hj by (simp add: integer_reps)
    have vBj: "vps (Bound (integer_of_nat j)) = {}" "\<forall>X\<in>tys (Bound (integer_of_nat j)). tyw ar (tyenv env1) A X"
      by simp_all
    show ?thesis
      by (rule exI[of _ \<rho>'], rule exI[of _ env1], rule exI[of _ "Bound (integer_of_nat j)"],
          rule exI[of _ "Us @ Cs"], rule exI[of _ env'], rule exI[of _ args])
        (use pc' te' pe' mx ag' rr' ma evp WsUC0 twUC0 tyBj wBj htrj vBj in blast)
  next
    case False
    with h(1) obtain c where hc: "h = dB.Var c" by (auto simp: is_atom_def)
    let ?H = "inst \<rho> (head_of u)"
    have hd: "(\<exists>a T. head_of u = Const a T) \<or> (\<exists>a T. head_of u = Free a T) \<or> (\<exists>i. head_of u = Bound i)"
      using hA hV head_of_not_App[of u] by (cases "head_of u") auto
    have trh: "mk_subst \<sigma> (tr ?H) = tr ?H" and ath: "is_atom (tr ?H)"
      using hd rigid_substD[OF \<sigma>(3)] by auto
    have equ: "mk_subst \<sigma> (tr (inst \<rho> u)) = tr ?H \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) uargs"
      using arg_cong[OF u_eq, of "\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))"] trh
      by (simp add: inst_list_comb tr_list_comb comp_def)
    let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs"
    have e2: "Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
      using Abs_m_apps_closed_head[of h ?st "length Ts" ss] hc h(2) lTs by simp
    have "h \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        tr ?H \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) uargs"
      using equiv_trans[OF equiv_sym[OF e2] eqs] equ by simp
    from atom_apps_equiv[OF h(1) ath this] have hh: "h = tr ?H" by auto
    from hd hh hc obtain a Tc where hu': "head_of u = Const a Tc \<or> head_of u = Free a Tc" by auto
    have tTc: "tnorm ?\<theta> Tc = tnorm ?\<theta> T0"
      using ty0(8) hu' by (auto elim: has_type.cases)
    have cTc: "const_typ_ok a (tnorm ?\<theta> Tc)" if "head_of u = Const a Tc"
      using ty0(8) that by (auto elim: has_type.cases)
    have twTc: "tyw ar ?\<theta> A Tc" using twu tys_head_of[of u] hu' by auto
    have iTc: "tsubst \<rho> Tc = foldr fun_type (map (tsubst \<rho>) As) ?\<rho>U"
    proof -
      have "tsubst \<rho> Tc = tsubst \<rho> (tnorm ?\<theta> Tc)" by (rule tsubst_tnorm[OF ac sol tcU[OF twTc], symmetric])
      also have "\<dots> = foldr fun_type (map (tsubst \<rho>) As) (tsubst \<rho> (tnorm ?\<theta> U))"
        using tTc T0 by (simp add: tsubst_foldr_fun)
      finally show ?thesis using iU by simp
    qed
    have tyhc: "(ibctx \<rho> Ts, \<tau>') \<turnstile> tr ?H : trty (tsubst \<rho> Tc)"
      by (rule solution_rigid_type[OF pc0(3)]) (use hu' in auto)
    from tyhc[folded hh] tyh' hc have "Ws \<Rrightarrow> trty ?\<rho>U = map trty (map (tsubst \<rho>) As) \<Rrightarrow> trty ?\<rho>U"
      by (auto simp: iTc trty_foldr)
    with arrows_base_inj[OF _ nf\<rho>U nf\<rho>U] have Ws: "Ws = map trty (map (tsubst \<rho>) As)" by blast
    have iUs0: "map (tsubst \<rho>) Us0 = map (tsubst \<rho>) As"
    proof -
      have "map (tsubst \<rho>) Us0 = map (tsubst \<rho>) (map (tnorm ?\<theta>) Us0)"
        using tsubst_tnorm[OF ac sol] twUs0 tcU by simp
      then show ?thesis using bt(2) by simp
    qed
    have "ev cfg imit (El_C (list_comb (head_of u) args0) env0 dps)"
      using hu' by (auto simp: imit_def intro: ev.single)
    then have evi: "ev cfg sq (El_C (list_comb (head_of u) args0) env0 dps)" by (rule imv)
    have tyhd: "typed env W (rev Ts') (head_of u) (foldr fun_type Us0 U)"
    proof -
      have "tnorm ?\<theta> (foldr fun_type Us0 U) = tnorm ?\<theta> Tc"
        using tTc T0 bt(2) by (simp add: tnorm_foldr_fun)
      then show ?thesis using hu' cTc by (auto simp: typed_def intro: has_type.Const has_type.Free)
    qed
    have "swf_tm ar rb (head_of u)" using wu u_eq by (metis swf_tm_list_comb)
    then have whd: "swf_cp ar (length Ts') (head_of u)" using hu' by (auto simp: swf_tm_def swf_cp_def)
    have htr: "mk_subst \<sigma>' (tr (inst \<rho> (head_of u))) = h" if "rigid_subst \<sigma>'" for \<sigma>'
      using hu' rigid_substD[OF that] hh by auto
    have vhd: "vps (head_of u) = {}" "\<forall>X\<in>tys (head_of u). tyw ar ?\<theta> A X" using hu' twTc by auto
    have Ws': "Ws = map trty (map (tsubst \<rho>) Us0)" using Ws iUs0 by simp
    have ag0: "tagree (maxidx env) \<rho> \<rho>" by (simp add: tagree_def)
    show ?thesis
      by (rule exI[of _ \<rho>], rule exI[of _ env], rule exI[of _ "head_of u"],
          rule exI[of _ Us0], rule exI[of _ env0], rule exI[of _ args0])
        (use pc ma0 evi Ws' twUs0 tyhd whd htr vhd ag0 in auto)
  qed
  then obtain \<rho>' env1 hd0 UC env' args where pc1: "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env1 dps"
    and te1: "tenv env1 = tenv env" and pe1: "pextends env1 env" and mx1: "maxidx env \<le> maxidx env1"
    and ag1: "tagree (maxidx env) \<rho> \<rho>'" and rr1: "\<And>Z. reach (instE \<rho>' env1) Z = reach (instE \<rho> env) Z"
    and ma: "make_args vname Ts' env1 UC = (env', args)" and evx: "ev cfg sq (El_C (list_comb hd0 args) env' dps)"
    and Ws: "Ws = map trty (map (tsubst \<rho>') UC)" and twUC: "\<forall>X\<in>set UC. tyw ar (tyenv env1) A X"
    and tyhd: "typed env1 W (rev Ts') hd0 (foldr fun_type UC U)" and vhd: "vps hd0 = {}"
    and twhd: "\<forall>X\<in>tys hd0. tyw ar (tyenv env1) A X" and whd: "swf_cp ar (length Ts') hd0"
    and htr: "\<And>\<sigma>'. rigid_subst \<sigma>' \<Longrightarrow> mk_subst \<sigma>' (tr (inst \<rho>' hd0)) = h"
    by blast
  note pi1 = pinvD[OF pcinvD(1)[OF pc1]]
  have ac1: "tacyc (tyenv env1)" by (rule tinv_tacyc[OF pi1(2)])
  have ext1: "textends ?\<theta> (tyenv env1)" using pe1 by (simp add: pextends_def)
  have iTs1: "map (tsubst \<rho>') Ts' = map (tsubst \<rho>) Ts"
    using iTs tyw_tagree[OF pi(2) _ ag1] ty0(5) by (metis (no_types, lifting) map_eq_conv)
  have tw1: "\<forall>X\<in>set Ts' \<union> set UC. tyw ar (tyenv env1) A X"
    using ty0(5) twUC tyw_textends[OF ac1 ext1] by blast
  have tyss1: "(ibctx \<rho>' Ts', \<tau>') \<tturnstile> ss : map trty (map (tsubst \<rho>') UC)"
    using tyss Ws iTs1 by simp
  have nlss1: "\<forall>w\<in>set ss. no_loose_bound w (length Ts')" using nlss lTs' by simp
  define D where "D = pmc_dom \<rho> u targs dps"
  have dD: "ivps \<rho>' dps \<subseteq> D" using ivps_tagree[OF pc ag1] by (auto simp: D_def)
  obtain W1 \<sigma>1 NV where c: "psext alg ar A W \<tau>' \<sigma> \<rho>' env1 W1 \<sigma>1 \<rho>' env' dps D NV"
    "typed env' W1 (rev Ts') (list_comb hd0 args) U" "swf_cp ar (length Ts') (list_comb hd0 args)"
    "\<forall>X\<in>tys (list_comb hd0 args). tyw ar (tyenv env') A X" "below (maxidx env') (list_comb hd0 args)"
    "vps (inst \<rho>' (list_comb hd0 args)) = NV"
    "mk_subst \<sigma>1 (tr (inst \<rho>' (list_comb hd0 args))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> ss"
    "sum (vsz \<tau>' \<sigma>1) NV = (\<Sum>i<length ss. lsize (ibctx \<rho>' Ts') \<tau>' (ss ! i) (trty (tsubst \<rho>' (UC ! i))))"
    by (rule pmake_args_copy[OF pc1 ma tw1 tyss1 nrss nlss1 tyhd vhd twhd whd htr dD])
  have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho>' env' dps D NV"
    by (rule psext_text[OF c(1) pe1 mx1 ag1 rr1])
  note sd = psextD[OF sx]
  note pi' = pinvD[OF pcinvD(1)[OF sd(1)]]
  have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pi'(2)])
  have ext': "textends ?\<theta> (tyenv env')" using sd(6) by (simp add: pextends_def)
  define u' where "u' = list_comb hd0 args"
  have cr: "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D Ts U s 1 u' env' dps W1 \<sigma>1 \<rho>' NV"
    unfolding pcopy_res_def
  proof (intro conjI sx)
    have "map (tnorm (tyenv env')) (rev Ts) = map (tnorm (tyenv env')) (rev Ts')"
      using arg_cong[OF ty0(4), of "\<lambda>xs. rev (map (tnorm (tyenv env')) xs)"]
      by (simp add: rev_map comp_def tnorm_textends[OF ac' ext'])
    with c(2) show "typed env' W1 (rev Ts) u' U" unfolding u'_def by (rule typed_tnorm_cong) simp
    show "swf_cp ar (length Ts) u'" using c(3) lTs' by (simp add: u'_def)
    show "\<forall>X\<in>tys u'. tyw ar (tyenv env') A X" using c(4) by (simp add: u'_def)
    show "below (maxidx env') u'" using c(5) by (simp add: u'_def)
    show "vps (inst \<rho>' u') \<subseteq> NV" using c(6) by (simp add: u'_def)
    show "mk_subst \<sigma>1 (tr (inst \<rho>' u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" using c(7) h(2) by (simp add: u'_def)
    have "(\<Sum>i<length ss. lsize (ibctx \<rho>' Ts') \<tau>' (ss ! i) (trty (tsubst \<rho>' (UC ! i)))) =
        (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i))"
      using lWs Ws iTs1 by simp
    then show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) + 1 \<le> lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U))"
      using c(8) lsz_s by simp
  qed
  moreover have "okW (match1 cfg vname rb targs u env dps) sq" using mp m1 by simp
  moreover have "reach (instE \<rho>' env') X = reach (instE \<rho> env) X" for X
  proof -
    have "reach (instE \<rho>' env') X = reach (instE \<rho>' env1) X"
      by (rule reach_lookup_eq) (simp add: make_args_props(1)[OF ma])
    also have "\<dots> = reach (instE \<rho> env) X" by (rule rr1)
    finally show ?thesis .
  qed
  ultimately show ?thesis using evx unfolding D_def u'_def by blast
qed

end


subsection \<open>Totality of the steps of \<open>MATCH\<close>\<close>

text \<open>The occurs check terminates on typed terms, with the result of the instance.\<close>

context csig
begin

lemma occurs_terms_pinst:
  assumes inv: "penv_inv alg ar W env" and g: "gsol alg ar (tyenv env) \<rho>"
    and ty: "\<And>t. t \<in> set ts \<Longrightarrow> \<exists>Bs T. typed env W Bs t T"
    and tc: "\<And>t. t \<in> set ts \<Longrightarrow> \<forall>U\<in>tys t. tcons (tyenv env) U"
    and bl: "\<And>t. t \<in> set ts \<Longrightarrow> below (maxidx env) t"
  shows "\<exists>b. occurs_terms env v ts = return b \<and> ok (occurs_terms (instE \<rho> env) v (map (inst \<rho>) ts)) b"
proof -
  let ?\<theta> = "tyenv env"
  note pe = penv_invD[OF inv]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pe(1)] tinv_tcons_env[OF pe(1)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using g by (simp add: gsol_def)
  note ei = env_invD[OF penv_inv_inst[OF inv g]]
  have e: "vt_is_empty (tyenv (instE \<rho> env))" by (rule wf_envD(1)[OF ei(2)])
  have vty: "\<forall>t\<in>set (map (inst \<rho>) ts). vtyped (\<lambda>x. tsubst \<rho> (tctx env W x)) t"
  proof
    fix t' assume "t' \<in> set (map (inst \<rho>) ts)"
    then obtain t where t: "t \<in> set ts" "t' = inst \<rho> t" by auto
    from ty[OF t(1)] obtain Bs T where tyt: "typed env W Bs t T" by blast
    have "tsubst \<rho> (tctx env W x) = tsubst \<rho> U" if "(x, U) \<in> vps t" for x U
    proof -
      have "tnorm ?\<theta> U = tctx env W x" by (rule typed_vps[OF tyt that])
      moreover have "tcons ?\<theta> U" using bspec[OF tc[OF t(1)] vps_tys[OF that, simplified]] .
      ultimately show ?thesis using tsubst_tnorm[OF ac sol] by metis
    qed
    then show "vtyped (\<lambda>x. tsubst \<rho> (tctx env W x)) t'" using t(2) by (auto simp: vtyped_def vps_inst)
  qed
  from occurs_terms_term[OF e ei(3) vty] obtain b where
    oc: "occurs_terms (instE \<rho> env) v (map (inst \<rho>) ts) = return b" by blast
  have tyok: "tyok env" by (rule tyok_tinv[OF pe(1)])
  have lkd: "\<forall>t\<in>set ts. lkdec \<rho> env (vps t \<union> bvps env)"
  proof
    fix t assume t: "t \<in> set ts"
    from ty[OF t] obtain Bs T where tyt: "typed env W Bs t T" by blast
    show "lkdec \<rho> env (vps t \<union> bvps env)"
      by (rule hyp_lkdec[OF typed_hyp[OF inv sol tyt _ bl[OF t]]]) (use tc[OF t] in blast)
  qed
  from oc obtain s' where o1: "occurs_list (instE \<rho> env) v [] (map (inst \<rho>) ts) = Some (Ok (b, s'))"
    by (cases "occurs_list (instE \<rho> env) v [] (map (inst \<rho>) ts)")
      (auto simp: occurs_terms_def bindM_def return_def split: res.splits)
  from occurs_list_pinst[OF o1 tyok lkd] obtain r where r: "occurs_list env v [] ts = Some r"
    "Ok (b, s') = instr \<rho> id r" by blast
  then have "r = Ok (b, s')" by (cases r) auto
  then show ?thesis using r(1) oc by (simp add: occurs_terms_def return_def bindM_def)
qed

lemma typed_list_comb_args:
  assumes "tacyc (tyenv env)" "typed env W Bs (list_comb h ts) B"
  obtains As where "typed env W Bs h (foldr fun_type As B)" "list_all2 (typed env W Bs) ts As"
    "map (tnorm (tyenv env)) As = As"
proof -
  let ?\<theta> = "tyenv env"
  from assms(2) obtain As where h: "has_type (tctx env W) (map (tnorm ?\<theta>) Bs) (tnormt ?\<theta> h)
      (foldr fun_type As (tnorm ?\<theta> B))"
    and a: "list_all2 (has_type (tctx env W) (map (tnorm ?\<theta>) Bs)) (map (tnormt ?\<theta>) ts) As"
    by (auto simp: typed_def has_type_list_comb)
  have nA: "tnorm ?\<theta> X = X" if "X \<in> set As" for X
  proof -
    from that obtain i where i: "i < length As" "X = As ! i" by (auto simp: in_set_conv_nth)
    have "has_type (tctx env W) (map (tnorm ?\<theta>) Bs) (tnormt ?\<theta> (ts ! i)) X"
      using a i list_all2_lengthD[OF a] by (auto simp: list_all2_conv_all_nth)
    from typed_type_normal[OF this assms(1)] show ?thesis .
  qed
  have mA: "map (tnorm ?\<theta>) As = As" using nA by (induction As) auto
  then have "typed env W Bs h (foldr fun_type As B)" using h by (simp add: typed_def tnorm_foldr_fun)
  moreover have "list_all2 (typed env W Bs) ts As"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length ts = length As" using list_all2_lengthD[OF a] by simp
    fix i assume i: "i < length ts"
    have "has_type (tctx env W) (map (tnorm ?\<theta>) Bs) (tnormt ?\<theta> (ts ! i)) (As ! i)"
      using a i by (auto simp: list_all2_conv_all_nth)
    moreover have "tnorm ?\<theta> (As ! i) = As ! i" using nA i list_all2_lengthD[OF a] by simp
    ultimately show "typed env W Bs (ts ! i) (As ! i)" by (simp add: typed_def)
  qed
  ultimately show ?thesis using mA by (rule that)
qed

end

context wf_csig
begin

lemma match1_total:
  assumes cfg: "cfg_alg cfg = alg" and pt: "ptot alg ar A W env rb targs u"
  shows "\<exists>sq. okW (match1 cfg vname rb targs u env dps) sq"
proof -
  let ?\<theta> = "tyenv env"
  obtain T0 base Ts' where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "length Ts' = length targs"
    "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T" "tyw ar (tyenv env) A T0" "tyw ar (tyenv env) A base"
    by (rule ptot_types[OF pt]) blast
  have pi0: "pinv alg ar A W env []" using pt by (simp add: ptot_def)
  note pi = pinvD[OF pi0]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have "tnorm ?\<theta> T0 = foldr fun_type (arg_types (tnorm ?\<theta> T0)) (res_type (tnorm ?\<theta> T0))"
    by (simp add: arg_res_type)
  from binder_types_ptnorm[OF ac tyw_tcons[OF pi(2) ty0(6)] this res_type_base] obtain Us0 where
    bt: "binder_types env T0 = return Us0" by blast
  from make_projs_exact[OF ty0(4), of u targs] obtain projs where
    pr: "make_projs u targs Ts' targs = returnW projs" by blast
  have pT: "T \<in> set Ts'" if "(bv, T, targ) \<in> set (rev projs)" for bv T targ
    using make_projs_ok[of u targs Ts' targs projs] pr that by fastforce
  have ptp: "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
    by (rule projs_total[OF cfg pi0 ty0(7,5)]) (use pT in blast)
  obtain env0 args0 where ma0: "make_args vname Ts' env Us0 = (env0, args0)"
    by (cases "make_args vname Ts' env Us0")
  define imit where "imit = (case head_of u of
      Const _ _ \<Rightarrow> S_Single (El_C (list_comb (head_of u) args0) env0 dps)
    | Free _ _ \<Rightarrow> S_Single (El_C (list_comb (head_of u) args0) env0 dps)
    | _ \<Rightarrow> S_Empty)"
  have m1: "match1 cfg vname rb targs u env dps = match1_projs cfg vname env dps base Ts' (rev projs) imit"
    using match1_punfold[OF ty0(1-3) bt, of cfg vname dps] pr ma0
    by (cases "head_of u") (simp_all add: imit_def)
  from match1_projs_presult[OF ptp, where vname = vname and dps = dps and Ts = Ts' and tail = imit]
  obtain sq where "okW (match1_projs cfg vname env dps base Ts' (rev projs) imit) sq" by blast
  then show ?thesis using m1 by auto
qed

text \<open>\<^const>\<open>match_pair\<close> terminates without an exception on a typed flexible pair.\<close>

lemma match_pair_total:
  assumes cfg: "cfg_alg cfg = alg" and pi0: "pinv alg ar A W env (dp # dps)"
    and dp: "dp = (rb, t, u)" and sc: "strip_comb t = (Var v T, targs)"
  shows "\<exists>s. okW (match_pair cfg env dp dps) s"
proof -
  let ?\<theta> = "tyenv env"
  note pi = pinvD[OF pi0]
  note pe = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  from pi(4)[of dp] dp obtain B where wd: "swf_dp ar (rb, t, u)"
    and twd: "\<forall>X\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A X"
    and tyt: "typed env W (map snd rb) t B" and tyu: "typed env W (map snd rb) u B"
    and bt: "below (maxidx env) t" and bu: "below (maxidx env) u"
    by auto
  have t_eq: "t = list_comb (Var v T) targs" by (rule strip_comb_list_comb[OF sc])
  from typed_list_comb_args[OF ac(1) tyt[unfolded t_eq]] obtain As where
    tyh: "typed env W (map snd rb) (Var v T) (foldr fun_type As B)"
    and tga: "list_all2 (typed env W (map snd rb)) targs As" by blast
  have tT: "T \<in> tys t" using t_eq by (simp add: tys_list_comb)
  have twT: "tyw ar ?\<theta> A T" using twd tT by blast
  have tgw: "\<forall>s\<in>set targs. \<forall>X\<in>tys s. tyw ar ?\<theta> A X" using twd t_eq by (auto simp: tys_list_comb)
  have tgb: "\<forall>s\<in>set targs. below (maxidx env) s" using bt t_eq by (simp add: below_list_comb)
  have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
    by (simp add: arg_res_type)
  from binder_types_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Ts where
    btT: "binder_types env T = return Ts" by blast
  \<comment> \<open>The occurs check\<close>
  obtain \<rho> where g: "gsol alg ar ?\<theta> \<rho>" using gsol_exists[OF pi(2) pe(2)] .
  let ?ts = "u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)"
  have tys: "\<exists>Bs X. typed env W Bs s X" and tcs: "\<forall>X\<in>tys s. tcons ?\<theta> X" and bls: "below (maxidx env) s"
    if "s \<in> set ?ts" for s
  proof -
    have "(\<exists>Bs X. typed env W Bs s X) \<and> (\<forall>X\<in>tys s. tyw ar ?\<theta> A X) \<and> below (maxidx env) s"
    proof (cases "s \<in> set (u # targs)")
      case True
      have "\<exists>X. typed env W (map snd rb) s X" if "s \<in> set targs"
        using that tga by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth)
      with True tyu twd tgw tgb bu show ?thesis by auto
    next
      case False
      with that obtain rb' t' u' where d: "(rb', t', u') \<in> set dps" "s = t' \<or> s = u'" by auto
      from pi(4)[of "(rb', t', u')"] d(1) obtain B' where "typed env W (map snd rb') t' B'"
        "typed env W (map snd rb') u' B'" "\<forall>X\<in>tys t' \<union> tys u'. tyw ar ?\<theta> A X"
        "below (maxidx env) t'" "below (maxidx env) u'" by auto
      with d(2) show ?thesis by blast
    qed
    then show "\<exists>Bs X. typed env W Bs s X" "\<forall>X\<in>tys s. tcons ?\<theta> X" "below (maxidx env) s"
      using tcU by blast+
  qed
  from occurs_terms_pinst[OF pi(1) g tys tcs bls] obtain occ where
    oc: "occurs_terms env v ?ts = return occ" by blast
  \<comment> \<open>The copy\<close>
  have pi00: "pinv alg ar A W env []" using pi0 by (simp add: pinv_def)
  have pt: "ptot alg ar A W env rb targs u"
    unfolding ptot_def using pi00 twd tgw tga tyu by blast
  have "\<exists>s. okW (if occ then match1 cfg (fst v) rb targs u env (dp # dps)
      else mc cfg (fst v) rb targs u env dps) s"
    using match1_total[OF cfg pt] mc_total[OF cfg pt] by (cases occ) simp_all
  then obtain s where "okW (if occ then match1 cfg (fst v) rb targs u env (dp # dps)
      else mc cfg (fst v) rb targs u env dps) s" by blast
  then show ?thesis using btT oc sc by (auto simp: match_pair_def dp liftM_return)
qed

end


text \<open>The \<open>\<eta>\<close>-expansion of a flexible pair saturates it.\<close>

context csig
begin

lemma arg_res_types_foldr:
  "arg_types (foldr fun_type As B) = As @ arg_types B" "res_type (foldr fun_type As B) = res_type B"
  by (induction As) auto

lemma foldr_fun_type_split:
  assumes "foldr fun_type As B = foldr fun_type Xs R" "\<not> is_funT R"
  shows "Xs = As @ arg_types B" "R = res_type B"
  using arg_cong[OF assms(1), of arg_types] arg_cong[OF assms(1), of res_type]
    arg_res_type_fun[OF assms(2), of Xs]
  by (simp_all add: arg_res_types_foldr)

lemma typed_eta_expand:
  assumes "typed env W Bs t (foldr fun_type Es R)"
  shows "typed env W (rev Es @ Bs)
    (list_comb (incr_boundvars (integer_of_nat (length Es)) t) (eta_bvs (length Es))) R"
proof (rule typed_list_comb)
  let ?\<theta> = "tyenv env" and ?n = "length Es"
  show "typed env W (rev Es @ Bs) (incr_boundvars (integer_of_nat ?n) t) (foldr fun_type Es R)"
  proof (cases "Es = []")
    case True
    then show ?thesis using assms by (simp add: incr_boundvars_def)
  next
    case False
    then have nz: "integer_of_nat ?n \<noteq> 0" by (simp add: integer_of_nat_eq_of_nat)
    have "has_type (tctx env W) (take (nat_of_integer 0) (map (tnorm ?\<theta>) Bs) @ map (tnorm ?\<theta>) (rev Es) @
        drop (nat_of_integer 0) (map (tnorm ?\<theta>) Bs)) (incr_bv (integer_of_nat ?n) 0 (tnormt ?\<theta> t))
        (tnorm ?\<theta> (foldr fun_type Es R))"
      by (rule has_type_incr_bv[OF assms[unfolded typed_def]]) (simp_all add: integer_of_nat_eq_of_nat)
    then show ?thesis using nz by (simp add: typed_def incr_boundvars_def rev_map)
  qed
  show "list_all2 (typed env W (rev Es @ Bs)) (eta_bvs (length Es)) Es"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length (eta_bvs ?n) = length Es" by simp
    fix i assume i: "i < length (eta_bvs ?n)"
    then have i': "i < ?n" by simp
    have e: "eta_bvs ?n ! i = Bound (integer_of_nat (?n - Suc i))" using i' by (simp add: rev_nth)
    have k: "nat_of_integer (integer_of_nat (?n - Suc i)) = ?n - Suc i"
      by (metis nat_of_integer_integer_of_nat)
    have nn: "0 \<le> integer_of_nat (?n - Suc i)" by (simp add: integer_of_nat_eq_of_nat)
    have lt: "?n - Suc i < ?n" using i' by simp
    have "map (tnorm ?\<theta>) (rev Es @ Bs) ! (?n - Suc i) = tnorm ?\<theta> (Es ! i)"
      using i' lt by (simp add: nth_append rev_nth)
    then show "typed env W (rev Es @ Bs) (eta_bvs ?n ! i) (Es ! i)"
      unfolding e typed_def using nn k i' by (simp add: has_type_Bound_iff)
  qed
qed

lemma pexpand:
  assumes pi0: "pinv alg ar A W env ((rb, t, u) # dps)"
    and tyt: "typed env W (map snd rb) t B" and tyu: "typed env W (map snd rb) u B"
    and sc: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts"
    and dp': "eta_expand_dpair (drop (length targs) Ts) (rb, t, u) = (rb', t', u')"
  shows "length targs \<le> length Ts" "pinv alg ar A W env ((rb', t', u') # dps)"
    "typed env W (map snd rb') t' (res_type (tnorm (tyenv env) T))"
    "typed env W (map snd rb') u' (res_type (tnorm (tyenv env) T))"
    "tnorm (tyenv env) (res_type (tnorm (tyenv env) T)) = res_type (tnorm (tyenv env) T)"
    "\<forall>X\<in>set Ts. tyw ar (tyenv env) A X"
proof -
  let ?\<theta> = "tyenv env" and ?R = "res_type (tnorm (tyenv env) T)"
  note pi = pinvD[OF pi0]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  from pi(4)[of "(rb, t, u)"] have wd: "swf_dp ar (rb, t, u)"
    and twd: "\<forall>X\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A X"
    and bt0: "below (maxidx env) t" and bu: "below (maxidx env) u"
    by auto
  have t_eq: "t = list_comb (Var v T) targs" by (rule strip_comb_list_comb[OF sc])
  from typed_list_comb_args[OF ac(1) tyt[unfolded t_eq]] obtain As where
    tyh: "typed env W (map snd rb) (Var v T) (foldr fun_type As B)"
    and tga: "list_all2 (typed env W (map snd rb)) targs As" and nAs: "map (tnorm ?\<theta>) As = As" by blast
  have tT: "T \<in> tys t" using t_eq by (simp add: tys_list_comb)
  have twT: "tyw ar ?\<theta> A T" using twd tT by blast
  have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) ?R" by (simp add: arg_res_type)
  from binder_types_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Ts' where
    bt': "binder_types env T = return Ts'" "map (tnorm ?\<theta>) Ts' = arg_types (tnorm ?\<theta> T)" by blast
  have mTs: "map (tnorm ?\<theta>) Ts = arg_types (tnorm ?\<theta> T)" using bt bt' by (simp add: return_def)
  show twTs: "\<forall>X\<in>set Ts. tyw ar ?\<theta> A X" using binder_types_tyw[OF bt[unfolded return_def] refl pi(2) twT] .
  have "tnorm ?\<theta> T = tnorm ?\<theta> (foldr fun_type As B)" using tyh by (auto simp: typed_def elim: has_type_elims)
  also have "\<dots> = foldr fun_type As (tnorm ?\<theta> B)" using nAs by (simp add: tnorm_foldr_fun)
  finally have "foldr fun_type As (tnorm ?\<theta> B) = foldr fun_type (arg_types (tnorm ?\<theta> T)) ?R"
    using arg_res_type[of "tnorm ?\<theta> T"] by simp
  from foldr_fun_type_split[OF this res_type_base] have aT: "arg_types (tnorm ?\<theta> T) = As @ arg_types (tnorm ?\<theta> B)"
    and rT: "?R = res_type (tnorm ?\<theta> B)" by simp_all
  have lA: "length As = length targs" using list_all2_lengthD[OF tga] by simp
  show lT: "length targs \<le> length Ts" using arg_cong[OF mTs, of length] aT lA by simp
  show nR: "tnorm ?\<theta> ?R = ?R" by (rule tnorm_res_type[OF tnorm_idem[OF ac(1)]])
  define Es where "Es = drop (length targs) Ts"
  have mEs: "map (tnorm ?\<theta>) Es = arg_types (tnorm ?\<theta> B)"
    using arg_cong[OF mTs, of "drop (length targs)"] aT lA by (simp add: Es_def drop_map)
  have tB: "tnorm ?\<theta> (foldr fun_type Es ?R) = tnorm ?\<theta> B"
    using mEs nR rT arg_res_type[of "tnorm ?\<theta> B"] by (simp add: tnorm_foldr_fun)
  have tyt': "typed env W (map snd rb) t (foldr fun_type Es ?R)" by (rule typed_tnorm_cong[OF tyt refl tB])
  have tyu': "typed env W (map snd rb) u (foldr fun_type Es ?R)" by (rule typed_tnorm_cong[OF tyu refl tB])
  have e: "rb' = eta_binder Es @ rb"
    "t' = list_comb (incr_boundvars (integer_of_nat (length Es)) t) (eta_bvs (length Es))"
    "u' = list_comb (incr_boundvars (integer_of_nat (length Es)) u) (eta_bvs (length Es))"
    using dp' by (simp_all add: eta_expand_dpair_simp Es_def)
  have mrb: "map snd rb' = rev Es @ map snd rb" using e(1) by (simp add: rev_map comp_def)
  show tyt'': "typed env W (map snd rb') t' ?R" unfolding mrb e(2) by (rule typed_eta_expand[OF tyt'])
  show tyu'': "typed env W (map snd rb') u' ?R" unfolding mrb e(3) by (rule typed_eta_expand[OF tyu'])
  have twEs: "\<forall>X\<in>set Es. tyw ar ?\<theta> A X" using twTs by (auto simp: Es_def dest: in_set_dropD)
  have "swf_dp ar (rb', t', u')"
    using swf_dp_eta_expand[OF wd, of Es] twEs dp' by (auto simp: Es_def tyw_def)
  moreover have "\<forall>X\<in>dtys (rb', t', u'). tyw ar ?\<theta> A X"
    using twd twEs e by (auto simp: tys_list_comb)
  moreover have "ptyped env W (rb', t', u')" using tyt'' tyu'' by auto
  moreover have "dp_below (maxidx env) (rb', t', u')"
  proof -
    have bi: "below (maxidx env) (incr_boundvars i s)" if "below (maxidx env) s" for s i
      using that by (simp add: below_def)
    have "\<forall>s\<in>set (eta_bvs (length Es)). below (maxidx env) s" by (simp add: below_def)
    then show ?thesis using bi[OF bt0] bi[OF bu] e by (simp add: below_list_comb)
  qed
  ultimately show "pinv alg ar A W env ((rb', t', u') # dps)" using pi0 by (simp add: pinv_def)
qed

end

context wf_csig
begin

lemma cunify_types_cases_ext:
  assumes "tinv ar (maxidx env) (tyenv env) A'" "tsorted alg (tyenv env)"
    "tyw ar (tyenv env) A' T" "tyw ar (tyenv env) A' U"
  shows "(\<exists>env'. cunify_types alg T U env = returnW env' \<and> tenv env' = tenv env \<and>
      textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and>
      tinv ar (maxidx env') (tyenv env') A' \<and> tsorted alg (tyenv env')) \<or>
    (\<exists>evs. cunify_types alg T U env = Some (evs, UErr CANTUNIFY))"
proof -
  from unify_types_poly[OF assms] consider (ok) env' where "ok (unify_types alg T U env) env'"
      "tenv env' = tenv env" "tstep alg ar A' (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) (tyenv env) (maxidx env)
        (tyenv env') (maxidx env')" "tsorted alg (tyenv env')"
    | (err) u where "unify_types alg T U env = Some (Err (Unif u))"
    by blast
  then show ?thesis
  proof cases
    case ok
    then show ?thesis using cunify_types_unify(1)[of alg T U env env'] tstepD(1-3)[OF ok(3)]
      by (intro disjI1 exI[of _ env']) simp
  next
    case err
    then show ?thesis using cunify_types_unify(2) by blast
  qed
qed

lemma match_sat_total:
  assumes cfg: "cfg_alg cfg = alg" and pi0: "pinv alg ar A W env (dp # dps)" and fr: "pfr_shape env W dp"
  shows "\<exists>s. okW (match_sat cfg env dp dps) s"
proof -
  let ?\<theta> = "tyenv env"
  note pi = pinvD[OF pi0]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp obtain B where tyt: "typed env W (map snd rb) t B" and tyu: "typed env W (map snd rb) u B"
    and nAu: "\<not> is_Abs u" and hvt: "is_Var (head_of t)" and hru: "is_rigid (head_of u)"
    by (auto simp: pfr_shape_def)
  from hvt obtain v T where ht: "head_of t = Var v T" by (cases "head_of t") auto
  define targs where "targs = snd (strip_comb t)"
  have sc: "strip_comb t = (Var v T, targs)"
    using fst_strip_comb[of t] ht by (simp add: targs_def prod_eq_iff)
  have hnu: "hnf u" using hru nAu by (auto simp: hnf_nonAbs is_rigid_def)
  from pi(4)[of dp] dp have twd: "\<forall>X\<in>tys t. tyw ar ?\<theta> A X" by auto
  have t_eq: "t = list_comb (Var v T) targs" by (rule strip_comb_list_comb[OF sc])
  have twT: "tyw ar ?\<theta> A T" using twd t_eq by (simp add: tys_list_comb)
  have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
    by (simp add: arg_res_type)
  from binder_types_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Ts where
    bt: "binder_types env T = return Ts" by blast
  obtain rb' t' u' where dp': "eta_expand_dpair (drop (length targs) Ts) (rb, t, u) = (rb', t', u')"
    by (cases "eta_expand_dpair (drop (length targs) Ts) (rb, t, u)")
  note ex = pexpand[OF pi0[unfolded dp] tyt tyu sc bt dp']
  note sh = eta_expand_dpair_shape[OF sc hnu nAu dp']
  from match_pair_total[OF cfg ex(2) refl sh(1)] obtain s where
    "okW (match_pair cfg env (rb', t', u') dps) s" by blast
  then show ?thesis using sc bt dp' by (auto simp: match_sat_def dp liftM_return)
qed

lemma match_eta_total:
  assumes cfg: "cfg_alg cfg = alg" and pi0: "pinv alg ar A W env (dp # dps)" and fr: "pfr_shape env W dp"
    and twB: "tyw ar (tyenv env) A B"
  shows "\<exists>s. okW (match_eta cfg env dp dps B j tail) s \<and> (\<forall>y. ev cfg tail y \<longrightarrow> ev cfg s y)"
proof (cases "j = 0")
  case True
  from match_sat_total[OF cfg pi0 fr] obtain s where "okW (match_sat cfg env dp dps) s" by blast
  then show ?thesis using True by (auto simp: match_eta_def intro: ev.append_r)
next
  case False
  note pi = pinvD[OF pi0]
  note pe = penv_invD[OF pi(1)]
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by (cases "gentvars (Suc j) env")
  note gs = gentvars_simps[OF g] and gm = gentvars_cases(1)[OF g]
  let ?A' = "A \<union> ctvars Rs"
  have ti1: "tinv ar (maxidx env1) (tyenv env1) ?A'" using tinv_gentvars[OF pi(2) g] gs(2) by simp
  have srt1: "tsorted alg (tyenv env1)" using pe(2) gs(2) by simp
  have twR: "\<forall>C\<in>set Rs. tyw ar (tyenv env1) ?A' C" using tyw_gentvars[OF pi(2) g] gs(2) by simp
  have Rs_ne: "Rs \<noteq> []" using gs(3) by auto
  have twB1: "tyw ar (tyenv env1) ?A' B" using twB gs(2) by (auto intro: tyw_mono)
  have twF: "tyw ar (tyenv env1) ?A' (foldr fun_type (tl Rs) (hd Rs))"
    using twR Rs_ne by (cases Rs) (simp_all add: tyw_foldr_fun)
  let ?m = "cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1"
  have me: "match_eta cfg env dp dps B j tail = handleW (do {
      env2 \<leftarrow> ?m; s \<leftarrow> match_sat cfg env2 dp dps; returnW (S_Append s tail)})
      (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)"
    using False g by (simp add: match_eta_def)
  from cunify_types_cases_ext[OF ti1 srt1 twB1 twF] show ?thesis
  proof (elim disjE exE conjE)
    fix env2 assume cu: "cunify_types alg B (foldr fun_type (tl Rs) (hd Rs)) env1 = returnW env2"
      and te: "tenv env2 = tenv env1" "textends (tyenv env1) (tyenv env2)" "maxidx env1 \<le> maxidx env2"
        "tinv ar (maxidx env2) (tyenv env2) ?A'" "tsorted alg (tyenv env2)"
    have pi1: "pinv alg ar A W env1 (dp # dps)"
      by (rule pinv_text[OF pi0 gs(1) _ gm]) (simp_all add: gs(2) tinv_mono[OF pi(2) gm] pe(2))
    have ti2: "tinv ar (maxidx env2) (tyenv env2) A" by (rule tinv_subset[OF te(4)]) blast
    have pi2: "pinv alg ar A W env2 (dp # dps)" by (rule pinv_text[OF pi1 te(1-3) ti2 te(5)])
    note pi2' = pinvD[OF pi2]
    have fr2: "pfr_shape env2 W dp"
      by (rule pfr_shape_wcons[OF fr tinv_tacyc[OF ti2] _ pi(6) pi2'(6)]) (use te(2) gs(2) in simp)
    from match_sat_total[OF cfg pi2 fr2] obtain s where "okW (match_sat cfg env2 dp dps) s" by blast
    then show ?thesis using me cu cfg by (auto simp: okW_handleW intro: ev.append_r)
  next
    fix evs assume "cunify_types alg B (foldr fun_type (tl Rs) (hd Rs)) env1 = Some (evs, UErr CANTUNIFY)"
    then show ?thesis using me cfg by (auto simp: okW_handleW bindW_def)
  qed
qed

end


subsection \<open>Binding the variable of the pair\<close>

context csig
begin

lemma inst_types_abs: "inst \<rho> (types_abs Ts u) = types_abs (map (tsubst \<rho>) Ts) (inst \<rho> u)"
  by (induction Ts) simp_all

lemma tnormt_types_abs: "tnormt \<theta> (types_abs Ts u) = types_abs (map (tnorm \<theta>) Ts) (tnormt \<theta> u)"
  by (induction Ts) simp_all

lemma tys_types_abs: "tys (types_abs Ts u) = set Ts \<union> tys u"
  by (induction Ts) auto

lemma typed_types_abs:
  "typed env W (rev Ts @ Bs) u U \<Longrightarrow> typed env W Bs (types_abs Ts u) (foldr fun_type Ts U)"
  unfolding typed_def
  using has_type_types_abs[of "tctx env W" "map (tnorm (tyenv env)) Ts" "map (tnorm (tyenv env)) Bs"
      "tnormt (tyenv env) u" "tnorm (tyenv env) U"]
  by (simp add: tnormt_types_abs tnorm_foldr_fun rev_map)

end

context wf_csig
begin

text \<open>
  \<^const>\<open>new_dset\<close> on a copy \<open>u'\<close> of the body \<open>s\<close> of the value of \<open>v\<close>: the measure decreases if
  the new variables are smaller than the value of \<open>v\<close> (the analogue of
  @{thm [source] new_dset_complete}).
\<close>

lemma pnew_dset_complete:
  assumes sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV"
    and pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps0"
    and tyu': "typed env' W' (rev Ts) u' U" and wc: "swf_cp ar (length Ts) u'"
    and twu': "\<forall>X\<in>tys u'. tyw ar (tyenv env') A X" and bu': "below (maxidx env') u'"
    and vu': "vps (inst \<rho>' u') \<subseteq> NV" and eq': "mk_subst \<sigma>' (tr (inst \<rho>' u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
    and vs: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length Ts) s"
    and TU: "tnorm (tyenv env) T = tnorm (tyenv env) (foldr fun_type Ts U)"
    and twT: "tyw ar (tyenv env) A T" and twTs: "\<forall>X\<in>set Ts. tyw ar (tyenv env) A X"
    and Wv: "tctx env W v = tnorm (tyenv env) T"
    and vZ: "(v, tsubst \<rho> T) \<in> unb (instE \<rho> env) Z" and DZ: "D \<subseteq> Z"
    and Zb: "\<forall>y\<in>Z. snd (fst y) \<le> maxidx env" and fZ: "finite Z"
    and ac: "(v, tsubst \<rho> T) \<notin> reach (instE \<rho>' env') (vps (inst \<rho>' u'))"
    and sz: "sum (vsz \<tau>' \<sigma>') NV < vsz \<tau>' \<sigma> (v, tsubst \<rho> T)"
  shows "\<exists>y. okW (new_dset (v, T) Ts u' env' dps') y \<and> (\<exists>env'' dps''. y = El_E env'' dps'' \<and>
    pcinv alg ar A W' \<rho>' \<tau>' \<sigma>' env'' dps'' \<and> pextends env'' env' \<and> maxidx env'' = maxidx env' \<and>
    sum (vsz \<tau>' \<sigma>') (unb (instE \<rho>' env'') (ivps \<rho>' dps'')) < sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) Z))"
proof -
  let ?\<theta> = "tyenv env" and ?\<theta>' = "tyenv env'" and ?a = "types_abs Ts u'"
  note sd = psextD[OF sx]
  note pc0 = pcinvD[OF pc] and pi = pinvD[OF pcinvD(1)[OF pc]]
  note pc' = pcinvD[OF sd(1)] and pi' = pinvD[OF pcinvD(1)[OF sd(1)]]
  note pe' = penv_invD[OF pi'(1)]
  have ac': "tacyc ?\<theta>'" "tcons_env ?\<theta>'" using tinv_tacyc[OF pi'(2)] tinv_tcons_env[OF pi'(2)] by simp_all
  have sol': "tsol ?\<theta>' \<rho>'" using pc'(2) by (simp add: gsol_def)
  have ext: "textends ?\<theta> ?\<theta>'" using sd(6) by (simp add: pextends_def)
  have tcU': "tcons ?\<theta>' X" if "tyw ar ?\<theta>' A X" for X by (rule tyw_tcons[OF pi'(2) that])
  note ci = pcinv_cinv[OF pc]
  note eii = env_invD[OF cinvD(1)[OF ci]]
  note ci' = pcinv_cinv[OF sd(1)]
  note eii' = env_invD[OF cinvD(1)[OF ci']]
  note isol' = cinvD(2)[OF ci']
  note \<sigma>' = solutionD[OF isol']
  have e': "vt_is_empty (tyenv (instE \<rho>' env'))" by (rule wf_envD(1)[OF eii'(2)])
  have fr: "fresh_env (instE \<rho> env)" by (rule eii(4))
  have Zb': "\<forall>y\<in>Z. snd (fst y) \<le> maxidx (instE \<rho> env)" using Zb by simp
  have vm: "snd v \<le> maxidx env" using reach_old[OF fr Zb', of "(v, tsubst \<rho> T)"] vZ by (simp add: unb_def)
  have vm': "snd v \<le> maxidx env'" using vm sd(5) by simp
  have twT': "tyw ar ?\<theta>' A T" by (rule tyw_textends[OF ac'(1) ext twT])
  have iT: "tsubst \<rho>' T = tsubst \<rho> T" by (rule tyw_tagree[OF pi(2) twT sd(4)])
  have Wv': "tctx env' W' v = tnorm ?\<theta>' T"
  proof -
    have "W' v = W v" using sd(2) vm unfolding agreeV_def by blast
    then have "tctx env' W' v = tnorm ?\<theta>' (W v)" using wcons_tctx[OF pi'(6)] by simp
    also have "\<dots> = tnorm ?\<theta>' (tnorm ?\<theta> (W v))" by (simp add: tnorm_textends[OF ac'(1) ext])
    also have "tnorm ?\<theta> (W v) = tnorm ?\<theta> T" using Wv wcons_tctx[OF pi(6)] by simp
    finally show ?thesis by (simp add: tnorm_textends[OF ac'(1) ext])
  qed
  let ?V' = "ityp \<rho>' env' W'"
  have V'v: "?V' v = tsubst \<rho>' T" using Wv' tsubst_tnorm[OF ac' sol' tcU'[OF twT']] by simp
  \<comment> \<open>The abstraction of the copy\<close>
  have twTs': "\<forall>X\<in>set Ts. tyw ar ?\<theta>' A X" using twTs tyw_textends[OF ac'(1) ext] by blast
  have tya: "typed env' W' [] ?a T"
  proof -
    have "typed env' W' [] ?a (foldr fun_type Ts U)" using typed_types_abs[of env' W' Ts "[]" u' U] tyu' by simp
    moreover have "tnorm ?\<theta>' T = tnorm ?\<theta>' (foldr fun_type Ts U)"
      using arg_cong[OF TU, of "tnorm ?\<theta>'"] by (simp add: tnorm_textends[OF ac'(1) ext])
    ultimately show ?thesis by (rule typed_tnorm_cong[OF _ refl])
  qed
  have twa: "\<forall>X\<in>tys ?a. tyw ar ?\<theta>' A X" using twTs' twu' by (auto simp: tys_types_abs)
  have wa: "swf_tm ar [] ?a" by (rule swf_tm_types_abs[OF _ wc]) (use twTs in \<open>auto simp: tyw_def\<close>)
  have tca: "\<forall>X\<in>set [] \<union> tys ?a. tcons ?\<theta>' X" using twa tcU' by auto
  have tyai: "has_type ?V' [] (inst \<rho>' ?a) (tsubst \<rho>' T)"
    using typed_inst[OF ac' sol' tca tcU'[OF twT'] tya] by simp
  have \<sigma>v: "\<sigma>' (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (inst \<rho>' ?a))"
    using agree_Var[OF sd(3) vm] vs equiv_Abs_m[OF equiv_sym[OF eq'], of "length Ts"]
    by (auto simp: inst_types_abs tr_types_abs intro: equiv_trans)
  have vai: "vps (inst \<rho>' ?a) = vps (inst \<rho>' u')" by (simp add: inst_types_abs)
  have bva: "below (maxidx env') ?a" using bu' by simp
  \<comment> \<open>The reachable variables\<close>
  have NVr: "reach (instE \<rho> env) NV = NV" using reach_new[OF fr] sd(8) by simp
  have vZr: "(v, tsubst \<rho> T) \<in> reach (instE \<rho> env) Z" using vZ by (simp add: unb_def)
  have RZ: "reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) Z \<union> NV" if "X \<subseteq> reach (instE \<rho> env) Z \<union> NV" for X
  proof -
    have "X \<union> D \<subseteq> reach (instE \<rho> env) Z \<union> NV"
      using that reach_subset[OF DZ, of "instE \<rho> env"] reach_incl[of D "instE \<rho> env"] by blast
    then have "reach (instE \<rho> env) (X \<union> D) \<subseteq> reach (instE \<rho> env) (reach (instE \<rho> env) Z \<union> NV)"
      by (rule reach_subset)
    also have "\<dots> = reach (instE \<rho> env) Z \<union> NV"
      using reach_mono[of "reach (instE \<rho> env) Z" "instE \<rho> env" Z] reach_incl[of "reach (instE \<rho> env) Z" "instE \<rho> env"]
        NVr by (auto simp: reach_Un)
    finally show ?thesis using sd(9)[of X] by blast
  qed
  have Yr: "ivps \<rho>' dps' \<subseteq> reach (instE \<rho> env) Z \<union> NV"
    using sd(10) reach_subset[OF DZ, of "instE \<rho> env"] by blast
  have fNV: "finite NV" by (rule sd(7))
  have ag0: "agree (maxidx (instE \<rho> env)) \<sigma> \<sigma>'" using sd(3) by simp
  have ext0: "extends (instE \<rho>' env') (instE \<rho> env)"
    by (rule extends_instE_tagree[OF pc _ sd(4)]) (use sd(6) in \<open>simp add: pextends_def\<close>)
  \<comment> \<open>The lookup of \<open>v\<close>\<close>
  have tyok': "tyok env'" by (rule tyok_tinv[OF pi'(2)])
  have hy: "hyp \<rho>' env' {(v, T)}"
    by (rule penv_inv_hyp[OF pi'(1) sol']) (use tcU'[OF twT'] Wv' vm' in simp)
  have lkd: "lkdec \<rho>' env' {(v, T)}" using hyp_lkdec[OF hy] lkdec_mono by blast
  from lookup_typed[OF e' eii'(3) V'v] obtain r' where
    lr': "lookup (instE \<rho>' env') v (tsubst \<rho>' T) = return r'" by blast
  have "instM \<rho>' (map_option (inst \<rho>')) (lookup env' v T) = return r'"
    using lookup_inst[OF tyok' lkd] lr' by simp
  then obtain r0 where lr: "lookup env' v T = return r0"
    by (cases "lookup env' v T") (auto simp: instM_def return_def elim: instr.elims)
  have lk: "ok (lookup env' v T) r0" using lr by (simp add: return_def)
  from ok_lookup_some[OF lk] show ?thesis
  proof (elim disjE exE conjE)
    assume r: "r0 = None"
    have vn: "vt_lookup (tenv env') v = None"
      using lr r by (auto simp: lookup_def return_def bind_def var_clash_def raise_def
          split: option.splits if_splits)
    from update_unbound_ok[OF vn, of T ?a] obtain env'' where
      upd: "update (v, T) ?a env' = Some (Ok env'')" by blast
    have upd': "ok (update (v, T) ?a env') env''" using upd by simp
    have ok: "okW (new_dset (v, T) Ts u' env' dps') (El_E env'' dps')"
      using lr r upd by (simp add: new_dset_def return_def)
    note up = ok_update[OF upd']
    have updi: "ok (update (v, tsubst \<rho>' T) (inst \<rho>' ?a) (instE \<rho>' env')) (instE \<rho>' env'')"
      using update_inst[of v \<rho>' T ?a env'] upd by simp
    have Fm: "snd v \<le> maxidx (instE \<rho>' env')" using vm' by simp
    have tm: "below (maxidx (instE \<rho>' env')) (inst \<rho>' ?a)" using bva by simp
    note su = solution_update[OF isol' eii'(4) eii'(3) updi \<sigma>v V'v tyai Fm tm]
    have acy: "acyc (instE \<rho>' env'')"
    proof -
      note upi = ok_update[OF updi]
      have d: "dep (instE \<rho>' env'') = dep (instE \<rho>' env') \<union>
          (\<lambda>y. (y, (v, tsubst \<rho>' T))) ` vps (inst \<rho>' ?a)"
        by (rule dep_update[OF upi(2,1)])
      have "(v, tsubst \<rho>' T) \<notin> reach (instE \<rho>' env') (vps (inst \<rho>' ?a))" using ac iT vai by simp
      from acyclic_update[OF d this] eii'(1) show ?thesis by (simp add: acyc_def)
    qed
    have lk': "vt_lookup (tenv env'') x = (if x = v then Some (T, ?a) else vt_lookup (tenv env') x)"
      for x using up(2) by simp
    have te': "tyenv env'' = tyenv env'" "maxidx env'' = maxidx env'" using up(3,4) by simp_all
    have wc': "wcons W' env''"
      using pi'(6) Wv' wcons_tctx[OF pi'(6), of v] te'(1) unfolding wcons_def
      by (auto simp: lk' simp del: split_paired_All)
    have tctx': "tctx env'' W' x = tctx env' W' x" for x
      using wcons_tctx[OF wc'] wcons_tctx[OF pi'(6)] te'(1) by simp
    have ityp': "ityp \<rho>' env'' W' = ?V'" using tctx' by simp
    have typed': "typed env'' W' Ts0 s0 S \<longleftrightarrow> typed env' W' Ts0 s0 S" for Ts0 s0 S
      using tctx' te'(1) by (simp add: typed_def)
    have etys': "etys env'' \<subseteq> insert T (tys ?a \<union> etys env')" by (rule etys_update[OF upd])
    have twe': "\<forall>X\<in>etys env''. tyw ar ?\<theta>' A X" using etys' twa twT' pi'(3) by blast
    have etv': "etvars env'' \<subseteq> tvars_env ?\<theta>' \<union> A" using twe' by (fastforce simp: etvars_def tyw_def)
    have pe'': "penv_inv alg ar W' env''"
      unfolding penv_inv_def
    proof (intro conjI)
      show "tinv ar (maxidx env'') (tyenv env'') (etvars env'')" using tinv_subset[OF pi'(2) etv'] te' by simp
      show "tsorted alg (tyenv env'')" using pe'(2) te' by simp
      show "nacyc env''" using acyc_instE[OF su(2)] acy by simp
      show "pwf_env ar env''"
      proof -
        have "pwf_term ar 0 ?a" using wa by (simp add: pwf_term_def swf_tm_def twft_tys)
        moreover have "wft ar T" using twT by (simp add: tyw_def)
        ultimately show ?thesis using pe'(4) by (auto simp: pwf_env_def lk')
      qed
      show "wt_env W' env''" using pi'(1) tya by (auto simp: penv_inv_def wt_env_def lk' typed')
      show "fresh_env env''" using su(3) by simp
    qed
    have "pcinv alg ar A W' \<rho>' \<tau>' \<sigma>' env'' dps'"
    proof -
      have "\<forall>dp\<in>set dps'. swf_dp ar dp \<and> (\<forall>X\<in>dtys dp. tyw ar (tyenv env'') A X) \<and> ptyped env'' W' dp \<and>
          dp_below (maxidx env'') dp"
      proof
        fix dp assume dp: "dp \<in> set dps'"
        obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
        from pi'(4)[OF dp] show "swf_dp ar dp \<and> (\<forall>X\<in>dtys dp. tyw ar (tyenv env'') A X) \<and>
            ptyped env'' W' dp \<and> dp_below (maxidx env'') dp"
          using te' typed' dpe by simp
      qed
      then show ?thesis
        using pe'' pi'(2,5) twe' wc' pc'(2,4) su(1) te' ityp'
        by (auto simp: pcinv_def pinv_def simp del: split_paired_All)
    qed
    moreover have "pextends env'' env'" using ok_update_extends[OF upd'] te' by (simp add: pextends_def)
    moreover have "sum (vsz \<tau>' \<sigma>') (unb (instE \<rho>' env'') (ivps \<rho>' dps')) < sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) Z)"
    proof (rule mu_decrease[OF fr Zb' fZ vZ extends_trans[OF ok_update_extends[OF updi] ext0] _ _ fNV ag0 sz])
      show "lk (instE \<rho>' env'') v (tsubst \<rho> T) \<noteq> None" using ok_update_lookup[OF updi] iT by (auto simp: lk_def)
      have "reach (instE \<rho>' env'') (ivps \<rho>' dps') \<subseteq> reach (instE \<rho>' env') (ivps \<rho>' dps' \<union> vps (inst \<rho>' ?a))"
        using Unify_Simpl_Complete.reach_update[OF updi] by simp
      also have "\<dots> \<subseteq> reach (instE \<rho> env) Z \<union> NV" by (rule RZ) (use Yr vu' vai in blast)
      finally show "reach (instE \<rho>' env'') (ivps \<rho>' dps') \<subseteq> reach (instE \<rho> env) Z \<union> NV" .
    qed
    ultimately show ?thesis using ok te'(2) by blast
  next
    fix s0 U0 assume r: "r0 = Some s0" and vs0: "vt_lookup (tenv env') v = Some (U0, s0)"
    let ?dp = "([], s0, ?a)"
    have ok: "okW (new_dset (v, T) Ts u' env' dps') (El_E env' (?dp # dps'))"
      using lr r by (simp add: new_dset_def return_def)
    have ws0: "swf_tm ar [] s0" using swf_envD(2)[OF penv_inv_swf_env[OF pi'(1)] vs0] by (simp add: swf_tm_def)
    have twe0: "\<forall>X\<in>insert U0 (tys s0). tyw ar ?\<theta>' A X" using etysI[OF vs0] pi'(3) by blast
    have ty0: "typed env' W' [] s0 U0" using wt_envD[OF _ vs0] pi'(1) by (simp add: penv_inv_def)
    have "tnorm ?\<theta>' U0 = tnorm ?\<theta>' (W' v)" using pi'(6) vs0 unfolding wcons_def by blast
    then have tU0: "tnorm ?\<theta>' U0 = tnorm ?\<theta>' T" using Wv' wcons_tctx[OF pi'(6), of v] by simp
    have tya0: "typed env' W' [] ?a U0" by (rule typed_tnorm_cong[OF tya refl tU0])
    have b0: "below (maxidx env') s0" using fresh_envD[OF pe'(6) vs0] by simp
    have iU0: "tsubst \<rho>' U0 = tsubst \<rho> T"
    proof -
      have "tsubst \<rho>' U0 = tsubst \<rho>' (tnorm ?\<theta>' U0)" using tsubst_tnorm[OF ac' sol' tcU'] twe0 by simp
      also have "\<dots> = tsubst \<rho>' T" using tU0 tsubst_tnorm[OF ac' sol' tcU'[OF twT']] by simp
      finally show ?thesis using iT by simp
    qed
    have vsi: "vt_lookup (tenv (instE \<rho>' env')) v = Some (tsubst \<rho> T, inst \<rho>' s0)" using vs0 iU0 by simp
    have ds: "dsolved \<sigma>' (instd \<rho>' ?dp)"
      using equiv_trans[OF equiv_sym[OF satD[OF \<sigma>'(4) vsi]] \<sigma>v] by (simp add: dsolved_def)
    have pcd: "pcinv alg ar A W' \<rho>' \<tau>' \<sigma>' env' (?dp # dps')"
    proof (rule pcinv_Cons[OF sd(1) _ _ _ _ ds])
      show "swf_dp ar ?dp" using ws0 wa by (simp add: swf_dp_def sbinders_def)
      show "\<forall>X\<in>dtys ?dp. tyw ar ?\<theta>' A X" using twe0 twa by auto
      show "ptyped env' W' ?dp" using ty0 tya0 by auto
      show "dp_below (maxidx env') ?dp" using b0 bva by simp
    qed
    have "sum (vsz \<tau>' \<sigma>') (unb (instE \<rho>' env') (ivps \<rho>' (?dp # dps'))) < sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) Z)"
    proof (rule mu_decrease[OF fr Zb' fZ vZ ext0 _ _ fNV ag0 sz])
      have lki: "lk (instE \<rho>' env') v (tsubst \<rho> T) = Some (inst \<rho>' s0)"
        using vs0 iU0 by (simp add: lk_def)
      show "lk (instE \<rho>' env') v (tsubst \<rho> T) \<noteq> None" using lki by simp
      have "vps (inst \<rho>' s0) \<subseteq> reach (instE \<rho>' env') {(v, tsubst \<rho> T)}"
        using reach_lk[OF lki] reach_incl[of "vps (inst \<rho>' s0)" "instE \<rho>' env'"] by blast
      moreover have "reach (instE \<rho>' env') {(v, tsubst \<rho> T)} \<subseteq> reach (instE \<rho> env) Z \<union> NV" using RZ vZr by blast
      ultimately have "ivps \<rho>' (?dp # dps') \<subseteq> reach (instE \<rho> env) Z \<union> NV" using Yr vu' vai by auto
      then show "reach (instE \<rho>' env') (ivps \<rho>' (?dp # dps')) \<subseteq> reach (instE \<rho> env) Z \<union> NV" by (rule RZ)
    qed
    then show ?thesis using ok pcd
      by (intro exI[of _ "El_E env' (?dp # dps')"] conjI exI[of _ env'] exI[of _ "?dp # dps'"]) simp_all
  qed
qed

end


subsection \<open>Completeness of \<open>match_pair\<close>\<close>

context wf_csig
begin

text \<open>
  Completeness of \<^const>\<open>match_pair\<close> on a saturated flex-rigid pair of type \<open>R\<close>, if the instance
  of \<open>R\<close> is not a function type: some element of the sequence is in the invariant for extensions
  of the solutions, and the measure on the instance decreases.
\<close>

lemma pmatch_pair_complete:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and inv: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env (dp # dps)" and kk: "kokA k \<rho> (tyenv env) A"
    and dp: "dp = (rb, t, u)" and sc: "strip_comb t = (Var v T, targs)"
    and bt: "binder_types env T = return Ts" and lT: "length Ts = length targs"
    and tyt: "typed env W (map snd rb) t R" and tyu: "typed env W (map snd rb) u R"
    and nR: "tnorm (tyenv env) R = R" and nfR: "\<not> is_funT R" and fR: "\<not> is_funT (tsubst \<rho> R)"
    and nAu: "\<not> is_Abs u" and hru: "is_rigid (head_of u)" and vn: "vt_lookup (tenv env) v = None"
  shows "\<exists>ms. okW (match_pair cfg env dp dps) ms \<and> (\<exists>env'' dps'' W'' \<sigma>'' \<rho>''. ev cfg ms (El_E env'' dps'') \<and>
    pcinv alg ar A W'' \<rho>'' \<tau>' \<sigma>'' env'' dps'' \<and> agree (maxidx env) \<sigma> \<sigma>'' \<and> agreeV (maxidx env) W W'' \<and>
    tagree (maxidx env) \<rho> \<rho>'' \<and> maxidx env \<le> maxidx env'' \<and> pextends env'' env \<and>
    sum (vsz \<tau>' \<sigma>'') (unb (instE \<rho>'' env'') (ivps \<rho>'' dps'')) <
      sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) (ivps \<rho> (dp # dps))))"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  note pc0 = pcinvD[OF inv]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  note \<sigma> = solutionD[OF pc0(3)]
  note ci = pcinv_cinv[OF inv]
  note eii = env_invD[OF cinvD(1)[OF ci]]
  have e: "vt_is_empty (tyenv (instE \<rho> env))" by (rule wf_envD(1)[OF eii(2)])
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  from pi(4)[of dp] dp have wd: "swf_dp ar (rb, t, u)"
    and twd: "\<forall>X\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A X"
    and bt0: "below (maxidx env) t" and bu: "below (maxidx env) u"
    by auto
  have ds: "dsolved \<sigma> (instd \<rho> (rb, t, u))" using pc0(4)[of dp] dp by simp
  have t_eq: "t = list_comb (Var v T) targs" by (rule strip_comb_list_comb[OF sc])
  from typed_list_comb_args[OF ac(1) tyt[unfolded t_eq]] obtain As where
    tyh: "typed env W (map snd rb) (Var v T) (foldr fun_type As R)"
    and tga: "list_all2 (typed env W (map snd rb)) targs As" and nAs: "map (tnorm ?\<theta>) As = As" by blast
  have tT: "T \<in> tys t" using t_eq by (simp add: tys_list_comb)
  have twT: "tyw ar ?\<theta> A T" using twd tT by blast
  have tg: "\<forall>s\<in>set targs. swf_tm ar rb s \<and> below (maxidx env) s \<and> (\<forall>X\<in>tys s. tyw ar ?\<theta> A X)"
    using wd bt0 twd t_eq by (auto simp: swf_tm_list_comb below_list_comb tys_list_comb swf_dp_def)
  have Vv: "?V v = tnorm ?\<theta> T" and TA: "tnorm ?\<theta> T = foldr fun_type As R"
    using tyh nAs nR by (auto simp: typed_def tnorm_foldr_fun elim: has_type_elims)
  have twTn: "tyw ar ?\<theta> A (tnorm ?\<theta> T)" by (rule tyw_tnorm[OF pi(2) twT])
  have twAs: "\<forall>X\<in>set As. tyw ar ?\<theta> A X" and twR: "tyw ar ?\<theta> A R"
    using twTn TA by (simp_all add: tyw_foldr_fun)
  have aT: "arg_types (tnorm ?\<theta> T) = As" using TA arg_res_type_fun[OF nfR, of As] by simp
  have mTs: "map (tnorm ?\<theta>) Ts = As"
  proof -
    have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
      by (simp add: arg_res_type)
    from binder_types_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Ts' where
      "binder_types env T = return Ts'" "map (tnorm ?\<theta>) Ts' = arg_types (tnorm ?\<theta> T)" by blast
    with bt aT show ?thesis by (simp add: return_def)
  qed
  have lTA: "length Ts = length As" using arg_cong[OF mTs, of length] by simp
  have twTs: "\<forall>X\<in>set Ts. tyw ar ?\<theta> A X" using binder_types_tyw[OF bt[unfolded return_def] refl pi(2) twT] .
  have TU: "tnorm ?\<theta> T = tnorm ?\<theta> (foldr fun_type Ts R)" using TA mTs nR by (simp add: tnorm_foldr_fun)
  \<comment> \<open>The target\<close>
  have iT: "tsubst \<rho> T = foldr fun_type (map (tsubst \<rho>) As) (tsubst \<rho> R)"
    using tsubst_tnorm[OF ac sol tcU[OF twT]] TA by (metis tsubst_foldr_fun)
  have Vvi: "ityp \<rho> env W v = foldr fun_type (map (tsubst \<rho>) As) (tsubst \<rho> R)"
    using Vv tsubst_tnorm[OF ac sol tcU[OF twT]] iT by simp
  obtain s where tys: "(ibctx \<rho> As, \<tau>') \<turnstile> s : trty (tsubst \<rho> R)"
    and nrs: "no_redex s" and nls: "no_loose_bound s (length (map (tsubst \<rho>) As))"
    and eqv: "Abs_m (length (map (tsubst \<rho>) As)) s \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))"
    and vszv0: "vsz \<tau>' \<sigma> (v, foldr fun_type (map (tsubst \<rho>) As) (tsubst \<rho> R)) =
      lsize (ibctx \<rho> As) \<tau>' s (trty (tsubst \<rho> R))"
    by (rule value_target[OF pc0(3) Vvi])
  have nls': "no_loose_bound s (length As)" using nls by simp
  have eqv': "Abs_m (length As) s \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))" using eqv by simp
  have vszv: "vsz \<tau>' \<sigma> (v, tsubst \<rho> T) = lsize (ibctx \<rho> As) \<tau>' s (trty (tsubst \<rho> R))" using vszv0 iT by simp
  let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs"
  have "mk_subst \<sigma> (tr (inst \<rho> t)) = \<sigma> (code (AVar v)) \<degree>\<degree> ?st"
    by (simp add: t_eq inst_list_comb tr_list_comb comp_def)
  moreover have "mk_subst \<sigma> (tr (inst \<rho> t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
    using ds by (simp add: dsolved_dsolvedB dsolvedB_unabs)
  moreover have "Abs_m (length As) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v)) \<degree>\<degree> ?st"
    by (rule equiv_list_app[OF eqv']) (simp add: list_all2_conv_all_nth equiv_refl)
  ultimately have eqs: "Abs_m (length As) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))" by (metis equiv_trans)
  have hA: "\<not> is_Abs (head_of u)" "\<not> is_Var (head_of u)" using hru by (auto simp: is_rigid_def)
  have hnu: "hnf u" using hA(1) nAu by (simp add: hnf_nonAbs)
  have hlu: "hlong ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> R)"
  proof (rule hlong.base)
    show "has_type ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> R)" using tyu by (simp add: typed_def)
    show "\<not> is_Abs (tnormt ?\<theta> u)" using nAu by (cases u) auto
    show "\<not> is_funT (tnorm ?\<theta> R)" using nfR nR by simp
  qed
  have fR': "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> R)))" using fR nR arg_res_type_base[OF nfR] by simp
  have pre: "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps' rb targs As u R s"
    if "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps'" for dps'
    unfolding pmc_pre_def
    using that kk wd twd tg tga twAs bu hnu hlu twR fR' tys nrs nls' eqs
    by (auto simp: swf_dp_def)
  \<comment> \<open>The measure\<close>
  define Z where "Z = ivps \<rho> (dp # dps)"
  have vZ0: "(v, tsubst \<rho> T) \<in> Z" by (auto simp: Z_def dp t_eq inst_list_comb vps_list_comb)
  have Zb: "\<forall>y\<in>Z. snd (fst y) \<le> maxidx env"
  proof
    fix y assume "y \<in> Z"
    then obtain dq where dq: "dq \<in> set (dp # dps)" "y \<in> vps_dp (instd \<rho> dq)"
      unfolding Z_def set_map by blast
    obtain rb' t' u' where dqe: "dq = (rb', t', u')" by (cases dq)
    from pi(4)[OF dq(1)] dq(2) dqe show "snd (fst y) \<le> maxidx env"
      by (auto simp: vps_inst dest: below_vps)
  qed
  have fZ: "finite Z"
  proof -
    have "finite (vps_dp dq)" for dq by (cases dq) simp
    then show ?thesis by (simp add: Z_def)
  qed
  have vm: "snd v \<le> maxidx env" using Zb vZ0 by auto
  have vZ: "(v, tsubst \<rho> T) \<in> unb (instE \<rho> env) Z"
    using vZ0 reach_incl[of Z "instE \<rho> env"] vn by (auto simp: unb_def lk_def)
  \<comment> \<open>The occurs check\<close>
  let ?ts = "u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)"
  have tys': "\<exists>Bs X. typed env W Bs s X" and tcs: "\<forall>X\<in>tys s. tcons ?\<theta> X" and bls: "below (maxidx env) s"
    if "s \<in> set ?ts" for s
  proof -
    have "(\<exists>Bs X. typed env W Bs s X) \<and> (\<forall>X\<in>tys s. tyw ar ?\<theta> A X) \<and> below (maxidx env) s"
    proof (cases "s \<in> set (u # targs)")
      case True
      have "\<exists>X. typed env W (map snd rb) s X" if "s \<in> set targs"
        using that tga by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth)
      with True tyu twd tg bu show ?thesis by auto
    next
      case False
      with that obtain rb' t' u' where d: "(rb', t', u') \<in> set dps" "s = t' \<or> s = u'" by auto
      from pi(4)[of "(rb', t', u')"] d(1) obtain B' where "typed env W (map snd rb') t' B'"
        "typed env W (map snd rb') u' B'" "\<forall>X\<in>tys t' \<union> tys u'. tyw ar ?\<theta> A X"
        "below (maxidx env) t'" "below (maxidx env) u'" by auto
      with d(2) show ?thesis by blast
    qed
    then show "\<exists>Bs X. typed env W Bs s X" "\<forall>X\<in>tys s. tcons ?\<theta> X" "below (maxidx env) s"
      using tcU by blast+
  qed
  from occurs_terms_pinst[OF pi(1) pc0(2) tys' tcs bls] obtain occ where
    oc: "occurs_terms env v ?ts = return occ" and oci: "ok (occurs_terms (instE \<rho> env) v (map (inst \<rho>) ?ts)) occ"
    by blast
  have vl: "vps_list (map (inst \<rho>) ?ts) = vps (inst \<rho> u) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps"
  proof -
    have "\<Union> (vps ` set (map (inst \<rho>) (concat (map (\<lambda>(_, t, u). [t, u]) dps')))) = ivps \<rho> dps'" for dps'
    proof (induction dps')
      case (Cons d dps')
      then show ?case by (cases d) (auto simp: vps_dp_def)
    qed simp
    then show ?thesis by auto
  qed
  have occ: "occ \<longleftrightarrow> occ_in (instE \<rho> env) v (vps (inst \<rho> u) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps)"
    using occurs_terms_correct[OF e eii(1) oci] unfolding vl .
  have M: "match_pair cfg env dp dps = do {
      s \<leftarrow> (if occ then match1 cfg (fst v) rb targs u env (dp # dps) else mc cfg (fst v) rb targs u env dps);
      returnW (S_MapNewDset (v, T) Ts s)}"
    by (simp add: match_pair_def dp sc bt oc liftM_return)
  \<comment> \<open>The element of the copy is mapped to an element of the sequence\<close>
  have step: "?thesis"
    if sq: "okW (if occ then match1 cfg (fst v) rb targs u env (dp # dps) else mc cfg (fst v) rb targs u env dps) sq"
      and evc: "ev cfg sq (El_C u' env' dps')"
      and cr: "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D As R s 1 u' env' dps' W' \<sigma>' \<rho>' NV"
      and DZ: "D \<subseteq> Z" and acy: "(v, tsubst \<rho> T) \<notin> reach (instE \<rho>' env') (vps (inst \<rho>' u'))"
    for sq u' env' dps' W' \<sigma>' \<rho>' NV D
  proof -
    from cr have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV"
      and tyu': "typed env' W' (rev As) u' R" and wc: "swf_cp ar (length As) u'"
      and twu': "\<forall>X\<in>tys u'. tyw ar (tyenv env') A X" and bu': "below (maxidx env') u'"
      and vu': "vps (inst \<rho>' u') \<subseteq> NV" and eq': "mk_subst \<sigma>' (tr (inst \<rho>' u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
      and szc: "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + 1 \<le> lsize (ibctx \<rho> As) \<tau>' s (trty (tsubst \<rho> R))"
      unfolding pcopy_res_def by blast+
    note sd = psextD[OF sx]
    note pi' = pinvD[OF pcinvD(1)[OF sd(1)]]
    have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pi'(2)])
    have ext': "textends ?\<theta> (tyenv env')" using sd(6) by (simp add: pextends_def)
    have tyu'': "typed env' W' (rev Ts) u' R"
    proof (rule typed_tnorm_cong[OF tyu' _ refl])
      show "map (tnorm (tyenv env')) (rev Ts) = map (tnorm (tyenv env')) (rev As)"
        using arg_cong[OF mTs, of "\<lambda>xs. rev (map (tnorm (tyenv env')) xs)"]
        by (simp add: rev_map comp_def tnorm_textends[OF ac' ext'])
    qed
    have wc': "swf_cp ar (length Ts) u'" using wc lTA by simp
    have vs: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length Ts) s" using equiv_sym[OF eqv'] lTA by simp
    have sz: "sum (vsz \<tau>' \<sigma>') NV < vsz \<tau>' \<sigma> (v, tsubst \<rho> T)" using szc vszv by simp
    from pnew_dset_complete[OF sx inv tyu'' wc' twu' bu' vu' eq' vs TU twT twTs Vv vZ DZ Zb fZ acy sz]
    obtain y env'' dps'' where nd: "okW (new_dset (v, T) Ts u' env' dps') y" "y = El_E env'' dps''"
      "pcinv alg ar A W' \<rho>' \<tau>' \<sigma>' env'' dps''" "pextends env'' env'" "maxidx env'' = maxidx env'"
      "sum (vsz \<tau>' \<sigma>') (unb (instE \<rho>' env'') (ivps \<rho>' dps'')) < sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) Z)"
      by blast
    have "okW (match_pair cfg env dp dps) (S_MapNewDset (v, T) Ts sq)" using M sq by simp
    moreover have "ev cfg (S_MapNewDset (v, T) Ts sq) (El_E env'' dps'')"
      using ev.new_dset[OF evc nd(1)] nd(2) by simp
    ultimately show ?thesis using nd(3-6) sd(2-6) pextends_trans[OF nd(4) sd(6)] unfolding Z_def by fastforce
  qed
  have tl: "\<Union> (vps ` inst \<rho> ` set targs) \<subseteq> vps (inst \<rho> t)"
    by (auto simp: t_eq inst_list_comb vps_list_comb)
  have nNV: "(v, tsubst \<rho> T) \<notin> NV" if "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV"
    for W' \<sigma>' \<rho>' env' dps' D NV
    using psextD(8)[OF that, of "(v, tsubst \<rho> T)"] vm by auto
  have rNV: "reach (instE \<rho> env) NV = NV" if "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV"
    for W' \<sigma>' \<rho>' env' dps' D NV
    using reach_new[OF eii(4)] psextD(8)[OF that] by simp
  show ?thesis
  proof (cases occ)
    case True
    from pmatch1_complete[OF cfg pre[OF inv] hA, of "fst v"] obtain sq u' env' W' \<sigma>' \<rho>' NV where
      m: "okW (match1 cfg (fst v) rb targs u env (dp # dps)) sq" "ev cfg sq (El_C u' env' (dp # dps))"
      "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env (pmc_dom \<rho> u targs (dp # dps)) As R s 1 u' env' (dp # dps) W' \<sigma>' \<rho>' NV"
      "\<And>X. reach (instE \<rho>' env') X = reach (instE \<rho> env) X"
      by blast
    from m(3) have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' (dp # dps) (pmc_dom \<rho> u targs (dp # dps)) NV"
      and vu': "vps (inst \<rho>' u') \<subseteq> NV"
      unfolding pcopy_res_def by blast+
    have DZ: "pmc_dom \<rho> u targs (dp # dps) \<subseteq> Z" using tl by (auto simp: Z_def dp)
    have "reach (instE \<rho>' env') (vps (inst \<rho>' u')) \<subseteq> NV"
      using m(4) reach_subset[OF vu', of "instE \<rho> env"] rNV[OF sx] by simp
    then have acy: "(v, tsubst \<rho> T) \<notin> reach (instE \<rho>' env') (vps (inst \<rho>' u'))" using nNV[OF sx] by blast
    from True m(1) have "okW (if occ then match1 cfg (fst v) rb targs u env (dp # dps)
      else mc cfg (fst v) rb targs u env dps) sq" by simp
    from step[OF this m(2,3) DZ acy] show ?thesis .
  next
    case False
    have inv0: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" using inv by (simp add: pcinv_def pinv_def)
    have kk1: "(if is_Var (head_of (strip_abs_body u)) then 0 else 1) = (1::nat)"
      using hA nAu by (simp add: strip_abs_body_nonAbs)
    define D where "D = pmc_dom \<rho> u targs dps"
    from pmc_complete[OF cfg pre[OF inv0], of "fst v"] kk1 obtain sq u' env' dps' W' \<sigma>' \<rho>' NV where
      m: "okW (mc cfg (fst v) rb targs u env dps) sq" "ev cfg sq (El_C u' env' dps')"
      "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D As R s 1 u' env' dps' W' \<sigma>' \<rho>' NV"
      unfolding pmc_post_def D_def by auto
    from m(3) have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV"
      and vu': "vps (inst \<rho>' u') \<subseteq> NV"
      unfolding pcopy_res_def by blast+
    have DZ: "D \<subseteq> Z" using tl by (auto simp: Z_def dp D_def)
    have nD: "(v, tsubst \<rho> T) \<notin> reach (instE \<rho> env) D" using False occ by (auto simp: occ_in_def D_def)
    have "reach (instE \<rho>' env') (vps (inst \<rho>' u')) \<subseteq> reach (instE \<rho> env) (vps (inst \<rho>' u') \<union> D) \<union> NV"
      by (rule psextD(9)[OF sx])
    also have "\<dots> \<subseteq> reach (instE \<rho> env) D \<union> NV"
      using reach_subset[OF vu', of "instE \<rho> env"] rNV[OF sx] by (auto simp: reach_Un)
    finally have acy: "(v, tsubst \<rho> T) \<notin> reach (instE \<rho>' env') (vps (inst \<rho>' u'))" using nD nNV[OF sx] by blast
    from False m(1) have "okW (if occ then match1 cfg (fst v) rb targs u env (dp # dps)
      else mc cfg (fst v) rb targs u env dps) sq" by simp
    from step[OF this m(2,3) DZ acy] show ?thesis .
  qed
qed

end


subsection \<open>Completeness of \<open>match_sat\<close>\<close>

context csig
begin

lemma instd_eta_expand:
  "instd \<rho> (eta_expand_dpair Es (rb, t, u)) = eta_expand_dpair (map (tsubst \<rho>) Es) (instd \<rho> (rb, t, u))"
  by (simp add: eta_expand_dpair_simp instb_def inst_list_comb inst_incr_boundvars rev_map comp_def)

lemma vps_eta_expand:
  "vps_dp (eta_expand_dpair Es (rb, t, u)) = vps_dp (rb, t, u)"
  by (simp add: eta_expand_dpair_simp vps_dp_def vps_list_comb)

lemma rigid_eta_expand:
  assumes "is_rigid (head_of u)"
  shows "is_rigid (head_of (list_comb (incr_boundvars (integer_of_nat j) u) (eta_bvs j)))"
proof -
  have "head_of (list_comb (incr_boundvars (integer_of_nat j) u) (eta_bvs j)) =
      incr_boundvars (integer_of_nat j) (head_of u)"
    unfolding head_of_list_comb_eq by (simp add: incr_boundvars_def head_of_incr_bv_eq)
  with assms show ?thesis
    by (auto simp: is_rigid_def incr_boundvars_def integer_of_nat_eq_of_nat)
qed

end

context wf_csig
begin

text \<open>
  Completeness of \<^const>\<open>match_sat\<close>: the pair is \<open>\<eta>\<close>-expanded to a saturated pair of the result
  type \<open>R\<close> of its variable, and \<^const>\<open>match_pair\<close> is complete on it if the instance of \<open>R\<close> is
  not a function type.
\<close>

lemma pmatch_sat_complete:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and inv: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env (dp # dps)" and kk: "kokA k \<rho> (tyenv env) A"
    and fr: "pfr_shape env W dp" and hun: "heads_unb env dp"
    and ht0: "head_of (fst (snd dp)) = Var v T"
    and faith: "\<not> is_funT (tsubst \<rho> (res_type (tnorm (tyenv env) T)))"
  shows "\<exists>ms. okW (match_sat cfg env dp dps) ms \<and> (\<exists>env'' dps'' W'' \<sigma>'' \<rho>''. ev cfg ms (El_E env'' dps'') \<and>
    pcinv alg ar A W'' \<rho>'' \<tau>' \<sigma>'' env'' dps'' \<and> agree (maxidx env) \<sigma> \<sigma>'' \<and> agreeV (maxidx env) W W'' \<and>
    tagree (maxidx env) \<rho> \<rho>'' \<and> maxidx env \<le> maxidx env'' \<and> pextends env'' env \<and>
    sum (vsz \<tau>' \<sigma>'') (unb (instE \<rho>'' env'') (ivps \<rho>'' dps'')) <
      sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) (ivps \<rho> (dp # dps))))"
proof -
  let ?\<theta> = "tyenv env"
  note pc0 = pcinvD[OF inv]
  note pi = pinvD[OF pc0(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp obtain B where tyt: "typed env W (map snd rb) t B" and tyu: "typed env W (map snd rb) u B"
    and nAu: "\<not> is_Abs u" and hru: "is_rigid (head_of u)"
    by (auto simp: pfr_shape_def)
  have ht: "head_of t = Var v T" using ht0 dp by simp
  define targs where "targs = snd (strip_comb t)"
  have sc: "strip_comb t = (Var v T, targs)"
    using fst_strip_comb[of t] ht by (simp add: targs_def prod_eq_iff)
  have hnu: "hnf u" using hru nAu by (auto simp: hnf_nonAbs is_rigid_def)
  have vn: "vt_lookup (tenv env) v = None" using hun ht by (cases v) (auto simp: heads_unb_def dp)
  from pi(4)[of dp] dp have twd: "\<forall>X\<in>tys t. tyw ar ?\<theta> A X" and wdp: "swf_dp ar (rb, t, u)" by auto
  have t_eq: "t = list_comb (Var v T) targs" by (rule strip_comb_list_comb[OF sc])
  have twT: "tyw ar ?\<theta> A T" using twd t_eq by (simp add: tys_list_comb)
  have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
    by (simp add: arg_res_type)
  from binder_types_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Ts where
    bt: "binder_types env T = return Ts" by blast
  define Es where "Es = drop (length targs) Ts"
  obtain rb' t' u' where dp': "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
    by (cases "eta_expand_dpair Es (rb, t, u)")
  note ex = pexpand[OF pc0(1)[unfolded dp] tyt tyu sc bt dp'[unfolded Es_def]]
  note sh = eta_expand_dpair_shape[OF sc hnu nAu dp']
  have e: "u' = list_comb (incr_boundvars (integer_of_nat (length Es)) u) (eta_bvs (length Es))"
    using dp' by (simp add: eta_expand_dpair_simp)
  have ru': "is_rigid (head_of u')" unfolding e by (rule rigid_eta_expand[OF hru])
  have lT': "length Ts = length (map (incr_boundvars (integer_of_nat (length Es))) targs @ eta_bvs (length Es))"
    using ex(1) by (simp add: Es_def)
  \<comment> \<open>The expanded pair is in the invariant\<close>
  have "proper t" "proper u" using wdp by (simp_all add: swf_dp_def swf_tm_def)
  then have dse: "dsolved \<sigma> (instd \<rho> (rb', t', u'))"
    using dsolved_eta_expand_dpair[of "inst \<rho> t" "inst \<rho> u" \<sigma> "map (tsubst \<rho>) Es" "instb \<rho> rb"]
      solutionD(1)[OF pc0(3)] pc0(4)[of dp] dp'[symmetric] instd_eta_expand[of \<rho> Es rb t u]
    by (simp add: dp)
  have inv': "pcinv alg ar A W \<rho> \<tau>' \<sigma> env ((rb', t', u') # dps)"
    using ex(2) pc0 dse by (auto simp: pcinv_def)
  have ivps_eq: "ivps \<rho> ((rb', t', u') # dps) = ivps \<rho> (dp # dps)"
    using vps_eta_expand[of "map (tsubst \<rho>) Es" "instb \<rho> rb" "inst \<rho> t" "inst \<rho> u"]
      instd_eta_expand[of \<rho> Es rb t u] dp' by (simp add: dp)
  have fR: "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> T)))" by (rule faith)
  have M: "match_sat cfg env dp dps = match_pair cfg env (rb', t', u') dps"
    using dp' by (simp add: match_sat_def dp sc bt liftM_return Es_def)
  from pmatch_pair_complete[OF cfg inv' kk refl sh(1) bt lT' ex(3,4,5) res_type_base fR sh(3) ru' vn]
  show ?thesis unfolding M ivps_eq .
qed

end


subsection \<open>Completeness of \<open>MATCH\<close>\<close>

context csig
begin

lemma unb_lookup_eq:
  "(\<And>x. vt_lookup (tenv e1) x = vt_lookup (tenv e2) x) \<Longrightarrow> unb e1 X = unb e2 X"
  unfolding unb_def lk_def using reach_lookup_eq[of e1 e2 X] by simp

lemma is_funT_tsubst: "is_funT T \<Longrightarrow> is_funT (tsubst \<rho> T)"
  by (cases T rule: is_funT.cases) auto

lemma pcinv_kokA:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and kk: "kokA k \<rho> (tyenv env) A"
    and pc': "pcinv alg ar A W' \<rho>' \<tau>' \<sigma>' env' dps'" and pe: "pextends env' env"
    and ag: "tagree (maxidx env) \<rho> \<rho>'"
  shows "kokA k \<rho>' (tyenv env') A"
proof -
  note pi = pinvD[OF pcinvD(1)[OF pc]]
  note pi' = pinvD[OF pcinvD(1)[OF pc']]
  have sol: "tsol (tyenv env') \<rho>'" using pcinvD(2)[OF pc'] by (simp add: gsol_def)
  have ext: "textends (tyenv env) (tyenv env')" using pe by (simp add: pextends_def)
  show ?thesis
    by (rule kokA_textends[OF pi(2) tinv_tacyc[OF pi'(2)] ext sol ag tinv_tcons_env[OF pi'(2)] pi'(2) kk])
qed

end

context wf_csig
begin

text \<open>
  Completeness of \<^const>\<open>MATCH\<close> on a flex-rigid pair, for a solution \<open>\<rho>\<close> of the type environment
  that satisfies the k-condition: some element of the sequence is in the invariant for
  extensions of the solutions, the k-condition is preserved, and the measure on the instance
  decreases. If the body type \<open>B\<close> of the variable of the pair is an unbound type variable, the
  guess \<open>j\<close> is the number of arguments of its instance under \<open>\<rho>\<close>, which is at most \<open>k\<close>; the
  other guesses terminate without an exception.
\<close>

theorem MATCH_pcomplete:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and inv: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env (dp # dps)" and kk: "kokA k \<rho> (tyenv env) A"
    and fr: "pfr_shape env W dp" and hun: "heads_unb env dp"
  shows "\<exists>ms. okW (MATCH cfg env dp dps) ms \<and> (\<exists>env'' dps'' W'' \<sigma>'' \<rho>''. ev cfg ms (El_E env'' dps'') \<and>
    pcinv alg ar A W'' \<rho>'' \<tau>' \<sigma>'' env'' dps'' \<and> kokA k \<rho>'' (tyenv env'') A \<and>
    agree (maxidx env) \<sigma> \<sigma>'' \<and> agreeV (maxidx env) W W'' \<and> tagree (maxidx env) \<rho> \<rho>'' \<and>
    maxidx env \<le> maxidx env'' \<and> pextends env'' env \<and>
    sum (vsz \<tau>' \<sigma>'') (unb (instE \<rho>'' env'') (ivps \<rho>'' dps'')) <
      sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) (ivps \<rho> (dp # dps))))"
proof -
  let ?\<theta> = "tyenv env"
  define good where "good env'' dps'' \<longleftrightarrow> (\<exists>W'' \<sigma>'' \<rho>''.
    pcinv alg ar A W'' \<rho>'' \<tau>' \<sigma>'' env'' dps'' \<and> kokA k \<rho>'' (tyenv env'') A \<and>
    agree (maxidx env) \<sigma> \<sigma>'' \<and> agreeV (maxidx env) W W'' \<and> tagree (maxidx env) \<rho> \<rho>'' \<and>
    maxidx env \<le> maxidx env'' \<and> pextends env'' env \<and>
    sum (vsz \<tau>' \<sigma>'') (unb (instE \<rho>'' env'') (ivps \<rho>'' dps'')) <
      sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) (ivps \<rho> (dp # dps))))" for env'' dps''
  note pc0 = pcinvD[OF inv]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp have hvt: "is_Var (head_of t)" by (auto simp: pfr_shape_def)
  from hvt obtain v T where ht: "head_of t = Var v T" by (cases "head_of t") auto
  define targs where "targs = snd (strip_comb t)"
  have sc: "strip_comb t = (Var v T, targs)"
    using fst_strip_comb[of t] ht by (simp add: targs_def prod_eq_iff)
  from pi(4)[of dp] dp have twd: "\<forall>X\<in>tys t. tyw ar ?\<theta> A X" by auto
  have twT: "tyw ar ?\<theta> A T" using twd strip_comb_list_comb[OF sc] by (simp add: tys_list_comb)
  define R where "R = res_type (tnorm ?\<theta> T)"
  have tnT: "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) R" by (simp add: arg_res_type R_def)
  from body_type_ptnorm[OF ac tcU[OF twT] tnT res_type_base[of "tnorm ?\<theta> T", folded R_def]]
  obtain B0 where bt: "body_type env T = return B0" and nB0: "tnorm ?\<theta> B0 = R" and tcB0: "tcons ?\<theta> B0"
    by blast
  have twB0: "tyw ar ?\<theta> A B0" using body_type_tyw[OF bt[unfolded return_def] refl pi(2) twT] .
  have iR: "tsubst \<rho> R = tsubst \<rho> B0" using tsubst_tnorm[OF ac sol tcB0] nB0 by simp
  have M: "MATCH cfg env dp dps = (if is_TVar B0 then foldrW (match_eta cfg env dp dps B0) (arity_guesses cfg B0) S_Empty
      else match_sat cfg env dp dps)"
    by (simp add: MATCH_def dp sc bt liftM_return)
  \<comment> \<open>\<^const>\<open>match_sat\<close> in an extension of the type environment\<close>
  have sat_good: "\<exists>ms. okW (match_sat cfg envX dp dps) ms \<and> (\<exists>env'' dps''. ev cfg ms (El_E env'' dps'') \<and> good env'' dps'')"
    if pcX: "pcinv alg ar A W \<rho>X \<tau>' \<sigma> envX (dp # dps)" and peX: "pextends envX env"
      and mxX: "maxidx env \<le> maxidx envX" and agX: "tagree (maxidx env) \<rho> \<rho>X" and teX: "tenv envX = tenv env"
      and lkX: "\<And>x. vt_lookup (tenv (instE \<rho>X envX)) x = vt_lookup (tenv (instE \<rho> env)) x"
      and faithX: "\<not> is_funT (tsubst \<rho>X (res_type (tnorm (tyenv envX) T)))"
    for \<rho>X envX
  proof -
    note piX = pinvD[OF pcinvD(1)[OF pcX]]
    have extX: "textends ?\<theta> (tyenv envX)" using peX by (simp add: pextends_def)
    have kkX: "kokA k \<rho>X (tyenv envX) A" by (rule pcinv_kokA[OF inv kk pcX peX agX])
    have frX: "pfr_shape envX W dp" by (rule pfr_shape_wcons[OF fr tinv_tacyc[OF piX(2)] extX pi(6) piX(6)])
    have hunX: "heads_unb envX dp" using hun teX by (simp add: heads_unb_def)
    have htX: "head_of (fst (snd dp)) = Var v T" using dp ht by simp
    from pmatch_sat_complete[OF cfg pcX kkX frX hunX htX faithX] obtain ms env'' dps'' W'' \<sigma>'' \<rho>'' where
      m: "okW (match_sat cfg envX dp dps) ms" "ev cfg ms (El_E env'' dps'')"
      "pcinv alg ar A W'' \<rho>'' \<tau>' \<sigma>'' env'' dps''" "agree (maxidx envX) \<sigma> \<sigma>''" "agreeV (maxidx envX) W W''"
      "tagree (maxidx envX) \<rho>X \<rho>''" "maxidx envX \<le> maxidx env''" "pextends env'' envX"
      "sum (vsz \<tau>' \<sigma>'') (unb (instE \<rho>'' env'') (ivps \<rho>'' dps'')) <
        sum (vsz \<tau>' \<sigma>) (unb (instE \<rho>X envX) (ivps \<rho>X (dp # dps)))"
      by blast
    have pe'': "pextends env'' env" by (rule pextends_trans[OF m(8) peX])
    have ag'': "tagree (maxidx env) \<rho> \<rho>''" by (rule tagree_trans[OF agX m(6) mxX])
    have "unb (instE \<rho>X envX) (ivps \<rho>X (dp # dps)) = unb (instE \<rho> env) (ivps \<rho> (dp # dps))"
      using unb_lookup_eq[OF lkX] ivps_tagree[OF inv agX] by simp
    then have "good env'' dps''"
      unfolding good_def
      using m(3,5,4,7,9) pcinv_kokA[OF inv kk m(3) pe'' ag''] agree_mono[OF m(4) mxX]
        agreeV_mono[OF m(5) mxX] ag'' mxX pe''
      by (intro exI[of _ W''] exI[of _ \<sigma>''] exI[of _ \<rho>'']) auto
    with m(1,2) show ?thesis by blast
  qed
  have "\<exists>ms. okW (MATCH cfg env dp dps) ms \<and> (\<exists>env'' dps''. ev cfg ms (El_E env'' dps'') \<and> good env'' dps'')"
  proof (cases "is_TVar B0")
    case False
    have "\<not> is_funT B0"
    proof
      assume "is_funT B0"
      then obtain X Y where "B0 = X \<rightarrow>\<^sub>T Y" by (auto simp: is_funT_fun)
      then have "is_funT R" using nB0 by auto
      with res_type_base show False by (simp add: R_def)
    qed
    from nonfun_tsubst[OF this False] iR have fa: "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> T)))"
      by (simp add: R_def)
    from sat_good[OF inv pextends_refl order_refl _ refl refl fa] False M show ?thesis
      by (simp add: tagree_def)
  next
    case TV: True
    define X where "X = tsubst \<rho> B0"
    define j0 where "j0 = length (arg_types X)"
    have "length (arg_types (tsubst \<rho> (res_type (tnorm ?\<theta> T)))) \<le> k"
      by (rule kok_res_type[OF kok_tyw[OF pi(2) twT kk]])
    then have j0k: "j0 \<le> k" using iR by (simp add: j0_def X_def R_def)
    have j0g: "j0 \<in> set (arity_guesses cfg B0)" using TV j0k cfg(2) by (auto simp: arity_guesses_def)
    \<comment> \<open>The guess \<open>j0\<close>\<close>
    obtain ms env'' dps'' where eta: "\<And>tl. okW (match_eta cfg env dp dps B0 j0 tl) (S_Append ms tl)"
      and evm: "ev cfg ms (El_E env'' dps'')" and gd: "good env'' dps''"
    proof (cases "j0 = 0")
      case True
      have fa: "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> T)))"
        using True iR by (simp add: R_def j0_def X_def is_funT_arg_types)
      from sat_good[OF inv pextends_refl order_refl _ refl refl fa] obtain ms env'' dps'' where
        m: "okW (match_sat cfg env dp dps) ms" "ev cfg ms (El_E env'' dps'')" "good env'' dps''"
        by (auto simp: tagree_def)
      show ?thesis by (rule that[OF _ m(2,3)]) (use True m(1) in \<open>auto simp: match_eta_def\<close>)
    next
      case False
      let ?A' = "A \<union> ctvars Rs"
      obtain env1 Rs where g: "gentvars (Suc j0) env = (env1, Rs)" by (cases "gentvars (Suc j0) env")
      note gs = gentvars_simps[OF g] and gm = gentvars_cases(1)[OF g]
      define Cs' where "Cs' = res_type X # arg_types X"
      have lC: "length Cs' = Suc j0" by (simp add: Cs'_def j0_def)
      have grX: "ground ar X" using twB0 pc0(2) by (auto simp: X_def tyw_def gsol_def intro: ground_tsubst)
      have gC: "\<forall>C\<in>set Cs'. ground ar C" using ground_arg_types[OF grX] ground_res_type[OF grX] by (simp add: Cs'_def)
      from gentvars_inst[OF g lC gC pc0(2) pi(2)] obtain \<rho>1 where
        r1: "gsol alg ar ?\<theta> \<rho>1" "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Rs = Cs'" by blast
      have ti0: "tinv ar (maxidx env1) ?\<theta> A" by (rule tinv_mono[OF pi(2) gm])
      have pc1: "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 (dp # dps)"
        by (rule pcinv_text[OF inv gs(1)]) (simp_all add: gs(2) gm ti0 ei(2) r1(1,2))
      have ti0': "tinv ar (maxidx env1) (tyenv env1) (A \<union> ctvars Rs)" using tinv_gentvars[OF pi(2) g] gs(2) by simp
      have twR: "\<forall>C\<in>set Rs. tyw ar (tyenv env1) (A \<union> ctvars Rs) C" using tyw_gentvars[OF pi(2) g] gs(2) by simp
      obtain R0 Rs' where Rs: "Rs = R0 # Rs'" using gs(3) by (cases Rs) auto
      have twB1: "tyw ar (tyenv env1) (A \<union> ctvars Rs) B0" using twB0 gs(2) by (auto intro: tyw_mono)
      have twF: "tyw ar (tyenv env1) (A \<union> ctvars Rs) (foldr fun_type (tl Rs) (hd Rs))"
        using twR Rs by (simp add: tyw_foldr_fun)
      have iR0: "tsubst \<rho>1 R0 = res_type X" and iRs': "map (tsubst \<rho>1) Rs' = arg_types X"
        using r1(3) Rs by (simp_all add: Cs'_def)
      have eq: "tsubst \<rho>1 B0 = tsubst \<rho>1 (foldr fun_type (tl Rs) (hd Rs))"
      proof -
        have "tsubst \<rho>1 B0 = X" using tyw_tagree[OF pi(2) twB0 r1(2)] by (simp add: X_def)
        also have "\<dots> = foldr fun_type (arg_types X) (res_type X)" by (simp add: arg_res_type)
        finally show ?thesis using iR0 iRs' Rs by (simp add: tsubst_foldr_fun)
      qed
      from cunify_types_pcomplete'[OF pc1 Un_upper1 ti0' twB1 twF eq] obtain env2 \<rho>2 where
        cu: "cunify_types alg B0 (foldr fun_type (tl Rs) (hd Rs)) env1 = returnW env2"
        and pc2: "pcinv alg ar A W \<rho>2 \<tau>' \<sigma> env2 (dp # dps)" and te2: "tenv env2 = tenv env1"
        and pe2: "pextends env2 env1" and mx2: "maxidx env1 \<le> maxidx env2" and ag2: "tagree (maxidx env1) \<rho>1 \<rho>2"
        and "\<And>Z. reach (instE \<rho>2 env2) Z = reach (instE \<rho>1 env1) Z"
        and tn2: "tnorm (tyenv env2) B0 = tnorm (tyenv env2) (foldr fun_type (tl Rs) (hd Rs))"
        and ti2: "tinv ar (maxidx env2) (tyenv env2) (A \<union> ctvars Rs)"
        by blast
      have peT: "pextends env2 env" using pe2 gentvars_pextends[OF g] by (rule pextends_trans)
      have mxT: "maxidx env \<le> maxidx env2" using gm mx2 by simp
      have agT: "tagree (maxidx env) \<rho> \<rho>2" by (rule tagree_trans[OF r1(2) ag2 gm])
      have teT: "tenv env2 = tenv env" using te2 gs(1) by simp
      note pi1 = pinvD[OF pcinvD(1)[OF pc1]]
      have lkT: "vt_lookup (tenv (instE \<rho>2 env2)) x = vt_lookup (tenv (instE \<rho> env)) x" for x
        using instE_tagree_lookup[OF pi1(2) ballI[OF pi1(3)] te2 ag2, of x]
          instE_tagree_lookup[OF pi(2) ballI[OF pi(3)] gs(1) r1(2), of x]
        by simp
      \<comment> \<open>The result type in the extended type environment\<close>
      let ?\<theta>2 = "tyenv env2"
      have ac2: "tacyc ?\<theta>2" "tcons_env ?\<theta>2" using tinv_tacyc[OF ti2] tinv_tcons_env[OF ti2] by simp_all
      have sol2: "tsol ?\<theta>2 \<rho>2" using pcinvD(2)[OF pc2] by (simp add: gsol_def)
      have ext2: "textends ?\<theta> ?\<theta>2" using peT by (simp add: pextends_def)
      have ext12: "textends (tyenv env1) ?\<theta>2" using pe2 by (simp add: pextends_def)
      have "tnorm ?\<theta>2 T = foldr fun_type (map (tnorm ?\<theta>2) (arg_types (tnorm ?\<theta> T))) (tnorm ?\<theta>2 R)"
      proof -
        have "tnorm ?\<theta>2 T = tnorm ?\<theta>2 (tnorm ?\<theta> T)" by (simp add: tnorm_textends[OF ac2(1) ext2])
        also have "\<dots> = tnorm ?\<theta>2 (foldr fun_type (arg_types (tnorm ?\<theta> T)) R)" using tnT by simp
        finally show ?thesis by (simp add: tnorm_foldr_fun)
      qed
      also have "tnorm ?\<theta>2 R = tnorm ?\<theta>2 B0" using nB0 tnorm_textends[OF ac2(1) ext2, of B0] by simp
      also have "\<dots> = foldr fun_type (map (tnorm ?\<theta>2) Rs') (tnorm ?\<theta>2 R0)"
        using tn2 Rs by (simp add: tnorm_foldr_fun)
      finally have rt2: "res_type (tnorm ?\<theta>2 T) = res_type (tnorm ?\<theta>2 R0)"
        by (simp add: arg_res_types_foldr)
      have twR0: "tyw ar ?\<theta>2 (A \<union> ctvars Rs) R0" using twR Rs tyw_textends[OF ac2(1) ext12] by simp
      from gentvars_tvar[OF g, of R0] Rs obtain n where R0: "R0 = TVar (gtv (maxidx env + 1) n) []"
        and mx1: "maxidx env1 = maxidx env + 1" by auto
      have "tsubst \<rho>2 (tnorm ?\<theta>2 R0) = tsubst \<rho>2 R0" by (rule tsubst_tnorm[OF ac2 sol2 tyw_tcons[OF ti2 twR0]])
      also have "\<dots> = tsubst \<rho>1 R0" using tagreeD[OF ag2, of "gtv (maxidx env + 1) n" "[]"] R0 mx1 by simp
      finally have i2: "tsubst \<rho>2 (tnorm ?\<theta>2 R0) = res_type X" using iR0 by simp
      have nf2: "\<not> is_funT (tnorm ?\<theta>2 R0)"
        using is_funT_tsubst[of "tnorm ?\<theta>2 R0" \<rho>2] i2 res_type_base[of X] by auto
      have fa2: "\<not> is_funT (tsubst \<rho>2 (res_type (tnorm ?\<theta>2 T)))"
        using rt2 arg_res_type_base[OF nf2] i2 res_type_base[of X] by simp
      from sat_good[OF pc2 peT mxT agT teT lkT fa2] obtain ms env'' dps'' where
        m: "okW (match_sat cfg env2 dp dps) ms" "ev cfg ms (El_E env'' dps'')" "good env'' dps''"
        by blast
      have "okW (match_eta cfg env dp dps B0 j0 tl0) (S_Append ms tl0)" for tl0
      proof -
        have "match_eta cfg env dp dps B0 j0 tl0 = handleW (do {
            env2' \<leftarrow> cunify_types (cfg_alg cfg) B0 (foldr fun_type (tl Rs) (hd Rs)) env1;
            s \<leftarrow> match_sat cfg env2' dp dps; returnW (S_Append s tl0)})
            (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tl0 | _ \<Rightarrow> raiseW e)"
          using False g by (simp add: match_eta_def)
        then show ?thesis using cu cfg(1) m(1) by (auto simp: okW_handleW)
      qed
      then show ?thesis by (rule that[OF _ m(2,3)])
    qed
    \<comment> \<open>All guesses\<close>
    have "\<exists>r. okW (foldrW (match_eta cfg env dp dps B0) (arity_guesses cfg B0) S_Empty) r \<and>
        (\<forall>y. ev cfg S_Empty y \<longrightarrow> ev cfg r y) \<and>
        (\<forall>x\<in>set (arity_guesses cfg B0). \<forall>y. x = j0 \<and> y = El_E env'' dps'' \<longrightarrow> ev cfg r y)"
    proof (rule ev_foldrW)
      fix x t assume "x \<in> set (arity_guesses cfg B0)"
      show "\<exists>r. okW (match_eta cfg env dp dps B0 x t) r \<and> (\<forall>y. ev cfg t y \<longrightarrow> ev cfg r y) \<and>
          (\<forall>y. x = j0 \<and> y = El_E env'' dps'' \<longrightarrow> ev cfg r y)"
      proof (cases "x = j0")
        case True
        then show ?thesis using eta[of t] evm
          by (intro exI[of _ "S_Append ms t"]) (auto intro: ev.append_l ev.append_r)
      next
        case False
        from match_eta_total[OF cfg(1) pc0(1) fr twB0, of x t] obtain r where
          "okW (match_eta cfg env dp dps B0 x t) r" "\<forall>y. ev cfg t y \<longrightarrow> ev cfg r y" by blast
        with False show ?thesis by blast
      qed
    qed
    then obtain r where r: "okW (foldrW (match_eta cfg env dp dps B0) (arity_guesses cfg B0) S_Empty) r"
      "ev cfg r (El_E env'' dps'')" using j0g by blast
    show ?thesis using M TV r gd by auto
  qed
  then show ?thesis unfolding good_def by blast
qed

end

end
