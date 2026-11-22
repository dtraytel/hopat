section \<open>The Type Invariant for the Elements of \<open>MATCH\<close>\<close>

theory Unify_Typed_Match
  imports Unify_Acyclic_Simpl
begin

text \<open>
  The elements that \<open>MATCH\<close> enumerates keep the type-level part of the invariant of the
  search (\<open>tyinv\<close>), for any names of the variables. The sequence of \<open>MATCH\<close> is lazy:
  its closures run type unification, \<open>SIMPL\<close> and further copies when they are pulled.
  As for soundness (\<open>seqinv\<close>), an invariant of the sequences (\<open>tseq\<close>) records what the
  closures need, and the elements are treated by induction on the evaluation (\<open>ev\<close>),
  with \<open>seqinv\<close> alongside for the typing of the pairs. No termination is involved.

  The development is parametrized by a flag \<open>b\<close>: if it is set, the states of the sequences
  also have acyclic environments (\<open>b \<longrightarrow> acyc env\<close>). The soundness of the search needs only
  \<open>b = False\<close>; acyclicity of the results uses \<open>b = True\<close> (theory \<open>Unify_Acyclic\<close>).
\<close>

context pure_sig_gen
begin

lemma state_below:
  assumes gt: "gtyped env dps" and ei: "einv A K (tyonly env)"
  shows "below (maxidx env) (dvars dps \<union> evars env)"
proof -
  have r: "tsol (tyenv env) (tnorm_inst (tyenv env))" "cert_inst (tnorm_inst (tyenv env))"
    using einv_rho0[OF ei] by simp_all
  from gt r have "vinv (tnorm_inst (tyenv env)) env (dvars dps)" unfolding gtyped_def by blast
  then show ?thesis by (simp add: vinv_def)
qed

lemma vars_types_abs_mi: "vars (types_abs Ts t) = vars t"
  by (induction Ts) auto

context
  fixes b :: bool
begin

lemma acyc_fresh_update:
  assumes ac: "b \<longrightarrow> acyc env" and te: "tenv env' = tenv env" and upd: "ok (update (v, T) t env') env''"
    and bl: "below (maxidx env) (insert (v, T) (evars env))"
    and fr: "\<And>y U. (y, U) \<in> vars t \<Longrightarrow> maxidx env < snd y"
  shows "b \<longrightarrow> acyc env''"
proof
  assume b
  with ac have "acyc env" by simp
  then have a': "acyc env'" using acyc_tenv[OF te] by simp
  show "acyc env''"
  proof (rule acyc_update[OF upd a'])
    fix y U assume yU: "(y, U) \<in> vars t"
    have "vt_lookup (tenv env') y = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env') y \<noteq> None"
      then obtain U' u' where "vt_lookup (tenv env) y = Some (U', u')" using te by fastforce
      then have "(y, U') \<in> evars env" unfolding evars_def bnds_def by (cases y) blast
      from belowD[OF bl insertI2[OF this]] fr[OF yU] show False by simp
    qed
    moreover have "v \<noteq> y" using belowD[OF bl insertI1] fr[OF yU] by auto
    ultimately show "(v, y) \<notin> (dep env')\<^sup>*" by (rule not_dep_unbound)
  qed
qed

subsection \<open>The invariant of the sequences\<close>

text \<open>The type-level invariant of a state, for type variables \<open>P\<close> that stay known:\<close>

definition tst :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "tst P env dps \<longleftrightarrow> (\<exists>A K. finite K \<and> P \<subseteq> tvars_env (tyenv env) \<union> A \<and> einv A K (tyonly env) \<and>
    tknown A env dps) \<and> (b \<longrightarrow> acyc env)"

lemma tst_mono: "tst P' env dps \<Longrightarrow> P \<subseteq> P' \<Longrightarrow> tst P env dps"
  unfolding tst_def by blast

lemma tst_tyinv: "tst P env dps \<Longrightarrow> \<exists>A K. tyinv A K env dps"
  unfolding tst_def tyinv_def by blast

lemma tstI: "finite K \<Longrightarrow> einv A K (tyonly env) \<Longrightarrow> tknown A env dps \<Longrightarrow> P \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    (b \<longrightarrow> acyc env) \<Longrightarrow> tst P env dps"
  unfolding tst_def by blast

inductive tseq :: "(indexname \<times> psort) set \<Rightarrow> seq \<Rightarrow> bool" where
  Empty: "tseq P S_Empty"
| Single: "tst P env dps \<Longrightarrow> tseq P (S_Single (El_E env dps))"
| Append: "tseq P xq \<Longrightarrow> tseq P yq \<Longrightarrow> tseq P (S_Append xq yq)"
| Proj: "(\<forall>env1 args env2. make_args vname Ts env' Us = (env1, args) \<longrightarrow>
      ok (update X (types_abs Ts (list_comb head args)) env1) env2 \<longrightarrow>
      tst P env2 ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) \<Longrightarrow>
    tseq P tail \<Longrightarrow> tseq P (S_Proj vname env' Ts Us targs rb u dps head targ X tail)"
| Maps: "tseq P1 xq \<Longrightarrow> P \<subseteq> P1 \<Longrightarrow> ttvars (G \<degree>\<degree> targs) \<union> ttvars uarg \<union> btvars rb \<subseteq> P1 \<Longrightarrow>
    tseq P (S_Maps vname envM rb targs G uarg xq)"

inductive_cases tseq_SingleE: "tseq P (S_Single x)"
inductive_cases tseq_ProjE: "tseq P (S_Proj vname env Ts Us targs rb u dps head targ X tail)"
inductive_cases tseq_MapsE: "tseq P (S_Maps vname envM rb targs G' uarg xq)"
inductive_cases tseq_AppendE: "tseq P (S_Append xq yq)"

lemma tseq_mono: "tseq P' s \<Longrightarrow> P \<subseteq> P' \<Longrightarrow> tseq P s"
proof (induction arbitrary: P rule: tseq.induct)
  case (Single P' env dps)
  then show ?case by (auto intro: tseq.Single tst_mono)
next
  case (Proj vname Ts env' Us X head P' rb targ targs u dps tail)
  then show ?case by (intro tseq.Proj) (auto intro: tst_mono)
next
  case (Maps P1 xq P' G targs uarg rb vname envM)
  then show ?case by (intro tseq.Maps[of P1]) auto
qed (auto intro: tseq.intros)


subsection \<open>Typing at the most general solution\<close>

lemma state_typing:
  assumes gt: "gtyped env ((rb, t, u) # dps)" and ei: "einv A K (tyonly env)"
  obtains e W where "bs_env (tnorm_inst (tyenv env)) e rb" "e \<turnstile> inst (tnorm_inst (tyenv env)) t : W"
    "e \<turnstile> inst (tnorm_inst (tyenv env)) u : W" "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)"
  using gtyped_rho0(2)[OF gt ei] by auto

lemma fastype_known:
  assumes ei: "einv A K (tyonly env)" and f: "ok (fastype env rb t) T"
    and ty: "e \<turnstile> inst (tnorm_inst (tyenv env)) t : W" and bs: "bs_env (tnorm_inst (tyenv env)) e rb"
    and lb: "\<not> loose_bvar t (ilength rb)" and k: "ttvars t \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "tnorm (tyenv env) T = W" "cert_typ alg ar W"
proof -
  have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  from env_fastype_term[OF ti refl ty bs lb k] obtain T' where
    T': "env_fastype env (map snd rb) t = return T'" "tvars T' \<subseteq> tvars_env (tyenv env) \<union> A"
      "tnorm (tyenv env) T' = W"
    by blast
  have "T = T'" using f T'(1) by (simp add: fastype_def return_def)
  with T' show "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "tnorm (tyenv env) T = W" by simp_all
  show "cert_typ alg ar W" by (rule bs_env_cert[OF bs ty lb])
qed

lemma mapM_fastype_known:
  assumes ei: "einv A K (tyonly env)" and f: "ok (mapM (fastype env rb) ts) Ts"
    and ty: "e \<tturnstile> map (inst (tnorm_inst (tyenv env))) ts : Ws" and bs: "bs_env (tnorm_inst (tyenv env)) e rb"
    and lb: "\<forall>t\<in>set ts. \<not> loose_bvar t (ilength rb)"
    and k: "\<forall>t\<in>set ts. ttvars t \<subseteq> tvars_env (tyenv env) \<union> A" "btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "map (tnorm (tyenv env)) Ts = Ws"
    "\<forall>W\<in>set Ws. cert_typ alg ar W"
proof -
  from f have l: "list_all2 (\<lambda>t T. ok (fastype env rb t) T) ts Ts" by (simp add: ok_mapM)
  have len: "length Ts = length ts" "length Ws = length ts"
    using list_all2_lengthD[OF l] typings_nth[OF ty] by simp_all
  have each: "tvars (Ts ! i) \<subseteq> tvars_env (tyenv env) \<union> A \<and> tnorm (tyenv env) (Ts ! i) = Ws ! i \<and>
      cert_typ alg ar (Ws ! i)" if i: "i < length ts" for i
  proof -
    have fi: "ok (fastype env rb (ts ! i)) (Ts ! i)" using l i by (simp add: list_all2_conv_all_nth)
    have ti: "e \<turnstile> inst (tnorm_inst (tyenv env)) (ts ! i) : Ws ! i" using typings_nth[OF ty] i by simp
    have "ts ! i \<in> set ts" using i by simp
    with lb k have "\<not> loose_bvar (ts ! i) (ilength rb)" "ttvars (ts ! i) \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
      by blast+
    note fk = fastype_known[OF ei fi ti bs this]
    then show ?thesis by blast
  qed
  show "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  proof
    fix T assume "T \<in> set Ts"
    then obtain i where "i < length Ts" "T = Ts ! i" by (auto simp: in_set_conv_nth)
    with each len show "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" by simp
  qed
  show "map (tnorm (tyenv env)) Ts = Ws" using each len by (auto intro: nth_equalityI)
  show "\<forall>W\<in>set Ws. cert_typ alg ar W" using each len by (auto simp: in_set_conv_nth)
qed

lemma app_typing:
  assumes "e \<turnstile> inst \<rho> (h \<degree>\<degree> ts) : W"
  obtains Ws where "e \<turnstile> inst \<rho> h : Ws \<Rrightarrow> W" "e \<tturnstile> map (inst \<rho>) ts : Ws"
  using list_app_typeD[of e "inst \<rho> h" "map (inst \<rho>) ts" W] assms by (auto simp: inst_apps)

lemma known_wft:
  assumes ei: "einv A K (tyonly env)" and tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tnorm (tyenv env) T)"
  shows "wft ar T" "sorts_ok alg T"
  using known_cert[OF ei tv, of "tnorm_inst (tyenv env)"] c by simp_all


subsection \<open>Type unification and new type variables\<close>

lemma tyinv_cunify_c:
  assumes cu: "okW (cunify_types alg T U env) env1" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar T"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar U"
  shows "einv A K (tyonly env1)" "tenv env1 = tenv env" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    "textends (tyenv env) (tyenv env1)" "maxidx env \<le> maxidx env1"
proof -
  note c = cunify_types_tyonly[OF cu]
  have tT: "tvars T \<subseteq> tvars_env (tyenv (tyonly env)) \<union> A" and tU: "tvars U \<subseteq> tvars_env (tyenv (tyonly env)) \<union> A"
    using T(1) U(1) by simp_all
  from xokW_okW[OF cunify_types_term[OF ei fK tT _ _ tU] c(1)] T(2) U(2)
  show "einv A K (tyonly env1)" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    "textends (tyenv env) (tyenv env1)" "maxidx env \<le> maxidx env1"
    by (simp_all add: cert_typ_def)
  show "tenv env1 = tenv env" by (rule c(2))
qed

lemma gentvars_tyonly: "gentvars p env = (env1, Cs) \<Longrightarrow> gentvars p (tyonly env) = (tyonly env1, Cs)"
  by (cases env) (auto simp: gentvars_def tyonly_def split: if_splits)

lemma cert_ntv:
  assumes "gentvars p env = (env1, Cs)" "C \<in> set Cs"
  shows "cert_typ alg ar C"
  using gentvars_simps(6)[OF assms] by (auto simp: cert_typ_def sort_ok_def)

lemma tvars_ntv: "C \<in> set Cs \<Longrightarrow> tvars C \<subseteq> ntv Cs"
  by (auto simp: ntv_def)

lemma einv_tyonly_maxidx:
  "einv A K (tyonly env) \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> maxidx env \<le> maxidx env' \<Longrightarrow> einv A K (tyonly env')"
  using einv_maxidx[of A K "tyonly env" "tyonly env'"] by simp

lemma okW_test_unify_types:
  "okW (test_unify_types al T U env) env' \<Longrightarrow> okW (cunify_types al T U env) env'"
  by (auto simp: test_unify_types_def okW_whenW)

lemma proj_unify_inv:
  assumes pu: "okW (proj_unify cfg base bary Cs env) env'" and cfg: "cfg_alg cfg = alg"
    and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tv: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A"
      "\<forall>C\<in>set Cs. tvars C \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar base" "cert_typ alg ar bary" "\<forall>C\<in>set Cs. cert_typ alg ar C"
  shows "einv A K (tyonly env') \<and> tenv env' = tenv env \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
    maxidx env \<le> maxidx env'"
proof (cases "Cs = []")
  case True
  with pu have h: "okW (if cfg_trace_types cfg then test_unify_types (cfg_alg cfg) base bary env
      else cunify_types (cfg_alg cfg) base bary env) env'"
    by (simp add: proj_unify_def)
  have "okW (cunify_types alg base bary env) env'"
  proof (cases "cfg_trace_types cfg")
    case True
    with h have "okW (test_unify_types (cfg_alg cfg) base bary env) env'" by (simp only: if_True)
    from okW_test_unify_types[OF this] show ?thesis by (simp only: cfg)
  next
    case False
    with h show ?thesis by (simp only: if_False cfg)
  qed
  from tyinv_cunify_c[OF this fK ei tv(1) c(1) tv(2) c(2)] show ?thesis by simp
next
  case False
  with pu cfg have cu: "okW (cunify_types alg bary (Cs \<Rrightarrow> base) env) env'"
    by (simp add: proj_unify_def)
  have "tvars (Cs \<Rrightarrow> base) \<subseteq> tvars_env (tyenv env) \<union> A" using tv(1,3) by (auto simp: tvars_funs)
  moreover have "cert_typ alg ar (Cs \<Rrightarrow> base)" using c(1,3) by (simp add: cert_typ_funs)
  ultimately show ?thesis using tyinv_cunify_c[OF cu fK ei tv(2) c(2)] by simp
qed


subsection \<open>Imitation\<close>

lemma tknown_lift:
  "tknown A env dps \<Longrightarrow> tvars_env (tyenv env) \<union> A \<subseteq> tvars_env (tyenv env') \<union> A' \<Longrightarrow>
    etvars env' \<subseteq> tvars_env (tyenv env') \<union> A' \<Longrightarrow> tknown A' env' dps"
  unfolding tknown_def by blast

lemma tknown_Cons: "tknown A env (p # dps) \<longleftrightarrow> tknown A env [p] \<and> tknown A env dps"
  unfolding tknown_def by auto

lemma copyargs_tseq:
  "tst P env1 dps \<Longrightarrow> \<forall>(G, uarg)\<in>set gus. ttvars (G \<degree>\<degree> targs) \<union> ttvars uarg \<union> btvars rb \<subseteq> P \<Longrightarrow>
    tseq P (copyargs vname envM rb targs gus env1 dps)"
proof (induction gus)
  case Nil
  then show ?case by (auto intro: tseq.Single)
next
  case (Cons gu gus)
  obtain G uarg where gu: "gu = (G, uarg)" by (cases gu)
  from Cons show ?case by (auto simp: gu intro!: tseq.Maps[of P])
qed

lemma imitate_tseq:
  assumes im: "okW (imitate vname envM rb targs env dps X Ts uhead uargs) s"
    and u: "u = uhead \<degree>\<degree> uargs" and Tsok: "ok (mapM (fastype env rb) targs) Ts"
    and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)"
    and gt: "gtyped env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)"
    and ac: "b \<longrightarrow> acyc env" and hv: "vars uhead = {}"
  shows "tseq (tvars_env (tyenv env) \<union> A) s"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A" and ?\<rho> = "tnorm_inst (tyenv env)"
  from im[unfolded imitate_def okW_bindW okW_liftM] obtain Us where Us: "ok (mapM (fastype env rb) uargs) Us"
    and r: "okW (case make_args vname Ts env Us of (env', args) \<Rightarrow> do {
        env'' \<leftarrow> liftM (update X (types_abs Ts (list_comb uhead args)) env');
        returnW (copyargs vname envM rb targs (zip (map head_of args) uargs) env'' dps)}) s"
    by blast
  obtain env' args where ma: "make_args vname Ts env Us = (env', args)" by fastforce
  from r ma obtain env'' where up: "ok (update X (types_abs Ts (list_comb uhead args)) env') env''"
    and s: "s = copyargs vname envM rb targs (zip (map head_of args) uargs) env'' dps"
    by auto
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    and ma': "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    and fG: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    by (rule make_args_props_idx[OF ma]) blast
  obtain v TX where X: "X = (v, TX)" by (cases X)
  have kt: "ttvars (Var v TX \<degree>\<degree> targs) \<union> ttvars u \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
    and kd: "\<forall>(rb', t', u')\<in>set dps. ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> ?KN"
    using tk by (auto simp: tknown_def X)
  have ac'': "b \<longrightarrow> acyc env''"
  proof (rule acyc_fresh_update[OF ac ma'(1) up[unfolded X]])
    have "(v, TX) \<in> dvars ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)" by (simp add: dvars_def X vars_apps)
    with state_below[OF gt ei] show "below (maxidx env) (insert (v, TX) (evars env))" by (auto simp: below_def X vars_apps)
    show "maxidx env < snd y" if "(y, U) \<in> vars (types_abs Ts (list_comb uhead args))" for y U
    proof -
      from that hv obtain G where "G \<in> set Gs" "(y, U) \<in> vars G"
        by (auto simp: vars_types_abs_mi list_comb_apps vars_apps args)
      with fG show ?thesis by auto
    qed
  qed
  from state_typing[OF gt ei] obtain e W where bs: "bs_env ?\<rho> e rb"
    and tyt: "e \<turnstile> inst ?\<rho> (Var (fst X) (snd X) \<degree>\<degree> targs) : W" and tyu: "e \<turnstile> inst ?\<rho> u : W"
    and lbt: "\<not> loose_bvar (Var (fst X) (snd X) \<degree>\<degree> targs) (ilength rb)" and lbu: "\<not> loose_bvar u (ilength rb)"
    by blast
  from app_typing[OF tyt] obtain Ws where tts: "e \<tturnstile> map (inst ?\<rho>) targs : Ws" by blast
  from app_typing[OF tyu[unfolded u]] obtain Vs where tus: "e \<tturnstile> map (inst ?\<rho>) uargs : Vs" by blast
  have kTs: "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN"
    by (rule mapM_fastype_known(1)[OF ei Tsok tts bs]) (use lbt kt in \<open>auto simp: X loose_bvar_apps ttvars_apps\<close>)
  have kUs: "\<forall>T\<in>set Us. tvars T \<subseteq> ?KN"
    by (rule mapM_fastype_known(1)[OF ei Us tus bs]) (use lbu kt in \<open>auto simp: u loose_bvar_apps ttvars_apps\<close>)
  have kG: "ttvars G \<subseteq> ?KN" if "G \<in> set Gs" for G
  proof -
    from that obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF Gs i(1)] obtain x where G: "G = Var x (Ts \<Rrightarrow> (Us ! i))" using i(2) by blast
    have "Us ! i \<in> set Us" using i(1) list_all2_lengthD[OF Gs] by simp
    with G kTs kUs show ?thesis by (auto simp: tvars_funs)
  qed
  have kA: "ttvars a \<subseteq> ?KN" if "a \<in> set args" for a
  proof -
    from that obtain G where G: "G \<in> set Gs" "a = G \<degree>\<degree> bvs (length Ts)" by (auto simp: args)
    have "ttvars a = ttvars G" by (auto simp: G(2) ttvars_apps)
    with kG[OF G(1)] show ?thesis by simp
  qed
  have ei'': "einv A K (tyonly env'')"
    using einv_tyonly_maxidx[OF ei ma'(2,3)] tyonly_update[OF up[unfolded X]] by simp
  have te'': "tyenv env'' = tyenv env" using ok_update(3)[OF up[unfolded X]] ma'(2) by simp
  have "ttvars (types_abs Ts (list_comb uhead args)) \<subseteq> ?KN"
    using kTs kA kt by (auto simp: list_comb_apps ttvars_apps u)
  then have kE'': "etvars env'' \<subseteq> ?KN"
    using etvars_update[OF up[unfolded X]] etvars_tenv[OF ma'(1)] kE kt by (auto simp: ttvars_apps)
  have "tst ?KN env'' dps"
    by (rule tstI[OF fK ei'' _ _ ac'']) (use kE'' kd te'' in \<open>auto simp: tknown_def\<close>)
  moreover have each: "ttvars (G \<degree>\<degree> targs) \<union> ttvars uarg \<union> btvars rb \<subseteq> ?KN"
    if "(G, uarg) \<in> set (zip (map head_of args) uargs)" for G uarg
  proof -
    from that have "G \<in> set (map head_of args)" "uarg \<in> set uargs" by (auto dest: set_zip_leftD set_zip_rightD)
    then obtain G' where G': "G' \<in> set Gs" "G = head_of (G' \<degree>\<degree> bvs (length Ts))" by (auto simp: args)
    have "head_of (G' \<degree>\<degree> bvs (length Ts)) = G'" using G'(1) Gs
      by (auto simp: head_of_apps list_all2_conv_all_nth in_set_conv_nth)
    with G' have "ttvars G \<subseteq> ?KN" using kG by simp
    with \<open>uarg \<in> set uargs\<close> kt show ?thesis by (auto simp: ttvars_apps u)
  qed
  have "\<forall>(G, uarg)\<in>set (zip (map head_of args) uargs). ttvars (G \<degree>\<degree> targs) \<union> ttvars uarg \<union> btvars rb \<subseteq> ?KN"
  proof
    fix p assume p: "p \<in> set (zip (map head_of args) uargs)"
    obtain G uarg where "p = (G, uarg)" by (cases p)
    with each[of G uarg] p show "case p of (G, uarg) \<Rightarrow> ttvars (G \<degree>\<degree> targs) \<union> ttvars uarg \<union> btvars rb \<subseteq> ?KN"
      by simp
  qed
  ultimately show ?thesis unfolding s by (rule copyargs_tseq)
qed


subsection \<open>Projections\<close>

lemma strip_type_known:
  assumes ei: "einv A K (tyonly env)" and st: "ok (strip_type env T) (Us, bary)"
    and kT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" and cT: "cert_typ alg ar (tnorm (tyenv env) T)"
  shows "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar U"
    "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar bary"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A"
  from st have bt: "ok (binder_types env T) Us" and bdy: "ok (body_type env T) bary"
    by (auto simp: strip_type_def)
  have ac: "tacyc (tyenv env)" using einvD(6)[OF ei] by simp
  have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  from mf_binder_types_sound[OF bt refl ac] have kUs: "\<forall>U\<in>set Us. tvars U \<subseteq> ?KN" using kT by blast
  from body_type_term[OF ti refl kT] bdy have kb: "tvars bary \<subseteq> ?KN" by (auto simp: return_def)
  have r0: "tsol (tyenv env) (tnorm_inst (tyenv env))" using einv_rho0(1)[OF ei] by simp
  have m: "map (tsubst (tnorm_inst (tyenv env))) Us = map (tnorm (tyenv env)) Us" by (rule map_cong) simp_all
  from strip_type_sound[OF st r0] have "tnorm (tyenv env) T = map (tnorm (tyenv env)) Us \<Rrightarrow> tnorm (tyenv env) bary"
    by (simp only: m tsubst_tnorm_inst)
  with cT have c: "\<forall>U\<in>set Us. cert_typ alg ar (tnorm (tyenv env) U)" "cert_typ alg ar (tnorm (tyenv env) bary)"
    by (simp_all add: cert_typ_funs)
  show "\<forall>U\<in>set Us. tvars U \<subseteq> ?KN \<and> cert_typ alg ar U"
    using kUs c(1) known_wft[OF ei] by (auto simp: cert_typ_def)
  show "tvars bary \<subseteq> ?KN" by (rule kb)
  show "cert_typ alg ar bary" using known_wft[OF ei kb c(2)] by (simp add: cert_typ_def)
qed

lemma projenv_tseq:
  assumes pe: "okW (projenv cfg vname rb targs u env dps X base Ts head Usb targ p tail) s"
    and tl: "tseq (tvars_env (tyenv env) \<union> A) tail"
    and st: "ok (strip_type env T) Usb"
    and hk: "k < length targs" "head = Bound i" "targ = targs ! k" "T = Ts ! k"
    and Tsok: "ok (mapM (fastype env rb) targs) Ts"
    and kb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" and cb: "cert_typ alg ar base"
    and cfg: "cfg_alg cfg = alg" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)"
    and gt: "gtyped env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)"
    and ac: "b \<longrightarrow> acyc env"
  shows "tseq (tvars_env (tyenv env) \<union> A) s"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A" and ?\<rho> = "tnorm_inst (tyenv env)"
  obtain Us bary where Usb: "Usb = (Us, bary)" by (cases Usb)
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by fastforce
  note gs = gentvars_simps[OF g]
  from okW_handle_CANTUNIFY[OF pe[unfolded projenv_def Usb g prod.case]]
  consider (ok) env' where "okW (proj_unify cfg base bary Cs env0) env'"
      "s = S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ X tail"
    | (cu) "s = tail"
    by auto
  then show ?thesis
  proof cases
    case (ok env')
    obtain v TX where X: "X = (v, TX)" by (cases X)
    have kt: "ttvars (Var v TX \<degree>\<degree> targs) \<union> ttvars u \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
      and kd: "\<forall>(rb', t', u')\<in>set dps. ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> ?KN"
      using tk by (auto simp: tknown_def X)
    from state_typing[OF gt ei] obtain e W where bs: "bs_env ?\<rho> e rb"
      and tyt: "e \<turnstile> inst ?\<rho> (Var (fst X) (snd X) \<degree>\<degree> targs) : W"
      and lbt: "\<not> loose_bvar (Var (fst X) (snd X) \<degree>\<degree> targs) (ilength rb)"
      by blast
    from app_typing[OF tyt] obtain Ws where tts: "e \<tturnstile> map (inst ?\<rho>) targs : Ws" by blast
    have lbts: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)" using lbt by (auto simp: loose_bvar_apps)
    have kts: "\<forall>t\<in>set targs. ttvars t \<subseteq> ?KN" using kt by (auto simp: ttvars_apps)
    have kbr: "btvars rb \<subseteq> ?KN" using kt by blast
    note mk = mapM_fastype_known[OF ei Tsok tts bs lbts kts kbr]
    have lTs: "length Ts = length targs" using mapM_fastype_sound(1)[OF Tsok] .
    have kT: "tvars T \<subseteq> ?KN" using mk(1) hk(1,4) lTs by simp
    have cT: "cert_typ alg ar (tnorm (tyenv env) T)"
    proof -
      have "length Ws = length targs" using typings_nth[OF tts] by simp
      then have "Ws ! k \<in> set Ws" using hk(1) by simp
      moreover have "tnorm (tyenv env) T = Ws ! k" using mk(2) hk(1,4) lTs by (metis nth_map)
      ultimately show ?thesis using mk(3) by simp
    qed
    note sk = strip_type_known[OF ei st[unfolded Usb] kT cT]
    let ?A' = "A \<union> ntv Cs" and ?K' = "K \<union> ntv Cs"
    have ei0: "einv ?A' ?K' (tyonly env0)" by (rule einv_gentvars[OF ei gentvars_tyonly[OF g]])
    have fK': "finite ?K'" using fK by simp
    have te0: "tyenv env0 = tyenv env" "tenv env0 = tenv env" using gs by simp_all
    have kC: "\<forall>C\<in>set Cs. tvars C \<subseteq> tvars_env (tyenv env0) \<union> ?A'" using tvars_ntv by blast
    have cC: "\<forall>C\<in>set Cs. cert_typ alg ar C" using cert_ntv[OF g] by blast
    from proj_unify_inv[OF ok(1) cfg fK' ei0 _ _ kC cb sk(3) cC] kb sk(2) te0
    have pu: "einv ?A' ?K' (tyonly env')" "tenv env' = tenv env" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
      "maxidx env0 \<le> maxidx env'"
      by auto
    have mx: "maxidx env \<le> maxidx env'" using pu(4) gs(3) by simp
    have "tst ?KN env2 ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)"
      if ma: "make_args vname Ts env' (Us @ Cs) = (env1, args)"
        and up: "ok (update X (types_abs Ts (list_comb head args)) env1) env2" for env1 args env2
    proof -
      obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
        and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs (Us @ Cs)"
        and ma': "tenv env1 = tenv env'" "tyenv env1 = tyenv env'" "maxidx env' \<le> maxidx env1"
        and fG: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U"
        by (rule make_args_props_idx[OF ma]) blast
      let ?KN' = "tvars_env (tyenv env2) \<union> ?A'"
      have ac2: "b \<longrightarrow> acyc env2"
      proof (rule acyc_fresh_update[OF ac _ up[unfolded X]])
        show "tenv env1 = tenv env" using ma'(1) pu(2) by simp
        have "(v, TX) \<in> dvars ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)" by (simp add: dvars_def X vars_apps)
        with state_below[OF gt ei] show "below (maxidx env) (insert (v, TX) (evars env))" by (auto simp: below_def X vars_apps)
        show "maxidx env < snd y" if "(y, U) \<in> vars (types_abs Ts (list_comb head args))" for y U
        proof -
          from that hk(2) obtain G where "G \<in> set Gs" "(y, U) \<in> vars G"
            by (auto simp: vars_types_abs_mi list_comb_apps vars_apps args)
          with fG mx show ?thesis by fastforce
        qed
      qed
      have te2: "tyenv env2 = tyenv env'" using ok_update(3)[OF up[unfolded X]] ma'(2) by simp
      have ei2: "einv ?A' ?K' (tyonly env2)"
        using einv_tyonly_maxidx[OF pu(1) ma'(2,3)] tyonly_update[OF up[unfolded X]] by simp
      have sub: "?KN \<subseteq> ?KN'" using pu(3) te2 by auto
      have kG: "ttvars G \<subseteq> ?KN'" if "G \<in> set Gs" for G
      proof -
        from that obtain j where j: "j < length Gs" "G = Gs ! j" by (auto simp: in_set_conv_nth)
        from list_all2_nthD[OF Gs j(1)] obtain x where G: "G = Var x (Ts \<Rrightarrow> ((Us @ Cs) ! j))" using j(2) by blast
        have "(Us @ Cs) ! j \<in> set Us \<or> (Us @ Cs) ! j \<in> set Cs"
          using j(1) list_all2_lengthD[OF Gs] by (metis nth_mem set_append Un_iff)
        then have "tvars ((Us @ Cs) ! j) \<subseteq> ?KN'"
          using sk(1) tvars_ntv sub by blast
        moreover have "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN'" using mk(1) sub by blast
        ultimately show ?thesis by (auto simp: G tvars_funs)
      qed
      have hG: "head_of a \<in> set Gs" if "a \<in> set args" for a
      proof -
        from that obtain G where G: "G \<in> set Gs" "a = G \<degree>\<degree> bvs (length Ts)" by (auto simp: args)
        have "head_of a = G" using G Gs by (auto simp: head_of_apps list_all2_conv_all_nth in_set_conv_nth)
        with G(1) show ?thesis by simp
      qed
      have kA: "ttvars a \<subseteq> ?KN'" if "a \<in> set args" for a
      proof -
        from that obtain G where G: "G \<in> set Gs" "a = G \<degree>\<degree> bvs (length Ts)" by (auto simp: args)
        have "ttvars a = ttvars G" by (auto simp: G(2) ttvars_apps)
        with kG[OF G(1)] show ?thesis by simp
      qed
      have "ttvars (types_abs Ts (list_comb head args)) = (\<Union>T\<in>set Ts. tvars T) \<union> (\<Union>a\<in>set args. ttvars a)"
        using hk(2) by (simp add: list_comb_apps ttvars_apps)
      then have kH: "ttvars (types_abs Ts (list_comb head args)) \<subseteq> ?KN'" using mk(1) sub kA by blast
      have e2: "etvars env2 = tvars TX \<union> ttvars (types_abs Ts (list_comb head args)) \<union> etvars env"
        using etvars_update[OF up[unfolded X]] etvars_tenv[OF ma'(1)] etvars_tenv[OF pu(2)] by simp
      have kTX: "tvars TX \<subseteq> ?KN" using kt by (auto simp: ttvars_apps)
      have kE2: "etvars env2 \<subseteq> ?KN'" unfolding e2 using kTX kH kE sub by blast
      have targ: "targ \<in> set targs" using hk(1,3) by simp
      have "ttvars (list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args)) \<subseteq>
          ttvars targ \<union> (\<Union>a\<in>set args. ttvars (head_of a)) \<union> (\<Union>t\<in>set targs. ttvars t)"
        by (auto simp: list_comb_apps ttvars_apps)
      moreover have "(\<Union>a\<in>set args. ttvars (head_of a)) \<subseteq> ?KN'" using hG kG by blast
      ultimately have kN: "ttvars (list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args)) \<subseteq> ?KN'"
        using kts targ sub by blast
      have "tknown ?A' env2 [(rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u)]"
        unfolding tknown_pair using kE2 kN kt sub by blast
      moreover have "tknown ?A' env2 dps"
        by (rule tknown_lift[OF tknown_Cons[THEN iffD1, OF tk, THEN conjunct2] sub kE2])
      ultimately have "tknown ?A' env2 ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)"
        by (simp add: tknown_Cons[of _ _ _ dps])
      from tstI[OF fK' ei2 this _ ac2] sub show ?thesis by blast
    qed
    with tl ok(2) show ?thesis by (auto intro!: tseq.Proj)
  qed (use tl in simp)
qed

lemma matchfun_tseq:
  assumes "okW (matchfun cfg vname envM rb targs u env dps X uhead uargs base Ts projs) s"
    and projs: "\<forall>q\<in>set projs. \<exists>k<length targs. q = (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k)"
    and u: "u = uhead \<degree>\<degree> uargs" and Tsok: "ok (mapM (fastype env rb) targs) Ts"
    and kb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" and cb: "cert_typ alg ar base"
    and cfg: "cfg_alg cfg = alg" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)"
    and gt: "gtyped env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)"
    and ac: "b \<longrightarrow> acyc env"
  shows "tseq (tvars_env (tyenv env) \<union> A) s"
  using assms(1,2)
proof (induction projs arbitrary: s)
  case Nil
  then show ?case
    by (cases uhead) (auto intro: imitate_tseq[OF _ u Tsok fK ei tk gt ac] tseq.Empty)
next
  case (Cons q projs)
  obtain bvar T targ where q: "q = (bvar, T, targ)" by (cases q)
  from Cons.prems(2) q obtain k where hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    "T = Ts ! k" "targ = targs ! k" by auto
  from Cons.prems(1)[unfolded q matchfun.simps] obtain Usb tail where st: "ok (strip_type env T) Usb"
    and mt: "okW (matchfun cfg vname envM rb targs u env dps X uhead uargs base Ts projs) tail"
    and fo: "okW (foldrW (projenv cfg vname rb targs u env dps X base Ts bvar Usb targ)
      (arity_guesses cfg (snd Usb)) tail) s"
    by auto
  let ?P = "tvars_env (tyenv env) \<union> A"
  have tl: "tseq ?P tail" by (rule Cons.IH[OF mt]) (use Cons.prems(2) in auto)
  have "tseq ?P tail \<longrightarrow> tseq ?P s'"
    if "okW (foldrW (projenv cfg vname rb targs u env dps X base Ts bvar Usb targ) ps tail) s'" for ps s'
    using that
  proof (induction rule: okW_foldrW_induct)
    case (Cons p ps b b1 b')
    show ?case
    proof
      assume "tseq ?P b"
      with Cons.IH have b1: "tseq ?P b1" by simp
      show "tseq ?P b'"
        by (rule projenv_tseq[OF Cons.hyps(2) b1 st hk(1,2,4,3) Tsok kb cb cfg fK ei tk gt ac])
    qed
  qed simp
  with fo tl show ?case by blast
qed


subsection \<open>Copies\<close>

lemma head_fastype_known:
  assumes ei: "einv A K (tyonly env)" and f: "ok (fastype env rb (fst (strip_comb u))) T0"
    and tyu: "e \<turnstile> inst (tnorm_inst (tyenv env)) u : W" and bs: "bs_env (tnorm_inst (tyenv env)) e rb"
    and lbu: "\<not> loose_bvar u (ilength rb)" and k: "ttvars u \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar (tnorm (tyenv env) T0)"
proof -
  obtain h ts where hts: "strip_comb u = (h, ts)" by fastforce
  have u: "u = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
  have h: "fst (strip_comb u) = h" using hts by simp
  from app_typing[OF tyu[unfolded u]] obtain Ws where
    th: "e \<turnstile> inst (tnorm_inst (tyenv env)) h : Ws \<Rrightarrow> W" by blast
  have lb: "\<not> loose_bvar h (ilength rb)" using lbu u by (simp add: loose_bvar_apps)
  have kh: "ttvars h \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
    using k u by (auto simp: ttvars_apps)
  note fk = fastype_known[OF ei f[unfolded h] th bs lb kh]
  show "tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A" by (rule fk(1))
  show "cert_typ alg ar (tnorm (tyenv env) T0)" using fk(2,3) by simp
qed

lemma ttvars_Abs_strip:
  assumes "fst (strip_comb u) = Abs a T body"
  shows "tvars T \<union> ttvars body \<subseteq> ttvars u"
proof -
  have u: "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps[OF prod.collapse[symmetric]])
  have "ttvars (Abs a T body) \<subseteq> ttvars u" using u assms by (metis Un_upper1 ttvars_apps)
  then show ?thesis by simp
qed

lemma mc_tseq:
  assumes "okW (mc cfg vname envM X rb targs u env dps) s" "msat ot env rb u"
    "\<forall>t. ot = Some t \<longrightarrow> t = Var (fst X) (snd X) \<degree>\<degree> targs"
    and cfg: "cfg_alg cfg = alg" and fK: "finite K"
  shows "einv A K (tyonly env) \<Longrightarrow> tknown A env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps) \<Longrightarrow>
    gtyped env ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps) \<Longrightarrow> (b \<longrightarrow> acyc env) \<Longrightarrow>
    tseq (tvars_env (tyenv env) \<union> A) s"
  using assms(1-3)
proof (induction "size u" arbitrary: X rb targs u env s ot rule: less_induct)
  case less
  obtain v TX where X: "X = (v, TX)" by (cases X)
  note ei = less.prems(1) and tk = less.prems(2) and gt = less.prems(3) and ac = less.prems(4)
  have blX: "below (maxidx env) (insert (v, TX) (evars env))"
  proof -
    have "(v, TX) \<in> dvars ((rb, Var (fst X) (snd X) \<degree>\<degree> targs, u) # dps)" by (simp add: dvars_def X vars_apps)
    with state_below[OF gt ei] show ?thesis by (auto simp: below_def X vars_apps)
  qed
  let ?KN = "tvars_env (tyenv env) \<union> A" and ?\<rho> = "tnorm_inst (tyenv env)"
  have kt: "ttvars (Var v TX \<degree>\<degree> targs) \<union> ttvars u \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
    using tk by (auto simp: tknown_def X)
  have kTX: "tvars TX \<subseteq> ?KN" and kts: "\<forall>t\<in>set targs. ttvars t \<subseteq> ?KN" and kbr: "btvars rb \<subseteq> ?KN"
    and ku: "ttvars u \<union> btvars rb \<subseteq> ?KN"
    using kt by (auto simp: ttvars_apps)
  have tkd: "tknown A env dps" using tknown_Cons tk by blast
  from state_typing[OF gt ei] obtain e W where bs: "bs_env ?\<rho> e rb"
    and tyt: "e \<turnstile> inst ?\<rho> (Var (fst X) (snd X) \<degree>\<degree> targs) : W" and tyu: "e \<turnstile> inst ?\<rho> u : W"
    and lbt: "\<not> loose_bvar (Var (fst X) (snd X) \<degree>\<degree> targs) (ilength rb)" and lbu: "\<not> loose_bvar u (ilength rb)"
    by blast
  from app_typing[OF tyt] obtain Ws where tts: "e \<tturnstile> map (inst ?\<rho>) targs : Ws" by blast
  have lbts: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)" using lbt by (auto simp: loose_bvar_apps)
  have kTs: "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN" if "ok (mapM (fastype env rb) targs) Ts" for Ts
    using mapM_fastype_known(1)[OF ei that tts bs lbts kts kbr] .
  have r0: "tsol (tyenv env) ?\<rho>" using einv_rho0(1)[OF ei] by simp
  have bse: "U = tsubst \<rho> base"
    if na: "\<not> is_Abs (fst (strip_comb u))" and T0: "ok (fastype env rb (fst (strip_comb u))) T0"
      and base: "ok (body_type env T0) base" and tsol: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e rb"
      and tyt: "e \<turnstile> inst \<rho> (Var v TX \<degree>\<degree> targs) : U" and tyu: "e \<turnstile> inst \<rho> u : U" for \<rho> e U T0 base
  proof (cases ot)
    case None
    with less.prems(6) have sat: "satd env rb u" by (simp add: msat_def)
    show ?thesis by (rule satd_base[OF na sat T0 base tsol bs tyu])
  next
    case (Some t)
    with less.prems(6,7) X have "rsat env rb (Var v TX \<degree>\<degree> targs) u" by (simp add: msat_def)
    from this[unfolded rsat_def] T0 base tsol bs tyt tyu show ?thesis by blast
  qed
  have base_known: "tvars base \<subseteq> ?KN \<and> cert_typ alg ar base"
    if na: "\<not> is_Abs (fst (strip_comb u))" and T0: "ok (fastype env rb (fst (strip_comb u))) T0"
      and base: "ok (body_type env T0) base" for T0 base
  proof -
    note hk = head_fastype_known[OF ei T0 tyu bs lbu ku]
    have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
    from body_type_term[OF ti refl hk(1)] base have kb: "tvars base \<subseteq> ?KN" by (auto simp: return_def)
    have "W = tnorm (tyenv env) base" using bse[OF na T0 base r0 bs tyt[unfolded X fst_conv snd_conv] tyu] by simp
    moreover have "cert_typ alg ar W" by (rule bs_env_cert[OF bs tyu lbu])
    ultimately have "cert_typ alg ar (tnorm (tyenv env) base)" by simp
    from known_wft[OF ei kb this] kb show ?thesis by (simp add: cert_typ_def)
  qed
  show ?case
    using less.prems(5)[unfolded X]
  proof (cases rule: mc_okW_cases)
    case (asg r)
    have "tst ?KN env ((rb, list_comb (Var v TX) targs, u) # dps)"
      by (rule tstI[OF fK ei _ _ ac]) (use tk in \<open>simp_all add: X list_comb_apps\<close>)
    then show ?thesis by (simp add: asg(2) tseq.Single)
  next
    case (abs a A' body Ts B env' Y Y' env'')
    have sat: "satd env rb u" using less.prems(6,7) abs(2) by (cases ot) (simp_all add: msat_def)
    note st = mc_abs_step[OF abs(1-7) sat]
    note gs = genvar_simps[OF abs(5)]
    let ?targs' = "map (incr_boundvars 1) targs @ [Bound 0]"
    let ?p = "((a, A') # rb, Var (fst Y') (snd Y') \<degree>\<degree> ?targs', body)"
    have gt'': "gtyped env'' (?p # dps)"
    proof -
      have "gtyped env'' ((((a, A') # rb, Y \<degree>\<degree> (map (\<lambda>t. lift t 0) targs @ [Bound 0]), body) # dps))"
        by (rule gtyped_dstep[OF st(3) gt[unfolded X fst_conv snd_conv]])
      then show ?thesis by (simp only: st(2) map_incr_boundvars_lift)
    qed
    have mx: "maxidx env \<le> maxidx env''" using st(5) by (simp add: extends_def)
    have ei'': "einv A K (tyonly env'')" by (rule einv_tyonly_maxidx[OF ei st(4) mx])
    have kA: "tvars A' \<union> ttvars body \<subseteq> ?KN" using ttvars_Abs_strip[OF abs(2)] kt by blast
    have kB: "tvars B \<subseteq> ?KN"
    proof -
      from state_typing[OF gt'' ei''] obtain e' W' where bs': "bs_env (tnorm_inst (tyenv env'')) e' ((a, A') # rb)"
        and tyb: "e' \<turnstile> inst (tnorm_inst (tyenv env'')) body : W'" and lbb: "\<not> loose_bvar body (ilength ((a, A') # rb))"
        by blast
      have "ttvars body \<union> btvars ((a, A') # rb) \<subseteq> ?KN" using kA kbr by (auto simp: btvars_def)
      from fastype_known(1)[OF ei abs(4) tyb[unfolded st(4)] bs'[unfolded st(4)] lbb this] show ?thesis .
    qed
    have kY: "tvars (snd Y') \<subseteq> ?KN"
    proof -
      have "Y' = (fst Y', snd Y')" by simp
      moreover have "snd Y' = foldr fun_type (Ts @ [A']) B" using st(2) gs(4) by simp
      ultimately show ?thesis using kTs[OF abs(3)] kA kB by (auto simp: tvars_funs)
    qed
    have te'': "tyenv env'' = tyenv env" by (rule st(4))
    have e'': "etvars env'' = tvars TX \<union> ttvars (types_abs Ts (Abs a A' (combound Y 0 (Suc (length Ts))))) \<union> etvars env"
      using etvars_update[OF abs(7)] etvars_tenv[OF gs(1)] by simp
    have "ttvars (types_abs Ts (Abs a A' (combound Y 0 (Suc (length Ts))))) \<subseteq> ?KN"
      using kTs[OF abs(3)] kA kY st(2) by (auto simp: ttvars_combound)
    then have kE'': "etvars env'' \<subseteq> tvars_env (tyenv env'') \<union> A" unfolding e'' te'' using kTX kE by blast
    have "ttvars (Var (fst Y') (snd Y') \<degree>\<degree> ?targs') \<subseteq> ?KN"
      using kY kts by (auto simp: ttvars_apps incr_boundvars_def)
    then have "tknown A env'' [?p]"
      unfolding tknown_pair te'' using kE'' kA kbr te'' by (auto simp: btvars_def)
    moreover have "tknown A env'' dps" by (rule tknown_lift[OF tkd _ kE'']) (simp add: te'')
    ultimately have tk'': "tknown A env'' (?p # dps)" by (simp add: tknown_Cons[of _ _ _ dps])
    have ac'': "b \<longrightarrow> acyc env''"
    proof (rule acyc_fresh_update[OF ac gs(1) abs(7) blX])
      show "maxidx env < snd y" if "(y, U) \<in> vars (types_abs Ts (Abs a A' (combound Y 0 (Suc (length Ts)))))" for y U
        using that gs(4) by (simp add: vars_types_abs_mi combound_apps vars_apps)
    qed
    have "tseq (tvars_env (tyenv env'') \<union> A) s"
    proof (rule less.hyps[OF _ ei'' tk'' gt'' ac'' abs(8)])
      show "size body < size u" by (simp add: st(1))
      show "msat None env'' ((a, A') # rb) body" by (simp add: msat_def st(6))
    qed simp
    then show ?thesis by (simp add: te'')
  next
    case (var w W0 T0 base Ts env' newhd env'')
    have na: "\<not> is_Abs (fst (strip_comb u))" using var(2) by simp
    note bk = base_known[OF na var(3)[folded var(2)] var(4)]
    note gs = genvar_simps[OF var(6)]
    have te'': "tyenv env'' = tyenv env" using ok_update(3)[OF var(7)] gs(2) by simp
    have mx: "maxidx env \<le> maxidx env''" using ok_update(4)[OF var(7)] gs(3) by simp
    have ei'': "einv A K (tyonly env'')" by (rule einv_tyonly_maxidx[OF ei te'' mx])
    have kN: "ttvars newhd \<subseteq> ?KN" using gs(4) kTs[OF var(5)] bk by (auto simp: tvars_funs)
    have e'': "etvars env'' = tvars TX \<union> ttvars (types_abs Ts (combound newhd 0 (length Ts))) \<union> etvars env"
      using etvars_update[OF var(7)] etvars_tenv[OF gs(1)] by simp
    have "ttvars (types_abs Ts (combound newhd 0 (length Ts))) \<subseteq> ?KN"
      using kTs[OF var(5)] kN by (auto simp: ttvars_combound)
    then have kE'': "etvars env'' \<subseteq> tvars_env (tyenv env'') \<union> A" unfolding e'' te'' using kTX kE by blast
    have "tknown A env'' [(rb, newhd \<degree>\<degree> targs, u)]"
      unfolding tknown_pair te'' using kE'' kN kts ku by (auto simp: ttvars_apps te'')
    moreover have "tknown A env'' dps" by (rule tknown_lift[OF tkd _ kE'']) (simp add: te'')
    ultimately have tkn: "tknown A env'' ((rb, newhd \<degree>\<degree> targs, u) # dps)" by (simp add: tknown_Cons[of _ _ _ dps])
    have ac'': "b \<longrightarrow> acyc env''"
    proof (rule acyc_fresh_update[OF ac gs(1) var(7) blX])
      show "maxidx env < snd y" if "(y, U) \<in> vars (types_abs Ts (combound newhd 0 (length Ts)))" for y U
        using that gs(4) by (simp add: vars_types_abs_mi combound_apps vars_apps)
    qed
    from tstI[OF fK ei'' tkn _ ac''] te'' have "tst ?KN env'' ((rb, newhd \<degree>\<degree> targs, u) # dps)" by simp
    then show ?thesis by (simp add: var(8) list_comb_apps tseq.Single)
  next
    case (rigid T0 base Ts projs)
    have u: "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps[OF prod.collapse[symmetric]])
    note bk = base_known[OF rigid(2,4,5)]
    show ?thesis
      by (rule matchfun_tseq[OF rigid(8)[folded X] _ u rigid(6) _ _ cfg fK ei tk gt ac])
        (use make_projs_props[OF rigid(7)] bk in simp_all)
  qed
qed


lemma etvars_extends: "extends env env' \<Longrightarrow> etvars env \<subseteq> etvars env'"
  unfolding etvars_def bnds_def extends_def by fastforce

lemma copycons_tseq:
  assumes cc: "okW (copycons cfg vname envM rb targs G uarg env dps) cs" and extM: "extends envM env"
    and cfg: "cfg_alg cfg = alg" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env ((rb, G \<degree>\<degree> targs, uarg) # dps)" and gt: "gtyped env ((rb, G \<degree>\<degree> targs, uarg) # dps)"
    and ac: "b \<longrightarrow> acyc env"
  shows "tseq (tvars_env (tyenv env) \<union> A) cs"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A" and ?\<rho> = "tnorm_inst (tyenv env)"
  from cc[unfolded copycons_def okW_bindW okW_liftM] obtain X u1 u2 d where X: "okW (dest_Var G) X"
    and h: "ok (head_norm envM uarg) u1" and e: "ok (eta_norm env rb u1) u2"
    and s: "okW (if d then returnW (S_Single (El_E env ((rb, list_comb G targs, u2) # dps)))
      else mc cfg vname envM X rb targs u2 env dps) cs"
    by blast
  from X obtain x U where G: "G = Var x U" "X = (x, U)" by (cases G) auto
  have kp: "ttvars (G \<degree>\<degree> targs) \<union> ttvars uarg \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
    using tk by (auto simp: tknown_def)
  have tkd: "tknown A env dps" using tknown_Cons tk by blast
  have tc1: "tconv env rb uarg u1" by (rule tconv_extends[OF head_norm_tconv[OF h] extM])
  have d1: "dstep env ((rb, G \<degree>\<degree> targs, uarg) # dps) env ((rb, G \<degree>\<degree> targs, u1) # dps)"
    using dstep_frame[OF tconv_dstep[OF tconv_refl tc1], where fs = dps] by simp
  have gt1: "gtyped env ((rb, G \<degree>\<degree> targs, u1) # dps)" by (rule gtyped_dstep[OF d1 gt])
  have tc: "tconv env rb uarg u2" by (rule tconv_trans[OF tc1 eta_norm_tconv[OF e]])
  have dc: "dstep env ((rb, G \<degree>\<degree> targs, uarg) # dps) env ((rb, G \<degree>\<degree> targs, u2) # dps)"
    using dstep_frame[OF tconv_dstep[OF tconv_refl tc], where fs = dps] by simp
  have gt2: "gtyped env ((rb, G \<degree>\<degree> targs, u2) # dps)" by (rule gtyped_dstep[OF dc gt])
  have k1: "ttvars u1 \<union> btvars rb \<subseteq> ?KN"
    using head_norm_ttvars[OF h refl] etvars_extends[OF extM] kE kp by blast
  have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  from state_typing[OF gt1 ei] obtain e1 W1 where bs: "bs_env ?\<rho> e1 rb" and ty1: "e1 \<turnstile> inst ?\<rho> u1 : W1"
    and lb1: "\<not> loose_bvar u1 (ilength rb)"
    by blast
  from eta_norm_term[OF ti refl ty1 bs lb1 k1] e have k2: "ttvars u2 \<subseteq> ?KN" by (auto simp: return_def)
  have tk2: "tknown A env ((rb, G \<degree>\<degree> targs, u2) # dps)"
    using tknown_Cons[of A env "(rb, G \<degree>\<degree> targs, u2)" dps] tkd k2 kp kE by (auto simp: tknown_pair)
  show ?thesis
  proof (cases d)
    case True
    with s have "cs = S_Single (El_E env ((rb, G \<degree>\<degree> targs, u2) # dps))" by (simp add: list_comb_apps)
    with tstI[OF fK ei tk2 _ ac] show ?thesis by (simp add: tseq.Single)
  next
    case False
    with s have m: "okW (mc cfg vname envM X rb targs u2 env dps) cs" by simp
    have "msat None env rb u2" using head_norm_eta_norm_satd[OF h e] by (simp add: msat_def)
    from mc_tseq[OF m this _ cfg fK, of A] ei tk2 gt2 ac show ?thesis by (simp add: G)
  qed
qed


subsection \<open>The elements of the sequences\<close>

inductive_cases tseq_AddUnifyE: "tseq P (S_AddUnify td env dps R)"
inductive_cases tseq_ItRightE: "tseq P (S_ItRight td xq R)"

theorem tseq_ev:
  assumes cfg: "cfg_alg cfg = alg"
  shows "ev cfg s x \<Longrightarrow> tseq P s \<Longrightarrow> seqinv (GE env0 dps0) s \<Longrightarrow> gtyped env0 dps0 \<Longrightarrow>
    \<exists>env dps. x = El_E env dps \<and> tst P env dps"
proof (induction arbitrary: P env0 dps0 rule: ev.induct)
  case (single x)
  then show ?case by (auto elim: tseq_SingleE)
next
  case (proj vname Ts env Us env' args X head env'' rb targ targs u dpairs env2 frigid fflex tail)
  let ?p = "(rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u)"
  from proj.prems(1) have t: "tst P env'' (?p # dpairs)"
    by (rule tseq_ProjE) (use proj.hyps(1,2) in blast)
  from proj.prems(2) have d: "dstep env0 dps0 env'' (?p # dpairs)"
    by (rule seqinv_ProjE) (use proj.hyps(1,2) in blast)
  have gt: "gtyped env'' (?p # dpairs)" by (rule gtyped_dstep[OF d proj.prems(3)])
  from t obtain A K where fK: "finite K" and P: "P \<subseteq> tvars_env (tyenv env'') \<union> A"
    and ei: "einv A K (tyonly env'')" and tk: "tknown A env'' (?p # dpairs)" and ac: "b \<longrightarrow> acyc env''"
    unfolding tst_def by blast
  have ac2: "b \<longrightarrow> acyc env2" using SIMPL_acyc[OF proj.hyps(3)] ac by blast
  from SIMPL_inv[OF fK proj.hyps(3)[unfolded cfg] ei tk gt]
  have ei2: "einv A K (tyonly env2)" and tk2: "tknown A env2 (fflex @ frigid)"
    and m: "tvars_env (tyenv env'') \<subseteq> tvars_env (tyenv env2)" by auto
  have "tknown A env2 (frigid @ fflex)" by (rule tknown_perm[OF tk2]) auto
  from tstI[OF fK ei2 this _ ac2] P m show ?case by auto
next
  case (proj_tail tail x vname env Ts Us targs rb u dpairs head targ X)
  from proj_tail.prems(1) have "tseq P tail" by (rule tseq_ProjE)
  moreover from proj_tail.prems(2) have "seqinv (GE env0 dps0) tail" by (rule seqinv_ProjE) simp
  ultimately show ?case by (rule proj_tail.IH[OF _ _ proj_tail.prems(3)])
next
  case (maps xq env dps vname envM rb targs G' uarg cs x)
  from maps.prems(1) obtain P1 where t1: "tseq P1 xq" and PP: "P \<subseteq> P1"
    and kp: "ttvars (G' \<degree>\<degree> targs) \<union> ttvars uarg \<union> btvars rb \<subseteq> P1"
    by (rule tseq_MapsE) blast
  from maps.prems(2) show ?case
  proof (rule seqinv_MapsE)
    fix env0' dps0' env1 dps1 y U
    assume G: "GE env0 dps0 = GE env0' dps0'" and Gv: "G' = Var y U"
      and d0': "dstep env0' dps0' env1 ((rb, Var y U \<degree>\<degree> targs, uarg) # dps1)"
      and xs: "seqinv (GE env1 dps1) xq" and extM: "extends envM env1"
    from d0' Gv G have d0: "dstep env0 dps0 env1 ((rb, G' \<degree>\<degree> targs, uarg) # dps1)" by simp
    have g1: "gtyped env1 ((rb, G' \<degree>\<degree> targs, uarg) # dps1)" by (rule gtyped_dstep[OF d0 maps.prems(3)])
    then have g1': "gtyped env1 dps1" by (rule gtyped_mono) auto
    from maps.IH(1)[OF t1 xs g1'] obtain A K where fK: "finite K" and P1: "P1 \<subseteq> tvars_env (tyenv env) \<union> A"
      and ei: "einv A K (tyonly env)" and tk: "tknown A env dps" and ac: "b \<longrightarrow> acyc env"
      unfolding tst_def by blast
    from ev_sound[OF maps.hyps(1) xs] have d1: "dstep env1 dps1 env dps" by simp
    have ext: "extends envM env" by (rule extends_trans[OF extM dstepD(1)[OF d1]])
    have d2: "dstep env1 ((rb, G' \<degree>\<degree> targs, uarg) # dps1) env ((rb, G' \<degree>\<degree> targs, uarg) # dps)"
      by (rule dstep_set[OF dstep_frame[OF d1, where fs = "[(rb, G' \<degree>\<degree> targs, uarg)]"]]) auto
    have gt: "gtyped env ((rb, G' \<degree>\<degree> targs, uarg) # dps)" by (rule gtyped_dstep[OF d2 g1])
    have tkp: "tknown A env ((rb, G' \<degree>\<degree> targs, uarg) # dps)"
      using tknown_Cons[of A env "(rb, G' \<degree>\<degree> targs, uarg)" dps] tk kp P1 by (auto simp: tknown_def)
    have ts: "tseq (tvars_env (tyenv env) \<union> A) cs" by (rule copycons_tseq[OF maps.hyps(2) ext cfg fK ei tkp gt ac])
    have sq: "seqinv (GE env ((rb, G' \<degree>\<degree> targs, uarg) # dps)) cs"
      by (rule copycons_sinv[OF maps.hyps(2) ext head_norm_eta_norm_satd])
    from maps.IH(2)[OF ts sq gt] obtain env' dps' where "x = El_E env' dps'"
      "tst (tvars_env (tyenv env) \<union> A) env' dps'" by blast
    with PP P1 show ?thesis by (blast intro: tst_mono)
  qed
next
  case (append_l xq x yq)
  from append_l.prems(1) have "tseq P xq" by (rule tseq_AppendE)
  moreover from append_l.prems(2) have "seqinv (GE env0 dps0) xq" by (rule seqinv_AppendE)
  ultimately show ?case by (rule append_l.IH[OF _ _ append_l.prems(3)])
next
  case (append_r yq x xq)
  from append_r.prems(1) have "tseq P yq" by (rule tseq_AppendE)
  moreover from append_r.prems(2) have "seqinv (GE env0 dps0) yq" by (rule seqinv_AppendE)
  ultimately show ?case by (rule append_r.IH[OF _ _ append_r.prems(3)])
qed (auto elim: tseq_AddUnifyE tseq_ItRightE)


subsection \<open>\<open>MATCH\<close>\<close>

lemma match_pair_tseq:
  assumes m: "okW (match_pair cfg env (rb, t, u) dps) s" and st: "strip_comb t = (Var v T, targs)"
    and sat: "rsat env rb t u" and nab: "\<not> is_Abs (fst (strip_comb u))"
    and cfg: "cfg_alg cfg = alg" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env ((rb, t, u) # dps)" and gt: "gtyped env ((rb, t, u) # dps)"
    and ac: "b \<longrightarrow> acyc env"
  shows "tseq (tvars_env (tyenv env) \<union> A) s"
proof -
  from m st have mc: "okW (mc cfg (fst v) env (v, T) rb targs u env dps) s" by (simp add: match_pair_def)
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have "msat (Some t) env rb u" using sat nab by (simp add: msat_def)
  from mc_tseq[OF mc this _ cfg fK, of A] ei tk gt ac t show ?thesis by simp
qed

lemma match_sat_tseq:
  assumes m: "okW (match_sat cfg env dp dps) s" and ms: "msat_ok env dp"
    and cfg: "cfg_alg cfg = alg" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env (dp # dps)" and gt: "gtyped env (dp # dps)"
    and acy: "b \<longrightarrow> acyc env"
  shows "tseq (tvars_env (tyenv env) \<union> A) s"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A"
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
  from sat ed have sat': "rsat env rb' t' u'" and nab: "\<not> is_Abs (fst (strip_comb u'))" by (simp_all add: Es_def)
  have d: "dstep env (dp # dps) env ((rb', t', u') # dps)"
    using dstep_frame[OF dstep_eta_expand[OF st bt len, of rb u], of dps] ed by (simp add: dp Es_def)
  have gt': "gtyped env ((rb', t', u') # dps)" by (rule gtyped_dstep[OF d gt])
  have kp: "ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
    using tk by (auto simp: tknown_def dp)
  have tkd: "tknown A env dps" using tknown_Cons tk by blast
  have kT: "tvars T \<subseteq> ?KN" using kp strip_comb_apps[OF st] by (auto simp: ttvars_apps)
  have ac: "tacyc (tyenv env)" using einvD(6)[OF ei] by simp
  from mf_binder_types_sound[OF bt refl ac] kT have kTs: "\<forall>U\<in>set Ts. tvars U \<subseteq> ?KN" by blast
  have kEs: "\<forall>U\<in>set Es. tvars U \<subseteq> ?KN" using kTs by (auto simp: Es_def dest: in_set_dropD)
  have "ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> ?KN"
    using kp kEs by (auto simp: t'_def u'_def rb'_def ttvars_apps btvars_def)
  then have "tknown A env ((rb', t', u') # dps)"
    using tknown_Cons[of A env "(rb', t', u')" dps] tkd kE by (auto simp: tknown_pair)
  from match_pair_tseq[OF mp[folded Es_def, unfolded ed] st' sat' nab cfg fK ei this gt' acy] show ?thesis .
qed

lemma sorts_ok_known_TVar:
  assumes ei: "einv A K (tyonly env)" and k: "tvars (TVar v S) \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "cert_typ alg ar (TVar v S)"
proof -
  have tc: "tcert alg (tvars_env (tyenv env) \<union> A)" using einvD(10)[OF ei] by simp
  have "(v, S) \<in> tvars_env (tyenv env) \<union> A" using k by simp
  from tc[unfolded tcert_def] this have "sort_ok alg (snd (v, S))" by (rule bspec)
  then have "sort_ok alg S" by simp
  then show ?thesis by (simp add: cert_typ_def)
qed

lemma match_eta_tseq:
  assumes m: "okW (match_eta cfg env dp dps B j tail) s" and tl: "tseq (tvars_env (tyenv env) \<union> A) tail"
    and ms: "\<And>env'. extends env env' \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> msat_ok env' dp"
    and kB: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" and tvB: "is_TVar B"
    and cfg: "cfg_alg cfg = alg" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env (dp # dps)" and gt: "gtyped env (dp # dps)"
    and ac: "b \<longrightarrow> acyc env"
  shows "tseq (tvars_env (tyenv env) \<union> A) s"
proof (cases "j = 0")
  case True
  with m obtain s' where "okW (match_sat cfg env dp dps) s'" and s: "s = S_Append s' tail"
    by (auto simp: match_eta_def)
  from match_sat_tseq[OF this(1) ms[OF extends_refl refl] cfg fK ei tk gt ac] tl show ?thesis
    by (simp add: s tseq.Append)
next
  case False
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by fastforce
  note g' = gentvars_props[OF g] and gs = gentvars_simps[OF g]
  from okW_handle_CANTUNIFY[OF m[unfolded match_eta_def, simplified False if_False g prod.case]]
  consider (ok) env2 s' where "okW (cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1) env2"
      "okW (match_sat cfg env2 dp dps) s'" "s = S_Append s' tail"
    | (cu) "s = tail"
    by auto
  then show ?thesis
  proof cases
    case (ok env2 s')
    let ?A' = "A \<union> ntv Rs" and ?K' = "K \<union> ntv Rs"
    have ei1: "einv ?A' ?K' (tyonly env1)" by (rule einv_gentvars[OF ei gentvars_tyonly[OF g]])
    have fK': "finite ?K'" using fK by simp
    have Rs: "Rs \<noteq> []" using g'(4) by simp
    have kR: "tvars (foldr fun_type (tl Rs) (hd Rs)) \<subseteq> tvars_env (tyenv env1) \<union> ?A'"
      using Rs tvars_ntv[of _ Rs] by (auto simp: tvars_funs dest: list.set_sel)
    have cR: "cert_typ alg ar (foldr fun_type (tl Rs) (hd Rs))"
      using Rs cert_ntv[OF g] by (auto simp: cert_typ_funs dest: list.set_sel)
    obtain bv bS where B: "B = TVar bv bS" using tvB by (cases B) auto
    have cB: "cert_typ alg ar B" using sorts_ok_known_TVar[OF ei kB[unfolded B]] B by simp
    have kB1: "tvars B \<subseteq> tvars_env (tyenv env1) \<union> ?A'" using kB g'(2) by auto
    note c = tyinv_cunify_c[OF ok(1)[unfolded cfg] fK' ei1 kB1 cB kR cR]
    note cs = cunify_types_sound[OF ok(1)]
    have ext1: "extends env env1" by (rule extends_tenv_eq) (use g' in simp_all)
    have ext: "extends env env2" by (rule extends_trans[OF ext1 cs(2)])
    have te: "tenv env2 = tenv env" using cs(1) g'(1) by simp
    have gt2: "gtyped env2 (dp # dps)" by (rule gtyped_dstep[OF dstep_tenv[OF te ext] gt])
    have sub: "tvars_env (tyenv env) \<union> A \<subseteq> tvars_env (tyenv env2) \<union> ?A'" using c(3) g'(2) by auto
    have "etvars env \<subseteq> tvars_env (tyenv env) \<union> A" using tk by (simp add: tknown_def)
    then have "etvars env2 \<subseteq> tvars_env (tyenv env2) \<union> ?A'"
      using etvars_tenv[OF te] sub by blast
    then have tk2: "tknown ?A' env2 (dp # dps)" by (rule tknown_lift[OF tk sub])
    have "tseq (tvars_env (tyenv env2) \<union> ?A') s'"
      by (rule match_sat_tseq[OF ok(2) ms[OF ext te] cfg fK' c(1) tk2 gt2]) (use ac acyc_tenv[OF te] in simp)
    then have "tseq (tvars_env (tyenv env) \<union> A) s'" by (rule tseq_mono[OF _ sub])
    with tl show ?thesis by (simp add: ok(3) tseq.Append)
  qed (use tl in simp)
qed

theorem MATCH_tseq:
  assumes m: "okW (MATCH cfg env dp dps) s" and mo: "MATCH_ok env dp"
    and cfg: "cfg_alg cfg = alg" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env (dp # dps)" and gt: "gtyped env (dp # dps)"
    and ac: "b \<longrightarrow> acyc env"
  shows "tseq (tvars_env (tyenv env) \<union> A) s"
proof -
  let ?P = "tvars_env (tyenv env) \<union> A"
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
  have kT: "tvars T \<subseteq> ?P" using tk strip_comb_apps[OF st] by (auto simp: tknown_def dp ttvars_apps)
  have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  from body_type_term[OF ti refl kT] B have kB: "tvars B \<subseteq> ?P" by (auto simp: return_def)
  show ?thesis
  proof (cases "is_TVar B")
    case True
    with r have f: "okW (foldrW (match_eta cfg env dp dps B) (arity_guesses cfg B) S_Empty) s" by simp
    have "tseq ?P b \<longrightarrow> tseq ?P s'" if "okW (foldrW (match_eta cfg env dp dps B) js b) s'" for js b s'
      using that
    proof (induction rule: okW_foldrW_induct)
      case (Cons j js b b1 b')
      show ?case
      proof
        assume "tseq ?P b"
        with Cons.IH have "tseq ?P b1" by simp
        from match_eta_tseq[OF Cons.hyps(2) this ms kB True cfg fK ei tk gt ac] show "tseq ?P b'" .
      qed
    qed simp
    with f show ?thesis by (blast intro: tseq.Empty)
  next
    case False
    with r have "okW (match_sat cfg env dp dps) s" by simp
    from match_sat_tseq[OF this ms[OF extends_refl refl] cfg fK ei tk gt ac] show ?thesis .
  qed
qed

end

theorem MATCH_tyinv:
  assumes cfg: "cfg_alg cfg = alg" and ni: "ninv env (dp # dps)" and sh: "frs_shape dp"
    and m: "okW (MATCH cfg env dp dps) ms" and ev: "ev cfg ms (El_E env2 dps2)"
  shows "\<exists>A K. tyinv A K env2 dps2"
proof -
  from ni obtain A K where gt: "gtyped env (dp # dps)" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env (dp # dps)"
    unfolding ninv_def tyinv_def by blast
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have mo: "MATCH_ok env dp" using ninv_MATCH_ok[OF ni[unfolded dp] sh[unfolded dp]] by (simp add: dp)
  have sq: "seqinv (GE env (dp # dps)) ms" by (rule MATCH_sound[OF m mo])
  have ts: "tseq False (tvars_env (tyenv env) \<union> A) ms" by (rule MATCH_tseq[OF m mo cfg fK ei tk gt]) simp
  from tseq_ev[OF cfg ev ts sq gt] obtain env' dps' where "El_E env2 dps2 = El_E env' dps'"
    "tst False (tvars_env (tyenv env) \<union> A) env' dps'" by blast
  then show ?thesis using tst_tyinv by simp
qed


subsection \<open>The search\<close>

text \<open>
  The soundness of the search for names with several types: every element of the enumeration of
  \<^const>\<open>hounifiers\<close> is a step from the input pairs, if the input pairs are well-typed at every
  certified solution of a well-formed type environment whose type variables are known
  (\<^const>\<open>ninv\<close>). There is no hypothesis on the names of the variables.
\<close>

theorem hounifiers_ev_sound_loose:
  assumes cfg: "cfg_alg cfg = alg"
    and NI0: "ninv env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and ev: "ev cfg (hounifiers rb env tus) x"
  shows "elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x"
  by (rule hounifiers_ev_sound_ninv[OF cfg NI0 MATCH_tyinv[OF cfg] ev])

end

end
