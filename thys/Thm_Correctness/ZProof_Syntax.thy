section \<open>Syntactic invariants of tight proofs\<close>

theory ZProof_Syntax
  imports ZProof_Bicompose Proof_Indices
begin

text \<open>
  The lifting of tight proofs is correct for proofs without proof constants whose schematic
  (type) variables have non-negative indices (\<open>zvalid_zlift_proof\<close>). The tight proofs of
  lifted rules and of the results of compositions have these properties again, if the proofs
  of the theorems have them, the indices of the theorems are not negative and the environment
  of the composition binds terms and types whose indices are not negative.
\<close>

definition tnn :: "ptyp \<Rightarrow> bool" where
  "tnn T \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. 0 \<le> snd v)"

definition zinv :: "zproof \<Rightarrow> bool" where
  "zinv p \<longleftrightarrow> zconst_free p \<and> zprf_all zterm_ok ztyp_ok p"


subsection \<open>Types\<close>

lemma tnn_simps [simp]:
  "tnn (Type a Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. tnn T)" "tnn (TFree a S)" "tnn (TVar v S) \<longleftrightarrow> 0 \<le> snd v"
  by (auto simp: tnn_def)

lemma ztyp_ok_tnn: "ztyp_ok T \<longleftrightarrow> tnn (typ_of T)"
  by (simp add: ztyp_ok_def tnn_def)

lemma ztyp_ok_simps [simp]:
  "ztyp_ok (ZFun T U) \<longleftrightarrow> ztyp_ok T \<and> ztyp_ok U" "ztyp_ok ZProp" "ztyp_ok (ZType0 c)"
  "ztyp_ok (ZType1 c T) \<longleftrightarrow> ztyp_ok T" "ztyp_ok (ZType c Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. ztyp_ok T)"
  "ztyp_ok (ZTVar v S) \<longleftrightarrow> snd v = -1 \<or> 0 \<le> snd v"
  by (auto simp: ztyp_ok_tnn propT_def)

lemma tnn_typ_of_ztyp_of: "tnn T \<Longrightarrow> typ_of (ztyp_of T) = T"
  by (rule typ_of_ztyp_of) (auto simp: tnn_def integer_nonneg_ne_m1)

lemma ztyp_ok_ztyp_of: "tnn T \<Longrightarrow> ztyp_ok (ztyp_of T)"
  using tnn_typ_of_ztyp_of[of T] by (simp add: ztyp_ok_tnn)

lemma tvars_incr_tvar: "(v, S) \<in> tvars (incr_tvar inc T) \<Longrightarrow> \<exists>w. (w, S) \<in> tvars T \<and> snd v = snd w + inc"
  by (induction inc T rule: incr_tvar.induct) fastforce+

lemma ztyp_ok_zincr_tvar:
  assumes "ztyp_ok T" "0 \<le> inc"
  shows "ztyp_ok (zincr_tvar inc T)"
  unfolding ztyp_ok_def typ_of_zincr_tvar[OF assms]
proof (clarify)
  fix v S assume "(v, S) \<in> tvars (incr_tvar inc (typ_of T))"
  from tvars_incr_tvar[OF this] obtain w where "(w, S) \<in> tvars (typ_of T)" "snd v = snd w + inc" by blast
  with assms show "0 \<le> snd v" by (force simp: ztyp_ok_def)
qed

lemma ztyp_ok_ZFuns: "ztyp_ok (ZFuns Ts T) \<longleftrightarrow> (\<forall>U\<in>set Ts. ztyp_ok U) \<and> ztyp_ok T"
  by (induction Ts) (simp_all add: ZFuns_def)

lemma ztyp_ok_zsubst_type:
  "ztyp_ok T \<Longrightarrow> (\<And>v S U. f (v, S) = Some U \<Longrightarrow> ztyp_ok U) \<Longrightarrow> ztyp_ok (zsubst_type f T)"
proof (induction T)
  case (ZTVar v S)
  then show ?case by (cases "f (v, S)") auto
qed auto

context pure_sig
begin

lemma tnn_tnorm: "tacyc \<theta> \<Longrightarrow> \<forall>p\<in>tvars_env \<theta>. 0 \<le> snd (fst p) \<Longrightarrow> tnn T \<Longrightarrow> tnn (tnorm \<theta> T)"
  using tvars_tnorm[of \<theta> T] unfolding tnn_def by fastforce

lemma tyenv_ok_nn: "\<forall>p\<in>tvars_env \<theta>. 0 \<le> snd (fst p) \<Longrightarrow> tyenv_ok \<theta>"
  unfolding tyenv_ok_def tnoneg_def tvars_env_def by (fastforce simp: integer_nonneg_ne_m1)

lemma ztyp_ok_znorm_type:
  assumes "znorm_type \<theta> T = returnZ T'" "tacyc \<theta>" "\<forall>p\<in>tvars_env \<theta>. 0 \<le> snd (fst p)" "ztyp_ok T"
  shows "ztyp_ok T'"
proof -
  have "typ_of T' = tnorm \<theta> (typ_of T)"
    using znorm_type_success[OF assms(1,2) tyenv_ok_nn[OF assms(3)]] by blast
  moreover have "tnn (typ_of T)" using assms(4) by (simp add: ztyp_ok_tnn)
  ultimately show ?thesis using tnn_tnorm[OF assms(2,3)] by (simp add: ztyp_ok_tnn)
qed

end


subsection \<open>Terms\<close>

lemma zterm_ok_zcombound [simp]: "zterm_ok (zcombound t n k) \<longleftrightarrow> zterm_ok t"
  by (induction t n k rule: zcombound.induct) simp_all

lemma zterm_ok_zlift_term:
  "zterm_ok t \<Longrightarrow> \<forall>T\<in>set Ts. ztyp_ok T \<Longrightarrow> 0 \<le> inc \<Longrightarrow> zterm_ok (zlift_term inc Ts lev t)"
  by (induction inc Ts lev t rule: zlift_term.induct) (auto simp: ztyp_ok_zincr_tvar ztyp_ok_ZFuns)

lemma zterm_ok_zlift_term':
  "zterm_ok t \<Longrightarrow> \<forall>T\<in>set Ts. ztyp_ok T \<Longrightarrow> 0 \<le> inc \<Longrightarrow> zterm_ok (zlift_term' inc Ts lev t)"
  by (simp add: zlift_term'_def zterm_ok_zlift_term)

lemma zterm_ok_zincr_bv [simp]: "zterm_ok (zincr_bv inc lev t) \<longleftrightarrow> zterm_ok t"
  by (induction inc lev t rule: zincr_bv.induct) simp_all

lemma zterm_ok_zsubst_bound: "zterm_ok arg \<Longrightarrow> zterm_ok t \<Longrightarrow> zterm_ok (zsubst_bound arg lev t)"
  by (induction arg lev t rule: zsubst_bound.induct) (simp_all add: zincr_boundvars_def)

lemma zterm_ok_subst_term_bound: "zterm_ok u \<Longrightarrow> zterm_ok t \<Longrightarrow> zterm_ok (subst_term_bound u t)"
  by (simp add: subst_term_bound_def zterm_ok_zsubst_bound)

lemma zterm_ok_beta_norm_term:
  assumes "beta_norm_term t = Some t'"
  shows "zterm_ok t \<Longrightarrow> zterm_ok t'"
  using assms
proof (induction t t' rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn t t')
  note h = "1.hyps" and IH = "1.IH" and ok = "1.prems"
  show ?case
  proof (cases t)
    case (ZAbs a T b)
    with h obtain b' where "bn b = Some b'" "t' = ZAbs a T b'" by (auto simp: bind_eq_Some_conv)
    with IH ok ZAbs show ?thesis by auto
  next
    case (ZApp g u)
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbs b U body")
      case True
      then obtain b U body where g: "g = ZAbs b U body" by blast
      have "bn (subst_term_bound u body) = Some t'" using h ZApp g by simp
      with IH ok ZApp g show ?thesis by (auto simp: zterm_ok_subst_term_bound)
    next
      case False
      with h ZApp obtain nf where hf: "bn g = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (bn u) (\<lambda>nu. Some (ZApp nf nu))) = Some t'"
        by (cases g) (auto simp: bind_eq_Some_conv)
      have of: "zterm_ok nf" using IH[OF hf] ok ZApp by simp
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbs b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbs b U body" by blast
        have "bn (subst_term_bound u body) = Some t'" using rest nfb by simp
        with IH of nfb ok ZApp show ?thesis by (auto simp: zterm_ok_subst_term_bound)
      next
        case False
        with rest obtain nu where hu: "bn u = Some nu" and t': "t' = ZApp nf nu"
          by (cases nf) (auto simp: bind_eq_Some_conv)
        with IH of ok ZApp show ?thesis by auto
      qed
    qed
  qed (use h ok in auto)
qed

lemma zterm_ok_zsubst_term:
  "zterm_ok t \<Longrightarrow> (\<And>T. ztyp_ok T \<Longrightarrow> ztyp_ok (tf T)) \<Longrightarrow> (\<And>v u. vf v = Some u \<Longrightarrow> zterm_ok u) \<Longrightarrow>
    zterm_ok (zsubst_term tf vf t)"
  by (induction tf vf t rule: zsubst_term.induct) (auto split: option.splits)

lemma zterm_ok_zren_term [simp]: "zterm_ok (zren_term r m t) \<longleftrightarrow> zterm_ok t"
  by (induction r m t rule: zren_term.induct) simp_all

text \<open>Conversion:\<close>

context pure_sig
begin

lemma ztargs_tvars:
  assumes u: "ztargs c T = return Us" and U: "U \<in> set Us"
  shows "tvars U \<subseteq> tvars T"
proof (cases "c = STR ''Pure.imp''")
  case True
  with assms show ?thesis by (simp add: ztargs_def return_def)
next
  case ni: False
  show ?thesis
  proof (cases "c = STR ''Pure.all''")
    case True
    with ni assms show ?thesis
      by (auto simp: ztargs_def return_def raise_def split: ptyp.splits list.splits)
  next
    case na: False
    from u ni na obtain D where ex: "\<exists>\<rho>. T = tsubst \<rho> D" and Us: "Us = map (targ D T) (tparams D)"
      by (auto simp: ztargs_def return_def raise_def split: option.splits if_splits)
    from ex obtain \<rho> where T: "T = tsubst \<rho> D" by blast
    from U Us obtain p where p: "p \<in> tvars D" "U = targ D T p" by (auto simp: set_tparams)
    obtain v S where vS: "p = (v, S)" by (cases p)
    have "U = \<rho> v S" using targ_eq[OF T] p vS by simp
    then show ?thesis using p(1) vS T by (auto simp: tvars_tsubst)
  qed
qed

lemma zterm_ok_zterm_of:
  "zterm_of ztargs t = returnZ z \<Longrightarrow> \<forall>v\<in>vars t. 0 \<le> snd (fst v) \<Longrightarrow> \<forall>U\<in>typs t. tnn U \<Longrightarrow> zterm_ok z"
proof (induction ztargs t arbitrary: z rule: zterm_of.induct)
  case (1 x T)
  then show ?case by (auto simp: returnZ_def ztyp_ok_ztyp_of)
next
  case (2 xi T)
  then show ?case by (cases xi) (auto simp: returnZ_def ztyp_ok_ztyp_of)
next
  case (4 c T)
  then obtain Us where u: "ztargs c T = return Us"
    and z: "z = (case Us of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Us))"
    by (auto simp: Z_ok_simps returnZ_def return_def split: option.splits)
  have "ztyp_ok (ztyp_of U)" if "U \<in> set Us" for U
  proof (rule ztyp_ok_ztyp_of)
    show "tnn U" using ztargs_tvars[OF u that] "4.prems"(3) by (fastforce simp: tnn_def)
  qed
  then show ?case unfolding z by (cases Us rule: remdups_adj.cases) auto
next
  case (5 a T b)
  then show ?case by (auto simp: Z_ok_simps returnZ_def ztyp_ok_ztyp_of)
next
  case (6 t u)
  show ?case
  proof (cases "match_of_class (t $ u)")
    case (Some Tc)
    show ?thesis
    proof (cases "t $ u = mk_of_class (fst Tc) (snd Tc)")
      case True
      have "returnZ (ZOfclass (ztyp_of (fst Tc)) (snd Tc)) = returnZ z"
        using "6.prems"(1) unfolding zterm_of.simps(6) Some option.case if_P[OF True] .
      then have z: "z = ZOfclass (ztyp_of (fst Tc)) (snd Tc)" by simp
      have "Type STR ''itself'' [fst Tc] \<in> typs (t $ u)" using True by (simp add: mk_of_class_def)
      then have "tnn (fst Tc)" using "6.prems"(3) by (auto simp: tnn_def)
      then show ?thesis by (simp add: z ztyp_ok_ztyp_of)
    next
      case False
      with Some "6.prems"(1) obtain t' u' where tu: "zterm_of ztargs t = returnZ t'" "zterm_of ztargs u = returnZ u'"
        "z = ZApp t' u'"
        by (auto simp: Z_ok_simps returnZ_def)
      with "6.hyps"(3)[OF Some False tu(1)] "6.hyps"(4)[OF Some False tu(1)[unfolded returnZ_def] tu(2)] "6.prems"(2,3)
      show ?thesis by auto
    qed
  next
    case None
    with "6.prems"(1) obtain t' u' where tu: "zterm_of ztargs t = returnZ t'" "zterm_of ztargs u = returnZ u'"
      "z = ZApp t' u'"
      by (auto simp: Z_ok_simps returnZ_def)
    with "6.hyps"(1)[OF None tu(1)] "6.hyps"(2)[OF None tu(1)[unfolded returnZ_def] tu(2)] "6.prems"(2,3)
    show ?thesis by auto
  qed
qed (simp add: returnZ_def)

end


subsection \<open>Normalization of terms\<close>

text \<open>The terms and types bound by an environment have non-negative indices:\<close>

definition zenv_nn :: "env \<Rightarrow> bool" where
  "zenv_nn env \<longleftrightarrow> (\<forall>p\<in>tvars_env (tyenv env). 0 \<le> snd (fst p)) \<and>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> (\<forall>v\<in>vars u. 0 \<le> snd (fst v)) \<and> (\<forall>T\<in>typs u. tnn T))"

context prf_sig
begin

lemma zterm_ok_znorm_term_aux:
  assumes "znorm_term_aux x = Some r"
  shows "r = ZOk t' \<Longrightarrow> fst (fst x) = ztargs \<Longrightarrow> snd (fst x) = env \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> zenv_nn env \<Longrightarrow>
    zterm_ok (snd x) \<Longrightarrow> zterm_ok t'"
  using assms
proof (induction x r arbitrary: t' rule: znorm_term_aux.raw_induct[rotated, consumes 1])
  case (1 nt x r)
  let ?\<theta> = "tyenv env"
  note r = "1.prems"(1) and T = "1.prems"(2) and E = "1.prems"(3) and tac = "1.prems"(4)
    and en = "1.prems"(5) and ok = "1.prems"(6)
  obtain t where x: "x = ((ztargs, env), t)" using T E by (metis prod.collapse)
  have h: "(case t of
      ZVar xi T \<Rightarrow> do {
        r \<leftarrow> zlookup ztargs env xi T;
        case r of
          Some u \<Rightarrow> nt ((ztargs, env), u)
        | None \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; returnZ (ZVar xi T')}}
    | ZConst1 a T \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; returnZ (ZConst1 a T')}
    | ZConst a Ts \<Rightarrow> do {Ts' \<leftarrow> mapZ (znorm_type ?\<theta>) Ts; returnZ (ZConst a Ts')}
    | ZAbs a T b \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; b' \<leftarrow> nt ((ztargs, env), b); returnZ (ZAbs a T' b')}
    | ZApp g u \<Rightarrow>
        (case g of
          ZAbs _ _ body \<Rightarrow> nt ((ztargs, env), subst_term_bound u body)
        | _ \<Rightarrow> do {
            nf \<leftarrow> nt ((ztargs, env), g);
            case nf of
              ZAbs _ _ body \<Rightarrow> nt ((ztargs, env), subst_term_bound u body)
            | _ \<Rightarrow> do {nu \<leftarrow> nt ((ztargs, env), u); returnZ (ZApp nf nu)}})
    | ZOfclass T c \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; returnZ (ZOfclass T' c)}
    | t \<Rightarrow> returnZ t) = returnZ t'"
    using "1.hyps" r unfolding x prod.sel by (simp add: returnZ_def)
  have IH: "zterm_ok u'" if "nt ((ztargs, env), u) = returnZ u'" "zterm_ok u" for u u'
  proof -
    have "fst (fst ((ztargs, env), u)) = ztargs" "snd (fst ((ztargs, env), u)) = env" by simp_all
    from "1.IH"[OF that(1)[unfolded returnZ_def] HOL.refl this tac en] that(2) show ?thesis by simp
  qed
  have tn: "\<forall>p\<in>tvars_env ?\<theta>. 0 \<le> snd (fst p)" using en by (simp add: zenv_nn_def)
  have nT: "ztyp_ok T'" if "znorm_type ?\<theta> T = returnZ T'" "ztyp_ok T" for T T'
    by (rule ztyp_ok_znorm_type[OF that(1) tac tn that(2)])
  have "zterm_ok t'"
  proof (cases t)
    case (ZVar xi T)
    from h ZVar obtain lr where lk: "zlookup ztargs env xi T = returnZ lr"
      and rest: "(case lr of Some u \<Rightarrow> nt ((ztargs, env), u)
        | None \<Rightarrow> bindZ (znorm_type ?\<theta> T) (\<lambda>T'. returnZ (ZVar xi T'))) = returnZ t'"
      by (auto simp: bindZ_eq_returnZ)
    from lk tac show ?thesis
    proof (cases rule: zlookup_success)
      case None
      from rest None obtain T' where T': "znorm_type ?\<theta> T = returnZ T'" and t': "t' = ZVar xi T'"
        by (auto simp: bindZ_eq_returnZ)
      with nT ok ZVar x show ?thesis by simp
    next
      case (Some U u u')
      have "(\<forall>v\<in>vars u. 0 \<le> snd (fst v)) \<and> (\<forall>T\<in>typs u. tnn T)"
        using en Some(1) unfolding zenv_nn_def by blast
      with zterm_ok_zterm_of[OF Some(3)] have "zterm_ok u'" by blast
      moreover have "nt ((ztargs, env), u') = returnZ t'" using rest Some(2) by simp
      ultimately show ?thesis using IH by blast
    qed
  next
    case (ZConst1 a T)
    with h obtain T' where "znorm_type ?\<theta> T = returnZ T'" "t' = ZConst1 a T'" by (auto simp: bindZ_eq_returnZ)
    with nT ok ZConst1 x show ?thesis by simp
  next
    case (ZConst a Ts)
    with h obtain Ts' where l: "list_all2 (\<lambda>T T'. znorm_type ?\<theta> T = returnZ T') Ts Ts'" and t': "t' = ZConst a Ts'"
      by (auto simp: bindZ_eq_returnZ mapZ_eq_returnZ)
    have "\<forall>T'\<in>set Ts'. ztyp_ok T'"
    proof
      fix T' assume "T' \<in> set Ts'"
      from list_all2_ex2[OF l this] obtain T where "T \<in> set Ts" "znorm_type ?\<theta> T = returnZ T'" by blast
      with nT ok ZConst x show "ztyp_ok T'" by simp
    qed
    then show ?thesis by (simp add: t')
  next
    case (ZAbs a T b)
    with h obtain T' b' where "znorm_type ?\<theta> T = returnZ T'" "nt ((ztargs, env), b) = returnZ b'" "t' = ZAbs a T' b'"
      by (auto simp: bindZ_eq_returnZ)
    with nT IH ok ZAbs x show ?thesis by simp
  next
    case (ZOfclass T c)
    with h obtain T' where "znorm_type ?\<theta> T = returnZ T'" "t' = ZOfclass T' c" by (auto simp: bindZ_eq_returnZ)
    with nT ok ZOfclass x show ?thesis by simp
  next
    case (ZApp g u)
    have og: "zterm_ok g" and ou: "zterm_ok u" using ok ZApp x by simp_all
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbs b U body")
      case True
      then obtain b U body where g: "g = ZAbs b U body" by blast
      have "nt ((ztargs, env), subst_term_bound u body) = returnZ t'" using h ZApp g by simp
      moreover have "zterm_ok (subst_term_bound u body)" using og ou g by (simp add: zterm_ok_subst_term_bound)
      ultimately show ?thesis by (rule IH)
    next
      case False
      with h ZApp obtain nf where hf: "nt ((ztargs, env), g) = returnZ nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> nt ((ztargs, env), subst_term_bound u body)
          | _ \<Rightarrow> bindZ (nt ((ztargs, env), u)) (\<lambda>nu. returnZ (ZApp nf nu))) = returnZ t'"
        by (cases g) (auto simp: bindZ_eq_returnZ)
      have onf: "zterm_ok nf" by (rule IH[OF hf og])
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbs b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbs b U body" by blast
        have "nt ((ztargs, env), subst_term_bound u body) = returnZ t'" using rest nfb by simp
        moreover have "zterm_ok (subst_term_bound u body)" using onf ou nfb by (simp add: zterm_ok_subst_term_bound)
        ultimately show ?thesis by (rule IH)
      next
        case False
        with rest obtain nu where hu: "nt ((ztargs, env), u) = returnZ nu" and t': "t' = ZApp nf nu"
          by (cases nf) (auto simp: bindZ_eq_returnZ)
        with IH[OF hu ou] onf show ?thesis by simp
      qed
    qed
  qed (use h ok x in auto)
  then show ?case .
qed

theorem zterm_ok_znorm_term:
  assumes "znorm_term ztargs env t = returnZ t'" "tacyc (tyenv env)" "zenv_nn env" "zterm_ok t"
  shows "zterm_ok t'"
proof (cases "env_is_empty env")
  case True
  with assms(1) have "beta_norm_term t = Some t'" by (simp add: znorm_term_def liftOZ_eq_returnZ)
  from zterm_ok_beta_norm_term[OF this assms(4)] show ?thesis .
next
  case False
  with assms(1) have "znorm_term_aux ((ztargs, env), t) = Some (ZOk t')" by (simp add: znorm_term_def returnZ_def)
  from zterm_ok_znorm_term_aux[OF this HOL.refl _ _ assms(2,3)] assms(4) show ?thesis by simp
qed

end


subsection \<open>Proofs\<close>

lemma raiseZ_neq_returnZ [simp]: "raiseZ e \<noteq> returnZ x"
  by (simp add: raiseZ_def returnZ_def)

lemma zinv_simps [simp]:
  "zinv (ZAbst a T p) \<longleftrightarrow> ztyp_ok T \<and> zinv p" "zinv (ZAbsp a t p) \<longleftrightarrow> zterm_ok t \<and> zinv p"
  "zinv (ZAppt p t) \<longleftrightarrow> zinv p \<and> zterm_ok t" "zinv (ZAppp p q) \<longleftrightarrow> zinv p \<and> zinv q"
  "zinv ZNop" "zinv (ZBoundp i)" "zinv (ZHyp h)" "zinv (OFCLASSp T c) \<longleftrightarrow> ztyp_ok T" "zinv (ZConstp x) \<longleftrightarrow> False"
  by (auto simp: zinv_def)

lemma zinv_ZAppps: "zinv (ZAppps p qs) \<longleftrightarrow> zinv p \<and> (\<forall>q\<in>set qs. zinv q)"
  unfolding ZAppps_def by (induction qs arbitrary: p) auto

lemma zinv_ZAppts: "zinv (ZAppts p ts) \<longleftrightarrow> zinv p \<and> (\<forall>t\<in>set ts. zterm_ok t)"
  unfolding ZAppts_def by (induction ts arbitrary: p) auto

lemma zinv_ZAbsps: "zinv (ZAbsps ts p) \<longleftrightarrow> (\<forall>t\<in>set ts. zterm_ok t) \<and> zinv p"
  by (induction ts) (auto simp: ZAbsps_def)

text \<open>Terms whose schematic variables and type variables have non-negative indices:\<close>

definition pnn :: "pterm \<Rightarrow> bool" where
  "pnn t \<longleftrightarrow> (\<forall>v\<in>vars t. 0 \<le> snd (fst v)) \<and> (\<forall>T\<in>typs t. tnn T)"

lemma pnn_simps [simp]: "pnn (s $ t) \<longleftrightarrow> pnn s \<and> pnn t" "pnn (Abs a T t) \<longleftrightarrow> tnn T \<and> pnn t"
  by (auto simp: pnn_def)

lemma (in pure_sig) zterm_ok_zterm_of_pnn: "zterm_of ztargs t = returnZ z \<Longrightarrow> pnn t \<Longrightarrow> zterm_ok z"
  using zterm_ok_zterm_of by (simp add: pnn_def)

text \<open>Lifting:\<close>

lemma zinv_zlift_prf:
  "zlift_prf inc Ts lev p = returnZ q \<Longrightarrow> zinv p \<Longrightarrow> \<forall>T\<in>set Ts. ztyp_ok T \<Longrightarrow> 0 \<le> inc \<Longrightarrow> zinv q"
  by (induction p arbitrary: lev q) (auto simp: bindZ_eq_returnZ zterm_ok_zlift_term' ztyp_ok_zincr_tvar)

lemma zinv_spine: "zinv (snd (snd (foldr zmk_app bs (a, b, ZBoundp c))))"
  by (induction bs) (auto simp: zmk_app_def split: prod.splits)

context pure_sig
begin

lemma zinv_zlift_prems:
  "zlift_prems ztargs inc k pf Ts bs i j G = returnZ q \<Longrightarrow> zinv pf \<Longrightarrow> 0 \<le> inc \<Longrightarrow>
    \<forall>T\<in>set Ts. ztyp_ok T \<Longrightarrow> pnn G \<Longrightarrow> zinv q"
proof (induction ztargs inc k pf Ts bs i j G arbitrary: q rule: zlift_prems.induct)
  case (1 inc k pf Ts bs i j c U A B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with "1.prems"(1) obtain A' p where A': "zterm_of ztargs A = returnZ A'"
      and p: "zlift_prems ztargs inc k pf Ts (True # bs) (i + 1) j B = returnZ p" and q: "q = ZAbsp (STR ''H'') A' p"
      by (auto simp: bindZ_eq_returnZ)
    have "zinv p" by (rule "1.hyps"(1)[OF True A'[unfolded returnZ_def] p]) (use "1.prems" in simp_all)
    moreover have "zterm_ok A'" by (rule zterm_ok_zterm_of_pnn[OF A']) (use "1.prems"(5) in simp)
    ultimately show ?thesis by (simp add: q)
  next
    case False
    with "1.prems" show ?thesis
      by (auto simp: bindZ_eq_returnZ zinv_ZAppps zinv_spine dest: zinv_zlift_prf)
  qed
next
  case (2 inc k pf Ts bs i j c U a T t)
  then show ?case
    by (auto simp: bindZ_eq_returnZ zinv_ZAppps zinv_spine ztyp_ok_ztyp_of split: if_splits
      dest: zinv_zlift_prf)
qed (auto simp: bindZ_eq_returnZ zinv_ZAppps zinv_spine dest: zinv_zlift_prf)

theorem zinv_zlift_proof:
  assumes "zlift_proof ztargs G inc prems pf = returnZ q" "zinv pf" "0 \<le> inc" "pnn G" "\<forall>A\<in>set prems. pnn A"
  shows "zinv q"
proof -
  from assms(1) obtain As p where As: "list_all2 (\<lambda>A z. zterm_of ztargs A = returnZ z) prems As"
    and p: "zlift_prems ztargs inc (integer_of_nat (length prems)) pf [] [] 0 0 G = returnZ p"
    and q: "q = ZAbsps As p"
    by (auto simp: zlift_proof_def bindZ_eq_returnZ mapZ_eq_returnZ)
  have "\<forall>z\<in>set As. zterm_ok z"
  proof
    fix z assume "z \<in> set As"
    from list_all2_ex2[OF As this] obtain A where "A \<in> set prems" "zterm_of ztargs A = returnZ z" by blast
    with assms(5) show "zterm_ok z" by (blast intro: zterm_ok_zterm_of_pnn)
  qed
  moreover have "zinv p" by (rule zinv_zlift_prems[OF p assms(2,3)]) (use assms(4) in simp_all)
  ultimately show ?thesis by (simp add: q zinv_ZAbsps)
qed

end

text \<open>Instantiation, \<open>\<beta>\<close>-normalization and renaming:\<close>

lemma zinv_map_zproof:
  "map_zproof tf tm p = returnZ p' \<Longrightarrow> zinv p \<Longrightarrow> (\<And>T. ztyp_ok T \<Longrightarrow> ztyp_ok (tf T)) \<Longrightarrow>
    (\<And>t t'. tm t = returnZ t' \<Longrightarrow> zterm_ok t \<Longrightarrow> zterm_ok t') \<Longrightarrow> zinv p'"
  by (induction p arbitrary: p') (auto simp: bindZ_eq_returnZ)

lemma zinv_zsubst_proof_bound: "zterm_ok arg \<Longrightarrow> zinv p \<Longrightarrow> zinv (zsubst_proof_bound arg lev p)"
  by (induction arg lev p rule: zsubst_proof_bound.induct) (auto simp: zterm_ok_zsubst_bound)

lemma zinv_subst_proof_bound: "zterm_ok u \<Longrightarrow> zinv p \<Longrightarrow> zinv (subst_proof_bound u p)"
  by (simp add: subst_proof_bound_def zinv_zsubst_proof_bound)

lemma zinv_beta_norm_prooft:
  assumes "beta_norm_prooft p = Some p'"
  shows "zinv p \<Longrightarrow> zinv p'"
  using assms
proof (induction p p' rule: beta_norm_prooft.raw_induct[rotated, consumes 1])
  case (1 bn p p')
  note h = "1.hyps" and IH = "1.IH" and ok = "1.prems"
  show ?case
  proof (cases p)
    case (ZAbst a T q)
    with h obtain q' where "bn q = Some q'" "p' = ZAbst a T q'" by (auto simp: bind_eq_Some_conv)
    with IH ok ZAbst show ?thesis by auto
  next
    case (ZAppt g u)
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbst b U body")
      case True
      then obtain b U body where g: "g = ZAbst b U body" by blast
      have "bn (subst_proof_bound u body) = Some p'" using h ZAppt g by simp
      with IH ok ZAppt g show ?thesis by (auto simp: zinv_subst_proof_bound)
    next
      case False
      with h ZAppt obtain nf where hf: "bn g = Some nf"
        and rest: "(case nf of ZAbst _ _ body \<Rightarrow> bn (subst_proof_bound u body)
          | _ \<Rightarrow> Option.bind (beta_norm_term u) (\<lambda>nu. Some (ZAppt nf nu))) = Some p'"
        by (cases g) (auto simp: bind_eq_Some_conv)
      have onf: "zinv nf" using IH[OF hf] ok ZAppt by simp
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbst b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbst b U body" by blast
        have "bn (subst_proof_bound u body) = Some p'" using rest nfb by simp
        with IH onf nfb ok ZAppt show ?thesis by (auto simp: zinv_subst_proof_bound)
      next
        case False
        with rest obtain nu where hu: "beta_norm_term u = Some nu" and p': "p' = ZAppt nf nu"
          by (cases nf) (auto simp: bind_eq_Some_conv)
        with zterm_ok_beta_norm_term[OF hu] onf ok ZAppt show ?thesis by simp
      qed
    qed
  qed (use h ok in auto)
qed

lemma zinv_zren_proof: "zren_proof r m p = returnZ p' \<Longrightarrow> zinv p \<Longrightarrow> zinv p'"
  unfolding zren_proof_def by (erule zinv_map_zproof) auto

text \<open>Normalization of proofs:\<close>

context prf_sig
begin

theorem zinv_znorm_proof:
  assumes nz: "znorm_proof ztargs env vis q = returnZ r" and q: "zinv q"
    and tac: "tacyc (tyenv env)" and en: "zenv_nn env"
    and vv: "\<forall>(x, T)\<in>set (visible_vars vis). 0 \<le> snd x \<and> tnn T"
    and vt: "\<forall>(v, S)\<in>set (visible_tvars vis). 0 \<le> snd v"
  shows "zinv r"
proof (cases "env_is_empty env \<or> vis = []")
  case True
  with nz have "beta_norm_prooft q = Some r" by (auto simp: znorm_proof_def liftOZ_eq_returnZ)
  from zinv_beta_norm_prooft[OF this q] show ?thesis .
next
  case False
  let ?\<theta> = "tyenv env" and ?VT = "visible_tvars vis" and ?VV = "visible_vars vis"
  define ityp where "ityp instT = (case instT of None \<Rightarrow> id
    | Some xs \<Rightarrow> if List.null xs then id else zsubst_type (map_of xs))" for instT :: "((indexname \<times> psort) \<times> ztyp) list option"
  obtain instT us m where
    iT: "(if vt_is_empty ?\<theta> then returnZ None
      else bindZ (mapZ (\<lambda>(v, S). znorm_type ?\<theta> (ZTVar v S)) ?VT) (\<lambda>Us. returnZ (Some (zip ?VT Us)))) = returnZ instT"
    and us: "mapZ (\<lambda>(a, T). znorm_term ztargs env (ZVar a T))
      (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) = returnZ us"
    and m: "map_zproof (ityp instT) (\<lambda>t.
      if zvars_all (\<lambda>(x, T). \<not> Option.is_none (zlookup_var (zip (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) us)
          (x, ityp instT T)) \<or> Option.is_none (vt_lookup (tenv env) x)) t
      then liftOZ (beta_norm_term (zsubst_term (ityp instT)
        (zlookup_var (zip (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) us)) t))
      else raiseZ (ZExn (Term_Error STR ''norm_proof: variable bound by the environment is not visible'' []))) q = returnZ m"
    and bn: "beta_norm_prooft m = Some r"
    using nz False unfolding znorm_proof_def Let_def ityp_def
    by (auto simp: bindZ_eq_returnZ liftOZ_eq_returnZ)
  define vs where "vs = zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)"
  have tn: "\<forall>p\<in>tvars_env ?\<theta>. 0 \<le> snd (fst p)" using en by (simp add: zenv_nn_def)
  have ity: "ztyp_ok (ityp instT T)" if T: "ztyp_ok T" for T
  proof (cases "vt_is_empty ?\<theta>")
    case True
    with iT have "instT = None" by simp
    with T show ?thesis by (simp add: ityp_def)
  next
    case False
    with iT obtain Us where Us: "mapZ (\<lambda>(v, S). znorm_type ?\<theta> (ZTVar v S)) ?VT = returnZ Us"
      "instT = Some (zip ?VT Us)"
      by (auto simp: bindZ_eq_returnZ)
    have l: "list_all2 (\<lambda>x U. ztyp_ok U) ?VT Us"
      using Us(1) unfolding mapZ_eq_returnZ
    proof (rule list.rel_mono_strong)
      fix x U assume x: "x \<in> set ?VT" and z: "(case x of (v, S) \<Rightarrow> znorm_type ?\<theta> (ZTVar v S)) = returnZ U"
      obtain v S where xv: "x = (v, S)" by (cases x)
      have "ztyp_ok (ZTVar v S)" using vt x xv by auto
      with z xv show "ztyp_ok U" using ztyp_ok_znorm_type[OF _ tac tn] by simp
    qed
    have "ztyp_ok (zsubst_type (map_of (zip ?VT Us)) T)"
      by (rule ztyp_ok_zsubst_type[OF T]) (rule map_of_zip_Some[OF l])
    then show ?thesis using T by (simp add: ityp_def Us(2))
  qed
  have vs_ok: "zterm_ok (ZVar a T)" if "(a, T) \<in> set vs" for a T
  proof -
    from that obtain T0 where "(a, T0) \<in> set ?VV" "T = ityp instT (ztyp_of T0)" by (auto simp: vs_def)
    with vv show ?thesis by (auto intro!: ity ztyp_ok_ztyp_of)
  qed
  have us': "list_all2 (\<lambda>v u. zterm_ok u) vs us"
    using us unfolding vs_def[symmetric] mapZ_eq_returnZ
  proof (rule list.rel_mono_strong)
    fix v u assume v: "v \<in> set vs" and z: "(case v of (a, T) \<Rightarrow> znorm_term ztargs env (ZVar a T)) = returnZ u"
    obtain a T where va: "v = (a, T)" by (cases v)
    from z va have "znorm_term ztargs env (ZVar a T) = returnZ u" by simp
    from zterm_ok_znorm_term[OF this tac en vs_ok] v va show "zterm_ok u" by simp
  qed
  have "zinv m"
  proof (rule zinv_map_zproof[OF m q ity])
    fix t t' assume tt: "(if zvars_all (\<lambda>(x, T). \<not> Option.is_none (zlookup_var (zip (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) us)
          (x, ityp instT T)) \<or> Option.is_none (vt_lookup (tenv env) x)) t
      then liftOZ (beta_norm_term (zsubst_term (ityp instT)
        (zlookup_var (zip (zdedup_vars (map (\<lambda>(a, T). (a, ityp instT (ztyp_of T))) ?VV)) us)) t))
      else raiseZ (ZExn (Term_Error STR ''norm_proof: variable bound by the environment is not visible'' []))) = returnZ t'"
      and ok: "zterm_ok t"
    from tt have bt: "beta_norm_term (zsubst_term (ityp instT) (zlookup_var (zip vs us)) t) = Some t'"
      by (auto simp: liftOZ_eq_returnZ vs_def split: if_splits)
    have "zterm_ok (zsubst_term (ityp instT) (zlookup_var (zip vs us)) t)"
    proof (rule zterm_ok_zsubst_term[OF ok ity])
      fix v u assume "zlookup_var (zip vs us) v = Some u"
      from zlookup_var_zip_Some[OF us' this] show "zterm_ok u" by blast
    qed
    from zterm_ok_beta_norm_term[OF bt this] show "zterm_ok t'" .
  qed
  from zinv_beta_norm_prooft[OF bn this] show ?thesis .
qed

end

text \<open>Composition:\<close>

lemma zinv_zimp_prf: "zterm_ok A \<Longrightarrow> zinv (zimp_prf A i m)"
  by (induction A i m rule: zimp_prf.induct) auto

lemma zinv_zmk_asm_prf: "zterm_ok C \<Longrightarrow> zinv (zmk_asm_prf C i m)"
proof -
  have "zterm_ok A \<Longrightarrow> zinv (zall_prf i m A)" for A
    by (induction i m A rule: zall_prf.induct) (auto simp: zinv_zimp_prf)
  then show "zterm_ok C \<Longrightarrow> zinv (zmk_asm_prf C i m)" by (simp add: zmk_asm_prf_def)
qed

lemma zinv_zflatten_params_proof: "zterm_ok (fst x) \<Longrightarrow> zinv (zflatten_params_proof i j n x)"
  by (induction i j n x rule: zflatten_params_proof.induct) (auto simp: zinv_ZAppps zinv_ZAppts)

context prf_sig
begin

lemma zinv_zbicompose_core:
  assumes c: "zbicompose_core ztargs env flatten Bs As A oldAs n m vis p q = returnZ r"
    and p: "zinv p" and q: "zinv q" and tac: "tacyc (tyenv env)" and en: "zenv_nn env"
    and vv: "\<forall>(x, T)\<in>set (visible_vars vis). 0 \<le> snd x \<and> tnn T"
    and vt: "\<forall>(v, S)\<in>set (visible_tvars vis). 0 \<le> snd v"
    and nn: "\<forall>t\<in>set (Bs @ As @ oldAs). pnn t" "\<forall>C. A = Some C \<longrightarrow> pnn C"
  shows "zinv r"
proof -
  let ?normt = "\<lambda>t. bindZ (zterm_of ztargs t) (znorm_term ztargs env)"
  obtain Ns asm Os ks fs where Ns: "mapZ ?normt (Bs @ As) = returnZ Ns"
    and asm: "(if n > 0 then (case A of None \<Rightarrow> raiseZ ZOption
        | Some C \<Rightarrow> bindZ (?normt C) (\<lambda>C'. returnZ [zmk_asm_prf C' n (zasm_count m C)])) else returnZ []) = returnZ asm"
    and Os: "mapZ (zterm_of ztargs) oldAs = returnZ Os"
    and ks: "liftMZ (zip_eq Os (downto (integer_of_nat (length As) - 1) 0)) = returnZ ks"
    and fs: "(if flatten then mapZ (\<lambda>x. znorm_proof ztargs env vis (zflatten_params_proof 0 0 n x)) ks
        else returnZ (map (\<lambda>x. ZBoundp (snd x)) ks)) = returnZ fs"
    and r: "r = ZAbsps Ns (ZAppp (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As))))) (ZAppps p (asm @ fs)))"
    using c unfolding zbicompose_core_def Let_def by (auto simp: bindZ_eq_returnZ)
  have normt: "zterm_ok t'" if "?normt t = returnZ t'" "pnn t" for t t'
  proof -
    from that(1) obtain z where "zterm_of ztargs t = returnZ z" "znorm_term ztargs env z = returnZ t'"
      by (auto simp: bindZ_eq_returnZ)
    with zterm_ok_zterm_of_pnn[OF _ that(2)] zterm_ok_znorm_term[OF _ tac en] show ?thesis by blast
  qed
  have "\<forall>t'\<in>set Ns. zterm_ok t'"
  proof
    fix t' assume "t' \<in> set Ns"
    from list_all2_ex2[OF Ns[unfolded mapZ_eq_returnZ] this] obtain t where "t \<in> set (Bs @ As)" "?normt t = returnZ t'"
      by blast
    with normt nn(1) show "zterm_ok t'" by auto
  qed
  moreover have "\<forall>a\<in>set asm. zinv a"
  proof (cases "0 < n")
    case True
    with asm obtain C C' where "A = Some C" "?normt C = returnZ C'" "asm = [zmk_asm_prf C' n (zasm_count m C)]"
      by (auto simp: bindZ_eq_returnZ split: option.splits)
    with normt nn(2) show ?thesis by (auto intro: zinv_zmk_asm_prf)
  next
    case False
    with asm show ?thesis by simp
  qed
  moreover have "\<forall>f\<in>set fs. zinv f"
  proof -
    have kO: "\<forall>x\<in>set ks. zterm_ok (fst x)"
    proof
      fix x assume x: "x \<in> set ks"
      from ks have "ks = zip Os (downto (integer_of_nat (length As) - 1) 0)"
        by (auto simp: liftMZ_eq_returnZ dest: ok_zip_eq_D)
      with x have "(fst x, snd x) \<in> set (zip Os (downto (integer_of_nat (length As) - 1) 0))" by simp
      then have "fst x \<in> set Os" by (rule set_zip_leftD)
      from list_all2_ex2[OF Os[unfolded mapZ_eq_returnZ] this] obtain B0 where "B0 \<in> set oldAs" "zterm_of ztargs B0 = returnZ (fst x)"
        by blast
      with nn(1) show "zterm_ok (fst x)" by (auto intro: zterm_ok_zterm_of_pnn)
    qed
    show ?thesis
    proof (cases flatten)
      case True
      show ?thesis
      proof
        fix f assume "f \<in> set fs"
        from list_all2_ex2[OF fs[unfolded if_P[OF True] mapZ_eq_returnZ] this] obtain x where
          "x \<in> set ks" "znorm_proof ztargs env vis (zflatten_params_proof 0 0 n x) = returnZ f" by blast
        with kO show "zinv f" by (blast intro: zinv_znorm_proof[OF _ zinv_zflatten_params_proof tac en vv vt])
      qed
    next
      case False
      with fs show ?thesis by auto
    qed
  qed
  ultimately show ?thesis using p q by (auto simp: r zinv_ZAbsps zinv_ZAppps)
qed

theorem zinv_zbicompose_proof:
  assumes c: "zbicompose_proof ztargs env smax flatten Bs As A oldAs n m vis rprf sprf = returnZ r"
    and p: "zinv rprf" and q: "zinv sprf" and tac: "tacyc (tyenv env)" and en: "zenv_nn env"
    and vv: "\<forall>(x, T)\<in>set (visible_vars vis). 0 \<le> snd x \<and> tnn T"
    and vt: "\<forall>(v, S)\<in>set (visible_tvars vis). 0 \<le> snd v"
    and nn: "\<forall>t\<in>set (Bs @ As @ oldAs). pnn t" "\<forall>C. A = Some C \<longrightarrow> pnn C"
  shows "zinv r"
proof (cases "env_is_empty env")
  case True
  with c have "zbicompose_core ztargs env flatten Bs As A oldAs n m vis rprf sprf = returnZ r"
    by (simp add: zbicompose_proof_def)
  from zinv_zbicompose_core[OF this p q tac en vv vt nn] show ?thesis .
next
  case False
  with c obtain rprf' sprf' where r': "znorm_proof ztargs env vis rprf = returnZ rprf'"
    and s': "(if above env smax then returnZ sprf else znorm_proof ztargs env vis sprf) = returnZ sprf'"
    and cc: "zbicompose_core ztargs env flatten Bs As A oldAs n m vis rprf' sprf' = returnZ r"
    by (auto simp: zbicompose_proof_def bindZ_eq_returnZ)
  have "zinv rprf'" by (rule zinv_znorm_proof[OF r' p tac en vv vt])
  moreover have "zinv sprf'"
    using s' q zinv_znorm_proof[OF _ q tac en vv vt] by (auto split: if_splits)
  ultimately show ?thesis by (rule zinv_zbicompose_core[OF cc _ _ tac en vv vt nn])
qed

end

end
