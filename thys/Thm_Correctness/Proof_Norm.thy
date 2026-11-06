section \<open>Normalizing proofs\<close>

theory Proof_Norm
  imports Proof_Flatten
begin

text \<open>
  \<^const>\<open>norm_proof\<close> normalizes the annotations of a proof with respect to an environment. For
  annotations without schematic variables whose type variables are consistent with the type
  environment, it raises no exception and prints no warning; the normalized annotations are
  \<open>\<beta>\<close>-reducts of the canonical type instances of the original ones.
\<close>

subsection \<open>Terms without schematic variables\<close>

definition tnormal :: "tyenv \<Rightarrow> pterm \<Rightarrow> bool" where
  "tnormal \<theta> t \<longleftrightarrow> (\<forall>U\<in>typs t. \<forall>(w, S)\<in>tvars U. vt_lookup \<theta> w = None)"

definition tconsT :: "tyenv \<Rightarrow> pterm \<Rightarrow> bool" where
  "tconsT \<theta> t \<longleftrightarrow> (\<forall>U\<in>typs t. tcons \<theta> U)"

lemma tconsT_tnormal: "tnormal \<theta> t \<Longrightarrow> tconsT \<theta> t"
  by (fastforce simp: tnormal_def tconsT_def tcons_def)

context prf_sig
begin

lemma inst_tsol0_tnormal: "tnormal \<theta> t \<Longrightarrow> inst (tsol0 \<theta>) t = t"
proof -
  assume "tnormal \<theta> t"
  then have "tsubst (tsol0 \<theta>) U = U" if "U \<in> typs t" for U
    using that tsubst_cong[of U "tsol0 \<theta>" TVar] by (fastforce simp: tnormal_def tsol0_def)
  then show ?thesis by (induction t) auto
qed

end

lemma typs_subst_bound: "typs (subst_bound u body) \<subseteq> typs body \<union> typs u"
  by (simp add: subst_bound_subst typs_subst)

lemma vars_subst_bound: "vars (subst_bound u body) \<subseteq> vars body \<union> vars u"
  by (simp add: subst_bound_subst vars_subst)

context prf_sig
begin

lemma norm_term2_varfree:
  assumes "norm_term2 env t = Some r"
  shows "tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow> vars t = {} \<Longrightarrow> tconsT (tyenv env) t \<Longrightarrow>
    \<exists>t'. r = Ok t' \<and> vars t' = {} \<and> tnormal (tyenv env) t' \<and> inst (tsol0 (tyenv env)) t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
  using assms
proof (induction env t r rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  let ?\<theta> = "tyenv env"
  note h = "1.hyps" and ac = "1.prems"(1) and tc = "1.prems"(2) and vt = "1.prems"(3) and ct = "1.prems"(4)
  have IH: "\<exists>t'. r' = Ok t' \<and> vars t' = {} \<and> tnormal ?\<theta> t' \<and> inst (tsol0 ?\<theta>) u \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
    if "nt env u = Some r'" "vars u = {}" "tconsT ?\<theta> u" for u r'
    using "1.IH"[OF that(1) ac tc that(2,3)] .
  have nT: "norm_type_aux ?\<theta> T = return (tnorm ?\<theta> T)" if "tcons ?\<theta> T" for T
    by (rule norm_type_aux_ok[OF ac tc that])
  have tsT: "tsubst (tsol0 ?\<theta>) T = tnorm ?\<theta> T" if "tcons ?\<theta> T" for T
    by (rule tsubst_tsol0[OF ac that])
  have tnT: "\<forall>(w, S)\<in>tvars (tnorm ?\<theta> T). vt_lookup ?\<theta> w = None" for T
    using tnorm_unbound[OF ac] by fast
  have redex: "\<exists>t'. r = Ok t' \<and> vars t' = {} \<and> tnormal ?\<theta> t' \<and> inst (tsol0 ?\<theta>) (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
    if hs: "nt env (subst_bound u body) = Some r" and vs: "vars body = {}" "vars u = {}"
      and cs: "tconsT ?\<theta> body" "tconsT ?\<theta> u"
    for b U0 body u
  proof -
    have "vars (subst_bound u body) = {}" using vars_subst_bound[of u body] vs by blast
    moreover have "tconsT ?\<theta> (subst_bound u body)" using typs_subst_bound[of u body] cs
      by (auto simp: tconsT_def)
    ultimately have "\<exists>t'. r = Ok t' \<and> vars t' = {} \<and> tnormal ?\<theta> t' \<and> inst (tsol0 ?\<theta>) (subst_bound u body) \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
      by (rule IH[OF hs])
    then obtain t' where t': "r = Ok t'" "vars t' = {}" "tnormal ?\<theta> t'"
      "inst (tsol0 ?\<theta>) (subst_bound u body) \<rightarrow>\<^sub>\<beta>\<^sup>* t'" by blast
    have "inst (tsol0 ?\<theta>) (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta> inst (tsol0 ?\<theta>) (subst_bound u body)"
      using inst_beta by (simp add: subst_bound_subst)
    with t' show ?thesis by (blast intro: converse_rtranclp_into_rtranclp)
  qed
  show ?case
  proof (cases t)
    case (Const a T)
    with ct have "tcons ?\<theta> T" by (simp add: tconsT_def)
    with h Const nT tsT tnT show ?thesis by (auto simp: tnormal_def return_def bindM_def)
  next
    case (Free a T)
    with ct have "tcons ?\<theta> T" by (simp add: tconsT_def)
    with h Free nT tsT tnT show ?thesis by (auto simp: tnormal_def return_def bindM_def)
  next
    case (Var x T)
    with vt show ?thesis by simp
  next
    case (Bound i)
    with h show ?thesis by (auto simp: tnormal_def return_def bindM_def)
  next
    case (Abs a T body)
    with ct have cT: "tcons ?\<theta> T" and cb: "tconsT ?\<theta> body" by (simp_all add: tconsT_def)
    from h Abs nT[OF cT] obtain rb where rb: "nt env body = Some rb"
      and r: "r = (case rb of Ok body' \<Rightarrow> Ok (Abs a (tnorm ?\<theta> T) body') | Err e \<Rightarrow> Err e)"
      by (auto simp: bindM_def return_def split: option.splits res.splits)
    from IH[OF rb _ cb] vt Abs obtain body' where "rb = Ok body'" "vars body' = {}" "tnormal ?\<theta> body'"
      "inst (tsol0 ?\<theta>) body \<rightarrow>\<^sub>\<beta>\<^sup>* body'" by auto
    with r tsT[OF cT] tnT[of T] show ?thesis by (auto simp: Abs tnormal_def)
  next
    case (App f u)
    have vf: "vars f = {}" "vars u = {}" and cf: "tconsT ?\<theta> f" "tconsT ?\<theta> u"
      using vt ct App by (auto simp: tconsT_def)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      have "nt env (subst_bound u body) = Some r" using h App f by simp
      from redex[OF this] vf cf f App show ?thesis by (simp add: tconsT_def)
    next
      case False
      with h App obtain rf where hf: "nt env f = Some rf"
        and rest: "(case rf of Ok nf \<Rightarrow> (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) | Err e \<Rightarrow> Some (Err e)) = Some r"
        by (cases f) (auto simp: bindM_def split: option.splits)
      from IH[OF hf vf(1) cf(1)] obtain nf where nf: "rf = Ok nf" "vars nf = {}" "tnormal ?\<theta> nf"
        "inst (tsol0 ?\<theta>) f \<rightarrow>\<^sub>\<beta>\<^sup>* nf" by blast
      have fu: "inst (tsol0 ?\<theta>) (f $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* nf $ inst (tsol0 ?\<theta>) u" using nf(4) by (simp add: rtrancl_beta_AppL)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfb: "nf = Abs b U0 body" by (cases nf) auto
        have hb: "nt env (subst_bound u body) = Some r" using rest nf(1) nfb by simp
        have "tnormal ?\<theta> body" using nf(3) nfb by (simp add: tnormal_def)
        then have vb: "vars body = {}" "tconsT ?\<theta> body" using nf(2) nfb by (simp_all add: tconsT_tnormal)
        from redex[OF hb vb(1) vf(2) vb(2) cf(2)] obtain t' where t': "r = Ok t'" "vars t' = {}" "tnormal ?\<theta> t'"
          "inst (tsol0 ?\<theta>) (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* t'" by blast
        have "inst (tsol0 ?\<theta>) nf = nf" by (rule inst_tsol0_tnormal[OF nf(3)])
        then have "nf $ inst (tsol0 ?\<theta>) u = inst (tsol0 ?\<theta>) (Abs b U0 body $ u)" by (simp add: nfb)
        with fu t' show ?thesis by (auto simp: App)
      next
        case False
        with rest nf(1) obtain ru where hu: "nt env u = Some ru"
          and r: "r = (case ru of Ok nu \<Rightarrow> Ok (nf $ nu) | Err e \<Rightarrow> Err e)"
          by (cases nf) (auto simp: bindM_def return_def split: option.splits res.splits)
        from IH[OF hu vf(2) cf(2)] obtain nu where "ru = Ok nu" "vars nu = {}" "tnormal ?\<theta> nu"
          "inst (tsol0 ?\<theta>) u \<rightarrow>\<^sub>\<beta>\<^sup>* nu" by blast
        with r nf fu show ?thesis
          by (auto simp: App tnormal_def intro: rtranclp_trans rtrancl_beta_App)
      qed
    qed
  qed
qed

lemma norm_term1_varfree:
  assumes "norm_term1 te t = Some r"
  shows "vars t = {} \<Longrightarrow> \<exists>t'. r = Ok t' \<and> vars t' = {} \<and> typs t' \<subseteq> typs t \<and> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
  using assms
proof (induction te t r rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps" and vt = "1.prems"
  have IH: "\<exists>t'. r' = Ok t' \<and> vars t' = {} \<and> typs t' \<subseteq> typs u \<and> u \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
    if "nt te u = Some r'" "vars u = {}" for u r'
    using "1.IH"[OF that] .
  have redex: "\<exists>t'. r = Ok t' \<and> vars t' = {} \<and> typs t' \<subseteq> typs (Abs b U0 body $ u) \<and> Abs b U0 body $ u \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
    if hs: "nt te (subst_bound u body) = Some r" and vs: "vars body = {}" "vars u = {}" for b U0 body u
  proof -
    have "vars (subst_bound u body) = {}" using vars_subst_bound[of u body] vs by blast
    then have "\<exists>t'. r = Ok t' \<and> vars t' = {} \<and> typs t' \<subseteq> typs (subst_bound u body) \<and> subst_bound u body \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
      by (rule IH[OF hs])
    then obtain t' where t': "r = Ok t'" "vars t' = {}" "typs t' \<subseteq> typs (subst_bound u body)"
      "subst_bound u body \<rightarrow>\<^sub>\<beta>\<^sup>* t'" by blast
    have "Abs b U0 body $ u \<rightarrow>\<^sub>\<beta> subst_bound u body" by (simp add: subst_bound_subst)
    then have "Abs b U0 body $ u \<rightarrow>\<^sub>\<beta>\<^sup>* t'" using t'(4) by (rule converse_rtranclp_into_rtranclp)
    moreover have "typs t' \<subseteq> typs (Abs b U0 body $ u)" using t'(3) typs_subst_bound[of u body] by auto
    ultimately show ?thesis using t'(1,2) by blast
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    with vt show ?thesis by simp
  next
    case (Abs a T body)
    from h Abs obtain rb where rb: "nt te body = Some rb"
      and r: "r = (case rb of Ok body' \<Rightarrow> Ok (Abs a T body') | Err e \<Rightarrow> Err e)"
      by (auto simp: bindM_def return_def split: option.splits res.splits)
    from IH[OF rb] vt Abs obtain body' where "rb = Ok body'" "vars body' = {}" "typs body' \<subseteq> typs body"
      "body \<rightarrow>\<^sub>\<beta>\<^sup>* body'" by auto
    with r show ?thesis by (auto simp: Abs)
  next
    case (App f u)
    have vf: "vars f = {}" "vars u = {}" using vt App by auto
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      have "nt te (subst_bound u body) = Some r" using h App f by simp
      from redex[OF this] vf f App show ?thesis by simp
    next
      case False
      with h App obtain rf where hf: "nt te f = Some rf"
        and rest: "(case rf of Ok nf \<Rightarrow> (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) | Err e \<Rightarrow> Some (Err e)) = Some r"
        by (cases f) (auto simp: bindM_def split: option.splits)
      from IH[OF hf vf(1)] obtain nf where nf: "rf = Ok nf" "vars nf = {}" "typs nf \<subseteq> typs f"
        "f \<rightarrow>\<^sub>\<beta>\<^sup>* nf" by blast
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfb: "nf = Abs b U0 body" by (cases nf) auto
        have hb: "nt te (subst_bound u body) = Some r" using rest nf(1) nfb by simp
        have vb: "vars body = {}" using nf(2) nfb by simp
        from redex[OF hb vb vf(2)] obtain t' where t': "r = Ok t'" "vars t' = {}"
          "typs t' \<subseteq> typs (Abs b U0 body $ u)" "Abs b U0 body $ u \<rightarrow>\<^sub>\<beta>\<^sup>* t'" by blast
        from rtranclp_trans[OF rtrancl_beta_AppL[OF nf(4)] t'(4)[folded nfb]] t' nf(3) nfb
        show ?thesis by (auto simp: App)
      next
        case False
        with rest nf(1) obtain ru where hu: "nt te u = Some ru"
          and r: "r = (case ru of Ok nu \<Rightarrow> Ok (nf $ nu) | Err e \<Rightarrow> Err e)"
          by (cases nf) (auto simp: bindM_def return_def split: option.splits res.splits)
        from IH[OF hu vf(2)] obtain nu where "ru = Ok nu" "vars nu = {}" "typs nu \<subseteq> typs u" "u \<rightarrow>\<^sub>\<beta>\<^sup>* nu"
          by blast
        with r nf show ?thesis by (auto simp: App intro: rtrancl_beta_App)
      qed
    qed
  qed (use h in \<open>auto simp: return_def\<close>)
qed

lemma tsol0_empty: "vt_is_empty \<theta> \<Longrightarrow> tsol0 \<theta> = TVar"
  by (auto simp: fun_eq_iff tsol0_def vt_is_empty_lookup)

theorem norm_term_varfree:
  assumes "norm_term env t = Some r" "tacyc (tyenv env)" "tcons_env (tyenv env)" "vars t = {}" "tconsT (tyenv env) t"
  shows "\<exists>t'. r = Ok t' \<and> vars t' = {} \<and> tnormal (tyenv env) t' \<and> inst (tsol0 (tyenv env)) t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    then have "vt_is_empty (tyenv env)" by (simp add: env_is_empty_def)
    with id assms(1,4) show ?thesis
      by (auto simp: norm_term_def tnormal_def tsol0_empty vt_is_empty_lookup return_def inst_TVar_id)
  next
    case n1
    with assms(1) have "norm_term1 (tenv env) t = Some r" by (simp add: norm_term_def)
    from norm_term1_varfree[OF this assms(4)] n1(2) show ?thesis
      by (auto simp: tnormal_def tsol0_empty vt_is_empty_lookup)
  next
    case n2
    with assms(1) have "norm_term2 env t = Some r" by (simp add: norm_term_def)
    from norm_term2_varfree[OF this assms(2-5)] show ?thesis .
  qed
qed


end

end
