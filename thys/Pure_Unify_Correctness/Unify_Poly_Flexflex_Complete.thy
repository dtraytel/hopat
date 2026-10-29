section \<open>Problems with Type Variables: Completeness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Poly_Flexflex_Complete
  imports Unify_Poly_Match_Complete Unify_Flexflex_Complete
begin

text \<open>
  Completeness of \<^const>\<open>add_ffpair\<close> on polymorphic problems: the analogue of theory
  \<^theory>\<open>Pure_Unify_Correctness.Unify_Flexflex_Complete\<close> for the invariant
  \<^const>\<open>pcinv\<close>. The flex-flex phase does not change the type environment: the type unification
  in \<^const>\<open>ff_assign\<close> is on types that are equal modulo the type environment. A flex-flex
  pair that a later pair in \<^const>\<open>SIMPL\<close> made unsaturated is kept, since \<^const>\<open>clean_term\<close>
  fails on it.
\<close>


hide_const (open) Unify_Flexflex_Complete.inst

subsection \<open>Normalization terminates\<close>

lemma typed_proper: "typed env W Ts t T \<Longrightarrow> proper t"
  unfolding typed_def using has_type_proper by fastforce

context
  fixes alg ar A W env \<rho>
  assumes pi: "pinv alg ar A W env []" and g: "gsol alg ar (tyenv env) \<rho>"
begin

abbreviation pinst :: "pterm \<Rightarrow> dB" where
  "pinst t \<equiv> mk_subst (env_inst (instE \<rho> env)) (tr (inst \<rho> t))"

lemma pnt_facts:
  shows "tacyc (tyenv env)" "tcons_env (tyenv env)" "tsol (tyenv env) \<rho>"
    "acyc (instE \<rho> env)" "wf_env ar (instE \<rho> env)" "env_typed (ityp \<rho> env W) (instE \<rho> env)"
proof -
  note p = pinvD[OF pi]
  note ei = env_invD[OF penv_inv_inst[OF p(1) g]]
  show "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF p(2)] tinv_tcons_env[OF p(2)] by simp_all
  show "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  show "acyc (instE \<rho> env)" "wf_env ar (instE \<rho> env)" "env_typed (ityp \<rho> env W) (instE \<rho> env)"
    using ei(1-3) by simp_all
qed

text \<open>
  \<^const>\<open>norm_term2\<close> terminates on typed terms, with a typed result whose instance is a
  \<open>\<beta>\<close>-reduct of the instance; the head variable of the result is unbound.
\<close>

lemma norm_term12_pterm:
  "typed env W Ts t T \<Longrightarrow> \<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U \<Longrightarrow> below (maxidx env) t \<Longrightarrow>
    \<exists>t'. norm_term2 env t = Some (Ok t') \<and> (vt_is_empty (tyenv env) \<longrightarrow> norm_term1 (tenv env) t = Some (Ok t')) \<and> typed env W Ts t' T \<and> (\<forall>U\<in>tys t'. tyw ar (tyenv env) A U) \<and>
      below (maxidx env) t' \<and> pinst t \<rightarrow>\<^sub>\<beta>\<^sup>* pinst t' \<and>
      (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and> (is_Abs t' \<or> fhd t' = head_of t') \<and>
      (\<forall>x U. head_of t = Var x U \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> (\<exists>U'. head_of t' = Var x U')) \<and>
      (\<forall>x U. head_of t' = Var x U \<longrightarrow> tnorm (tyenv env) U = U) \<and>
      (\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t \<longrightarrow> fh env0 t')"
proof (induction t arbitrary: Ts T rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (pinst t, card (reach (instE \<rho> env) (vps (inst \<rho> t))))"]])
  case (1 t)
  note fa = pnt_facts
  note p = pinvD[OF pi]
  note pe = penv_invD[OF p(1)]
  let ?\<theta> = "tyenv env"
  let ?P = "\<lambda>t Ts T t'. norm_term2 env t = Some (Ok t') \<and>
    (vt_is_empty ?\<theta> \<longrightarrow> norm_term1 (tenv env) t = Some (Ok t')) \<and> typed env W Ts t' T \<and>
    (\<forall>U\<in>tys t'. tyw ar ?\<theta> A U) \<and> below (maxidx env) t' \<and> pinst t \<rightarrow>\<^sub>\<beta>\<^sup>* pinst t' \<and>
    (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and> (is_Abs t' \<or> fhd t' = head_of t') \<and>
      (\<forall>x U. head_of t = Var x U \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> (\<exists>U'. head_of t' = Var x U')) \<and>
      (\<forall>x U. head_of t' = Var x U \<longrightarrow> tnorm (tyenv env) U = U) \<and>
    (\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t \<longrightarrow> fh env0 t')"
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF p(2) that])
  have tyi: "has_type (ityp \<rho> env W) (map (tsubst \<rho>) Ts) (inst \<rho> t) (tsubst \<rho> (tnorm ?\<theta> T))"
  proof (rule typed_inst[OF fa(1,2,3) _ tcons_tnorm[OF fa(1)]])
    show "\<forall>U\<in>set Ts \<union> tys t. tcons ?\<theta> U" using "1.prems"(2) tcU by blast
    show "typed env W Ts t (tnorm ?\<theta> T)" using "1.prems"(1) typed_tnorm[OF fa(1)] by simp
  qed
  have tp: "typable (pinst t)" by (rule inst_typable[OF fa(4,5,6) tyi])
  have red: "\<exists>t'. ?P u Us U t'"
    if "(sup beta subt)\<^sup>+\<^sup>+ (pinst t) (pinst u)" "typed env W Us u U" "\<forall>X\<in>set Us \<union> tys u. tyw ar ?\<theta> A X"
      "below (maxidx env) u" for u Us U
    using "1.IH"[OF _ that(2-4)] sn_lessI[OF tp that(1)] by simp
  have wte: "wt_env W env" using p(1) by (simp add: penv_inv_def)
  show ?case
  proof (cases t)
    case (Var x U)
    have tyV: "tctx env W x = tnorm ?\<theta> U" "tnorm ?\<theta> T = tnorm ?\<theta> U"
      using "1.prems"(1) Var by (auto simp: typed_def elim: has_type_elims)
    have twU: "tyw ar ?\<theta> A U" using "1.prems"(2) Var by simp
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case None
      have "norm_term2 env t = Some (Ok (Var x (tnorm ?\<theta> U)))"
        using None Var norm_type_aux_ok[OF fa(1,2) tcU[OF twU]]
        by (subst norm_term2.simps) (simp add: lookup_def return_def bindM_def)
      moreover have "norm_term1 (tenv env) t = Some (Ok (Var x (tnorm ?\<theta> U)))" if "vt_is_empty ?\<theta>"
        using None Var tnorm_empty[OF that] by (subst norm_term1.simps) (simp add: lookup1_def return_def bindM_def)
      moreover have "typed env W Ts (Var x (tnorm ?\<theta> U)) T"
        using tyV by (simp add: typed_def tnorm_idem[OF fa(1)] has_type.Var)
      moreover have "tyw ar ?\<theta> A (tnorm ?\<theta> U)" by (rule tyw_tnorm[OF p(2) twU])
      moreover have "fh env0 (Var x (tnorm ?\<theta> U))" if "fh env0 t" for env0 using that Var by (simp add: fh_def)
      ultimately show ?thesis using None Var "1.prems"(3) by (auto simp: below_def tnorm_idem[OF fa(1)])
    next
      case (Some pr)
      obtain U' u where lks: "vt_lookup (tenv env) x = Some (U', u)" using Some by (cases pr) auto
      have twe: "\<forall>X\<in>insert U' (tys u). tyw ar ?\<theta> A X" using etysI[OF lks] p(3) by blast
      have tU: "tnorm ?\<theta> U' = tnorm ?\<theta> U" using tctx_bound[OF lks, of W] tyV(1) by simp
      have lk: "lookup env x U = return (Some u)"
        using lks unified_ok[OF fa(1,2) tcU[OF twU] tcU[of U']] twe tU by (simp add: lookup_def bindM_def return_def)
      have tyu: "typed env W Ts u T"
      proof -
        have "typed env W Ts u U'" by (rule typed_weaken[OF wt_envD[OF wte lks]])
        then show ?thesis by (rule typed_tnorm_cong[OF _ refl]) (use tyV(2) tU in simp)
      qed
      have bu: "below (maxidx env) u" using fresh_envD[OF pe(6) lks] by simp
      have lki: "vt_lookup (tenv (instE \<rho> env)) x = Some (tsubst \<rho> U', inst \<rho> u)" using lks by simp
      have pt: "pinst t = pinst u" using inst_bound[OF fa(4,5,6) lki] Var by simp
      have iU: "tsubst \<rho> U' = tsubst \<rho> U"
        using tsubst_tnorm[OF fa(1,2,3) tcU[of U']] tsubst_tnorm[OF fa(1,2,3) tcU[OF twU]] twe twU tU by simp
      have "lk (instE \<rho> env) x (tsubst \<rho> U) = Some (inst \<rho> u)" using lks iU by (simp add: lk_def)
      from reach_card_less[OF fa(4,5,6) this] have card: "card (reach (instE \<rho> env) (vps (inst \<rho> u))) <
          card (reach (instE \<rho> env) (vps (inst \<rho> t)))" using Var by simp
      have twu: "\<forall>X\<in>set Ts \<union> tys u. tyw ar ?\<theta> A X" using "1.prems"(2) twe by auto
      from "1.IH"[OF _ tyu twu bu] pt card obtain t' where t': "?P u Ts T t'" by auto
      have "norm_term2 env t = Some (Ok t')"
        using t' lk Var by (subst norm_term2.simps) (simp add: bindM_def return_def)
      moreover have "norm_term1 (tenv env) t = Some (Ok t')" if "vt_is_empty ?\<theta>"
        using t' lks tU Var tnorm_empty[OF that] that
        by (subst norm_term1.simps) (simp add: lookup1_def bindM_def return_def)
      moreover have "fh env0 t'" if "flexb env0 env" "fh env0 t" for env0
      proof -
        from that(2) Var have "vt_lookup (tenv env0) x = None" by (auto simp: fh_def)
        with that(1) lks have "fh env0 u" unfolding flexb_def by blast
        with t' that(1) show ?thesis by blast
      qed
      ultimately show ?thesis using t' pt lks Var by auto
    qed
  next
    case (Abs a U b)
    from "1.prems"(1) Abs obtain X where tT: "tnorm ?\<theta> T = tnorm ?\<theta> U \<rightarrow>\<^sub>T X"
      and tyb0: "has_type (tctx env W) (tnorm ?\<theta> U # map (tnorm ?\<theta>) Ts) (tnormt ?\<theta> b) X"
      by (auto simp: typed_def elim: has_type_elims)
    have nX: "tnorm ?\<theta> X = X" using typed_type_normal[of env W "U # Ts" b X] tyb0 fa(1) by simp
    have tyb: "typed env W (U # Ts) b X" using tyb0 nX by (simp add: typed_def)
    have tw: "\<forall>Y\<in>set (U # Ts) \<union> tys b. tyw ar ?\<theta> A Y" using "1.prems"(2) Abs by auto
    have "\<exists>t'. ?P b (U # Ts) X t'"
      by (rule red[OF _ tyb tw]) (use "1.prems"(3) Abs in \<open>auto simp: subt_def below_def\<close>)
    then obtain b' where b': "?P b (U # Ts) X b'" by blast
    have twU: "tyw ar ?\<theta> A U" using "1.prems"(2) Abs by simp
    have "norm_term2 env t = Some (Ok (Abs a (tnorm ?\<theta> U) b'))"
      using b' Abs norm_type_aux_ok[OF fa(1,2) tcU[OF twU]] by (subst norm_term2.simps) (simp add: bindM_def return_def)
    moreover have "norm_term1 (tenv env) t = Some (Ok (Abs a (tnorm ?\<theta> U) b'))" if "vt_is_empty ?\<theta>"
      using b' Abs tnorm_empty[OF that] that by (subst norm_term1.simps) (simp add: bindM_def return_def)
    moreover have "typed env W Ts (Abs a (tnorm ?\<theta> U) b') T"
      using b' tT nX by (auto simp: typed_def tnorm_idem[OF fa(1)] intro: has_type.Abs)
    moreover have "pinst t \<rightarrow>\<^sub>\<beta>\<^sup>* pinst (Abs a (tnorm ?\<theta> U) b')" using b' Abs by (simp add: rtrancl_beta_Abs)
    moreover have "fh env0 (Abs a (tnorm ?\<theta> U) b')" if "flexb env0 env" "fh env0 t" for env0
      using b' that Abs by (simp add: fh_def)
    moreover have "tyw ar ?\<theta> A (tnorm ?\<theta> U)" by (rule tyw_tnorm[OF p(2) twU])
    ultimately show ?thesis using b' Abs by (auto simp: below_def)
  next
    case (App f u)
    from typed_App[OF fa(1) "1.prems"(1)[unfolded App]] obtain Y where tyf: "typed env W Ts f (Y \<rightarrow>\<^sub>T T)"
      and tyu: "typed env W Ts u Y" by blast
    have twf: "\<forall>X\<in>set Ts \<union> tys f. tyw ar ?\<theta> A X" and twu: "\<forall>X\<in>set Ts \<union> tys u. tyw ar ?\<theta> A X"
      using "1.prems"(2) App by auto
    have bf: "below (maxidx env) f" and bu: "below (maxidx env) u" using "1.prems"(3) App by (auto simp: below_def)
    have pu: "proper u" by (rule typed_proper[OF tyu])
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a U' body where f: "f = Abs a U' body" by (cases f) auto
      have tyb: "typed env W Ts (subst_bound u body) T" by (rule typed_beta[OF fa(1) tyf[unfolded f] tyu])
      have pb: "proper body" using typed_proper[OF tyf] f by simp
      have st: "pinst t \<rightarrow>\<^sub>\<beta> pinst (subst_bound u body)"
        using App f by (simp add: Poly_Inst.inst_subst_bound Pattern_Size.inst_subst_bound[OF fa(4,5,6)] pb pu)
      have twb: "\<forall>X\<in>set Ts \<union> tys (subst_bound u body). tyw ar ?\<theta> A X"
        using twf twu tys_subst_bound[of u body] f by auto
      have bb: "below (maxidx env) (subst_bound u body)"
        using bf bu vars_subst_bound[of u body] f by (auto simp: below_def)
      have "\<exists>t'. ?P (subst_bound u body) Ts T t'" by (rule red[OF _ tyb twb bb]) (use st in auto)
      then obtain t' where t': "?P (subst_bound u body) Ts T t'" by blast
      have "norm_term2 env t = Some (Ok t')" using t' App f by (subst norm_term2.simps) simp
      moreover have "norm_term1 (tenv env) t = Some (Ok t')" if "vt_is_empty ?\<theta>"
        using t' App f that by (subst norm_term1.simps) simp
      moreover have "fh env0 t'" if "flexb env0 env" "fh env0 t" for env0
      proof -
        from that(2) App f have "fh env0 body" by (simp add: fh_def)
        then have "fh env0 (subst_bound u body)" by (auto simp: fh_def fhd_subst_bound)
        with t' that(1) show ?thesis by blast
      qed
      moreover have "\<not> (\<exists>x U. head_of t = Var x U)" using App f by simp
      ultimately show ?thesis using t' st by (auto intro: converse_rtranclp_into_rtranclp)
    next
      case False
      have "\<exists>t'. ?P f Ts (Y \<rightarrow>\<^sub>T T) t'" by (rule red[OF _ tyf twf bf]) (auto simp: App subt_def)
      then obtain nf where nf: "?P f Ts (Y \<rightarrow>\<^sub>T T) nf" by blast
      have fhf: "fh env0 nf" if "flexb env0 env" "fh env0 t" for env0
        using nf that App by (simp add: fh_def)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a U' body where nfa: "nf = Abs a U' body" by (cases nf) auto
        have tyb: "typed env W Ts (subst_bound u body) T"
          using typed_beta[OF fa(1), of W Ts a U' body Y T u] nf nfa tyu by simp
        have pb: "proper body" using typed_proper[of env W Ts nf "Y \<rightarrow>\<^sub>T T"] nf nfa by simp
        have st: "beta\<^sup>+\<^sup>+ (pinst t) (pinst (subst_bound u body))"
        proof -
          have "pinst t \<rightarrow>\<^sub>\<beta>\<^sup>* pinst nf \<degree> pinst u" using nf App by (simp add: rtrancl_beta_AppL)
          moreover have "pinst nf \<degree> pinst u \<rightarrow>\<^sub>\<beta> pinst (subst_bound u body)"
            using nfa by (simp add: Poly_Inst.inst_subst_bound Pattern_Size.inst_subst_bound[OF fa(4,5,6)] pb pu)
          ultimately show ?thesis by (rule rtranclp_into_tranclp1)
        qed
        have twb: "\<forall>X\<in>set Ts \<union> tys (subst_bound u body). tyw ar ?\<theta> A X"
          using nf nfa twu tys_subst_bound[of u body] by auto
        have bb: "below (maxidx env) (subst_bound u body)"
          using nf nfa bu vars_subst_bound[of u body] by (auto simp: below_def)
        have "\<exists>t'. ?P (subst_bound u body) Ts T t'"
        proof (rule red[OF _ tyb twb bb])
          show "(sup beta subt)\<^sup>+\<^sup>+ (pinst t) (pinst (subst_bound u body))"
            using st by (induction rule: tranclp_induct) (auto intro: tranclp.trancl_into_trancl)
        qed
        then obtain t' where t': "?P (subst_bound u body) Ts T t'" by blast
        have "norm_term2 env (f $ u) = Some (Ok t')"
          using t' nf nfa False by (subst norm_term2.simps) (cases f; simp)
        moreover have "norm_term1 (tenv env) (f $ u) = Some (Ok t')" if "vt_is_empty ?\<theta>"
          using t' nf nfa False that by (subst norm_term1.simps) (cases f; simp)
        moreover have "fh env0 t'" if "flexb env0 env" "fh env0 t" for env0
        proof -
          from fhf[OF that] nfa have "fh env0 body" by (simp add: fh_def)
          then have "fh env0 (subst_bound u body)" by (auto simp: fh_def fhd_subst_bound)
          with t' that(1) show ?thesis by blast
        qed
        moreover have "\<not> (\<exists>x U. head_of f = Var x U \<and> vt_lookup (tenv env) x = None)" using nf nfa by auto
        ultimately show ?thesis using t' tranclp_into_rtranclp[OF st] App by (auto intro: rtranclp_trans)
      next
        case nA: False
        have "\<exists>t'. ?P u Ts Y t'" by (rule red[OF _ tyu twu bu]) (auto simp: App subt_def)
        then obtain nu where nu: "?P u Ts Y nu" by blast
        have "norm_term2 env (f $ u) = Some (Ok (nf $ nu))"
          using nf nu nA False by (subst norm_term2.simps) (cases f; cases nf; simp add: bindM_def return_def)
        moreover have "norm_term1 (tenv env) (f $ u) = Some (Ok (nf $ nu))" if "vt_is_empty ?\<theta>"
          using nf nu nA False that by (subst norm_term1.simps) (cases f; cases nf; simp add: bindM_def return_def)
        moreover have "typed env W Ts (nf $ nu) T" using nf nu by (auto intro: typed_AppI)
        moreover have "pinst t \<rightarrow>\<^sub>\<beta>\<^sup>* pinst (nf $ nu)" using nf nu App by (simp add: rtrancl_beta_App)
        moreover have "fh env0 (nf $ nu)" if "flexb env0 env" "fh env0 t" for env0
          using fhf[OF that] by (simp add: fh_def)
        ultimately show ?thesis using nf nu nA App by (auto simp: below_def)
      qed
    qed
  next
    case (Const a U)
    have twU: "tyw ar ?\<theta> A U" using "1.prems"(2) Const by simp
    have "norm_term2 env t = Some (Ok (Const a (tnorm ?\<theta> U)))"
      using Const norm_type_aux_ok[OF fa(1,2) tcU[OF twU]] by (subst norm_term2.simps) (simp add: bindM_def return_def)
    moreover have "norm_term1 (tenv env) t = Some (Ok (Const a (tnorm ?\<theta> U)))" if "vt_is_empty ?\<theta>"
      using Const tnorm_empty[OF that] by (subst norm_term1.simps) (simp add: return_def)
    moreover have "typed env W Ts (Const a (tnorm ?\<theta> U)) T"
      using "1.prems"(1) Const by (auto simp: typed_def tnorm_idem[OF fa(1)] elim: has_type_elims intro: has_type.Const)
    moreover have "tsubst \<rho> (tnorm ?\<theta> U) = tsubst \<rho> U" by (rule tsubst_tnorm[OF fa(1,2,3) tcU[OF twU]])
    ultimately show ?thesis using tyw_tnorm[OF p(2) twU] Const by (auto simp: below_def fh_def)
  next
    case (Free a U)
    have twU: "tyw ar ?\<theta> A U" using "1.prems"(2) Free by simp
    have "norm_term2 env t = Some (Ok (Free a (tnorm ?\<theta> U)))"
      using Free norm_type_aux_ok[OF fa(1,2) tcU[OF twU]] by (subst norm_term2.simps) (simp add: bindM_def return_def)
    moreover have "norm_term1 (tenv env) t = Some (Ok (Free a (tnorm ?\<theta> U)))" if "vt_is_empty ?\<theta>"
      using Free tnorm_empty[OF that] by (subst norm_term1.simps) (simp add: return_def)
    moreover have "typed env W Ts (Free a (tnorm ?\<theta> U)) T"
      using "1.prems"(1) Free by (auto simp: typed_def tnorm_idem[OF fa(1)] elim: has_type_elims intro: has_type.Free)
    moreover have "tsubst \<rho> (tnorm ?\<theta> U) = tsubst \<rho> U" by (rule tsubst_tnorm[OF fa(1,2,3) tcU[OF twU]])
    ultimately show ?thesis using tyw_tnorm[OF p(2) twU] Free by (auto simp: below_def fh_def)
  next
    case (Bound i)
    then show ?thesis using "1.prems" by (subst norm_term2.simps, subst norm_term1.simps) (auto simp: return_def fh_def)
  qed
qed

text \<open>The same for \<^const>\<open>norm_term\<close>.\<close>

lemma norm_term_pterm:
  assumes "typed env W Ts t T" "\<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U" "below (maxidx env) t"
  shows "\<exists>t'. norm_term env t = return t' \<and> typed env W Ts t' T \<and> (\<forall>U\<in>tys t'. tyw ar (tyenv env) A U) \<and>
    below (maxidx env) t' \<and> pinst t \<rightarrow>\<^sub>\<beta>\<^sup>* pinst t' \<and>
    (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and> (is_Abs t' \<or> fhd t' = head_of t') \<and>
      (\<forall>x U. head_of t = Var x U \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> (\<exists>U'. head_of t' = Var x U')) \<and>
      (\<forall>x U. head_of t' = Var x U \<longrightarrow> tnorm (tyenv env) U = U) \<and>
    (\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t \<longrightarrow> fh env0 t')"
proof (cases "env_is_empty env \<and> \<not> could_beta_contract t")
  case True
  then show ?thesis using assms fhd_no_beta[of t]
    by (auto simp: norm_term_def env_is_empty_def vt_is_empty_lookup tnorm_empty)
next
  case False
  then show ?thesis using norm_term12_pterm[OF assms]
    by (auto simp: norm_term_def return_def)
qed

end


subsection \<open>Flexible heads stay saturated\<close>

text \<open>
  A type variable may be bound to a function type after a flex-flex pair was classified: the pair
  is then no longer saturated in the final type environment. Its heads still have as many
  arguments as their arity in the type environment of its classification, and the bindings of
  the flex-flex phase preserve this: they bind variables to abstractions over as many bound
  variables as their arity, whose bodies are flexible and saturated (\<open>ffgood\<close>). Hence the heads of
  the normalized pairs remain variables.
\<close>

abbreviation ary :: "tyenv \<Rightarrow> ptyp \<Rightarrow> nat" where
  "ary \<theta> T \<equiv> length (arg_types (tnorm \<theta> T))"

lemma length_arg_types_tnorm: "length (arg_types S) \<le> length (arg_types (tnorm \<theta> S))"
  by (induction S rule: arg_types.induct) auto

lemma ary_mono: "tacyc \<theta>' \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> ary \<theta> T \<le> ary \<theta>' T"
  using length_arg_types_tnorm[of "tnorm \<theta> T" \<theta>'] by (simp add: tnorm_textends)

fun absp :: "nat \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "absp 0 u b \<longleftrightarrow> u = b"
| "absp (Suc n) u b \<longleftrightarrow> (case u of Abs _ _ u' \<Rightarrow> absp n u' b | _ \<Rightarrow> False)"

lemma absp_subst_bound_aux:
  "absp k b (list_comb (Var K U) cs) \<Longrightarrow>
    \<exists>cs'. absp k (subst_bound_aux a lev b) (list_comb (Var K U) cs') \<and> length cs' = length cs"
proof (induction k arbitrary: b lev)
  case 0
  then show ?case by (intro exI[of _ "map (subst_bound_aux a lev) cs"]) (simp add: subst_bound_aux_list_comb)
next
  case (Suc k)
  then obtain x T b' where "b = Abs x T b'" "absp k b' (list_comb (Var K U) cs)"
    by (cases b) auto
  with Suc.IH[of b' "lev + 1"] show ?case by auto
qed

lemma not_is_Abs_list_comb_Var: "\<not> is_Abs (list_comb (Var X U) as)"
  by (cases as rule: rev_cases) (auto simp: list_comb_def)

lemma absp_list_comb_Var_App:
  "absp j (f $ u) (list_comb (Var X U) as) \<Longrightarrow> j = 0 \<and> (\<exists>as'. as = as' @ [u] \<and> f = list_comb (Var X U) as')"
  by (cases j; cases as rule: rev_cases) (auto simp: list_comb_def)

lemma absp_list_comb_Var_nonAbs:
  "absp j t (list_comb (Var X U) as) \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> j = 0 \<and> t = list_comb (Var X U) as"
  by (cases j) (auto split: pterm.splits)

definition ffgood :: "tyenv \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "ffgood \<theta> W e0 env \<longleftrightarrow> (\<forall>X U u. vt_lookup (tenv env) X = Some (U, u) \<longrightarrow> vt_lookup (tenv e0) X = None \<longrightarrow>
    (\<exists>n K V bs. absp n u (list_comb (Var K V) bs) \<and> vt_lookup (tenv e0) K = None \<and>
      n = ary \<theta> (W X) \<and> length bs = ary \<theta> (W K)))"

lemma norm_term2_spine:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> ffgood \<theta> W e0 env \<Longrightarrow> extends env e0 \<Longrightarrow>
    absp j t (list_comb (Var X U) as) \<Longrightarrow> vt_lookup (tenv e0) X = None \<Longrightarrow> length as \<le> ary \<theta> (W X) \<Longrightarrow>
    \<exists>k K U' cs. absp k t' (list_comb (Var K U') cs) \<and> vt_lookup (tenv env) K = None \<and>
      (if vt_lookup (tenv env) X = None then k = j \<and> K = X \<and> length cs = length as
       else k = j + (ary \<theta> (W X) - length as) \<and> length cs = ary \<theta> (W K))"
  using assms
proof (induction env t r arbitrary: t' j X U as rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  have gd: "ffgood \<theta> W e0 env" and ext: "extends env e0" and sp: "absp j t (list_comb (Var X U) as)"
    and X0: "vt_lookup (tenv e0) X = None" and la: "length as \<le> ary \<theta> (W X)"
    and t': "ok (case t of
      Const a T \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (Const a T'))
    | Free a T \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (Free a T'))
    | pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of
          Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (pterm.Var xi T')))
    | pterm.Abs a T body \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'.
        nt env body \<bind> (\<lambda>body'. return (pterm.Abs a T' body')))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
        | _ \<Rightarrow> nt env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> nt env u \<bind> (\<lambda>nu. return (nf $ nu))))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  show ?case
  proof (cases t)
    case (Var xi T)
    from absp_list_comb_Var_nonAbs[OF sp] Var have j0: "j = 0" and e: "pterm.Var xi T = list_comb (Var X U) as"
      by auto
    from arg_cong[OF e, of strip_comb] strip_comb_list_comb_eq[of "Var X U" as] have xi: "xi = X" "T = U" "as = []"
      by (simp_all add: strip_comb_def)
    with Var t' obtain r' where lk: "ok (lookup env X U) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux (tyenv env) U \<bind> (\<lambda>T'. return (pterm.Var X T'))) t'"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_lookup_some[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume r': "r' = None"
      then have Xn: "vt_lookup (tenv env) X = None"
        using lk by (auto simp: lookup_def bind_def return_def var_clash_def raise_def split: option.splits if_splits)
      from r' rest obtain T' where "t' = pterm.Var X T'"
        by (auto simp: bind_def return_def split: option.splits res.splits)
      then show ?thesis using Xn j0 xi by (intro exI[of _ 0] exI[of _ X] exI[of _ T'] exI[of _ "[]"]) simp
    next
      fix V u assume r': "r' = Some u" and l: "vt_lookup (tenv env) X = Some (V, u)"
      from r' rest have nu: "nt env u = Some (Ok t')" by simp
      from gd l X0 obtain n K V' bs where b: "absp n u (list_comb (Var K V') bs)"
        "vt_lookup (tenv e0) K = None" "n = ary \<theta> (W X)" "length bs = ary \<theta> (W K)"
        unfolding ffgood_def by blast
      from "1.IH"[OF nu refl gd ext b(1,2)] b(4) obtain k K'' U'' cs where
        c: "absp k t' (list_comb (Var K'' U'') cs)" "vt_lookup (tenv env) K'' = None"
          "if vt_lookup (tenv env) K = None then k = n \<and> K'' = K \<and> length cs = length bs
           else k = n + (ary \<theta> (W K) - length bs) \<and> length cs = ary \<theta> (W K'')"
        by auto
      then have "k = n" "length cs = ary \<theta> (W K'')" using b(4) by (auto split: if_splits)
      then show ?thesis using c(1,2) l j0 xi b(3) by (intro exI[of _ k] exI[of _ K''] exI[of _ U''] exI[of _ cs]) auto
    qed
  next
    case (Abs a T body)
    have "t \<noteq> list_comb (Var X U) as"
      using Abs not_is_Abs_list_comb_Var[of X U as] by (cases "list_comb (Var X U) as") auto
    with sp Abs obtain j' where j: "j = Suc j'" and spb: "absp j' body (list_comb (Var X U) as)"
      by (cases j) auto
    with t' Abs obtain T' b' where b: "nt env body = Some (Ok b')" and t'': "t' = pterm.Abs a T' b'"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    from "1.IH"[OF b refl gd ext spb X0 la] obtain k K U' cs where
      c: "absp k b' (list_comb (Var K U') cs)" "vt_lookup (tenv env) K = None"
        "if vt_lookup (tenv env) X = None then k = j' \<and> K = X \<and> length cs = length as
         else k = j' + (ary \<theta> (W X) - length as) \<and> length cs = ary \<theta> (W K)"
      by blast
    then show ?thesis using t'' j by (intro exI[of _ "Suc k"] exI[of _ K] exI[of _ U'] exI[of _ cs]) auto
  next
    case (App f u)
    from absp_list_comb_Var_App[OF sp[unfolded App]] obtain as' where
      j0: "j = 0" and as: "as = as' @ [u]" and f: "f = list_comb (Var X U) as'" by blast
    have nAf: "\<not> is_Abs f" using f by (cases as' rule: rev_cases) (auto simp: list_comb_def)
    with t' App obtain nf where nf: "nt env f = Some (Ok nf)"
      and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
        | _ \<Rightarrow> nt env u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
      by (cases f) auto
    have la': "length as' \<le> ary \<theta> (W X)" using la as by simp
    have spf: "absp 0 f (list_comb (Var X U) as')" using f by simp
    from "1.IH"[OF nf refl gd ext spf X0 la'] obtain k K U' cs where
      c: "absp k nf (list_comb (Var K U') cs)" "vt_lookup (tenv env) K = None"
        "if vt_lookup (tenv env) X = None then k = 0 \<and> K = X \<and> length cs = length as'
         else k = 0 + (ary \<theta> (W X) - length as') \<and> length cs = ary \<theta> (W K)"
      by auto
    show ?thesis
    proof (cases "vt_lookup (tenv env) X = None")
      case True
      with c have k: "k = 0" "K = X" "length cs = length as'" by auto
      with c(1) have nfe: "nf = list_comb (Var X U') cs" by simp
      have "\<not> is_Abs nf" using nfe by (cases cs rule: rev_cases) (auto simp: list_comb_def)
      with rest obtain nu where "t' = nf $ nu" by (cases nf) (auto simp: bind_def return_def split: option.splits res.splits)
      then have "t' = list_comb (Var X U') (cs @ [nu])" using nfe by (simp add: list_comb_def)
      then show ?thesis using True k as j0 by (intro exI[of _ 0] exI[of _ X] exI[of _ U'] exI[of _ "cs @ [nu]"]) simp
    next
      case False
      with c have k: "k = ary \<theta> (W X) - length as'" "length cs = ary \<theta> (W K)" by auto
      have kpos: "0 < k" using k(1) la as by simp
      with c(1) obtain x T body where nfa: "nf = pterm.Abs x T body"
        and spb: "absp (k - 1) body (list_comb (Var K U') cs)"
        by (cases k; cases nf) auto
      from rest nfa have nb: "nt env (subst_bound u body) = Some (Ok t')" by simp
      from absp_subst_bound_aux[OF spb, of u 0] obtain cs' where
        spb': "absp (k - 1) (subst_bound u body) (list_comb (Var K U') cs')" "length cs' = length cs"
        by (auto simp: subst_bound_def)
      have K0: "vt_lookup (tenv e0) K = None" by (rule extends_unbound[OF ext c(2)])
      from "1.IH"[OF nb refl gd ext spb'(1) K0] spb'(2) k(2) obtain k' K' U'' cs'' where
        c': "absp k' t' (list_comb (Var K' U'') cs'')" "vt_lookup (tenv env) K' = None"
          "if vt_lookup (tenv env) K = None then k' = k - 1 \<and> K' = K \<and> length cs'' = length cs'
           else k' = k - 1 + (ary \<theta> (W K) - length cs') \<and> length cs'' = ary \<theta> (W K')"
        by auto
      have "k' = k - 1" "length cs'' = ary \<theta> (W K')" using c'(3) c(2) spb'(2) k(2) by auto
      then show ?thesis using c'(1,2) False k(1) as j0
        by (intro exI[of _ k'] exI[of _ K'] exI[of _ U''] exI[of _ cs'']) auto
    qed
  next
    case (Const a T)
    with absp_list_comb_Var_nonAbs[OF sp] show ?thesis by (cases as rule: rev_cases) (auto simp: list_comb_def)
  next
    case (Free a T)
    with absp_list_comb_Var_nonAbs[OF sp] show ?thesis by (cases as rule: rev_cases) (auto simp: list_comb_def)
  next
    case (Bound i)
    with absp_list_comb_Var_nonAbs[OF sp] show ?thesis by (cases as rule: rev_cases) (auto simp: list_comb_def)
  qed
qed


text \<open>The same for \<^const>\<open>norm_term\<close>.\<close>

lemma norm_term_spine:
  assumes nt: "norm_term env t = return t'" and pi: "pinv alg ar A W env []" and g: "gsol alg ar (tyenv env) \<rho>"
    and ty: "typed env W Ts t T" "\<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U" "below (maxidx env) t"
    and gd: "ffgood \<theta> W' e0 env" "extends env e0"
    and sp: "absp j t (list_comb (Var X U) as)" "vt_lookup (tenv e0) X = None" "length as \<le> ary \<theta> (W' X)"
  shows "\<exists>k K U' cs. absp k t' (list_comb (Var K U') cs) \<and> vt_lookup (tenv env) K = None \<and>
      (if vt_lookup (tenv env) X = None then k = j \<and> K = X \<and> length cs = length as
       else k = j + (ary \<theta> (W' X) - length as) \<and> length cs = ary \<theta> (W' K))"
proof (cases "env_is_empty env \<and> \<not> could_beta_contract t")
  case True
  then have "t' = t" "vt_lookup (tenv env) X = None"
    using nt by (auto simp: norm_term_def return_def env_is_empty_def vt_is_empty_lookup)
  then show ?thesis using sp by (intro exI[of _ j] exI[of _ X] exI[of _ U] exI[of _ as]) auto
next
  case False
  from norm_term12_pterm[OF pi g ty] obtain t'' where n: "norm_term2 env t = Some (Ok t'')"
    "vt_is_empty (tyenv env) \<longrightarrow> norm_term1 (tenv env) t = Some (Ok t'')"
    by blast
  have "t' = t''" using nt n False by (auto simp: norm_term_def return_def split: if_splits)
  then show ?thesis using norm_term2_spine[OF n(1) refl gd sp] by simp
qed

lemma absp_rlist_abs: "absp k u b \<Longrightarrow> absp (length rb + k) (rlist_abs rb u) b"
proof (induction rb arbitrary: u k)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Suc k" "Abs a T u"] Cons.prems show ?case by simp
qed simp

lemma absp_types_abs: "absp (length Ts) (types_abs Ts u) u"
  by (induction Ts) auto

lemma absp_unique:
  "absp n u (list_comb (Var K V) bs) \<Longrightarrow> absp n' u (list_comb (Var K' V') bs') \<Longrightarrow>
    n = n' \<and> K = K' \<and> V = V' \<and> bs = bs'"
proof (induction n arbitrary: u n')
  case 0
  then have "\<not> is_Abs u" using not_is_Abs_list_comb_Var by simp
  with "0.prems"(2) have "n' = 0" by (cases n'; cases u) auto
  with "0.prems" have "list_comb (Var K V) bs = list_comb (Var K' V') bs'" by simp
  from arg_cong[OF this, of strip_comb] show ?case
    using strip_comb_list_comb_eq[of "Var K V" bs] strip_comb_list_comb_eq[of "Var K' V'" bs'] \<open>n' = 0\<close> by simp
next
  case (Suc n)
  then obtain a T u' where u: "u = Abs a T u'" "absp n u' (list_comb (Var K V) bs)" by (cases u) auto
  have "n' \<noteq> 0"
    using Suc.prems(2) u(1) not_is_Abs_list_comb_Var[of K' V' bs'] by (cases n'; cases "list_comb (Var K' V') bs'") auto
  then obtain m where "n' = Suc m" by (cases n') auto
  with Suc.prems(2) u have "absp m u' (list_comb (Var K' V') bs')" by simp
  from Suc.IH[OF u(2) this] \<open>n' = Suc m\<close> show ?case by simp
qed

lemma absp_vars: "absp n u (list_comb (Var K V) bs) \<Longrightarrow> K \<in> vars u"
  by (induction n arbitrary: u) (auto simp: vars_list_comb split: pterm.splits)

lemma ffgood_between:
  assumes "ffgood \<theta>1 W e0 e" "ffgood \<theta>2 W e0 e" "tacyc \<theta>" "tacyc \<theta>2" "textends \<theta>1 \<theta>" "textends \<theta> \<theta>2"
  shows "ffgood \<theta> W e0 e"
  unfolding ffgood_def
proof (intro allI impI)
  fix X U u assume b: "vt_lookup (tenv e) X = Some (U, u)" "vt_lookup (tenv e0) X = None"
  from assms(1) b obtain n K V bs where g1: "absp n u (list_comb (Var K V) bs)" "vt_lookup (tenv e0) K = None"
    "n = ary \<theta>1 (W X)" "length bs = ary \<theta>1 (W K)"
    unfolding ffgood_def by blast
  from assms(2) b obtain n' K' V' bs' where g2: "absp n' u (list_comb (Var K' V') bs')"
    "n' = ary \<theta>2 (W X)" "length bs' = ary \<theta>2 (W K')"
    unfolding ffgood_def by blast
  from absp_unique[OF g1(1) g2(1)] have e: "n' = n" "K' = K" "bs' = bs" by simp_all
  have m: "ary \<theta>1 Y \<le> ary \<theta> Y" "ary \<theta> Y \<le> ary \<theta>2 Y" for Y
    using ary_mono[OF assms(3,5)] ary_mono[OF assms(4,6)] by auto
  have "n = ary \<theta> (W X)" using m[of "W X"] g1(3) g2(2) e by simp
  moreover have "length bs = ary \<theta> (W K)" using m[of "W K"] g1(4) g2(3) e by simp
  ultimately show "\<exists>n K V bs. absp n u (list_comb (Var K V) bs) \<and> vt_lookup (tenv e0) K = None \<and>
      n = ary \<theta> (W X) \<and> length bs = ary \<theta> (W K)"
    using g1(1,2) by blast
qed

lemma ffgood_trans:
  assumes g1: "ffgood \<theta> W e0 e1" and g2: "ffgood \<theta> W' e1 e2" and x1: "extends e1 e0" and x2: "extends e2 e1"
    and fr: "fresh_env e1" and ag: "agreeV (maxidx e1) W W'"
  shows "ffgood \<theta> W' e0 e2"
  unfolding ffgood_def
proof (intro allI impI)
  fix X U u assume b: "vt_lookup (tenv e2) X = Some (U, u)" "vt_lookup (tenv e0) X = None"
  show "\<exists>n K V bs. absp n u (list_comb (Var K V) bs) \<and> vt_lookup (tenv e0) K = None \<and>
      n = ary \<theta> (W' X) \<and> length bs = ary \<theta> (W' K)"
  proof (cases "vt_lookup (tenv e1) X")
    case None
    from g2 b(1) None obtain n K V bs where "absp n u (list_comb (Var K V) bs)" "vt_lookup (tenv e1) K = None"
      "n = ary \<theta> (W' X)" "length bs = ary \<theta> (W' K)"
      unfolding ffgood_def by blast
    then show ?thesis using extends_unbound[OF x1] by blast
  next
    case (Some p)
    with extendsD[OF x2 Some] b(1) have b1: "vt_lookup (tenv e1) X = Some (U, u)" by simp
    from g1 b1 b(2) obtain n K V bs where g: "absp n u (list_comb (Var K V) bs)" "vt_lookup (tenv e0) K = None"
      "n = ary \<theta> (W X)" "length bs = ary \<theta> (W K)"
      unfolding ffgood_def by blast
    from fresh_envD[OF fr b1] have m: "snd X \<le> maxidx e1" "below (maxidx e1) u" by simp_all
    have "snd K \<le> maxidx e1" using m(2) absp_vars[OF g(1)] by (simp add: below_def)
    then have "W' K = W K" "W' X = W X" using m(1) ag[unfolded agreeV_def] by blast+
    then show ?thesis using g by (intro exI[of _ n] exI[of _ K] exI[of _ V] exI[of _ bs]) auto
  qed
qed

lemma get_eta_var_args: "get_eta_var rb n t = returnW (v, T) \<Longrightarrow> length (snd (strip_comb t)) = length rb"
proof (induction rb n t rule: get_eta_var.induct)
  case (2 uu rbinder n f i)
  then show ?case by (auto simp: returnW_def raiseW_def strip_comb_App split: if_splits)
qed (auto simp: returnW_def raiseW_def strip_comb_def)

lemma ffgood_refl[simp]: "ffgood \<theta> W e e"
  by (simp add: ffgood_def)

subsection \<open>Assignments\<close>

text \<open>\<^const>\<open>update\<close> on a binding that the solution satisfies and that closes no cycle.\<close>

lemma pupdate_complete:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and xn: "vt_lookup (tenv env) x = None"
    and WT: "tnorm (tyenv env) (W x) = tnorm (tyenv env) T" and twT: "tyw ar (tyenv env) A T"
    and ty: "typed env W [] s T" and tws: "\<forall>X\<in>tys s. tyw ar (tyenv env) A X" and ws: "swf_tm ar [] s"
    and bs: "below (maxidx env) s" and xm: "snd x \<le> maxidx env"
    and ac: "(x, tsubst \<rho> T) \<notin> reach (instE \<rho> env) (vps (inst \<rho> s))"
    and eq: "\<sigma> (code (AVar x)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> s))"
  shows "\<exists>env'. update (x, T) s env = return env' \<and> pcinv alg ar A W \<rho> \<tau>' \<sigma> env' dps \<and> pextends env' env \<and>
    tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and> tenv env' = vt_update (x, (T, s)) (tenv env)"
proof -
  let ?\<theta> = "tyenv env" and ?V = "ityp \<rho> env W"
  note pcd = pcinvD[OF pc]
  note pi = pinvD[OF pcd(1)]
  note pe = penv_invD[OF pi(1)]
  have sol: "tsol ?\<theta> \<rho>" using pcd(2) by (simp add: gsol_def)
  have ac': "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  note ci = pcinv_cinv[OF pc]
  note eii = env_invD[OF cinvD(1)[OF ci]]
  note isol = cinvD(2)[OF ci]
  have Vx: "?V x = tsubst \<rho> T" using xn WT tsubst_tnorm[OF ac' sol tcU[OF twT]] by (simp add: vtyp_def)
  have tyi: "has_type ?V [] (inst \<rho> s) (tsubst \<rho> T)"
    using typed_inst[OF ac' sol _ tcU[OF twT] ty] tws tcU by simp
  from update_unbound_ok[OF xn, of T s] obtain env' where upd: "update (x, T) s env = Some (Ok env')" by blast
  have upd': "ok (update (x, T) s env) env'" using upd by simp
  have updi: "ok (update (x, tsubst \<rho> T) (inst \<rho> s) (instE \<rho> env)) (instE \<rho> env')"
    using update_inst[of x \<rho> T s env] upd by simp
  have Fm: "snd x \<le> maxidx (instE \<rho> env)" using xm by simp
  have tm: "below (maxidx (instE \<rho> env)) (inst \<rho> s)" using bs by simp
  note su = solution_update[OF isol eii(4) eii(3) updi eq Vx tyi Fm tm]
  have acy: "acyc (instE \<rho> env')"
  proof -
    note upi = ok_update[OF updi]
    have d: "dep (instE \<rho> env') = dep (instE \<rho> env) \<union> (\<lambda>y. (y, (x, tsubst \<rho> T))) ` vps (inst \<rho> s)"
      by (rule dep_update[OF upi(2,1)])
    from acyclic_update[OF d ac] eii(1) show ?thesis by (simp add: acyc_def)
  qed
  note up = ok_update[OF upd']
  have lk': "vt_lookup (tenv env') y = (if y = x then Some (T, s) else vt_lookup (tenv env) y)" for y
    using up(2) by simp
  have te': "tyenv env' = ?\<theta>" "maxidx env' = maxidx env" using up(3,4) by simp_all
  have wc': "wcons W env'"
    using pi(6) WT te'(1) unfolding wcons_def by (auto simp: lk' simp del: split_paired_All)
  have tctx': "tctx env' W y = tctx env W y" for y
    using wcons_tctx[OF wc'] wcons_tctx[OF pi(6)] te'(1) by simp
  have ityp': "ityp \<rho> env' W = ?V" using tctx' by simp
  have typed': "typed env' W Ts0 s0 S \<longleftrightarrow> typed env W Ts0 s0 S" for Ts0 s0 S
    using tctx' te'(1) by (simp add: typed_def)
  have etys': "etys env' \<subseteq> insert T (tys s \<union> etys env)" by (rule etys_update[OF upd])
  have twe': "\<forall>X\<in>etys env'. tyw ar ?\<theta> A X" using etys' tws twT pi(3) by blast
  have etv': "etvars env' \<subseteq> tvars_env ?\<theta> \<union> A" using twe' by (fastforce simp: etvars_def tyw_def)
  have pe'': "penv_inv alg ar W env'"
    unfolding penv_inv_def
  proof (intro conjI)
    show "tinv ar (maxidx env') (tyenv env') (etvars env')" using tinv_subset[OF pi(2) etv'] te' by simp
    show "tsorted alg (tyenv env')" using pe(2) te' by simp
    show "nacyc env'" using acyc_instE[OF su(2)] acy by simp
    show "pwf_env ar env'"
    proof -
      have "pwf_term ar 0 s" using ws by (simp add: pwf_term_def swf_tm_def twft_tys)
      moreover have "wft ar T" using twT by (simp add: tyw_def)
      ultimately show ?thesis using pe(4) by (auto simp: pwf_env_def lk')
    qed
    show "wt_env W env'" using pi(1) ty by (auto simp: penv_inv_def wt_env_def lk' typed')
    show "fresh_env env'" using su(3) by simp
  qed
  have "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' dps"
  proof -
    have "\<forall>dp\<in>set dps. swf_dp ar dp \<and> (\<forall>X\<in>dtys dp. tyw ar (tyenv env') A X) \<and> ptyped env' W dp \<and>
        dp_below (maxidx env') dp"
    proof
      fix dp assume dp: "dp \<in> set dps"
      obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
      from pi(4)[OF dp] show "swf_dp ar dp \<and> (\<forall>X\<in>dtys dp. tyw ar (tyenv env') A X) \<and>
          ptyped env' W dp \<and> dp_below (maxidx env') dp"
        using te' typed' dpe by simp
    qed
    then show ?thesis
      using pe'' pi(2,5) twe' wc' pcd(2,4) su(1) te' ityp'
      by (auto simp: pcinv_def pinv_def simp del: split_paired_All)
  qed
  then show ?thesis using upd te' ok_update_extends[OF upd'] up(2) by (auto simp: return_def pextends_def)
qed

text \<open>\<^const>\<open>vupdate\<close> on a binding that the solution satisfies and that closes no cycle.\<close>

lemma pvupdate_complete:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and vn: "vt_lookup (tenv env) v = None"
    and WT: "tnorm (tyenv env) (W v) = tnorm (tyenv env) T" and twT: "tyw ar (tyenv env) A T"
    and ty: "typed env W [] s T" and tws: "\<forall>X\<in>tys s. tyw ar (tyenv env) A X" and ws: "swf_tm ar [] s"
    and bs: "below (maxidx env) s" and vm: "snd v \<le> maxidx env"
    and ac: "\<forall>U. (v, U) \<notin> reach (instE \<rho> env) (vps (inst \<rho> s))"
    and eq: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> s))"
    and hs: "\<forall>w U. s = Var w U \<longrightarrow> vt_lookup (tenv env) w = None"
  shows "\<exists>env'. vupdate (v, T) s env = return env' \<and> pcinv alg ar A W \<rho> \<tau>' \<sigma> env' dps \<and> pextends env' env \<and>
    tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
    (\<forall>x U' u. vt_lookup (tenv env') x = Some (U', u) \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
      (x = v \<and> u = s) \<or> (\<exists>U. s = Var x U \<and> u = Var v U))"
proof -
  have plain: "?thesis" if "vupdate (v, T) s env = update (v, T) s env"
  proof -
    from pupdate_complete[OF pc vn WT twT ty tws ws bs vm _ eq] ac obtain env' where
      u: "update (v, T) s env = return env'" "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' dps" "pextends env' env"
      "tyenv env' = tyenv env" "maxidx env' = maxidx env" "tenv env' = vt_update (v, (T, s)) (tenv env)"
      by blast
    then show ?thesis using that by (intro exI[of _ env']) auto
  qed
  show ?thesis
  proof (cases s)
    case (Var w U)
    have wn: "vt_lookup (tenv env) w = None" using hs Var by simp
    have tU: "tnorm (tyenv env) (W w) = tnorm (tyenv env) U" "tnorm (tyenv env) T = tnorm (tyenv env) U"
      using ty Var wn by (auto simp: typed_def vtyp_def elim: has_type_elims)
    consider "v = w" | "v \<noteq> w" "indexname_less v w" | "v \<noteq> w" "\<not> indexname_less v w" by blast
    then show ?thesis
    proof cases
      case 1
      have "vupdate (v, T) s env = return env" using 1 Var by (subst vupdate.simps) simp
      then show ?thesis using pc by (intro exI[of _ env]) (auto simp: pextends_def extends_refl textends_refl)
    next
      case 2
      have lw: "lookup env w U = return None" using wn by (simp add: lookup_def)
      have twU: "tyw ar (tyenv env) A U" using tws Var by simp
      have "(w, tsubst \<rho> U) \<notin> reach (instE \<rho> env) (vps (inst \<rho> (Var v U)))"
      proof -
        have "lk (instE \<rho> env) v (tsubst \<rho> U) = None" using vn by (simp add: lk_def)
        from reach_unbound[OF this] 2(1) show ?thesis by simp
      qed
      moreover have "\<sigma> (code (AVar w)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (Var v U)))"
        using eq Var by (simp add: equiv_sym)
      moreover have "typed env W [] (Var v U) U"
        using vn WT tU(2) by (simp add: typed_def vtyp_def has_type.Var)
      moreover have "swf_tm ar [] (Var v U)" using ws Var by (simp add: swf_tm_def)
      moreover have "below (maxidx env) (Var v U)" using vm by (simp add: below_def)
      moreover have "snd w \<le> maxidx env" using bs Var by (simp add: below_def)
      ultimately obtain env' where
        u: "update (w, U) (Var v U) env = return env'" "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' dps" "pextends env' env"
        "tyenv env' = tyenv env" "maxidx env' = maxidx env" "tenv env' = vt_update (w, (U, Var v U)) (tenv env)"
        using pupdate_complete[OF pc wn tU(1) twU] twU by fastforce
      have "vupdate (v, T) s env = return env'"
        using 2 Var lw u(1) by (subst vupdate.simps) (simp add: bindM_def return_def)
      then show ?thesis using u Var by (intro exI[of _ env']) auto
    next
      case 3
      have "vupdate (v, T) s env = update (v, T) s env" using 3 Var by (subst vupdate.simps) simp
      then show ?thesis by (rule plain)
    qed
  qed (rule plain, subst vupdate.simps, simp)+
qed

text \<open>
  \<^const>\<open>ff_assign\<close> on a solved pair of a base type: it gives up with \<open>ASSIGN\<close>, or it binds the
  variable, and the solution and the type environment are kept.
\<close>

lemma pff_assign_complete:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and ty: "typed env W (map snd rb) t B" "typed env W (map snd rb) u B" "tnorm (tyenv env) B = B"
      "\<not> is_funT B"
    and swd: "swf_dp ar (rb, t, u)" and twd: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar (tyenv env) A U"
    and bl: "below (maxidx env) t" "below (maxidx env) u" and ds: "dsolved \<sigma> (instd \<rho> (rb, t, u))"
    and ht: "\<forall>x U. head_of t = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
    and hu: "\<forall>x U. head_of u = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
  shows "(\<exists>evs. ff_assign alg env rb t u = Some (evs, UErr ASSIGN)) \<or>
    (\<exists>env'. okW (ff_assign alg env rb t u) env' \<and> pcinv alg ar A W \<rho> \<tau>' \<sigma> env' dps \<and> pextends env' env \<and>
      tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
      (\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fh env0 u \<longrightarrow> flexb env0 env') \<and>
      (\<forall>\<theta>. hsat \<theta> W t \<longrightarrow> hsat \<theta> W u \<longrightarrow> is_Var (head_of u) \<longrightarrow> ffgood \<theta> W env env'))"
proof -
  let ?\<theta> = "tyenv env" and ?V = "ityp \<rho> env W"
  note pcd = pcinvD[OF pc]
  note pi = pinvD[OF pcd(1)]
  have sol: "tsol ?\<theta> \<rho>" using pcd(2) by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  note ci = pcinv_cinv[OF pc]
  note eii = env_invD[OF cinvD(1)[OF ci]]
  note isol = cinvD(2)[OF ci]
  have e: "vt_is_empty (tyenv (instE \<rho> env))" by (rule wf_envD(1)[OF eii(2)])
  have dsi: "dsolved \<sigma> (instb \<rho> rb, inst \<rho> t, inst \<rho> u)" using ds by simp
  have tct: "\<forall>U\<in>set (map snd rb) \<union> tys t. tcons ?\<theta> U" and tcu: "\<forall>U\<in>set (map snd rb) \<union> tys u. tcons ?\<theta> U"
    using twd tcU by auto
  consider "get_eta_var rb 0 t = raiseW ASSIGN" | v T where "get_eta_var rb 0 t = returnW (v, T)"
    using get_eta_var_cases by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: ff_assign_def bindW_def raiseW_def)
  next
    case 2
    have gevi: "okW (get_eta_var (instb \<rho> rb) 0 (inst \<rho> t)) (v, tsubst \<rho> T)"
      using get_eta_var_pinst[OF 2] by (simp add: returnW_def)
    have gevn: "okW (get_eta_var (tnormb ?\<theta> rb) 0 (tnormt ?\<theta> t)) (v, tnorm ?\<theta> T)"
      using get_eta_var_ptnorm[OF 2] by (simp add: returnW_def)
    have nt: "has_type (tctx env W) (map snd (tnormb ?\<theta> rb)) (tnormt ?\<theta> t) B"
      and nu: "has_type (tctx env W) (map snd (tnormb ?\<theta> rb)) (tnormt ?\<theta> u) B"
      using ty(1-3) by (simp_all add: typed_def)
    from get_eta_var_type[OF gevn _ nt] have Tn: "tnorm ?\<theta> T = foldr fun_type (rev (map snd (tnormb ?\<theta> rb))) B"
      and Vv: "tctx env W v = tnorm ?\<theta> T"
      by simp_all
    have htv: "head_of t = Var v T" by (rule get_eta_var_head[OF 2])
    have vu: "vt_lookup (tenv env) v = None" using ht htv by simp
    have WT: "tnorm ?\<theta> (W v) = tnorm ?\<theta> T" using Vv vu by (simp add: vtyp_def)
    have tT: "T \<in> tys t" using vps_tys[OF vps_head_of[OF htv]] by simp
    have twT: "tyw ar ?\<theta> A T" and tcT: "tcons ?\<theta> T" using twd tT tcU by auto
    have "\<exists>b. occurs_terms env v [u] = return b \<and> ok (occurs_terms (instE \<rho> env) v (map (inst \<rho>) [u])) b"
      by (rule occurs_terms_pinst[OF pi(1) pcd(2)]) (use ty(2) tcu bl(2) in auto)
    then obtain b where oc: "occurs_terms env v [u] = return b"
      and oci: "ok (occurs_terms (instE \<rho> env) v [inst \<rho> u]) b" by auto
    have bocc: "b \<longleftrightarrow> occ_in (instE \<rho> env) v (vps (inst \<rho> u))"
      using occurs_terms_correct[OF e eii(1) oci] by simp
    show ?thesis
    proof (cases b)
      case True
      then show ?thesis using 2 oc by (simp add: ff_assign_def bindW_def returnW_def return_def raiseW_def)
    next
      case False
      let ?s = "rlist_abs rb u"
      from body_type_ptnorm[OF ac tcT Tn ty(4)] obtain B1 where bt: "body_type env T = return B1"
        and B1: "tnorm ?\<theta> B1 = B" "tcons ?\<theta> B1" by blast
      from env_fastype_pterm[OF ac tcu] nu obtain T2 where
        ft0: "ok (env_fastype env (map snd rb) u) T2" "tnorm ?\<theta> T2 = B" by auto
      have ft: "ok (fastype env rb u) T2" using ft0 by (simp add: fastype_def)
      have tcT2: "tcons ?\<theta> T2" using fastype_tnorm[OF ac ft] tcu by auto
      have cu: "cunify_types alg B1 T2 env = returnW env"
        by (rule cunify_types_same_mod[OF ac B1(2) tcT2]) (simp add: B1(1) ft0(2))
      have eqv: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> ?s))"
      proof -
        have "mk_subst \<sigma> (tr (rlist_abs (instb \<rho> rb) (inst \<rho> t))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (dB.Var (code (AVar v)))"
          using mk_subst_equiv[OF conjunct1[OF get_eta_var_equiv[OF gevi]] solutionD(1)[OF isol]] .
        then have "mk_subst \<sigma> (tr (rlist_abs (instb \<rho> rb) (inst \<rho> t))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))" by simp
        from equiv_trans[OF equiv_sym[OF this] dsolvedD[OF dsi]] show ?thesis by (simp add: inst_rlist_abs)
      qed
      have tyrl: "typed env W [] ?s T"
      proof -
        have "has_type (tctx env W) (map snd (tnormb ?\<theta> rb) @ []) (tnormt ?\<theta> u) B" using nu by simp
        from has_type_rlist_abs[OF this] Tn show ?thesis by (simp add: typed_def tnormt_rlist_abs)
      qed
      have twr: "\<forall>U\<in>tys ?s. tyw ar ?\<theta> A U" using twd by (auto simp: tys_rlist_abs)
      have ws: "swf_tm ar [] ?s" using swf_tm_binding[of ar rb u] swd by (simp add: swf_tm_def swf_dp_def)
      have bs: "below (maxidx env) ?s" using bl(2) by (simp add: below_rlist_abs)
      have vm: "snd v \<le> maxidx env" using below_vps[OF bl(1) vps_head_of[OF htv]] by simp
      have nocc: "\<forall>U. (v, U) \<notin> reach (instE \<rho> env) (vps (inst \<rho> ?s))"
        using False bocc by (auto simp: occ_in_def vps_rlist_abs inst_rlist_abs)
      have hs: "\<forall>w U. ?s = Var w U \<longrightarrow> vt_lookup (tenv env) w = None"
      proof (intro allI impI)
        fix w U assume "?s = Var w U"
        then have "rb = [] \<and> u = Var w U" by (rule rlist_abs_Var)
        then show "vt_lookup (tenv env) w = None" using hu by simp
      qed
      from pvupdate_complete[OF pc vu WT twT tyrl twr ws bs vm nocc eqv hs] obtain env' where
        vup: "vupdate (v, T) ?s env = return env'" "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' dps" "pextends env' env"
        "tyenv env' = ?\<theta>" "maxidx env' = maxidx env"
        "\<forall>x U' u'. vt_lookup (tenv env') x = Some (U', u') \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
          (x = v \<and> u' = ?s) \<or> (\<exists>U. ?s = Var x U \<and> u' = Var v U)"
        by blast
      have ok: "okW (ff_assign alg env rb t u) env'"
        using 2 oc False bt ft cu vup(1)
        by (simp add: ff_assign_def bindW_def returnW_def return_def liftM_def)
      have "flexb env0 env'" if "flexb env0 env" "extends env env0" "fh env0 u" for env0
        unfolding flexb_def
      proof (intro allI impI)
        fix x U' u' assume l: "vt_lookup (tenv env') x = Some (U', u')" "vt_lookup (tenv env0) x = None"
        show "fh env0 u'"
        proof (cases "vt_lookup (tenv env) x")
          case None
          with vup(6) l(1) consider "x = v" "u' = ?s" | U where "?s = Var x U" "u' = Var v U" by blast
          then show ?thesis
          proof cases
            case 1
            then show ?thesis using that(3) by (simp add: fh_def)
          next
            case 2
            have "vt_lookup (tenv env0) v = None" by (rule extends_unbound[OF that(2) vu])
            with 2 show ?thesis by (simp add: fh_def)
          qed
        next
          case (Some p)
          with extendsD[of env' env] vup(3) l(1) have "vt_lookup (tenv env) x = Some (U', u')"
            by (auto simp: pextends_def)
          with that(1) l(2) show ?thesis unfolding flexb_def by blast
        qed
      qed
      moreover have "ffgood \<theta> W env env'" if "hsat \<theta> W t" "hsat \<theta> W u" "is_Var (head_of u)" for \<theta>
        unfolding ffgood_def
      proof (intro allI impI)
        fix x U' u' assume l: "vt_lookup (tenv env') x = Some (U', u')" "vt_lookup (tenv env) x = None"
        from that(3) obtain K V where hK: "head_of u = Var K V" by (cases "head_of u") auto
        have uK: "u = list_comb (Var K V) (snd (strip_comb u))" using head_of_list_comb[of u] hK by simp
        have Kn: "vt_lookup (tenv env) K = None" using hu hK by simp
        have nt: "length (snd (strip_comb t)) = ary \<theta> (W v)" using that(1) htv by (simp add: hsat_def)
        have nu: "length (snd (strip_comb u)) = ary \<theta> (W K)" using that(2) hK by (simp add: hsat_def)
        have lrb: "length (snd (strip_comb t)) = length rb" by (rule get_eta_var_args[OF 2])
        from vup(6) l consider "x = v" "u' = ?s" | U where "?s = Var x U" "u' = Var v U" by blast
        then show "\<exists>n K V bs. absp n u' (list_comb (Var K V) bs) \<and> vt_lookup (tenv env) K = None \<and>
            n = ary \<theta> (W x) \<and> length bs = ary \<theta> (W K)"
        proof cases
          case 1
          have "absp (length rb) u' u" using absp_rlist_abs[of 0 u u rb] 1(2) by simp
          then show ?thesis using uK Kn nt nu lrb 1(1)
            by (intro exI[of _ "length rb"] exI[of _ K] exI[of _ V] exI[of _ "snd (strip_comb u)"]) simp
        next
          case 2
          from rlist_abs_Var[OF 2(1)] have rb0: "rb = []" "u = Var x U" by simp_all
          have "length (snd (strip_comb u)) = 0" using rb0(2) by (simp add: strip_comb_def)
          then show ?thesis using 2(2) vu nt nu lrb rb0 hK
            by (intro exI[of _ 0] exI[of _ v] exI[of _ U] exI[of _ "[]"]) auto
        qed
      qed
      ultimately show ?thesis using ok vup(2-5) by blast
    qed
  qed
qed


subsection \<open>Cleaning a flexible term\<close>

lemma flexargs_short:
  "length js = length ts \<Longrightarrow> length ts < length Us \<Longrightarrow> flexargs js ts Us = raiseW CHANGE_FAIL"
proof (induction js ts arbitrary: Us rule: list_induct2)
  case Nil
  then show ?case by (cases Us) simp_all
next
  case (Cons j js t ts)
  then show ?case by (cases Us) (simp_all add: bindW_def raiseW_def)
qed

lemma arg_types_foldr_fun: "arg_types (foldr fun_type Us B) = Us @ arg_types B"
  by (induction Us) auto

lemma change_bnos_tnormt:
  "okW (change_bnos banned lev x) x' \<Longrightarrow> okW (change_bnos banned lev (tnormt \<theta> x)) (tnormt \<theta> x')"
  by (induction banned lev x arbitrary: x' rule: change_bnos.induct)
    (auto split: if_splits)

lemma change_bnos_tys: "okW (change_bnos banned lev x) x' \<Longrightarrow> tys x' = tys x"
  by (induction banned lev x arbitrary: x' rule: change_bnos.induct) (auto split: if_splits)

lemma rigid_bound_inst: "rigid_bound lev banned (inst \<rho> t) \<longleftrightarrow> rigid_bound lev banned t"
proof (induction lev banned t rule: rigid_bound.induct)
  case (1 lev banned t)
  obtain h args where sc: "strip_comb t = (h, args)" by (cases "strip_comb t")
  have sci: "strip_comb (inst \<rho> t) = (inst \<rho> h, map (inst \<rho>) args)" using strip_comb_inst[of \<rho> t] sc by simp
  show ?case
    using "1.IH"[OF sc[symmetric]] by (subst (1 2) rigid_bound.simps) (cases h; simp add: sc sci)
qed

lemma rigid_headed_inst[simp]: "rigid_headed (inst \<rho> t) \<longleftrightarrow> rigid_headed t"
  by (cases "head_of t") (simp_all add: rigid_headed_def)

text \<open>
  \<^const>\<open>clean_term\<close> on a flexible term whose instance only depends on the non-banned bound
  variables: it gives up with \<open>CHANGE_FAIL\<close>, or the term has a base type and it binds the head
  variable to an abstraction of a new variable applied to the kept arguments, for an extension of
  the solution. The type environment is kept.
\<close>

lemma pclean_term_complete:
  fixes rb rb' :: binders
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and tyt: "typed env W (map snd rb) t B" and nB: "tnorm (tyenv env) B = B"
    and twt: "\<forall>U\<in>snd ` set rb \<union> tys t. tyw ar (tyenv env) A U"
    and tw': "\<forall>U\<in>snd ` set rb'. tyw ar (tyenv env) A U"
    and bt: "below (maxidx env) t" and ht: "head_of t = Var v T" and vn: "vt_lookup (tenv env) v = None"
    and bn: "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j" "bset banned \<subseteq> {..<length rb}"
    and rb': "length rb' = length rb - card (bset banned)"
      "\<And>i. i < length rb \<Longrightarrow> i \<notin> bset banned \<Longrightarrow>
        squash (bset banned) i < length rb' \<and> rb' ! squash (bset banned) i = rb ! i"
    and dep: "dep_on Z (mk_subst \<sigma> (tr (inst \<rho> t)))" and Zb: "Z \<inter> bset banned = {}"
  shows "(\<exists>evs. clean_term banned env t = Some (evs, UErr CHANGE_FAIL)) \<or>
    (\<exists>env' t' W' \<sigma>'. okW (clean_term banned env t) (env', t') \<and> pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' dps \<and>
      agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env \<and>
      tyenv env' = tyenv env \<and> \<not> is_funT B \<and> typed env' W' (map snd rb') t' B \<and> is_Var (head_of t') \<and>
      (\<forall>U\<in>tys t'. tyw ar (tyenv env) A U) \<and> below (maxidx env') t' \<and>
      (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env') x = None) \<and>
      (\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v) \<and>
      (\<forall>x U. head_of t' = Var x U \<longrightarrow> x = v \<or> maxidx env < snd x) \<and>
      (\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
        flexb env0 env' \<and> fh env0 t') \<and>
      (\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> length (snd (strip_comb t)) = ary \<theta> (W v) \<longrightarrow>
        hsat \<theta> W' t' \<and> ffgood \<theta> W' env env'))"
proof -
  let ?\<theta> = "tyenv env"
  note pcd = pcinvD[OF pc]
  note pi = pinvD[OF pcd(1)]
  note pe = penv_invD[OF pi(1)]
  have sol: "tsol ?\<theta> \<rho>" using pcd(2) by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  note ci = pcinv_cinv[OF pc]
  note isol = cinvD(2)[OF ci]
  note \<sigma> = solutionD[OF isol]
  define ts where "ts = snd (strip_comb t)"
  let ?n = "length ts"
  have sc: "strip_comb t = (Var v T, ts)" using fst_strip_comb[of t] ht by (simp add: ts_def prod_eq_iff)
  have t_eq: "t = list_comb (Var v T) ts" using head_of_list_comb[of t] ht by (simp add: ts_def)
  from typed_list_comb_args[OF ac(1) tyt[unfolded t_eq]] obtain As where
    tyh: "typed env W (map snd rb) (Var v T) (foldr fun_type As B)"
    and tga: "list_all2 (typed env W (map snd rb)) ts As" and nAs: "map (tnorm ?\<theta>) As = As" by blast
  have lAs: "length As = ?n" using list_all2_lengthD[OF tga] by simp
  have Tn: "tnorm ?\<theta> T = foldr fun_type As B" and Vv: "tctx env W v = tnorm ?\<theta> T"
    using tyh nAs nB by (auto simp: typed_def tnorm_foldr_fun elim: has_type_elims)
  have WT: "tnorm ?\<theta> (W v) = tnorm ?\<theta> T" using Vv vn by (simp add: vtyp_def)
  have tT: "T \<in> tys t" using t_eq by (simp add: tys_list_comb)
  have twT: "tyw ar ?\<theta> A T" and tcT: "tcons ?\<theta> T" using twt tT tcU by auto
  have vm: "snd v \<le> maxidx env" using bt t_eq by (simp add: below_list_comb)
  show ?thesis
  proof (cases "is_funT B")
    case True
    have aB: "arg_types B \<noteq> []" using True is_funT_arg_types by blast
    obtain Us' B' where st: "strip_type env T = return (Us', B')"
      and mU: "map (tnorm ?\<theta>) Us' = arg_types (tnorm ?\<theta> T)"
      by (rule strip_type_ptnorm[OF ac tcT tnorm_arg_res res_type_nonfun])
    have "length Us' = ?n + length (arg_types B)"
      using arg_cong[OF mU, of length] Tn lAs by (simp add: arg_types_foldr_fun)
    then have "flexargs (downto0_list ?n) ts Us' = raiseW CHANGE_FAIL"
      using aB by (intro flexargs_short) (simp_all add: downto0_list_def)
    then show ?thesis by (simp add: clean_term_def sc st liftM_return bindW_def raiseW_def returnW_def)
  next
    case nfB: False
    obtain Ts B0 where st: "strip_type env T = return (Ts, B0)" and mTs: "map (tnorm ?\<theta>) Ts = As"
      and nB0: "tnorm ?\<theta> B0 = B" and tcTs: "\<forall>U\<in>set Ts. tcons ?\<theta> U" and tcB0: "tcons ?\<theta> B0"
      by (rule strip_type_ptnorm[OF ac tcT Tn nfB])
    have twTB: "(\<forall>U\<in>set Ts. tyw ar ?\<theta> A U) \<and> tyw ar ?\<theta> A B0"
      by (rule strip_type_tyw[OF _ pi(2) twT]) (use st in \<open>simp add: return_def\<close>)
    have lTs: "length Ts = ?n" using arg_cong[OF mTs, of length] lAs by simp
    have tsk: "typed env W (map snd rb) (ts ! k) (Ts ! k)" "below (maxidx env) (ts ! k)"
      "\<forall>U\<in>tys (ts ! k). tyw ar ?\<theta> A U" if "k < ?n" for k
    proof -
      have "typed env W (map snd rb) (ts ! k) (As ! k)" using tga that by (simp add: list_all2_conv_all_nth)
      moreover have "As ! k = tnorm ?\<theta> (Ts ! k)" using mTs that lTs by auto
      ultimately show "typed env W (map snd rb) (ts ! k) (Ts ! k)"
        using typed_tnorm[OF ac(1), of W "map snd rb" "ts ! k" "Ts ! k"] by simp
      show "below (maxidx env) (ts ! k)" using bt t_eq that by (simp add: below_list_comb)
      show "\<forall>U\<in>tys (ts ! k). tyw ar ?\<theta> A U" using twt t_eq that by (auto simp: tys_list_comb)
    qed
    let ?fas = "map (\<lambda>k. Flarg (downto0_list ?n ! k) (ts ! k) (Ts ! k)) [0..<?n]"
    have fa: "flexargs (downto0_list ?n) ts Ts = returnW ?fas"
      by (rule flexargs_return) (simp_all add: downto0_list_def lTs)
    let ?del = "list_all rigid_headed ts"
    define fas where "fas = map (\<lambda>k. Flarg (downto0_list ?n ! k) (ts ! k) (Ts ! k)) [0..<?n]"
    have lfas: "length fas = ?n" by (simp add: fas_def)
    have fas_nth: "fas ! k = Flarg (integer_of_nat (?n - 1 - k)) (ts ! k) (Ts ! k)" if "k < ?n" for k
      using that by (simp add: fas_def downto0_list_nth)
    define P where "P = (\<lambda>a. \<not> (?del \<and> rigid_bound 0 banned (fl_t a)))"
    define R where "R = (\<lambda>a' a. fl_j a' = fl_j a \<and> fl_T a' = fl_T a \<and> okW (change_bnos banned 0 (fl_t a)) (fl_t a'))"
    have ct: "clean_term banned env t = do {
        cas \<leftarrow> foldrW (change_arg ?del banned) fas [];
        let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) B0);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')})}"
      unfolding clean_term_def by (simp add: sc st fa liftM_return fas_def)
    consider (err) evs where "foldrW (change_arg ?del banned) fas [] = Some (evs, UErr CHANGE_FAIL)"
      | (ok) ks evs0 where "foldrW (change_arg ?del banned) fas [] = Some (evs0, UOk ks)"
        "list_all2 R ks (filter P fas)"
      using foldrW_change_arg_cases[of ?del banned fas "[]"] unfolding P_def R_def by auto
    then show ?thesis
    proof cases
      case err
      then show ?thesis by (simp add: ct bindW_def)
    next
      case (ok cas evs0)
      define args where "args = sort_args cas"
      define ts' where "ts' = map fl_t args"
      have sa: "set args = set cas" by (simp add: args_def set_sort_args)
      have lc: "length cas = length (filter P fas)" using ok(2) by (rule list_all2_lengthD)
      have Pa: "\<exists>k<?n. \<not> (?del \<and> rigid_bound 0 banned (ts ! k)) \<and> fl_j a = integer_of_nat (?n - 1 - k) \<and>
          fl_T a = Ts ! k \<and> okW (change_bnos banned 0 (ts ! k)) (fl_t a)" if "a \<in> set args" for a
      proof -
        from that sa obtain p where p: "p < length cas" "a = cas ! p" by (auto simp: in_set_conv_nth)
        with ok(2) have r: "R a (filter P fas ! p)" by (simp add: list_all2_conv_all_nth)
        have "filter P fas ! p \<in> set (filter P fas)" by (rule nth_mem) (use p(1) lc in simp)
        then have "filter P fas ! p \<in> set fas" "P (filter P fas ! p)" by simp_all
        then obtain k where k: "k < ?n" "filter P fas ! p = fas ! k" "P (fas ! k)"
          using lfas by (auto simp: in_set_conv_nth)
        with r show ?thesis by (intro exI[of _ k]) (simp add: fas_nth R_def P_def)
      qed
      have kept: "\<exists>a\<in>set args. fl_j a = integer_of_nat (?n - 1 - k)"
        if "k < ?n" "\<not> (?del \<and> rigid_bound 0 banned (ts ! k))" for k
      proof -
        have "fas ! k \<in> set fas" using that lfas by simp
        then have "fas ! k \<in> set (filter P fas)" using that by (simp add: fas_nth P_def)
        then obtain p where p: "p < length (filter P fas)" "filter P fas ! p = fas ! k"
          unfolding in_set_conv_nth by blast
        with ok(2) lc have "p < length cas" "R (cas ! p) (fas ! k)" by (auto simp: list_all2_conv_all_nth)
        then show ?thesis using that sa by (intro bexI[of _ "cas ! p"]) (simp_all add: R_def fas_nth)
      qed
      let ?rbn = "map (tnorm ?\<theta>) (map snd rb)" and ?rbn' = "map (tnorm ?\<theta>) (map snd rb')"
      have rel0: "\<forall>i<length ?rbn. (i < nat_of_integer 0 \<or> i - nat_of_integer 0 \<notin> bset banned) \<longrightarrow>
          shift_at (nat_of_integer 0) (squash (bset banned)) i < length ?rbn' \<and>
          ?rbn' ! shift_at (nat_of_integer 0) (squash (bset banned)) i = ?rbn ! i"
        using rb'(2) by (auto simp: shift_at_def)
      have tya: "typed env W (map snd rb') (fl_t a) (fl_T a) \<and> below (maxidx env) (fl_t a) \<and>
          (\<forall>U\<in>tys (fl_t a). tyw ar ?\<theta> A U)" if "a \<in> set args" for a
      proof -
        from Pa[OF that] obtain k where k: "k < ?n" "fl_T a = Ts ! k"
          "okW (change_bnos banned 0 (ts ! k)) (fl_t a)"
          by blast
        have "has_type (tctx env W) ?rbn (tnormt ?\<theta> (ts ! k)) (tnorm ?\<theta> (Ts ! k))"
          using tsk(1)[OF k(1)] by (simp add: typed_def)
        from change_bnos_typed[OF change_bnos_tnormt[OF k(3)] _ bn(1,2) this rel0]
        have "typed env W (map snd rb') (fl_t a) (Ts ! k)" by (simp add: typed_def)
        moreover have "below (maxidx env) (fl_t a)"
          using tsk(2)[OF k(1)] change_bnos_vars[OF k(3)] by (simp add: below_def)
        moreover have "\<forall>U\<in>tys (fl_t a). tyw ar ?\<theta> A U" using tsk(3)[OF k(1)] change_bnos_tys[OF k(3)] by simp
        ultimately show ?thesis using k(2) by simp
      qed
      have vn0: "vt_lookup (tenv env0) v = None" if "extends env env0" for env0
        by (rule extends_unbound[OF that vn])
      have tyv: "typed env W Bs (Var v T) (foldr fun_type Ts B0)" for Bs
        using Vv Tn mTs nB0 by (simp add: typed_def tnorm_foldr_fun has_type.Var)
      show ?thesis
      proof (cases "decreasing (ilength Ts) args")
        case True
        have ks: "map (nat_of_integer \<circ> fl_j) args = downs ?n"
          using decreasing_downs[of ?n args] True lTs by (simp add: ilength_eq)
        then have la: "length args = ?n" by (metis length_downs length_map)
        have argp: "fl_T (args ! p) = Ts ! p" if "p < ?n" for p
        proof -
          have "args ! p \<in> set args" using that la by simp
          from Pa[OF this] obtain k where k: "k < ?n" "fl_j (args ! p) = integer_of_nat (?n - 1 - k)"
            "fl_T (args ! p) = Ts ! k" by blast
          have "nat_of_integer (fl_j (args ! p)) = ?n - 1 - p"
            using arg_cong[OF ks, of "\<lambda>xs. xs ! p"] that la by (simp add: downs_nth)
          with k(2) have "?n - 1 - k = ?n - 1 - p" by simp
          with k(1) that have "k = p" by simp
          with k(3) show ?thesis by simp
        qed
        have "typed env W (map snd rb') (ts' ! i) (Ts ! i)" if "i < ?n" for i
          using tya[OF nth_mem[of i args]] argp[OF that] that la by (simp add: ts'_def)
        then have tyts': "list_all2 (typed env W (map snd rb')) ts' Ts"
          unfolding list_all2_conv_all_nth using la lTs by (simp add: ts'_def)
        have ok': "okW (clean_term banned env t) (env, list_comb (Var v T) ts')"
          using ok(1) True by (simp add: ct bindW_def Let_def returnW_def args_def ts'_def)
        have "typed env W (map snd rb') (list_comb (Var v T) ts') B0" by (rule typed_list_comb[OF tyv tyts'])
        then have "typed env W (map snd rb') (list_comb (Var v T) ts') B"
          using typed_tnorm[OF ac(1), of W "map snd rb'" "list_comb (Var v T) ts'" B0] nB0 nB
          by (metis typed_tnorm[OF ac(1)])
        moreover have "below (maxidx env) (list_comb (Var v T) ts')"
          using tya vm by (auto simp: below_list_comb ts'_def)
        moreover have "\<forall>U\<in>tys (list_comb (Var v T) ts'). tyw ar ?\<theta> A U"
          using tya twT by (auto simp: tys_list_comb ts'_def)
        moreover have "fh env0 (list_comb (Var v T) ts')" if "extends env env0" for env0
          using vn0[OF that] by (simp add: fh_def)
        moreover have "hsat \<theta> W (list_comb (Var v T) ts')" if "length (snd (strip_comb t)) = ary \<theta> (W v)" for \<theta>
          using that la sc strip_comb_list_comb_eq[of "Var v T" ts'] by (simp add: hsat_def ts'_def)
        ultimately show ?thesis using ok' pc vn nfB
          by (intro disjI2 exI[of _ env] exI[of _ "list_comb (Var v T) ts'"] exI[of _ W] exI[of _ \<sigma>])
            (auto simp: agree_def agreeV_def)
      next
        case False
        have nTs: "Ts \<noteq> []"
        proof
          assume "Ts = []"
          then have "?n = 0" using lTs by simp
          then have "args = []" using Pa by (cases args) auto
          with False \<open>Ts = []\<close> show False by simp
        qed
        define ks where "ks = map (nat_of_integer \<circ> fl_j) args"
        have ksb: "\<forall>k\<in>set ks. k < ?n" using Pa by (fastforce simp: ks_def integer_reps)
        have rk: "rev Ts ! nat_of_integer (fl_j a) = fl_T a \<and> 0 \<le> fl_j a \<and> nat_of_integer (fl_j a) < ?n"
          if "a \<in> set args" for a
        proof -
          from Pa[OF that] obtain k where k: "k < ?n" "fl_j a = integer_of_nat (?n - 1 - k)" "fl_T a = Ts ! k"
            by blast
          have nj: "nat_of_integer (fl_j a) = ?n - 1 - k" using k(2) by simp
          have pj: "0 \<le> fl_j a" using k(2) by (simp add: less_eq_integer.rep_eq)
          have "length Ts - Suc (?n - 1 - k) = k" using k(1) lTs by simp
          then show ?thesis using nj pj k lTs by (simp add: rev_nth)
        qed
        have nodel: "?del \<and> rigid_bound 0 banned (ts ! (?n - 1 - k))" if "k < ?n" "k \<notin> set ks" for k
        proof (rule ccontr)
          assume nd: "\<not> (?del \<and> rigid_bound 0 banned (ts ! (?n - 1 - k)))"
          have "?n - 1 - k < ?n" using that(1) by simp
          from kept[OF this nd] obtain a where a: "a \<in> set args" "fl_j a = integer_of_nat (?n - 1 - (?n - 1 - k))"
            by blast
          have "?n - 1 - (?n - 1 - k) = k" using that(1) by simp
          with a have "k \<in> set ks" by (force simp: ks_def)
          with that(2) show False by blast
        qed
        \<comment> \<open>The instance\<close>
        let ?V = "ityp \<rho> env W" and ?Is = "map (tsubst \<rho>) Ts" and ?IB = "tsubst \<rho> B0"
        have tsk_i: "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> (ts ! k)) (tsubst \<rho> (Ts ! k))" if "k < ?n" for k
        proof -
          have "\<forall>U\<in>set (map snd rb) \<union> tys (ts ! k). tcons ?\<theta> U" using twt tsk(3)[OF that] tcU by auto
          moreover have "tcons ?\<theta> (Ts ! k)" using tcTs that lTs by simp
          ultimately show ?thesis using typed_inst[OF ac sol _ _ tsk(1)[OF that]] by (simp add: map_snd_instb)
        qed
        have iAs: "map (tsubst \<rho>) As = ?Is" unfolding mTs[symmetric] using tcTs by (auto simp: tsubst_tnorm[OF ac sol])
        have iB: "tsubst \<rho> B = ?IB" using nB0 tsubst_tnorm[OF ac sol tcB0] by auto
        have iV: "?V v = foldr fun_type ?Is ?IB"
          using Vv Tn iAs iB by (simp add: tsubst_foldr_fun)
        define sts where "sts = map (\<lambda>a. mk_subst \<sigma> (tr (inst \<rho> a))) ts"
        have rsts: "rev sts ! k = mk_subst \<sigma> (tr (inst \<rho> (ts ! (?n - 1 - k))))" if "k < ?n" for k
          using that by (simp add: sts_def rev_nth)
        have tyv: "(e, \<tau>') \<turnstile> \<sigma> (code (AVar v)) : map trty ?Is \<Rrightarrow> trty ?IB" for e
          using typed_onD[OF \<sigma>(2), of "code (AVar v)" e] iV by (simp add: trty_foldr)
        have dep': "dep_on Z (\<sigma> (code (AVar v)) \<degree>\<degree> sts)"
          using dep by (simp add: t_eq inst_list_comb tr_list_comb sts_def comp_def)
        obtain w where w: "no_loose_bound w 0" "\<And>e. (e, \<tau>') \<turnstile> w : map (\<lambda>k. rev (map trty ?Is) ! k) ks \<Rrightarrow> trty ?IB"
          "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (map trty ?Is)) (w \<degree>\<degree> map BVar ks)"
        proof (rule prune_value[of "\<sigma> (code (AVar v))" \<tau>' "map trty ?Is" "trty ?IB" sts Z ks])
          show "no_loose_bound (\<sigma> (code (AVar v))) 0" using closed_onD[OF \<sigma>(1)] by simp
          show "(e, \<tau>') \<turnstile> \<sigma> (code (AVar v)) : map trty ?Is \<Rrightarrow> trty ?IB" for e by (rule tyv)
          show "dep_on Z (\<sigma> (code (AVar v)) \<degree>\<degree> sts)" by (rule dep')
          show "\<forall>k\<in>set ks. k < length (map trty ?Is)" using ksb lTs by simp
          show "length sts = length (map trty ?Is)" using lTs by (simp add: sts_def)
          show "\<forall>i<length (map trty ?Is). \<exists>h A. is_atom h \<and> rev sts ! i = h \<degree>\<degree> A"
            if "\<exists>k<length (map trty ?Is). k \<notin> set ks"
          proof -
            from that lTs obtain k where "k < ?n" "k \<notin> set ks" by auto
            from nodel[OF this] have del: ?del by blast
            show ?thesis
            proof (intro allI impI)
              fix i assume "i < length (map trty ?Is)"
              then have i: "i < ?n" using lTs by simp
              have "rigid_headed (inst \<rho> (ts ! (?n - 1 - i)))" using del i by (simp add: list_all_length)
              from rigid_headed_atom[OF this \<sigma>(3)] show "\<exists>h A. is_atom h \<and> rev sts ! i = h \<degree>\<degree> A"
                using rsts[OF i] by simp
            qed
          qed
          show "\<forall>i<length (map trty ?Is). \<exists>E T. (E, \<tau>') \<turnstile> rev sts ! i : T"
          proof (intro allI impI)
            fix i assume "i < length (map trty ?Is)"
            then have i: "i < ?n" "?n - 1 - i < ?n" using lTs by simp_all
            from solution_tr_typed[OF isol tsk_i[OF i(2)]] rsts[OF i(1)]
            show "\<exists>E T. (E, \<tau>') \<turnstile> rev sts ! i : T" by auto
          qed
          show "\<not> dep_on Z (rev sts ! k)" if "k < length (map trty ?Is)" "k \<notin> set ks" for k
          proof
            assume d: "dep_on Z (rev sts ! k)"
            from that lTs have k: "k < ?n" by simp
            from nodel[OF k that(2)] have "rigid_bound 0 banned (inst \<rho> (ts ! (?n - 1 - k)))"
              by (simp add: rigid_bound_inst)
            from rigid_bound_dep[OF \<sigma>(1,3) this _ bn(2)] d rsts[OF k]
            obtain j where "j \<in> set banned" "nat_of_integer j \<in> Z" by auto
            with Zb show False by (auto simp: bset_def)
          qed
        qed (rule that)
        \<comment> \<open>The new variable\<close>
        define T' where "T' = foldr fun_type (map fl_T args) B0"
        have fTs: "fl_T a \<in> set Ts" if "a \<in> set args" for a using Pa[OF that] lTs by auto
        have "rev (map trty ?Is) ! nat_of_integer (fl_j a) = trty (tsubst \<rho> (fl_T a))" if "a \<in> set args" for a
          using rk[OF that] lTs by (simp add: rev_map)
        then have mty: "map (\<lambda>k. rev (map trty ?Is) ! k) ks = map trty (map (tsubst \<rho>) (map fl_T args))"
          unfolding ks_def map_map by (intro map_cong) auto
        have wT': "(e, \<tau>') \<turnstile> w : trty (tsubst \<rho> T')" for e
          using w(2)[of e] mty by (simp add: T'_def tsubst_foldr_fun trty_foldr)
        have twT': "tyw ar ?\<theta> A T'" using twTB fTs by (auto simp: T'_def tyw_foldr_fun)
        obtain env1 G where g: "genvar (fst v) env T' = (env1, G)" by (cases "genvar (fst v) env T'")
        define x' where "x' = (fst v, maxidx env + 1)"
        define \<sigma>1 where "\<sigma>1 = \<sigma>(code (AVar x') := w)"
        define W1 where "W1 = W(x' := T')"
        note ge = genvar_pextend[OF pc g twT' w(1) wT', folded x'_def, folded \<sigma>1_def W1_def]
        note pi1 = pinvD[OF pcinvD(1)[OF ge(1)]]
        have x'n: "vt_lookup (tenv env1) x' = None"
        proof (rule ccontr)
          assume "vt_lookup (tenv env1) x' \<noteq> None"
          then obtain U u where "vt_lookup (tenv env) x' = Some (U, u)" using ge(7) by auto
          from fresh_envD[OF pe(6) this] show False by (simp add: x'_def)
        qed
        have vx': "v \<noteq> x'" using vm by (cases v) (auto simp: x'_def less_eq_integer.rep_eq plus_integer.rep_eq)
        have tcx': "tctx env1 W1 x' = tnorm ?\<theta> T'" using x'n ge(8,10) by (simp add: vtyp_def)
        define body where "body = list_comb G (map (Bound \<circ> fl_j) args)"
        have tybody: "typed env1 W1 (rev Ts) body B0"
        proof -
          have "typed env1 W1 (rev Ts) G T'" using ge(5,8) tcx' by (simp add: typed_def has_type.Var)
          moreover have "list_all2 (typed env1 W1 (rev Ts)) (map (Bound \<circ> fl_j) args) (map fl_T args)"
            using rk lTs by (auto simp: list_all2_conv_all_nth typed_def has_type_Bound_iff rev_map)
          ultimately show ?thesis unfolding body_def T'_def by (rule typed_list_comb)
        qed
        have tyabs: "typed env1 W1 [] (types_abs Ts body) T"
        proof -
          have "typed env1 W1 [] (types_abs Ts body) (foldr fun_type Ts B0)"
            using typed_types_abs[of env1 W1 Ts "[]" body B0] tybody by simp
          moreover have "tnorm ?\<theta> T = tnorm ?\<theta> (foldr fun_type Ts B0)"
            using Tn mTs nB0 by (simp add: tnorm_foldr_fun)
          ultimately show ?thesis using ge(8) by (simp add: typed_tnorm_cong)
        qed
        have WT1: "tnorm (tyenv env1) (W1 v) = tnorm (tyenv env1) T" using WT vx' ge(8) by (simp add: W1_def)
        have vn1: "vt_lookup (tenv env1) v = None" using vn ge(7) by simp
        have twabs: "\<forall>X\<in>tys (types_abs Ts body). tyw ar (tyenv env1) A X"
          using twTB twT' ge(5,8) by (auto simp: tys_types_abs body_def tys_list_comb)
        have wsabs: "swf_tm ar [] (types_abs Ts body)"
        proof -
          have h: "has_type (tctx env1 W1) [] (tnormt ?\<theta> (types_abs Ts body)) (tnorm ?\<theta> T)"
            using tyabs ge(8) by (simp add: typed_def)
          have "proper (types_abs Ts body)" using has_type_proper[OF h] by simp
          moreover have "no_loose_bound (tr (types_abs Ts body)) 0" using has_type_closed[OF h] by simp
          moreover have "twft ar (types_abs Ts body)" using twabs by (simp add: twft_tys tyw_def)
          ultimately show ?thesis by (simp add: swf_tm_def)
        qed
        have vm1: "snd v \<le> maxidx env1" using vm ge(4) by (simp add: less_eq_integer.rep_eq plus_integer.rep_eq)
        have babs: "below (maxidx env1) (types_abs Ts body)"
          using ge(4,5) by (simp add: below_vps_iff body_def vps_list_comb x'_def comp_def)
        have vpsb: "vps (inst \<rho> (types_abs Ts body)) = {(x', tsubst \<rho> T')}"
          using ge(5) by (simp add: inst_types_abs body_def inst_list_comb vps_list_comb comp_def)
        have nocc: "\<forall>U. (v, U) \<notin> reach (instE \<rho> env1) (vps (inst \<rho> (types_abs Ts body)))"
        proof -
          have "lk (instE \<rho> env1) x' (tsubst \<rho> T') = None" using x'n by (simp add: lk_def)
          from reach_unbound[OF this] show ?thesis using vx' vpsb by simp
        qed
        have mabs: "mk_subst \<sigma>1 (tr (inst \<rho> (types_abs Ts body))) = Abs_m (length Ts) (w \<degree>\<degree> map BVar ks)"
          using ge(5,9) by (simp add: inst_types_abs tr_types_abs mk_subst_Abs_m body_def inst_list_comb
              tr_list_comb ks_def comp_def)
        have eqv: "\<sigma>1 (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>1 (tr (inst \<rho> (types_abs Ts body)))"
          using agree_Var[OF ge(2) vm] w(3) mabs by simp
        have hs: "\<forall>w U. types_abs Ts body = Var w U \<longrightarrow> vt_lookup (tenv env1) w = None"
          using nTs by (cases Ts) auto
        from pvupdate_complete[OF ge(1) vn1 WT1 _ tyabs twabs wsabs babs vm1 nocc eqv hs] twT ge(8)
        obtain env2 where vu: "vupdate (v, T) (types_abs Ts body) env1 = return env2"
          "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env2 dps" "pextends env2 env1" "tyenv env2 = tyenv env1"
          "maxidx env2 = maxidx env1"
          "\<forall>x U' u. vt_lookup (tenv env2) x = Some (U', u) \<longrightarrow> vt_lookup (tenv env1) x = None \<longrightarrow>
            (x = v \<and> u = types_abs Ts body) \<or> (\<exists>U. types_abs Ts body = Var x U \<and> u = Var v U)"
          by auto
        have te2: "tyenv env2 = ?\<theta>" using vu(4) ge(8) by simp
        have tl2: "vt_lookup (tenv env2) x \<noteq> None \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x = v" for x
          using vu(6) ge(7) nTs by (cases Ts) fastforce+
        \<comment> \<open>The normalized new term\<close>
        note pc2 = pcinvD[OF pcinv_Nil[OF vu(2)]]
        note pi2 = pinvD[OF vu(2)[THEN pcinvD(1)]]
        have x'n2: "vt_lookup (tenv env2) x' = None"
        proof (rule ccontr)
          assume "vt_lookup (tenv env2) x' \<noteq> None"
          from tl2[OF this] x'n ge(7) vx' show False by simp
        qed
        have tyG: "typed env2 W1 (map snd rb') (list_comb G ts') B0"
        proof -
          have "typed env2 W1 (map snd rb') G T'"
            using ge(5,10) x'n2 te2 by (simp add: typed_def vtyp_def has_type.Var)
          moreover have "list_all2 (typed env2 W1 (map snd rb')) ts' (map fl_T args)"
            unfolding list_all2_conv_all_nth ts'_def
            using tya[OF nth_mem] typed_pext[OF _ te2 pi(6) pi2(6) ge(3)] by auto
          ultimately show ?thesis unfolding T'_def by (rule typed_list_comb)
        qed
        have twG: "\<forall>U\<in>set (map snd rb') \<union> tys (list_comb G ts'). tyw ar (tyenv env2) A U"
          using tw' tya twT' ge(5) te2 by (auto simp: tys_list_comb ts'_def)
        have mx2: "maxidx env2 = maxidx env + 1" using vu(5) ge(4) by simp
        have mle: "maxidx env \<le> maxidx env2" using mx2 by (simp add: less_eq_integer.rep_eq plus_integer.rep_eq)
        have "below (maxidx env2) G" using ge(5) mx2 by (simp add: x'_def below_def)
        moreover have "\<forall>s\<in>set ts'. below (maxidx env2) s" using tya below_mono[OF _ mle] by (auto simp: ts'_def)
        ultimately have bG: "below (maxidx env2) (list_comb G ts')" by (simp add: below_list_comb)
        from norm_term_pterm[OF pc2(1) pc2(2) tyG twG bG] obtain t'' where
          nt: "norm_term env2 (list_comb G ts') = return t''" "typed env2 W1 (map snd rb') t'' B0"
          "\<forall>U\<in>tys t''. tyw ar (tyenv env2) A U" "below (maxidx env2) t''"
          "\<forall>x U. head_of t'' = Var x U \<longrightarrow> vt_lookup (tenv env2) x = None"
          "\<forall>x U. head_of (list_comb G ts') = Var x U \<longrightarrow> vt_lookup (tenv env2) x = None \<longrightarrow>
            (\<exists>U'. head_of t'' = Var x U')"
          "\<forall>env0. flexb env0 env2 \<longrightarrow> fh env0 (list_comb G ts') \<longrightarrow> fh env0 t''"
          by blast
        have ok2: "okW (clean_term banned env t) (env2, t'')"
          using ok(1) False g[unfolded T'_def] vu(1) nt(1) unfolding ct
          by (simp add: bindW_def Let_def args_def ts'_def body_def liftM_def returnW_def return_def)
        have ty'': "typed env2 W1 (map snd rb') t'' B"
          using nB0 nB te2 typed_tnorm_cong[OF nt(2) refl, of B] by simp
        from nt(6) ge(5) x'n2 obtain U' where hx': "head_of t'' = Var x' U'" by auto
        have hd: "\<forall>x U. head_of t'' = Var x U \<longrightarrow> x = v \<or> maxidx env < snd x"
          using hx' by (simp add: x'_def less_integer.rep_eq plus_integer.rep_eq)
        have fl: "flexb env0 env2 \<and> fh env0 t''"
          if "flexb env0 env" "extends env env0" "fresh_env env0" "maxidx env0 \<le> maxidx env" for env0
        proof -
          have x0: "vt_lookup (tenv env0) x' = None"
          proof (rule ccontr)
            assume "vt_lookup (tenv env0) x' \<noteq> None"
            then obtain U u where "vt_lookup (tenv env0) x' = Some (U, u)" by auto
            from fresh_envD[OF that(3) this] that(4) show False
              by (simp add: x'_def less_eq_integer.rep_eq plus_integer.rep_eq)
          qed
          have fG: "fh env0 (list_comb G ts')" using ge(5) x0 by (simp add: fh_def)
          have "flexb env0 env2"
            unfolding flexb_def
          proof (intro allI impI)
            fix x U u assume l: "vt_lookup (tenv env2) x = Some (U, u)" "vt_lookup (tenv env0) x = None"
            show "fh env0 u"
            proof (cases "vt_lookup (tenv env1) x")
              case None
              from vu(6)[rule_format, OF l(1) None] nTs have "u = types_abs Ts body" by (cases Ts) auto
              then show ?thesis using fG by (simp add: fh_def body_def)
            next
              case (Some p)
              with extendsD[OF pextendsD(1)[OF vu(3)] Some] l(1) ge(7)
              have "vt_lookup (tenv env) x = Some (U, u)" by simp
              with that(1) l(2) show ?thesis unfolding flexb_def by blast
            qed
          qed
          with nt(7) fG show ?thesis by blast
        qed
        have ext2: "pextends env2 env" by (rule pextends_trans[OF vu(3) ge(6)])
        have aryT': "ary \<theta> T' = length args" if "tacyc \<theta>" "textends \<theta> ?\<theta>" for \<theta>
        proof -
          have "ary ?\<theta> B0 = 0" using nB0 nfB arg_types_nonfun by simp
          then have "ary \<theta> B0 = 0" using ary_mono[OF ac(1) that(2), of B0] by simp
          then show ?thesis by (simp add: T'_def tnorm_foldr_fun arg_types_foldr_fun)
        qed
        have hs: "hsat \<theta> W1 t'' \<and> ffgood \<theta> W1 env env2"
          if "tacyc \<theta>" "textends \<theta> ?\<theta>" "length (snd (strip_comb t)) = ary \<theta> (W v)" for \<theta>
        proof -
          have a: "ary \<theta> (W1 x') = length ts'" using aryT'[OF that(1,2)] ge(10) by (simp add: ts'_def)
          have sp: "absp 0 (list_comb G ts') (list_comb (Var x' T') ts')" using ge(5) by simp
          from norm_term_spine[OF nt(1) pc2(1) pc2(2) tyG twG bG ffgood_refl[of \<theta> W1 env2] extends_refl[of env2]
              sp x'n2] a x'n2
          obtain U' cs where t'': "t'' = list_comb (Var x' U') cs" "length cs = length ts'"
            by auto
          have "hsat \<theta> W1 t''" using a t'' strip_comb_list_comb_eq[of "Var x' U'" cs] by (simp add: hsat_def)
          moreover have "ffgood \<theta> W1 env env2"
            unfolding ffgood_def
          proof (intro allI impI)
            fix X U u assume l: "vt_lookup (tenv env2) X = Some (U, u)" "vt_lookup (tenv env) X = None"
            then have Xv: "X = v" using tl2 by auto
            have "vt_lookup (tenv env1) X = None" using l(2) ge(7) by simp
            from vu(6)[rule_format, OF l(1) this] nTs have ue: "u = types_abs Ts body" by (cases Ts) auto
            have "ary \<theta> (W1 X) = length Ts" using Xv vx' that(3) sc lTs by (simp add: W1_def)
            moreover have "length (map (Bound \<circ> fl_j) args) = ary \<theta> (W1 x')" using a by (simp add: ts'_def)
            moreover have "vt_lookup (tenv env) x' = None" using x'n ge(7) by simp
            ultimately show "\<exists>n K V bs. absp n u (list_comb (Var K V) bs) \<and> vt_lookup (tenv env) K = None \<and>
                n = ary \<theta> (W1 X) \<and> length bs = ary \<theta> (W1 K)"
              using absp_types_abs[of Ts body] ue ge(5)
              by (intro exI[of _ "length Ts"] exI[of _ x'] exI[of _ T'] exI[of _ "map (Bound \<circ> fl_j) args"])
                (simp add: body_def)
          qed
          ultimately show ?thesis ..
        qed
        show ?thesis
          using ok2 vu(2) ge(2,3) mx2 ext2 te2 nfB ty'' nt(3,4,5) tl2 hd fl hs hx'
          by (intro disjI2 exI[of _ env2] exI[of _ t''] exI[of _ W1] exI[of _ \<sigma>1])
            (auto simp: less_eq_integer.rep_eq plus_integer.rep_eq)
      qed
    qed
  qed
qed


subsection \<open>Cleaning flex-flex pairs\<close>

text \<open>The remaining pairs are solved by the instance of the solution.\<close>

abbreviation itps :: "tinst \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list" where
  "itps \<rho> tps \<equiv> map (\<lambda>(a, b). (inst \<rho> a, inst \<rho> b)) tps"

lemma padd_tpair_complete:
  "dsolved \<sigma> (instd \<rho> (rb, t, u)) \<Longrightarrow> tsolved \<sigma> (itps \<rho> tps) \<Longrightarrow> tsolved \<sigma> (itps \<rho> (add_tpair rb t u tps))"
  by (auto simp: add_tpair_def Let_def tsolved_def dsolved_def inst_rlist_abs)

lemma ptsolved_agree:
  "tsolved \<sigma> (itps \<rho> tps) \<Longrightarrow> \<forall>(a, b)\<in>set tps. below m a \<and> below m b \<Longrightarrow> agree m \<sigma> \<sigma>' \<Longrightarrow>
    tsolved \<sigma>' (itps \<rho> tps)"
  by (rule tsolved_agree) auto

lemma loose_BVars_tr_inst[simp]: "loose_BVars (tr (inst \<rho> t)) = loose_BVars (tr t)"
  by (induction t) auto

text \<open>
  The remaining pairs are flex-flex pairs under a binder, as \<^const>\<open>tpok\<close>: typed terms of the
  same type, whose flexible heads are unbound in the environment \<open>e0\<close> of the flex-flex phase.
\<close>

definition ptpok :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> env \<Rightarrow>
    pterm \<times> pterm \<Rightarrow> bool" where
  "ptpok ar A W env e0 ab \<longleftrightarrow> (\<exists>rb a b B. ab = (rlist_abs rb a, rlist_abs rb b) \<and> sbinders ar rb \<and>
    swf_tm ar rb a \<and> swf_tm ar rb b \<and> (\<forall>U\<in>snd ` set rb \<union> tys a \<union> tys b. tyw ar (tyenv env) A U) \<and>
    typed env W (map snd rb) a B \<and> typed env W (map snd rb) b B \<and>
    below (maxidx env) a \<and> below (maxidx env) b \<and> fh e0 a \<and> fh e0 b)"

text \<open>A step of the flex-flex phase keeps the bindings since \<open>e0\<close> flexible, and the remaining pairs:\<close>

definition ptpstep :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow>
    (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "ptpstep ar A W env W' env' t u tps tps' \<longleftrightarrow> (\<forall>e0. flexb e0 env \<longrightarrow> extends env e0 \<longrightarrow> fresh_env e0 \<longrightarrow>
    maxidx e0 \<le> maxidx env \<longrightarrow> fh e0 t \<longrightarrow> fh e0 u \<longrightarrow> (\<forall>ab\<in>set tps. ptpok ar A W env e0 ab) \<longrightarrow>
    flexb e0 env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W' env' e0 ab))"

lemma ptpok_mono:
  assumes "ptpok ar A W env e0 ab" "pinv alg ar A W env []" "pinv alg ar A W' env' []" "pextends env' env"
    "agreeV (maxidx env) W W'" "maxidx env \<le> maxidx env'"
  shows "ptpok ar A W' env' e0 ab"
proof -
  note p1 = pinvD[OF assms(2)] and p2 = pinvD[OF assms(3)]
  have ac: "tacyc (tyenv env')" by (rule tinv_tacyc[OF p2(2)])
  have ext: "textends (tyenv env) (tyenv env')" using assms(4) by (simp add: pextends_def)
  from assms(1) obtain rb a b B where c: "ab = (rlist_abs rb a, rlist_abs rb b)" "sbinders ar rb"
    "swf_tm ar rb a" "swf_tm ar rb b" "\<forall>U\<in>snd ` set rb \<union> tys a \<union> tys b. tyw ar (tyenv env) A U"
    "typed env W (map snd rb) a B" "typed env W (map snd rb) b B" "below (maxidx env) a" "below (maxidx env) b"
    "fh e0 a" "fh e0 b"
    unfolding ptpok_def by blast
  have "typed env' W' (map snd rb) a B" "typed env' W' (map snd rb) b B"
    using typed_psext[OF ac assms(4) p1(6) p2(6) assms(5) c(8,6)] typed_psext[OF ac assms(4) p1(6) p2(6) assms(5) c(9,7)] .
  moreover have "\<forall>U\<in>snd ` set rb \<union> tys a \<union> tys b. tyw ar (tyenv env') A U" using c(5) tyw_textends[OF ac ext] by blast
  ultimately show ?thesis unfolding ptpok_def using c below_mono[OF _ assms(6)] by blast
qed

lemma ptpok_tps_mono:
  "\<forall>ab\<in>set tps. ptpok ar A W env e0 ab \<Longrightarrow> pinv alg ar A W env [] \<Longrightarrow> pinv alg ar A W' env' [] \<Longrightarrow>
    pextends env' env \<Longrightarrow> agreeV (maxidx env) W W' \<Longrightarrow> maxidx env \<le> maxidx env' \<Longrightarrow>
    \<forall>ab\<in>set tps. ptpok ar A W' env' e0 ab"
  using ptpok_mono by blast

lemma add_tpair_ptpok:
  assumes "sbinders ar rb" "swf_tm ar rb t" "swf_tm ar rb u" "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar (tyenv env) A U"
    "typed env W (map snd rb) t B" "typed env W (map snd rb) u B" "below (maxidx env) t" "below (maxidx env) u"
    "fh e0 t" "fh e0 u" "\<forall>ab\<in>set tps. ptpok ar A W env e0 ab"
  shows "\<forall>ab\<in>set (add_tpair rb t u tps). ptpok ar A W env e0 ab"
proof -
  have "ptpok ar A W env e0 (rlist_abs rb t, rlist_abs rb u)" unfolding ptpok_def using assms(1-10) by blast
  with assms(11) show ?thesis by (auto simp: add_tpair_def Let_def)
qed

text \<open>
  \<^const>\<open>clean_ffpair\<close> on a solved flex-flex pair with different unbound head variables: an
  extension of the solution satisfies the resulting environment and solves the remaining pairs.
  The new bindings keep the flexible heads saturated.
\<close>

lemma pclean_ffpair_complete:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and ty: "typed env W (map snd rb) t B" "typed env W (map snd rb) u B" "tnorm (tyenv env) B = B"
    and swd: "swf_dp ar (rb, t, u)" and twd: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar (tyenv env) A U"
    and bt: "below (maxidx env) t" and bu: "below (maxidx env) u" and ds: "dsolved \<sigma> (instd \<rho> (rb, t, u))"
    and ht: "head_of t = Var v T" "vt_lookup (tenv env) v = None"
    and hu: "head_of u = Var w U" "vt_lookup (tenv env) w = None" and vw: "v \<noteq> w"
    and ts: "tsolved \<sigma> (itps \<rho> tps)" and tb: "\<forall>(a, b)\<in>set tps. below (maxidx env) a \<and> below (maxidx env) b"
  shows "\<exists>env' tps' W' \<sigma>'. okW (clean_ffpair alg rb t u env tps) (env', tps') \<and> pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' dps \<and>
    tsolved \<sigma>' (itps \<rho> tps') \<and> (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env \<and>
    tyenv env' = tyenv env \<and> ffgood (tyenv env) W' env env' \<and>
    (\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> hsat \<theta> W t \<longrightarrow> hsat \<theta> W u \<longrightarrow> ffgood \<theta> W' env env') \<and>
    ptpstep ar A W env W' env' t u tps tps'"
proof -
  let ?\<theta> = "tyenv env"
  note pcd = pcinvD[OF pc]
  note pi = pinvD[OF pcd(1)]
  note pe = penv_invD[OF pi(1)]
  have sol: "tsol ?\<theta> \<rho>" and gr: "\<forall>v S. ground ar (\<rho> v S)" using pcd(2) by (simp_all add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  note isol = cinvD(2)[OF pcinv_cinv[OF pc]]
  note \<sigma> = solutionD[OF isol]
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  note cb = clean_binder[OF fb]
  note ck = clean_binder_keeps[OF fb]
  let ?B = "bset banned"
  let ?K = "\<lambda>i. integer_of_nat i \<in> set (loose_bnos t) \<and> integer_of_nat i \<in> set (loose_bnos u)"
  have bok: "sbinders ar rb" and wt: "swf_tm ar rb t" and wu: "swf_tm ar rb u" using swd by simp_all
  have pt: "proper t" "proper u" using wt wu by (simp_all add: swf_tm_def)
  have K: "?K i \<longleftrightarrow> i \<in> loose_BVars (tr t) \<and> i \<in> loose_BVars (tr u)" for i
    using set_loose_bnos[OF pt(1)] set_loose_bnos[OF pt(2)] by (auto simp: image_iff integer_eq_iff)
  let ?Z = "loose_BVars (tr t) \<inter> loose_BVars (tr u)"
  have bs: "?B = {i. i < length rb \<and> i \<notin> ?Z}" using ck(1) K by auto
  then have Zb: "?Z \<inter> ?B = {}" by blast
  have keep: "squash ?B i < length rb' \<and> rb' ! squash ?B i = rb ! i" if "i < length rb" "i \<notin> ?B" for i
    using ck(2)[of i] that K bs by auto
  have bok': "sbinders ar rb'" using bok cb(5) by (auto simp: sbinders_def)
  have twt: "\<forall>X\<in>snd ` set rb \<union> tys t. tyw ar ?\<theta> A X" and twu: "\<forall>X\<in>snd ` set rb \<union> tys u. tyw ar ?\<theta> A X"
    using twd by auto
  have tw': "\<forall>X\<in>snd ` set rb'. tyw ar ?\<theta> A X" using twd cb(5) by auto
  have dsB: "mk_subst \<sigma> (tr (inst \<rho> t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
    using ds by (simp add: dsolved_dsolvedB dsolvedB_unabs)
  note dep = dsolved_dep[OF \<sigma>(1) dsB, simplified]
  have fallback: "\<exists>env' tps' W' \<sigma>'. okW (clean_ffpair alg rb t u env tps) (env', tps') \<and>
    pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' dps \<and>
    tsolved \<sigma>' (itps \<rho> tps') \<and> (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env \<and>
    tyenv env' = tyenv env \<and> ffgood (tyenv env) W' env env' \<and>
    (\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> hsat \<theta> W t \<longrightarrow> hsat \<theta> W u \<longrightarrow> ffgood \<theta> W' env env') \<and>
    ptpstep ar A W env W' env' t u tps tps'"
    if "okW (clean_ffpair alg rb t u env tps) (env, add_tpair rb t u tps)"
    using that pc padd_tpair_complete[OF ds ts] add_tpair_below[OF bt bu tb, of rb]
      add_tpair_ptpok[OF bok wt wu twd ty(1,2) bt bu] unfolding ptpstep_def
    by (intro exI[where x=env] exI[where x="add_tpair rb t u tps"] exI[where x=W] exI[where x=\<sigma>])
      (auto simp: agree_def agreeV_def)
  have hwb: "snd w \<le> maxidx env" using bu vps_head_of[OF hu(1)] by (auto dest: below_vps)
  have tsv: "length (snd (strip_comb t)) = ary \<theta> (W v)" if "hsat \<theta> W t" for \<theta>
    using that ht(1) by (simp add: hsat_def)
  from pclean_term_complete[OF pc ty(1,3) twt tw' bt ht cb(1-4) keep dep(1) Zb]
  consider (f1) "\<exists>evs. clean_term banned env t = Some (evs, UErr CHANGE_FAIL)"
    | (c1) env1 t1 W1 \<sigma>1 where "okW (clean_term banned env t) (env1, t1)" "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env1 dps"
      "agree (maxidx env) \<sigma> \<sigma>1" "agreeV (maxidx env) W W1" "maxidx env \<le> maxidx env1" "pextends env1 env"
      "tyenv env1 = ?\<theta>" "\<not> is_funT B" "typed env1 W1 (map snd rb') t1 B" "is_Var (head_of t1)"
      "\<forall>X\<in>tys t1. tyw ar ?\<theta> A X" "below (maxidx env1) t1"
      "\<forall>x U. head_of t1 = Var x U \<longrightarrow> vt_lookup (tenv env1) x = None"
      "\<forall>x. vt_lookup (tenv env1) x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v"
      "\<forall>x U. head_of t1 = Var x U \<longrightarrow> x = v \<or> maxidx env < snd x"
      "\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> ?\<theta> \<longrightarrow> length (snd (strip_comb t)) = ary \<theta> (W v) \<longrightarrow>
        hsat \<theta> W1 t1 \<and> ffgood \<theta> W1 env env1"
      "\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
        flexb env0 env1 \<and> fh env0 t1"
    by blast
  then show ?thesis
  proof cases
    case f1
    then show ?thesis by (rule fallback[OF clean_ffpair_run(1)[OF fb]])
  next
    case (c1 env1 t1 W1 \<sigma>1)
    note ok1 = c1(1) and pc1 = c1(2) and ag1 = c1(3) and agV1 = c1(4) and mx1 = c1(5) and ext1 = c1(6)
      and te1 = c1(7) and nfB = c1(8) and ty1 = c1(9) and hv1 = c1(10) and tw1 = c1(11) and bt1 = c1(12)
      and hn1 = c1(13) and new1 = c1(14) and hd1 = c1(15) and gd1 = c1(16)
    note pi1 = pinvD[OF pcinvD(1)[OF pc1]]
    have tyu1: "typed env1 W1 (map snd rb) u B"
      by (rule typed_pext[OF ty(2) te1 pi(6) pi1(6) agV1 bu])
    have bu1: "below (maxidx env1) u" by (rule below_mono[OF bu mx1])
    have hu1: "vt_lookup (tenv env1) w = None" using new1 hu(2) vw by blast
    have twu1: "\<forall>X\<in>snd ` set rb \<union> tys u. tyw ar (tyenv env1) A X" using twu te1 by simp
    have tw1': "\<forall>X\<in>snd ` set rb'. tyw ar (tyenv env1) A X" using tw' te1 by simp
    have dep1: "dep_on ?Z (mk_subst \<sigma>1 (tr (inst \<rho> u)))" using dep(2) mk_subst_agree[of _ "inst \<rho> u", OF _ ag1] bu by simp
    have W1w: "W1 w = W w" using agV1 hwb unfolding agreeV_def by blast
    from pclean_term_complete[OF pc1 tyu1 ty(3)[folded te1] twu1 tw1' bu1 hu(1) hu1 cb(1-4) keep dep1 Zb]
    consider (f2) "\<exists>evs. clean_term banned env1 u = Some (evs, UErr CHANGE_FAIL)"
      | (c2) env2 u1 W2 \<sigma>2 where "okW (clean_term banned env1 u) (env2, u1)" "pcinv alg ar A W2 \<rho> \<tau>' \<sigma>2 env2 dps"
        "agree (maxidx env1) \<sigma>1 \<sigma>2" "agreeV (maxidx env1) W1 W2" "maxidx env1 \<le> maxidx env2" "pextends env2 env1"
        "tyenv env2 = tyenv env1" "typed env2 W2 (map snd rb') u1 B" "is_Var (head_of u1)"
        "\<forall>X\<in>tys u1. tyw ar (tyenv env1) A X" "below (maxidx env2) u1"
        "\<forall>x U. head_of u1 = Var x U \<longrightarrow> vt_lookup (tenv env2) x = None"
        "\<forall>x. vt_lookup (tenv env2) x \<noteq> None \<longrightarrow> vt_lookup (tenv env1) x = None \<longrightarrow> x = w"
        "\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env1) \<longrightarrow> length (snd (strip_comb u)) = ary \<theta> (W1 w) \<longrightarrow>
          hsat \<theta> W2 u1 \<and> ffgood \<theta> W2 env1 env2"
        "\<forall>env0. flexb env0 env1 \<longrightarrow> extends env1 env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env1 \<longrightarrow>
          flexb env0 env2 \<and> fh env0 u1"
      by blast
    then show ?thesis
    proof cases
      case f2
      then show ?thesis by (rule fallback[OF clean_ffpair_run(2)[OF fb ok1]])
    next
      case (c2 env2 u1 W2 \<sigma>2)
      note ok2 = c2(1) and pc2 = c2(2) and ag2 = c2(3) and agV2 = c2(4) and mx2 = c2(5) and ext2 = c2(6)
        and te2 = c2(7) and tyu2 = c2(8) and hv2 = c2(9) and tw2 = c2(10) and bu2 = c2(11) and hn2 = c2(12)
        and new2 = c2(13) and gd2 = c2(14)
      note pi2 = pinvD[OF pcinvD(1)[OF pc2]]
      have te02: "tyenv env2 = ?\<theta>" using te1 te2 by simp
      note \<sigma>2 = solutionD[OF cinvD(2)[OF pcinv_cinv[OF pc2]]]
      have sol2: "tsol (tyenv env2) \<rho>" using pcinvD(2)[OF pc2] by (simp add: gsol_def)
      have mx12: "maxidx env \<le> maxidx env2" using mx1 mx2 by simp
      have ag02: "agree (maxidx env) \<sigma> \<sigma>2" by (rule agree_trans[OF ag1 ag2 mx1])
      have agV02: "agreeV (maxidx env) W W2" by (rule agreeV_trans[OF agV1 agV2 mx1])
      have ext02: "pextends env2 env" by (rule pextends_trans[OF ext2 ext1])
      \<comment> \<open>Soundness of the cleaning, for the instance\<close>
      have swe: "swf_env ar env" by (rule penv_inv_swf_env[OF pi(1)])
      have swe1: "swf_env ar env1" by (rule penv_inv_swf_env[OF pi1(1)])
      note st = clean_term_psound[OF ok1 swe wt cb(1-4)]
      note su = clean_term_psound[OF ok2 swe1 wu cb(1-4)]
      have wt1: "swf_tm ar rb' t1" and wu1: "swf_tm ar rb' u1" using st su by blast+
      have ps2: "psat (\<sigma>2 \<circ> cren \<rho>) env2" by (rule psat_instE[OF sol2 \<sigma>2(1,4)])
      have ps1: "psat (\<sigma>2 \<circ> cren \<rho>) env1" by (rule psat_pextends[OF ps2 ext2])
      have "mk_subst \<sigma>2 (tr (inst \<rho> t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash ?B) (mk_subst \<sigma>2 (tr (inst \<rho> t1)))"
        using st ps1 by (simp add: mk_subst_inst)
      moreover have "mk_subst \<sigma>2 (tr (inst \<rho> u)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash ?B) (mk_subst \<sigma>2 (tr (inst \<rho> u1)))"
        using su ps2 by (simp add: mk_subst_inst)
      moreover have "mk_subst \<sigma>2 (tr (inst \<rho> t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>2 (tr (inst \<rho> u))"
        using dsB mk_subst_agree[of _ "inst \<rho> t", OF _ ag02] mk_subst_agree[of _ "inst \<rho> u", OF _ ag02] bt bu by simp
      ultimately have "map_BVars (unsquash ?B) (mk_subst \<sigma>2 (tr (inst \<rho> t1))) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          map_BVars (unsquash ?B) (mk_subst \<sigma>2 (tr (inst \<rho> u1)))"
        by (meson equiv_sym equiv_trans)
      from unsquash_dsolved[OF cb(3) _ \<sigma>2(1) wf_tm_inst[OF wt1 gr] wf_tm_inst[OF wu1 gr] this] cb(4)
      have ds2: "dsolved \<sigma>2 (instd \<rho> (rb', t1, u1))" by simp
      have ty1': "typed env2 W2 (map snd rb') t1 B" by (rule typed_pext[OF ty1 te2 pi1(6) pi2(6) agV2 bt1])
      have bt1': "below (maxidx env2) t1" by (rule below_mono[OF bt1 mx2])
      have h1: "\<forall>x U. head_of t1 = Var x U \<longrightarrow> vt_lookup (tenv env2) x = None"
      proof (intro allI impI)
        fix x U assume h: "head_of t1 = Var x U"
        have "x \<noteq> w" using hd1 h vw hwb by force
        then show "vt_lookup (tenv env2) x = None" using hn1 h new2 by blast
      qed
      have swd2: "swf_dp ar (rb', t1, u1)" using bok' wt1 wu1 by simp
      have twd2: "\<forall>X\<in>snd ` set rb' \<union> tys t1 \<union> tys u1. tyw ar (tyenv env2) A X" using tw' tw1 tw2 te1 te02 by auto
      have ts2: "tsolved \<sigma>2 (itps \<rho> tps)" by (rule ptsolved_agree[OF ts tb ag02])
      have tb2: "\<forall>(a, b)\<in>set tps. below (maxidx env2) a \<and> below (maxidx env2) b"
        by (rule tps_below_mono[OF tb mx12])
      have nB2: "tnorm (tyenv env2) B = B" using ty(3) te02 by simp
      \<comment> \<open>The heads of the cleaned pair are saturated\<close>
      have fr1: "fresh_env env1" using penv_invD(6)[OF pi1(1)] .
      have fr2: "fresh_env env2" using penv_invD(6)[OF pi2(1)] .
      have hs1: "hsat \<theta> W2 t1" if "hsat \<theta> W1 t1" for \<theta>
      proof -
        obtain x X where hx: "head_of t1 = Var x X" using hv1 by (cases "head_of t1") auto
        have "snd x \<le> maxidx env1" using bt1 vps_head_of[OF hx] by (auto dest: below_vps)
        then have "W2 x = W1 x" using agV2 unfolding agreeV_def by blast
        then show ?thesis using that hx by (simp add: hsat_def)
      qed
      have gdl: "ffgood \<theta> W2 env env2" if "tacyc \<theta>" "textends \<theta> ?\<theta>" "length (snd (strip_comb t)) = ary \<theta> (W v)"
        "length (snd (strip_comb u)) = ary \<theta> (W w)" for \<theta>
      proof -
        from gd1 that(1-3) have g1: "hsat \<theta> W1 t1" "ffgood \<theta> W1 env env1" by auto
        from gd2 that(1,2,4) te1 W1w have g2: "hsat \<theta> W2 u1" "ffgood \<theta> W2 env1 env2" by auto
        show ?thesis by (rule ffgood_trans[OF g1(2) g2(2) pextendsD(1)[OF ext1] pextendsD(1)[OF ext2] fr1 agV2])
      qed
      have hsE: "length (snd (strip_comb t)) = ary ?\<theta> (W v)" "length (snd (strip_comb u)) = ary ?\<theta> (W w)"
        using tsv typed_hsat[OF ty(1) _ pi(6)] typed_hsat[OF ty(2) _ pi(6)] nfB ty(3) hu(1)
        by (auto simp: hsat_def)
      have fin: "\<exists>env' tps' W' \<sigma>'. okW (clean_ffpair alg rb t u env tps) (env', tps') \<and>
        pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' dps \<and>
        tsolved \<sigma>' (itps \<rho> tps') \<and> (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
        agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env \<and>
        tyenv env' = tyenv env \<and> ffgood (tyenv env) W' env env' \<and>
        (\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> hsat \<theta> W t \<longrightarrow> hsat \<theta> W u \<longrightarrow> ffgood \<theta> W' env env') \<and>
        ptpstep ar A W env W' env' t u tps tps'"
        if fa: "okW (clean_ffpair alg rb t u env tps) (env', tps')" "pcinv alg ar A W2 \<rho> \<tau>' \<sigma>2 env' dps"
          "tsolved \<sigma>2 (itps \<rho> tps')" "\<forall>(a, b)\<in>set tps'. below (maxidx env2) a \<and> below (maxidx env2) b"
          "maxidx env' = maxidx env2" "pextends env' env2" "tyenv env' = tyenv env2"
          "\<forall>\<theta>. hsat \<theta> W2 t1 \<longrightarrow> hsat \<theta> W2 u1 \<longrightarrow> ffgood \<theta> W2 env2 env'"
          "\<forall>e0. flexb e0 env2 \<longrightarrow> extends env2 e0 \<longrightarrow> fh e0 t1 \<longrightarrow> fh e0 u1 \<longrightarrow>
            (\<forall>ab\<in>set tps. ptpok ar A W2 env2 e0 ab) \<longrightarrow> flexb e0 env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W2 env' e0 ab)"
        for env' tps'
      proof -
        have ps: "ptpstep ar A W env W2 env' t u tps tps'"
          unfolding ptpstep_def
        proof (intro allI impI)
          fix e0 assume e: "flexb e0 env" "extends env e0" "fresh_env e0" "maxidx e0 \<le> maxidx env" "fh e0 t" "fh e0 u"
            "\<forall>ab\<in>set tps. ptpok ar A W env e0 ab"
          from c1(17) e(1-4) have f1: "flexb e0 env1" "fh e0 t1" by blast+
          have x1: "extends env1 e0" by (rule extends_trans[OF pextendsD(1)[OF ext1] e(2)])
          from c2(15) f1(1) x1 e(3) e(4) mx1 have f2: "flexb e0 env2" "fh e0 u1" by fastforce+
          have x2: "extends env2 e0" by (rule extends_trans[OF pextendsD(1)[OF ext2] x1])
          have "\<forall>ab\<in>set tps. ptpok ar A W2 env2 e0 ab"
            by (rule ptpok_tps_mono[OF e(7) pcinvD(1)[OF pcinv_Nil[OF pc]] pcinvD(1)[OF pcinv_Nil[OF pc2]] ext02 agV02 mx12])
          with fa(9) f1(2) f2 x2 show "flexb e0 env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W2 env' e0 ab)" by blast
        qed
        have gd: "ffgood \<theta> W2 env env'" if "tacyc \<theta>" "textends \<theta> ?\<theta>" "length (snd (strip_comb t)) = ary \<theta> (W v)"
          "length (snd (strip_comb u)) = ary \<theta> (W w)" for \<theta>
        proof -
          from gd1 that(1-3) have "hsat \<theta> W1 t1" by auto
          moreover from gd2 that(1,2,4) te1 W1w have "hsat \<theta> W2 u1" by auto
          ultimately have "ffgood \<theta> W2 env2 env'" using fa(8) hs1 by blast
          from ffgood_trans[OF gdl[OF that] this pextendsD(1)[OF ext02] pextendsD(1)[OF fa(6)] fr2] show ?thesis
            by (simp add: agreeV_def)
        qed
        have p1: "pextends env' env" by (rule pextends_trans[OF fa(6) ext02])
        have g1: "ffgood ?\<theta> W2 env env'" by (rule gd[OF ac(1) textends_refl hsE])
        have g2: "\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> ?\<theta> \<longrightarrow> hsat \<theta> W t \<longrightarrow> hsat \<theta> W u \<longrightarrow> ffgood \<theta> W2 env env'"
        proof (intro allI impI)
          fix \<theta> assume "tacyc \<theta>" "textends \<theta> ?\<theta>" "hsat \<theta> W t" "hsat \<theta> W u"
          moreover from \<open>hsat \<theta> W u\<close> have "length (snd (strip_comb u)) = ary \<theta> (W w)"
            using hu(1) by (simp add: hsat_def)
          ultimately show "ffgood \<theta> W2 env env'" using gd tsv by blast
        qed
        have tb': "\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b" using fa(4,5) by simp
        have mx': "maxidx env \<le> maxidx env'" using mx12 fa(5) by simp
        have te': "tyenv env' = tyenv env" using fa(7) te02 by simp
        show ?thesis using fa(1-3) tb' ag02 agV02 mx' p1 te' g1 g2 ps by blast
      qed
      have keep: "\<forall>e0. flexb e0 env2 \<longrightarrow> extends env2 e0 \<longrightarrow> fh e0 t1 \<longrightarrow> fh e0 u1 \<longrightarrow>
          (\<forall>ab\<in>set tps. ptpok ar A W2 env2 e0 ab) \<longrightarrow> flexb e0 env3 \<and> (\<forall>ab\<in>set tps. ptpok ar A W2 env3 e0 ab)"
        if "pcinv alg ar A W2 \<rho> \<tau>' \<sigma>2 env3 dps" "pextends env3 env2" "maxidx env3 = maxidx env2"
          "\<forall>e0. flexb e0 env2 \<longrightarrow> extends env2 e0 \<longrightarrow> fh e0 t1 \<longrightarrow> fh e0 u1 \<longrightarrow> flexb e0 env3" for env3
      proof (intro allI impI conjI)
        fix e0 assume e: "flexb e0 env2" "extends env2 e0" "fh e0 t1" "fh e0 u1" "\<forall>ab\<in>set tps. ptpok ar A W2 env2 e0 ab"
        show "flexb e0 env3" using that(4) e by blast
        show "\<forall>ab\<in>set tps. ptpok ar A W2 env3 e0 ab"
          by (rule ptpok_tps_mono[OF e(5) pcinvD(1)[OF pcinv_Nil[OF pc2]] pcinvD(1)[OF pcinv_Nil[OF that(1)]] that(2)])
            (use that(3) in \<open>simp_all add: agreeV_def\<close>)
      qed
      note run = clean_ffpair_run(3)[OF fb ok1 ok2]
      from pff_assign_complete[OF pc2 ty1' tyu2 nB2 nfB swd2 twd2 bt1' bu2 ds2 h1 hn2]
      consider (a1) env3 where "okW (ff_assign alg env2 rb' t1 u1) env3" "pcinv alg ar A W2 \<rho> \<tau>' \<sigma>2 env3 dps"
          "pextends env3 env2" "tyenv env3 = tyenv env2" "maxidx env3 = maxidx env2"
          "\<forall>\<theta>. hsat \<theta> W2 t1 \<longrightarrow> hsat \<theta> W2 u1 \<longrightarrow> is_Var (head_of u1) \<longrightarrow> ffgood \<theta> W2 env2 env3"
          "\<forall>env0. flexb env0 env2 \<longrightarrow> extends env2 env0 \<longrightarrow> fh env0 u1 \<longrightarrow> flexb env0 env3"
        | (r1) "\<exists>evs. ff_assign alg env2 rb' t1 u1 = Some (evs, UErr ASSIGN)"
        by blast
      then show ?thesis
      proof cases
        case (a1 env3)
        have "\<forall>e0. flexb e0 env2 \<longrightarrow> extends env2 e0 \<longrightarrow> fh e0 t1 \<longrightarrow> fh e0 u1 \<longrightarrow> flexb e0 env3"
          using a1(7) by blast
        note k = keep[OF a1(2,3,5) this]
        show ?thesis by (rule fin[OF run[OF ff_handler_complete(1)[OF a1(1)]] a1(2) ts2 tb2 a1(5) a1(3) a1(4) _ k])
          (use a1(6) hv2 in blast)
      next
        case r1
        have swd2': "swf_dp ar (rb', u1, t1)" using swd2 by simp
        have twd2': "\<forall>X\<in>snd ` set rb' \<union> tys u1 \<union> tys t1. tyw ar (tyenv env2) A X" using twd2 by auto
        have ds2': "dsolved \<sigma>2 (instd \<rho> (rb', u1, t1))" using dsolved_sym ds2 by simp
        from pff_assign_complete[OF pc2 tyu2 ty1' nB2 nfB swd2' twd2' bu2 bt1' ds2' hn2 h1]
        consider (a2) env3 where "okW (ff_assign alg env2 rb' u1 t1) env3" "pcinv alg ar A W2 \<rho> \<tau>' \<sigma>2 env3 dps"
            "pextends env3 env2" "tyenv env3 = tyenv env2" "maxidx env3 = maxidx env2"
            "\<forall>\<theta>. hsat \<theta> W2 u1 \<longrightarrow> hsat \<theta> W2 t1 \<longrightarrow> is_Var (head_of t1) \<longrightarrow> ffgood \<theta> W2 env2 env3"
            "\<forall>env0. flexb env0 env2 \<longrightarrow> extends env2 env0 \<longrightarrow> fh env0 t1 \<longrightarrow> flexb env0 env3"
          | (r2) "\<exists>evs. ff_assign alg env2 rb' u1 t1 = Some (evs, UErr ASSIGN)"
          by blast
        then show ?thesis
        proof cases
          case (a2 env3)
          have "\<forall>e0. flexb e0 env2 \<longrightarrow> extends env2 e0 \<longrightarrow> fh e0 t1 \<longrightarrow> fh e0 u1 \<longrightarrow> flexb e0 env3"
            using a2(7) by blast
          note k = keep[OF a2(2,3,5) this]
          show ?thesis by (rule fin[OF run[OF ff_handler_complete(2)[OF r1 a2(1)]] a2(2) ts2 tb2 a2(5) a2(3) a2(4) _ k])
            (use a2(6) hv1 in blast)
        next
          case r2
          show ?thesis
            by (rule fin[OF run[OF ff_handler_complete(3)[OF r1 r2]] pc2
              padd_tpair_complete[OF ds2 ts2] add_tpair_below[OF bt1' bu2 tb2]])
              (use add_tpair_ptpok[OF bok' wt1 wu1 twd2 ty1' tyu2 bt1' bu2] in auto)
        qed
      qed
    qed
  qed
qed

lemma ptpstep_sym: "ptpstep ar A W env W' env' u t tps tps' \<Longrightarrow> ptpstep ar A W env W' env' t u tps tps'"
  unfolding ptpstep_def by blast

lemma fhd_head_Var: "head_of t = Var x X \<Longrightarrow> fhd t = Var x X"
  by (induction t) auto

lemma typed_head_tctx:
  assumes "tacyc (tyenv env)" "typed env W Ts t B" "head_of t = Var v T"
  shows "tctx env W v = tnorm (tyenv env) T"
proof -
  obtain as where t: "t = list_comb (Var v T) as" using head_of_list_comb[of t] assms(3) by metis
  from typed_list_comb_args[OF assms(1) assms(2)[unfolded t]] obtain As where
    "typed env W Ts (Var v T) (foldr fun_type As B)" by blast
  then show ?thesis by (auto simp: typed_def elim: has_type_elims)
qed

text \<open>
  \<^const>\<open>add_ffpair\<close> on a solved flex-flex pair whose heads are unbound in the environment \<open>e0\<close>
  of the start of the flex-flex phase, and saturated in a type environment \<open>\<theta>q\<close> in which the
  bindings since \<open>e0\<close> are \<^const>\<open>ffgood\<close>: the normalized heads are variables.
\<close>

theorem padd_ffpair_complete:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb, t0, u0)]"
    and ty: "typed env W (map snd rb) t0 B" "typed env W (map snd rb) u0 B"
    and h0: "head_of t0 = Var x X" "head_of u0 = Var y Y"
    and e0: "extends env e0" "vt_lookup (tenv e0) x = None" "vt_lookup (tenv e0) y = None"
    and q: "tacyc \<theta>q" "textends \<theta>q (tyenv env)" "hsat \<theta>q W t0" "hsat \<theta>q W u0" "ffgood \<theta>q W e0 env"
    and ts: "tsolved \<sigma> (itps \<rho> tps)" and tb: "\<forall>(a, b)\<in>set tps. below (maxidx env) a \<and> below (maxidx env) b"
  shows "\<exists>env' tps' W' \<sigma>'. okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps') \<and>
    pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' [] \<and> tsolved \<sigma>' (itps \<rho> tps') \<and>
    (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env \<and>
    tyenv env' = tyenv env \<and> (ffgood (tyenv env) W e0 env \<longrightarrow> ffgood (tyenv env) W' e0 env') \<and>
    (\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> hsat \<theta> W t0 \<longrightarrow> hsat \<theta> W u0 \<longrightarrow> ffgood \<theta> W e0 env \<longrightarrow>
      ffgood \<theta> W' e0 env') \<and>
    (flexb e0 env \<longrightarrow> fresh_env e0 \<longrightarrow> maxidx e0 \<le> maxidx env \<longrightarrow> (\<forall>ab\<in>set tps. ptpok ar A W env e0 ab) \<longrightarrow>
      flexb e0 env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W' env' e0 ab))"
proof -
  let ?\<theta> = "tyenv env"
  note pcd = pcinvD[OF pc]
  note pi = pinvD[OF pcd(1)]
  note pe = penv_invD[OF pi(1)]
  have sol: "tsol ?\<theta> \<rho>" using pcd(2) by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  note isol = cinvD(2)[OF pcinv_cinv[OF pc]]
  note \<sigma> = solutionD[OF isol]
  have pc0: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env []" by (rule pcinv_Nil[OF pc])
  note pi0 = pcinvD(1,2)[OF pc0]
  from pi(4)[of "(rb, t0, u0)"] have swd: "swf_dp ar (rb, t0, u0)"
    and twd: "\<forall>U\<in>snd ` set rb \<union> tys t0 \<union> tys u0. tyw ar ?\<theta> A U"
    and bl: "below (maxidx env) t0" "below (maxidx env) u0"
    by auto
  have ds0: "dsolved \<sigma> (instd \<rho> (rb, t0, u0))" using pcd(4) by simp
  have twt: "\<forall>U\<in>set (map snd rb) \<union> tys t0. tyw ar ?\<theta> A U" and twu: "\<forall>U\<in>set (map snd rb) \<union> tys u0. tyw ar ?\<theta> A U"
    using twd by auto
  from norm_term_pterm[OF pi0 ty(1) twt bl(1)] obtain t where nt: "norm_term env t0 = return t"
    and tyt: "typed env W (map snd rb) t B" and twt': "\<forall>U\<in>tys t. tyw ar ?\<theta> A U" and bt: "below (maxidx env) t"
    and hnt: "\<forall>x U. head_of t = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
    and tnt: "\<forall>x U. head_of t = Var x U \<longrightarrow> tnorm ?\<theta> U = U"
    and fht: "\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t0 \<longrightarrow> fh env0 t"
    by blast
  from norm_term_pterm[OF pi0 ty(2) twu bl(2)] obtain u where nu: "norm_term env u0 = return u"
    and tyu: "typed env W (map snd rb) u B" and twu': "\<forall>U\<in>tys u. tyw ar ?\<theta> A U" and bu: "below (maxidx env) u"
    and hnu: "\<forall>x U. head_of u = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
    and tnu: "\<forall>x U. head_of u = Var x U \<longrightarrow> tnorm ?\<theta> U = U"
    and fhu: "\<forall>env0. flexb env0 env \<longrightarrow> fh env0 u0 \<longrightarrow> fh env0 u"
    by blast
  have fh0: "fh e0 t0" "fh e0 u0" using h0 e0(2,3) by (simp_all add: fh_def fhd_head_Var)
  \<comment> \<open>The heads of the normalized sides stay saturated variables\<close>
  have spine: "\<exists>K V cs. s = list_comb (Var K V) cs \<and> length cs = ary \<theta> (W K)"
    if "norm_term env s0 = return s" "typed env W (map snd rb) s0 B" "\<forall>U\<in>set (map snd rb) \<union> tys s0. tyw ar ?\<theta> A U"
      "below (maxidx env) s0" "head_of s0 = Var z Z" "vt_lookup (tenv e0) z = None" "hsat \<theta> W s0" "ffgood \<theta> W e0 env"
    for s0 s z Z \<theta>
  proof -
    have sp: "absp 0 s0 (list_comb (Var z Z) (snd (strip_comb s0)))" using head_of_list_comb[of s0] that(5) by simp
    have la: "length (snd (strip_comb s0)) = ary \<theta> (W z)" using that(5,7) by (simp add: hsat_def)
    from norm_term_spine[OF that(1) pi0 that(2-4) that(8) e0(1) sp that(6)] la
    obtain k K V cs where "absp k s (list_comb (Var K V) cs)" "k = 0" "length cs = ary \<theta> (W K)"
      by (auto split: if_splits)
    then show ?thesis by (intro exI[of _ K] exI[of _ V] exI[of _ cs]) simp
  qed
  have hsat_norm: "hsat \<theta> W t" "hsat \<theta> W u"
    if "hsat \<theta> W t0" "hsat \<theta> W u0" "ffgood \<theta> W e0 env" for \<theta>
    using spine[OF nt ty(1) twt bl(1) h0(1) e0(2) that(1,3)] spine[OF nu ty(2) twu bl(2) h0(2) e0(3) that(2,3)]
    strip_comb_list_comb_eq by (auto simp: hsat_def)
  from spine[OF nt ty(1) twt bl(1) h0(1) e0(2) q(3,5)] obtain v T cs where tv: "t = list_comb (Var v T) cs" by blast
  from spine[OF nu ty(2) twu bl(2) h0(2) e0(3) q(4,5)] obtain w U ds where uw: "u = list_comb (Var w U) ds" by blast
  have ht: "head_of t = Var v T" and hu: "head_of u = Var w U" using tv uw by simp_all
  have vn: "vt_lookup (tenv env) v = None" and wn: "vt_lookup (tenv env) w = None" using hnt hnu ht hu by blast+
  \<comment> \<open>The normalized pair is solved\<close>
  have swe: "swf_env ar env" by (rule penv_inv_swf_env[OF pi(1)])
  have okt: "ok (norm_term env t0) t" and oku: "ok (norm_term env u0) u" using nt nu by (simp_all add: return_def)
  have bok: "sbinders ar rb" and wt0: "swf_tm ar rb t0" and wu0: "swf_tm ar rb u0" using swd by simp_all
  note tn = norm_term_swf_tm[OF okt swe wt0] and un = norm_term_swf_tm[OF oku swe wu0]
  have swd': "swf_dp ar (rb, t, u)" using tn un bok by simp
  have ps: "psat (\<sigma> \<circ> cren \<rho>) env" by (rule psat_instE[OF sol \<sigma>(1,4)])
  have "dsolved (\<sigma> \<circ> cren \<rho>) (rb, t, u)"
    by (rule pdsolved_env_equiv[OF penv_equiv_rlist_abs penv_equiv_rlist_abs ps])
      (use tn un ds0[unfolded dsolved_instd] penv_equiv_sym in blast)+
  then have ds: "dsolved \<sigma> (instd \<rho> (rb, t, u))" unfolding dsolved_instd .
  have run: "okW (add_ffpair alg (rb, t0, u0) (env, tps)) r"
    if "okW (if v = w then
            (if T = U then returnW (env, add_tpair rb t u tps)
             else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
          else if indexname_less v w then clean_ffpair alg rb u t env tps
          else clean_ffpair alg rb t u env tps) r" for r
    using that nt nu ht hu by (auto simp: add_ffpair_def)
  have nB: "tnorm ?\<theta> (tnorm ?\<theta> B) = tnorm ?\<theta> B" by (simp add: tnorm_idem[OF ac(1)])
  have tyt': "typed env W (map snd rb) t (tnorm ?\<theta> B)" and tyu': "typed env W (map snd rb) u (tnorm ?\<theta> B)"
    using tyt tyu typed_tnorm[OF ac(1)] by simp_all
  have twd': "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A U" using twd twt' twu' by auto
  have fr: "fresh_env env" by (rule pe(6))
  have glue: "ffgood \<theta> W' e0 env'"
    if "ffgood \<theta> W e0 env" "ffgood \<theta> W' env env'" "pextends env' env" "agreeV (maxidx env) W W'" for \<theta> W' env'
    by (rule ffgood_trans[OF that(1,2) e0(1) pextendsD(1)[OF that(3)] fr that(4)])
  show ?thesis
  proof (cases "v = w")
    case True
    have "tctx env W v = tnorm ?\<theta> T" "tctx env W w = tnorm ?\<theta> U"
      using typed_head_tctx[OF ac(1) tyt ht] typed_head_tctx[OF ac(1) tyu hu] by simp_all
    then have TU: "T = U" using True tnt tnu ht hu by auto
    have "okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env, add_tpair rb t u tps)"
      by (rule run) (simp add: True TU)
    moreover have "\<forall>ab\<in>set (add_tpair rb t u tps). ptpok ar A W env e0 ab"
      if "flexb e0 env" "\<forall>ab\<in>set tps. ptpok ar A W env e0 ab"
      using add_tpair_ptpok[OF bok _ _ twd' tyt tyu bt bu _ _ that(2)] swd' fht fhu fh0 that(1) by simp
    ultimately show ?thesis using pc0 padd_tpair_complete[OF ds ts] add_tpair_below[OF bt bu tb, of rb]
      by (intro exI[where x=env] exI[where x="add_tpair rb t u tps"] exI[where x=W] exI[where x=\<sigma>])
        (auto simp: agree_def agreeV_def)
  next
    case False
    have fin: "\<exists>env' tps' W' \<sigma>'. okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps') \<and>
      pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' [] \<and> tsolved \<sigma>' (itps \<rho> tps') \<and>
      (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
      agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env \<and>
      tyenv env' = tyenv env \<and> (ffgood (tyenv env) W e0 env \<longrightarrow> ffgood (tyenv env) W' e0 env') \<and>
      (\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> hsat \<theta> W t0 \<longrightarrow> hsat \<theta> W u0 \<longrightarrow> ffgood \<theta> W e0 env \<longrightarrow>
        ffgood \<theta> W' e0 env') \<and>
      (flexb e0 env \<longrightarrow> fresh_env e0 \<longrightarrow> maxidx e0 \<le> maxidx env \<longrightarrow> (\<forall>ab\<in>set tps. ptpok ar A W env e0 ab) \<longrightarrow>
        flexb e0 env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W' env' e0 ab))"
      if c: "okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps')" "pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' []"
        "tsolved \<sigma>' (itps \<rho> tps')" "\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b"
        "agree (maxidx env) \<sigma> \<sigma>'" "agreeV (maxidx env) W W'" "maxidx env \<le> maxidx env'" "pextends env' env"
        "tyenv env' = tyenv env" "ffgood (tyenv env) W' env env'"
        "\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> hsat \<theta> W t \<longrightarrow> hsat \<theta> W u \<longrightarrow> ffgood \<theta> W' env env'"
        "ptpstep ar A W env W' env' t u tps tps'"
      for env' tps' W' \<sigma>'
    proof -
      have fl: "flexb e0 env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W' env' e0 ab)"
        if "flexb e0 env" "fresh_env e0" "maxidx e0 \<le> maxidx env" "\<forall>ab\<in>set tps. ptpok ar A W env e0 ab"
        using c(12) that e0(1) fht fhu fh0 unfolding ptpstep_def by blast
      have "ffgood \<theta> W' e0 env'"
        if "tacyc \<theta>" "textends \<theta> ?\<theta>" "hsat \<theta> W t0" "hsat \<theta> W u0" "ffgood \<theta> W e0 env" for \<theta>
        using glue[OF that(5) _ c(8,6)] c(11) hsat_norm[OF that(3-5)] that(1,2) by blast
      moreover have "ffgood ?\<theta> W' e0 env'" if "ffgood ?\<theta> W e0 env"
        by (rule glue[OF that c(10,8,6)])
      ultimately show ?thesis using c(1-9) fl by blast
    qed
    show ?thesis
    proof (cases "indexname_less v w")
      case True
      from False have wv: "w \<noteq> v" by simp
      have swdu: "swf_dp ar (rb, u, t)" using swd' by simp
      have twdu: "\<forall>X\<in>snd ` set rb \<union> tys u \<union> tys t. tyw ar ?\<theta> A X" using twd' by auto
      have dsu: "dsolved \<sigma> (instd \<rho> (rb, u, t))" using ds dsolved_sym by simp
      from pclean_ffpair_complete[OF pc0 tyu' tyt' nB swdu twdu bu bt dsu hu wn ht vn wv ts tb]
      obtain env' tps' W' \<sigma>' where c: "okW (clean_ffpair alg rb u t env tps) (env', tps')"
        "pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' []" "tsolved \<sigma>' (itps \<rho> tps')"
        "\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b"
        "agree (maxidx env) \<sigma> \<sigma>'" "agreeV (maxidx env) W W'" "maxidx env \<le> maxidx env'" "pextends env' env"
        "tyenv env' = tyenv env" "ffgood (tyenv env) W' env env'"
        "\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> hsat \<theta> W u \<longrightarrow> hsat \<theta> W t \<longrightarrow> ffgood \<theta> W' env env'"
        "ptpstep ar A W env W' env' u t tps tps'"
        by blast
      have "okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps')"
        using c(1) False True by (intro run) simp
      from fin[OF this c(2-10) _ ptpstep_sym[OF c(12)]] c(11) show ?thesis by blast
    next
      case nl: False
      from pclean_ffpair_complete[OF pc0 tyt' tyu' nB swd' twd' bt bu ds ht vn hu wn False ts tb]
      obtain env' tps' W' \<sigma>' where c: "okW (clean_ffpair alg rb t u env tps) (env', tps')"
        "pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' []" "tsolved \<sigma>' (itps \<rho> tps')"
        "\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b"
        "agree (maxidx env) \<sigma> \<sigma>'" "agreeV (maxidx env) W W'" "maxidx env \<le> maxidx env'" "pextends env' env"
        "tyenv env' = tyenv env" "ffgood (tyenv env) W' env env'"
        "\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> hsat \<theta> W t \<longrightarrow> hsat \<theta> W u \<longrightarrow> ffgood \<theta> W' env env'"
        "ptpstep ar A W env W' env' t u tps tps'"
        by blast
      have "okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps')"
        using c(1) False nl by (intro run) simp
      from fin[OF this c(2-12)] show ?thesis .
    qed
  qed
qed

lemma hsat_agreeV:
  assumes "hsat \<theta> W t" "below m t" "agreeV m W W'"
  shows "hsat \<theta> W' t"
  unfolding hsat_def
proof (intro allI impI)
  fix X U assume h: "head_of t = Var X U"
  have "snd X \<le> m" using below_vps[OF assms(2) vps_head_of[OF h]] by simp
  then have "W' X = W X" using assms(3) unfolding agreeV_def by blast
  then show "length (snd (strip_comb t)) = ary \<theta> (W' X)" using assms(1) h unfolding hsat_def by simp
qed

text \<open>
  The flex-flex phase: all pairs are added in turn, starting with no remaining pairs. The pairs
  are saturated in the type environments of their classification (\<^const>\<open>fch\<close>), and the
  bindings are \<^const>\<open>ffgood\<close> in all type environments between these and the final one.
\<close>

theorem foldrW_padd_ffpair_complete:
  assumes "pcinv alg ar A W \<rho> \<tau>' \<sigma> env ffs" "\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp"
    "fch W (tyenv env) \<theta>0 ffs"
  shows "\<exists>env' tps' W' \<sigma>'. okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps') \<and>
    pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' [] \<and> tsolved \<sigma>' (itps \<rho> tps') \<and>
    (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env \<and>
    tyenv env' = tyenv env \<and> ffgood (tyenv env) W' env env' \<and>
    (\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env) \<longrightarrow> fch W \<theta> \<theta>0 ffs \<longrightarrow> ffgood \<theta> W' env env') \<and>
    flexb env env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W' env' env ab)"
  using assms
proof (induction ffs)
  case Nil
  then show ?case
    by (intro exI[where x=env] exI[where x="[]"] exI[where x=W] exI[where x=\<sigma>])
      (auto simp: tsolved_def agree_def agreeV_def flexb_def intro: pcinv_Nil)
next
  case (Cons dp ffs)
  obtain rb t0 u0 where dp: "dp = (rb, t0, u0)" by (cases dp)
  let ?\<theta> = "tyenv env"
  note pi = pinvD[OF pcinvD(1)[OF Cons.prems(1)]]
  have ac: "tacyc ?\<theta>" by (rule tinv_tacyc[OF pi(2)])
  from Cons.prems(3) dp obtain \<theta>d where d: "tacyc \<theta>d" "textends \<theta>d ?\<theta>" "hsat \<theta>d W t0" "hsat \<theta>d W u0"
    "fch W \<theta>d \<theta>0 ffs"
    by auto
  have pcf: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env ffs" using Cons.prems(1) by (simp add: pcinv_def pinv_def)
  from Cons.IH[OF pcf _ fch_up[OF d(5,2)]] Cons.prems(2) obtain env1 tps1 W1 \<sigma>1 where
    f: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env1, tps1)" and pc1: "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env1 []"
    and ts1: "tsolved \<sigma>1 (itps \<rho> tps1)" and tb1: "\<forall>(a, b)\<in>set tps1. below (maxidx env1) a \<and> below (maxidx env1) b"
    and ag1: "agree (maxidx env) \<sigma> \<sigma>1" and agV1: "agreeV (maxidx env) W W1" and mx1: "maxidx env \<le> maxidx env1"
    and ext1: "pextends env1 env" and te1: "tyenv env1 = ?\<theta>" and gE1: "ffgood ?\<theta> W1 env env1"
    and g1: "\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> ?\<theta> \<longrightarrow> fch W \<theta> \<theta>0 ffs \<longrightarrow> ffgood \<theta> W1 env env1"
    and fb1: "flexb env env1" and tp1: "\<forall>ab\<in>set tps1. ptpok ar A W1 env1 env ab"
    by auto
  note pi1 = pinvD[OF pcinvD(1)[OF pc1]]
  from pi(4)[of dp] dp have swd: "swf_dp ar (rb, t0, u0)" and twd: "\<forall>U\<in>dtys (rb, t0, u0). tyw ar ?\<theta> A U"
    and bl: "below (maxidx env) t0" "below (maxidx env) u0"
    by (auto simp: dp_below_def)
  from Cons.prems(2) dp obtain B where ty: "typed env W (map snd rb) t0 B" "typed env W (map snd rb) u0 B"
    and hv: "is_Var (head_of t0)" "is_Var (head_of u0)" and hn: "heads_unb env (rb, t0, u0)"
    by (auto simp: pff_shape_def)
  obtain x X y Y where h0: "head_of t0 = Var x X" "head_of u0 = Var y Y"
    using hv by (cases "head_of t0"; cases "head_of u0") auto
  have xn: "vt_lookup (tenv env) x = None" "vt_lookup (tenv env) y = None"
    using hn h0 unfolding heads_unb_def prod.case by blast+
  have ty1: "typed env1 W1 (map snd rb) t0 B" "typed env1 W1 (map snd rb) u0 B"
    using typed_pext[OF ty(1) te1 pi(6) pi1(6) agV1 bl(1)] typed_pext[OF ty(2) te1 pi(6) pi1(6) agV1 bl(2)] .
  have ds: "dsolved \<sigma> (instd \<rho> dp)" using pcinvD(4)[OF Cons.prems(1)] by simp
  have ds1: "dsolved \<sigma>1 (instd \<rho> (rb, t0, u0))"
    using dsolved_agree[of \<sigma> "instb \<rho> rb" "inst \<rho> t0" "inst \<rho> u0" "maxidx env" \<sigma>1] ds dp bl ag1 by simp
  have pc1': "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env1 [(rb, t0, u0)]"
    by (rule pcinv_Cons[OF pc1 swd _ _ _ ds1]) (use twd te1 ty1 bl below_mono[OF _ mx1] in \<open>auto simp: dp_below_def\<close>)
  have hs1: "hsat \<theta> W1 t0" "hsat \<theta> W1 u0" if "hsat \<theta> W t0" "hsat \<theta> W u0" for \<theta>
    using hsat_agreeV[OF that(1) bl(1) agV1] hsat_agreeV[OF that(2) bl(2) agV1] .
  have gd1: "ffgood \<theta>d W1 env env1" using g1 d by blast
  from padd_ffpair_complete[OF pc1' ty1 h0 pextendsD(1)[OF ext1] xn d(1) d(2)[folded te1] hs1[OF d(3,4)] gd1 ts1 tb1]
  obtain env' tps' W' \<sigma>' where a: "okW (add_ffpair alg (rb, t0, u0) (env1, tps1)) (env', tps')"
    "pcinv alg ar A W' \<rho> \<tau>' \<sigma>' env' []" "tsolved \<sigma>' (itps \<rho> tps')"
    "\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b"
    "agree (maxidx env1) \<sigma>1 \<sigma>'" "agreeV (maxidx env1) W1 W'" "maxidx env1 \<le> maxidx env'" "pextends env' env1"
    "tyenv env' = tyenv env1" "ffgood (tyenv env1) W1 env env1 \<longrightarrow> ffgood (tyenv env1) W' env env'"
    "\<forall>\<theta>. tacyc \<theta> \<longrightarrow> textends \<theta> (tyenv env1) \<longrightarrow> hsat \<theta> W1 t0 \<longrightarrow> hsat \<theta> W1 u0 \<longrightarrow> ffgood \<theta> W1 env env1 \<longrightarrow>
      ffgood \<theta> W' env env'"
    "flexb env env1 \<longrightarrow> fresh_env env \<longrightarrow> maxidx env \<le> maxidx env1 \<longrightarrow> (\<forall>ab\<in>set tps1. ptpok ar A W1 env1 env ab) \<longrightarrow>
      flexb env env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W' env' env ab)"
    by blast
  have fl: "flexb env env' \<and> (\<forall>ab\<in>set tps'. ptpok ar A W' env' env ab)"
    using a(12) fb1 penv_invD(6)[OF pi(1)] mx1 tp1 by blast
  have gE: "ffgood ?\<theta> W' env env'" using a(10) gE1 te1 by simp
  have g: "ffgood \<theta> W' env env'" if "tacyc \<theta>" "textends \<theta> ?\<theta>" "fch W \<theta> \<theta>0 (dp # ffs)" for \<theta>
  proof -
    from that(3) dp obtain \<theta>' where e: "tacyc \<theta>'" "textends \<theta>' \<theta>" "hsat \<theta>' W t0" "hsat \<theta>' W u0"
      "fch W \<theta>' \<theta>0 ffs"
      by auto
    have "textends \<theta>' ?\<theta>" using e(2) that(2) by (rule textends_trans)
    with g1 e have "ffgood \<theta>' W1 env env1" by blast
    with a(11) e(1) \<open>textends \<theta>' ?\<theta>\<close> hs1[OF e(3,4)] te1 have "ffgood \<theta>' W' env env'" by auto
    from ffgood_between[OF this gE that(1) ac e(2) that(2)] show ?thesis .
  qed
  have "okW (foldrW (add_ffpair alg) (dp # ffs) (env, [])) (env', tps')" using f a(1) dp by auto
  then show ?case using a(2-4) agree_trans[OF ag1 a(5) mx1] agreeV_trans[OF agV1 a(6) mx1] mx1 a(7)
      pextends_trans[OF a(8) ext1] a(9) te1 gE g fl
    by (intro exI[where x=env'] exI[where x=tps'] exI[where x=W'] exI[where x=\<sigma>']) auto
qed

end
