section \<open>The Rigid Occurs Check Rejects Only Unsolvable Assignments\<close>

theory Unify_Occurs_Complete
  imports Unify_Typing
begin

text \<open>
  \<^const>\<open>rigid_occurs_term\<close> returns \<^const>\<open>Rigid\<close> for an occurrence of the variable on a path of
  rigid heads (constants, free and bound variables, possibly reached through assignments of
  head variables), where the occurrence is the variable applied to bound variables
  (\<^const>\<open>pattern_occ\<close>). As for the occurs check of pattern unification (theory
  \<open>Pattern_Unif_Complete\<close>), the depth \<^const>\<open>ld\<close> of the \<open>\<eta>\<close>-long
  form of the instance of such an occurrence equals that of the value of the variable, and it
  strictly increases below a rigid head. Hence the assignment of a term with a rigid occurrence
  has no well-typed solution.
\<close>

subsection \<open>Occurrences applied to bound variables\<close>

text \<open>As @{thm [source] ld_flex_occurrence}, without requiring the bound variables to be distinct.\<close>

lemma ld_bvars_occurrence:
  assumes \<sigma>F: "no_loose_bound (\<sigma> F) 0" "\<And>e'. (e', \<tau>\<sigma>) \<turnstile> \<sigma> F : \<tau> F"
    and nF: "\<beta>\<eta>cl (\<sigma> F) nF" "normal nF"
    and ys: "(e, \<tau>) \<turnstile> dB.Var F \<degree>\<degree> map BVar ys : T"
    and v: "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F \<degree>\<degree> map BVar ys" "no_redex v" "(e, \<tau>\<sigma>) \<turnstile> v : T"
  shows "ld e \<tau>\<sigma> v T = ld e' \<tau>\<sigma> nF (\<tau> F)"
proof -
  define m where "m = length ys"
  define Ts where "Ts = map e ys"
  define g where "g = (\<lambda>i. if i < m then ys ! (m - Suc i) else i - m)"
  have \<tau>F: "\<tau> F = Ts \<Rrightarrow> T" using ys by (simp add: typing_Var_app_BVars Ts_def)
  have lenTs: "length Ts = m" by (simp add: Ts_def m_def)
  have closed: "no_loose_bound nF 0"
    using loose_BVars_\<beta>\<eta>cl[OF nF(1)] no_loose_bound_loose_BVars[OF \<sigma>F(1)]
    by (intro loose_BVars_no_loose_bound) auto
  have tynF: "(e'', \<tau>\<sigma>) \<turnstile> nF : Ts \<Rrightarrow> T" for e''
    using subject_reduction_\<beta>\<eta>[OF nF(1) \<sigma>F(2)] \<tau>F by simp
  obtain w where w: "\<beta>\<eta>cl (nF \<degree>\<degree> map BVar (downs m)) w" "normal w" "(env_ext e' Ts, \<tau>\<sigma>) \<turnstile> w : T"
    "loose_BVars w \<subseteq> {..<m}"
    using typed_nf_args[OF closed tynF lenTs] .
  have nFw: "nF \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m w"
  proof -
    have "Abs_m m w \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m (nF \<degree>\<degree> map BVar (downs m))"
      using w(1) by (intro equiv_Abs_m equiv_sym[OF \<beta>\<eta>cl_into_equiv])
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> nF" using closed by (rule eta_expand_equiv)
    finally show ?thesis by (rule equiv_sym)
  qed
  have "ld e' \<tau>\<sigma> nF (Ts \<Rrightarrow> T) = ld e' \<tau>\<sigma> (Abs_m m w) (Ts \<Rrightarrow> T)"
  proof (rule ld_equiv[OF nFw])
    show "(e', \<tau>\<sigma>) \<turnstile> Abs_m m w : Ts \<Rrightarrow> T" using typing_Abs_m[OF w(3)] lenTs by simp
    show "no_redex nF" "no_redex (Abs_m m w)" using nF(2) w(2) by (simp_all add: normal_no_redex)
  qed (rule tynF)
  also have "\<dots> = ld (env_ext e' Ts) \<tau>\<sigma> w T" using ld_Abs_m[OF lenTs] .
  finally have K: "ld e' \<tau>\<sigma> nF (\<tau> F) = ld (env_ext e' Ts) \<tau>\<sigma> w T" by (simp add: \<tau>F)
  have env: "e (g i) = env_ext e' Ts i" if "i \<in> loose_BVars w" for i
  proof -
    have "i < m" using that w(4) by auto
    then have "m - Suc i < m" by arith
    then show ?thesis using \<open>i < m\<close> by (simp add: g_def env_ext_less lenTs Ts_def m_def)
  qed
  have red: "Abs_m m w \<degree>\<degree> map BVar ys \<rightarrow>\<^sub>\<beta>\<^sup>* map_BVars g w"
    using appb_reduces[of "Abs_m m w" ys] by (simp add: appb_Abs_m g_def m_def[symmetric])
  have "ld e \<tau>\<sigma> v T = ld e \<tau>\<sigma> (map_BVars g w) T"
  proof (rule ld_equiv)
    have "\<sigma> F \<degree>\<degree> map BVar ys \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m w \<degree>\<degree> map BVar ys"
      using equiv_trans[OF \<beta>\<eta>cl_into_equiv[OF nF(1)] nFw]
      by (intro equiv_list_app) (auto simp: list_all2_same)
    then show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars g w"
      using v(1) beta_into_equiv[OF red] by (meson equiv_trans)
    show "(e, \<tau>\<sigma>) \<turnstile> map_BVars g w : T" using typing_map_BVars[OF w(3)] env by blast
    show "no_redex (map_BVars g w)" using w(2) by (simp add: normal_no_redex)
  qed (use v in auto)
  also have "\<dots> = ld (env_ext e' Ts) \<tau>\<sigma> w T" using ld_map_BVars env by blast
  finally show ?thesis using K by simp
qed

lemma typings_append: "e \<tturnstile> ts : Ts \<Longrightarrow> e \<tturnstile> us : Us \<Longrightarrow> e \<tturnstile> ts @ us : Ts @ Us"
  by (induction ts arbitrary: Ts) (auto split: list.splits)

text \<open>Appending arguments to a \<open>\<beta>\<close>-normal atom application does not decrease \<^const>\<open>ld\<close>.\<close>

lemma ld_atom_apps_append:
  assumes "is_atom h" "(e, \<tau>) \<turnstile> h : Us \<Rrightarrow> Us' \<Rrightarrow> T" "(e, \<tau>) \<tturnstile> ws : Us" "(e, \<tau>) \<tturnstile> ws' : Us'"
    "\<forall>w\<in>set ws. no_redex w" "\<forall>w\<in>set ws'. no_redex w"
  shows "ld e \<tau> (h \<degree>\<degree> ws) (Us' \<Rrightarrow> T) \<le> ld e \<tau> (h \<degree>\<degree> (ws @ ws')) T"
  using assms(2-6)
proof (induction ws' arbitrary: Us' T rule: rev_induct)
  case (snoc w ws')
  from snoc.prems(3) obtain Vs U where Us': "Us' = Vs @ [U]" "(e, \<tau>) \<tturnstile> ws' : Vs" "(e, \<tau>) \<turnstile> w : U"
    by (elim types_snocE)
  have h: "(e, \<tau>) \<turnstile> h : Us \<Rrightarrow> Vs \<Rrightarrow> U \<Rightarrow> T" using snoc.prems(1) Us'(1) by simp
  have "(e, \<tau>) \<turnstile> h \<degree>\<degree> ws \<degree>\<degree> ws' : U \<Rightarrow> T"
    using list_app_typeI[OF h[folded foldr_append] typings_append[OF snoc.prems(2) Us'(2)]] by simp
  moreover have "no_redex (h \<degree>\<degree> ws \<degree>\<degree> ws')" "\<not> Unif_Occurs.is_Abs (h \<degree>\<degree> ws \<degree>\<degree> ws')"
    using snoc.prems(4,5) assms(1) no_redex_atom_apps[OF assms(1), of "ws @ ws'"]
      is_Abs_atom_apps[OF assms(1), of "ws @ ws'"] by auto
  ultimately have sp: "spine_type e \<tau> (h \<degree>\<degree> ws \<degree>\<degree> ws') = U \<Rightarrow> T" by (rule spine_type_typing)
  have "ld e \<tau> (h \<degree>\<degree> ws) (Us' \<Rrightarrow> T) \<le> ld e \<tau> (h \<degree>\<degree> ws \<degree>\<degree> ws') (U \<Rightarrow> T)"
    using snoc.IH[OF h snoc.prems(2) Us'(2) snoc.prems(4)] snoc.prems(5) Us'(1) by simp
  then show ?case by (simp add: sp)
qed simp

subsection \<open>Heads modulo the environment\<close>

lemma head_of_in_App: "head_of_in env (f $ u) = head_of_in env f"
  by (subst head_of_in.simps) simp

lemma head_of_in_list_comb: "head_of_in env (list_comb h ts) = head_of_in env h"
  by (induction ts rule: rev_induct) (simp_all add: list_comb_snoc head_of_in_App)

lemma lookup_unbound: "vt_is_empty (tyenv env) \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> lookup env x U = return None"
  by (simp add: lookup_def unified_empty var_clash_def)

lemma lookup_bound:
  "vt_is_empty (tyenv env) \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> lookup env x U = return (Some u)"
  by (simp add: lookup_def unified_empty var_clash_def)

lemma head_of_in_unbound:
  "vt_is_empty (tyenv env) \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> head_of_in env (Var x U) = return (Var x U)"
  by (subst head_of_in.simps) (simp add: lookup_unbound)

lemma head_of_in_bound:
  "vt_is_empty (tyenv env) \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> head_of_in env (Var x U) = head_of_in env u"
  by (subst head_of_in.simps) (simp add: lookup_bound)

lemma head_of_in_typed:
  assumes "head_of_in env t = Some r"
  shows "r = Ok h \<Longrightarrow> wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> has_type V Ts t T \<Longrightarrow> \<exists>U. has_type V Ts h U"
  using assms
proof (induction env t r arbitrary: T rule: head_of_in.raw_induct[rotated, consumes 1])
  case (1 hd env t r)
  note rh = "1.prems"(1) and wf = "1.prems"(2) and ety = "1.prems"(3) and ty = "1.prems"(4)
  show ?case
  proof (cases t)
    case (App f u)
    from ty App obtain U where "has_type V Ts f (U \<rightarrow>\<^sub>T T)" by (auto elim: has_type_elims)
    with "1.hyps" "1.IH"[of env f r] rh wf ety App show ?thesis by simp
  next
    case (Var x U)
    from "1.hyps" rh Var obtain y where lkp: "ok (lookup env x U) y"
      and rest: "(case y of Some u \<Rightarrow> hd env u | None \<Rightarrow> return t) = Some r"
      by (auto simp: bindM_def split: option.splits res.splits)
    note lk = ok_lookup[OF wf_envD(1)[OF wf] lkp]
    show ?thesis
    proof (cases y)
      case None
      with rest rh ty show ?thesis by (auto simp: return_def)
    next
      case (Some u)
      with lk have b: "vt_lookup (tenv env) x = Some (U, u)" by simp
      from Some rest have hu: "hd env u = Some r" by simp
      have "has_type V Ts u U" using has_type_weaken[of V "[]" u U Ts] env_typedD[OF ety b] by simp
      from "1.IH"[OF hu rh wf ety this] show ?thesis .
    qed
  qed (use "1.hyps" rh ty in \<open>auto simp: return_def\<close>)
qed

lemma head_of_in_not_App:
  assumes "head_of_in env t = Some r"
  shows "r = Ok (f $ u) \<Longrightarrow> False"
  using assms
proof (induction env t r rule: head_of_in.raw_induct[rotated, consumes 1])
  case (1 hd env t r)
  then show ?case
    by (cases t) (auto simp: bindM_def return_def split: option.splits res.splits)
qed

text \<open>The instance of a term whose head modulo the environment is rigid is an atom application.\<close>

lemma head_of_in_spine:
  assumes "head_of_in env t = Some r"
  shows "r = Ok h \<Longrightarrow> is_rigid h \<Longrightarrow> wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> solution V \<tau>' \<sigma> env \<Longrightarrow>
    has_type V Ts t T \<Longrightarrow>
    \<exists>Hs as. mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> as \<and> (bnd_env Ts, \<tau>') \<turnstile> tr h : Hs \<Rrightarrow> trty T \<and>
      (bnd_env Ts, \<tau>') \<tturnstile> as : Hs"
  using assms
proof (induction env t r arbitrary: T rule: head_of_in.raw_induct[rotated, consumes 1])
  case (1 hd env t r)
  note rh = "1.prems"(1) and rig = "1.prems"(2) and wf = "1.prems"(3) and ety = "1.prems"(4)
    and sol = "1.prems"(5) and ty = "1.prems"(6)
  note \<sigma> = solutionD[OF sol]
  show ?case
  proof (cases t)
    case (App f u)
    from ty App obtain U where tf: "has_type V Ts f (U \<rightarrow>\<^sub>T T)" and tu: "has_type V Ts u U"
      by (auto elim: has_type_elims)
    from "1.hyps" App have "hd env f = Some r" by simp
    from "1.IH"[OF this rh rig wf ety sol tf] obtain Hs as where
      eq: "mk_subst \<sigma> (tr f) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> as" and th: "(bnd_env Ts, \<tau>') \<turnstile> tr h : Hs \<Rrightarrow> trty (U \<rightarrow>\<^sub>T T)"
      and tas: "(bnd_env Ts, \<tau>') \<tturnstile> as : Hs" by blast
    show ?thesis
    proof (intro exI conjI)
      show "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> (as @ [mk_subst \<sigma> (tr u)])"
        using equiv_AppL[OF eq] App by simp
      show "(bnd_env Ts, \<tau>') \<turnstile> tr h : (Hs @ [trty U]) \<Rrightarrow> trty T" using th by simp
      show "(bnd_env Ts, \<tau>') \<tturnstile> as @ [mk_subst \<sigma> (tr u)] : Hs @ [trty U]"
        using types_snoc[OF tas has_type_subst[OF tu \<sigma>(2)]] .
    qed
  next
    case (Var x U)
    from "1.hyps" rh Var obtain y where lkp: "ok (lookup env x U) y"
      and rest: "(case y of Some u \<Rightarrow> hd env u | None \<Rightarrow> return t) = Some r"
      by (auto simp: bindM_def split: option.splits res.splits)
    note lk = ok_lookup[OF wf_envD(1)[OF wf] lkp]
    show ?thesis
    proof (cases y)
      case None
      with rest rh rig Var show ?thesis by (auto simp: return_def is_rigid_def)
    next
      case (Some u)
      with lk have b: "vt_lookup (tenv env) x = Some (U, u)" by simp
      from Some rest have hu: "hd env u = Some r" by simp
      from ty Var have T: "T = U" by (auto elim: has_type_elims)
      have "has_type V Ts u U" using has_type_weaken[of V "[]" u U Ts] env_typedD[OF ety b] by simp
      from "1.IH"[OF hu rh rig wf ety sol this] obtain Hs as where
        eq: "mk_subst \<sigma> (tr u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> as" and rest': "(bnd_env Ts, \<tau>') \<turnstile> tr h : Hs \<Rrightarrow> trty U"
          "(bnd_env Ts, \<tau>') \<tturnstile> as : Hs"
        by blast
      have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)" using satD[OF \<sigma>(4) b] Var by simp
      with eq rest' T show ?thesis by (meson equiv_trans)
    qed
  next
    case (Abs a U b)
    with "1.hyps" rh rig show ?thesis by (auto simp: return_def is_rigid_def)
  qed (use "1.hyps" rh rig rigid_tr[OF rig \<sigma>(3)] has_type_subst[OF ty \<sigma>(2)] in
    \<open>auto simp: return_def intro!: exI[of _ "[]"]\<close>)
qed

text \<open>A rigid occurrence found by \<^const>\<open>occomb\<close> lies in an argument or in the head of the spine.\<close>

lemma occomb_Rigid:
  assumes "occomb oc seen (list_comb h ts) = Some (Ok (Rigid, s))" "\<nexists>f u. h = f $ u"
  shows "(\<exists>i<length ts. \<exists>s1 s2. oc s1 (ts ! i) = Some (Ok (Rigid, s2))) \<or>
    (\<exists>s1 s2. oc s1 h = Some (Ok (Rigid, s2)))"
  using assms(1)
proof (induction ts arbitrary: seen s rule: rev_induct)
  case Nil
  have "occomb oc seen h = oc seen h" using assms(2) by (cases h) simp_all
  with Nil show ?case by auto
next
  case (snoc t ts)
  from snoc.prems obtain r1 where r1: "oc seen t = Some (Ok r1)"
    and rest: "ok (if fst r1 = Rigid then return (Rigid, snd r1)
      else occomb oc (snd r1) (list_comb h ts) \<bind>
        (\<lambda>r2. return (if fst r2 = NoOcc then fst r1 else fst r2, snd r2))) (Rigid, s)"
    by (auto simp: list_comb_snoc)
  show ?case
  proof (cases "fst r1 = Rigid")
    case True
    with r1 have "oc seen ((ts @ [t]) ! length ts) = Some (Ok (Rigid, snd r1))" by (cases r1) simp
    then show ?thesis by fastforce
  next
    case False
    with rest obtain r2 where r2: "occomb oc (snd r1) (list_comb h ts) = Some (Ok r2)" "fst r2 = Rigid"
      by (auto split: if_splits)
    then have "occomb oc (snd r1) (list_comb h ts) = Some (Ok (Rigid, snd r2))" by (cases r2) simp
    from snoc.IH[OF this] show ?thesis
    proof (elim disjE exE conjE)
      fix i s1 s2 assume "i < length ts" "oc s1 (ts ! i) = Some (Ok (Rigid, s2))"
      then show ?thesis by (intro disjI1 exI[of _ i]) (auto simp: nth_append)
    qed blast
  qed
qed

subsection \<open>Rigid occurrences\<close>

text \<open>Is the head of a term modulo the environment rigid?\<close>

definition hrig :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "hrig env t \<longleftrightarrow> (\<exists>h. ok (head_of_in env t) h \<and> is_rigid h)"

text \<open>
  The measure of every \<open>\<beta>\<close>-normal instance of a term with a rigid occurrence of the unbound
  variable \<open>v\<close> is at least that of the value of \<open>v\<close>, and strictly larger if the head of the
  term is rigid.
\<close>

lemma rocc_ld:
  assumes "rocc t env v seen = Some r"
  shows "r = Ok (Rigid, seen') \<Longrightarrow> wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> solution V \<tau>' \<sigma> env \<Longrightarrow>
    vt_lookup (tenv env) v = None \<Longrightarrow> \<beta>\<eta>cl (\<sigma> (code (AVar v))) nF \<Longrightarrow> normal nF \<Longrightarrow>
    has_type V Ts t T \<Longrightarrow> w \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t) \<Longrightarrow> no_redex w \<Longrightarrow>
    (bnd_env Ts, \<tau>') \<turnstile> w : trty T \<Longrightarrow>
    ld E \<tau>' nF (trty (V v)) \<le> ld (bnd_env Ts) \<tau>' w (trty T) \<and>
    (hrig env t \<longrightarrow> ld E \<tau>' nF (trty (V v)) < ld (bnd_env Ts) \<tau>' w (trty T))"
  using assms
proof (induction t env v seen r arbitrary: seen' Ts T w rule: rocc.raw_induct[rotated, consumes 1])
  case (1 R t env v seen r)
  note rR = "1.prems"(1) and wf = "1.prems"(2) and ety = "1.prems"(3) and sol = "1.prems"(4)
    and vu = "1.prems"(5) and nF = "1.prems"(6,7) and ty = "1.prems"(8) and weq = "1.prems"(9)
    and wnr = "1.prems"(10) and wty = "1.prems"(11)
  note \<sigma> = solutionD[OF sol]
  note e = wf_envD(1)[OF wf]
  let ?L = "ld E \<tau>' nF (trty (V v))"
  note IH = "1.IH"[OF _ refl wf ety sol vu nF]
  have \<sigma>F: "no_loose_bound (\<sigma> (code (AVar v))) 0" "\<And>e'. (e', \<tau>') \<turnstile> \<sigma> (code (AVar v)) : tau V (code (AVar v))"
    by (rule closed_onD[OF \<sigma>(1)], simp, rule typed_onD[OF \<sigma>(2)], simp)
  text \<open>An occurrence of \<open>v\<close> applied to bound variables.\<close>
  have occ: "?L \<le> ld (bnd_env Ts) \<tau>' w (trty T)"
    if "t = list_comb (Var v U) (map Bound is)" for U "is"
  proof -
    define ys where "ys = nats is"
    have trt: "tr t = dB.Var (code (AVar v)) \<degree>\<degree> map BVar ys"
      using that(1) by (simp add: tr_list_comb ys_def comp_def)
    have "ld (bnd_env Ts) \<tau>' w (trty T) = ld E \<tau>' nF (tau V (code (AVar v)))"
    proof (rule ld_bvars_occurrence[where \<sigma> = \<sigma> and F = "code (AVar v)" and \<tau> = "tau V", OF \<sigma>F nF])
      show "(bnd_env Ts, tau V) \<turnstile> dB.Var (code (AVar v)) \<degree>\<degree> map BVar ys : trty T"
        using has_type_tr[OF ty] trt by simp
      have "mk_subst \<sigma> (tr t) = \<sigma> (code (AVar v)) \<degree>\<degree> map BVar ys" using trt by simp
      with weq show "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v)) \<degree>\<degree> map BVar ys" by (simp only:)
    qed (use wnr wty in auto)
    then show ?thesis by simp
  qed
  show ?case
  proof (cases t)
    case (Var x U)
    show ?thesis
    proof (cases "x \<in> set seen")
      case True
      with "1.hyps" rR Var show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "v = x")
        case True
        have "\<not> hrig env t"
          using head_of_in_unbound[OF e vu] True Var by (auto simp: hrig_def return_def is_rigid_def)
        moreover have "?L \<le> ld (bnd_env Ts) \<tau>' w (trty T)"
          using occ[of U "[]"] True Var by (simp add: list_comb_def)
        ultimately show ?thesis by simp
      next
        case vx: False
        with False "1.hyps" rR Var obtain y where lkp: "ok (lookup env x U) y"
          and rest: "(case y of None \<Rightarrow> return (NoOcc, x # seen) | Some u \<Rightarrow> R u env v (x # seen)) = Some r"
          by (auto simp: bindM_def split: option.splits res.splits)
        note lk = ok_lookup[OF e lkp]
        show ?thesis
        proof (cases y)
          case None
          with rest rR show ?thesis by (simp add: return_def)
        next
          case (Some u)
          with lk have b: "vt_lookup (tenv env) x = Some (U, u)" by simp
          from Some rest rR have ru: "R u env v (x # seen) = Some (Ok (Rigid, seen'))" by simp
          from ty Var have T: "T = U" by (auto elim: has_type_elims)
          have tyu: "has_type V Ts u T"
            using has_type_weaken[of V "[]" u U Ts] env_typedD[OF ety b] T by simp
          have "mk_subst \<sigma> (tr t) = \<sigma> (code (AVar x))" using Var by simp
          with weq have "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar x))" by (simp only:)
          from equiv_trans[OF this satD[OF \<sigma>(4) b]] have "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)" .
          from IH[OF ru tyu this wnr wty] show ?thesis
            unfolding hrig_def Var head_of_in_bound[OF e b] .
        qed
      qed
    qed
  next
    case (Abs a A b)
    from "1.hyps" rR Abs have rb: "R b env v seen = Some (Ok (Rigid, seen'))" by simp
    from ty Abs obtain U where T: "T = A \<rightarrow>\<^sub>T U" and tyb: "has_type V (A # Ts) b U"
      by (auto elim: has_type_elims)
    have "(bnd_env (A # Ts), \<tau>') \<turnstile> mk_subst \<sigma> (tr b) : trty U" by (rule has_type_subst[OF tyb \<sigma>(2)])
    then obtain w' where w': "\<beta>\<eta>cl (mk_subst \<sigma> (tr b)) w'" "normal w'" "(bnd_env (A # Ts), \<tau>') \<turnstile> w' : trty U"
      by (rule nf_typed)
    from IH[OF rb tyb equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w'(1)]] normal_no_redex[OF w'(2)] w'(3)]
    have "?L \<le> ld (bnd_env (A # Ts)) \<tau>' w' (trty U)" by simp
    also have "\<dots> = ld (bnd_env Ts) \<tau>' (dB.Abs w') (trty T)" by (simp add: T bnd_env_Cons)
    also have "\<dots> = ld (bnd_env Ts) \<tau>' w (trty T)"
    proof (rule ld_equiv)
      have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs w'" using w'(1) Abs by (auto intro: equiv_Abs \<beta>\<eta>cl_into_equiv)
      then show "dB.Abs w' \<equiv>\<^sub>\<beta>\<^sub>\<eta> w" using weq by (meson equiv_sym equiv_trans)
      show "(bnd_env Ts, \<tau>') \<turnstile> dB.Abs w' : trty T" using w'(3) T by (auto simp: bnd_env_Cons)
    qed (use wty wnr normal_no_redex[OF w'(2)] in auto)
    finally have le: "?L \<le> ld (bnd_env Ts) \<tau>' w (trty T)" .
    have "head_of_in env t = return t" using Abs by (subst head_of_in.simps) simp
    then have "\<not> hrig env t" using Abs by (auto simp: hrig_def return_def is_rigid_def)
    with le show ?thesis by simp
  next
    case (App f u)
    with "1.hyps" rR obtain h where hd: "ok (head_of_in env f) h"
      and rest: "(case h of
          Var x _ \<Rightarrow> if v = x \<and> pattern_occ v t then return (Rigid, seen) else nonrigid env v seen t
        | Abs _ _ _ \<Rightarrow> nonrigid env v seen t
        | _ \<Rightarrow> occomb (\<lambda>seen t. R t env v seen) seen t) = Some (Ok (Rigid, seen'))"
      by (auto simp: bindM_def simp del: occomb.simps split: option.splits res.splits)
    have hdt: "head_of_in env t = head_of_in env f" using App by (simp add: head_of_in_App)
    have nonrig: False if "ok (nonrigid env v seen t) (Rigid, seen')"
      using nonrigid_cases[OF that] by (auto split: if_splits)
    obtain h0 ts where sc: "strip_comb t = (h0, ts)" by force
    note t0 = strip_comb_list_comb[OF sc]
    have h0: "\<nexists>f u. h0 = f $ u" by (rule strip_comb_head[OF sc])
    have hd0: "head_of_in env h0 = head_of_in env t" using t0 by (simp add: head_of_in_list_comb)
    have spine: "?L < ld (bnd_env Ts) \<tau>' w (trty T)"
      if oc: "occomb (\<lambda>seen t. R t env v seen) seen t = Some (Ok (Rigid, seen'))" and rig: "is_rigid h"
    proof -
      from ty t0 obtain Us where tyh0: "has_type V Ts h0 (foldr fun_type Us T)"
        and tyts: "list_all2 (has_type V Ts) ts Us"
        by (auto simp: has_type_list_comb)
      have lUs: "length Us = length ts" using list_all2_lengthD[OF tyts] by simp
      have hh0: "head_of_in env h0 = Some (Ok h)" using hd hd0 hdt by simp
      from head_of_in_spine[OF hh0 refl rig wf ety sol tyh0] obtain Hs as where
        eqh0: "mk_subst \<sigma> (tr h0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> as"
        and th: "(bnd_env Ts, \<tau>') \<turnstile> tr h : Hs \<Rrightarrow> map trty Us \<Rrightarrow> trty T"
        and tas: "(bnd_env Ts, \<tau>') \<tturnstile> as : Hs"
        by (auto simp: trty_foldr)
      have lHs: "length Hs = length as" using typings_length[OF tas] .
      define args where "args = map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
      have targs: "(bnd_env Ts, \<tau>') \<tturnstile> args : map trty Us"
        unfolding args_def
        by (rule typings_map2) (use lUs list_all2_nthD[OF tyts] has_type_subst[OF _ \<sigma>(2)] in auto)
      note atom = conjunct2[OF rigid_tr[OF rig \<sigma>(3)]]
      have th': "(bnd_env Ts, \<tau>') \<turnstile> tr h : (Hs @ map trty Us) \<Rrightarrow> trty T" using th by simp
      from atom_apps_nf[OF atom th' typings_append[OF tas targs]] obtain ws
        where ws: "length ws = length (as @ args)"
          "\<And>i. i < length (as @ args) \<Longrightarrow>
            \<beta>\<eta>cl ((as @ args) ! i) (ws ! i) \<and> normal (ws ! i) \<and> (bnd_env Ts, \<tau>') \<turnstile> ws ! i : (Hs @ map trty Us) ! i"
          "tr h \<degree>\<degree> (as @ args) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> ws" "no_redex (tr h \<degree>\<degree> ws)" "(bnd_env Ts, \<tau>') \<turnstile> tr h \<degree>\<degree> ws : trty T"
          "\<And>i. i < length (as @ args) \<Longrightarrow>
            Suc (ld (bnd_env Ts) \<tau>' (ws ! i) ((Hs @ map trty Us) ! i)) \<le> ld (bnd_env Ts) \<tau>' (tr h \<degree>\<degree> ws) (trty T)"
        by blast
      have lws: "length ws = length as + length ts" using ws(1) by (simp add: args_def)
      have wsi: "\<beta>\<eta>cl ((as @ args) ! i) (ws ! i) \<and> normal (ws ! i) \<and>
          (bnd_env Ts, \<tau>') \<turnstile> ws ! i : (Hs @ map trty Us) ! i" if "i < length ws" for i
        using ws(2)[of i] that ws(1) by simp
      have nrws: "\<forall>x\<in>set ws. no_redex x"
      proof
        fix x assume "x \<in> set ws"
        then obtain i where "i < length ws" "x = ws ! i" by (auto simp: in_set_conv_nth)
        with wsi[of i] show "no_redex x" by (simp add: normal_no_redex)
      qed
      have "mk_subst \<sigma> (tr t) = mk_subst \<sigma> (tr h0) \<degree>\<degree> args" using t0 by (simp add: tr_list_comb args_def comp_def)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> as \<degree>\<degree> args" using eqh0 by (intro equiv_list_app) (auto simp: list_all2_same)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> ws" using ws(3) by simp
      finally have eqw: "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> ws" by (rule equiv_trans[OF weq])
      have ldw: "ld (bnd_env Ts) \<tau>' w (trty T) = ld (bnd_env Ts) \<tau>' (tr h \<degree>\<degree> ws) (trty T)"
        by (rule ld_equiv[OF eqw wty ws(5) wnr ws(4)])
      from occomb_Rigid[OF oc[unfolded t0] h0] show ?thesis
      proof (elim disjE exE conjE)
        fix i s1 s2 assume i: "i < length ts" and ri: "R (ts ! i) env v s1 = Some (Ok (Rigid, s2))"
        let ?j = "length as + i"
        have j: "?j < length (as @ args)" using i by (simp add: args_def)
        have aj: "(as @ args) ! ?j = mk_subst \<sigma> (tr (ts ! i))" "(Hs @ map trty Us) ! ?j = trty (Us ! i)"
          using i lUs lHs by (simp_all add: nth_append args_def)
        from ws(2)[OF j] aj have wj: "\<beta>\<eta>cl (mk_subst \<sigma> (tr (ts ! i))) (ws ! ?j)" "normal (ws ! ?j)"
          "(bnd_env Ts, \<tau>') \<turnstile> ws ! ?j : trty (Us ! i)"
          by simp_all
        from IH[OF ri list_all2_nthD[OF tyts i] equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF wj(1)]]
            normal_no_redex[OF wj(2)] wj(3)]
        have "?L \<le> ld (bnd_env Ts) \<tau>' (ws ! ?j) (trty (Us ! i))" by simp
        also have "\<dots> < ld (bnd_env Ts) \<tau>' w (trty T)" using ws(6)[OF j] aj(2) ldw by simp
        finally show ?thesis .
      next
        fix s1 s2 assume rh0: "R h0 env v s1 = Some (Ok (Rigid, s2))"
        let ?w0 = "tr h \<degree>\<degree> take (length as) ws"
        have tws: "(bnd_env Ts, \<tau>') \<tturnstile> take (length as) ws : Hs"
        proof (rule typings_map2)
          fix i assume "i < length (take (length as) ws)"
          then show "(bnd_env Ts, \<tau>') \<turnstile> take (length as) ws ! i : Hs ! i"
            using wsi[of i] lws lHs by (simp add: nth_append)
        qed (use lws lHs in simp)
        have dws: "(bnd_env Ts, \<tau>') \<tturnstile> drop (length as) ws : map trty Us"
        proof (rule typings_map2)
          fix i assume "i < length (drop (length as) ws)"
          then show "(bnd_env Ts, \<tau>') \<turnstile> drop (length as) ws ! i : map trty Us ! i"
            using wsi[of "length as + i"] lws lHs lUs by (simp add: nth_append)
        qed (use lws lUs in simp)
        have "mk_subst \<sigma> (tr h0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?w0"
        proof -
          have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) as (take (length as) ws)"
            unfolding list_all2_conv_all_nth
          proof (intro conjI allI impI)
            fix i assume "i < length as"
            then show "as ! i \<equiv>\<^sub>\<beta>\<^sub>\<eta> take (length as) ws ! i"
              using wsi[of i] lws by (auto simp: nth_append intro: \<beta>\<eta>cl_into_equiv)
          qed (use lws in simp)
          from equiv_trans[OF eqh0 equiv_list_app[OF _ this]] show ?thesis by simp
        qed
        moreover have "no_redex ?w0" using nrws no_redex_atom_apps[OF atom] by (auto dest: in_set_takeD)
        moreover have "(bnd_env Ts, \<tau>') \<turnstile> ?w0 : trty (foldr fun_type Us T)"
          using list_app_typeI[OF th tws] by (simp add: trty_foldr)
        moreover have "hrig env h0" using hh0 rig by (simp add: hrig_def)
        ultimately have "?L < ld (bnd_env Ts) \<tau>' ?w0 (map trty Us \<Rrightarrow> trty T)"
          using IH[OF rh0 tyh0 equiv_sym] by (simp add: trty_foldr)
        also have "\<dots> \<le> ld (bnd_env Ts) \<tau>' (tr h \<degree>\<degree> (take (length as) ws @ drop (length as) ws)) (trty T)"
          using nrws by (intro ld_atom_apps_append[OF atom th tws dws]) (auto dest: in_set_takeD in_set_dropD)
        finally show ?thesis using ldw by simp
      qed
    qed
    show ?thesis
    proof (cases h)
      case (Var x Ux)
      show ?thesis
      proof (cases "v = x \<and> pattern_occ v t")
        case True
        then obtain Uv where h0v: "h0 = Var v Uv" and bs: "list_all is_Bound ts"
          using sc by (auto simp: pattern_occ_def split: pterm.splits)
        define "is" where "is = map (\<lambda>b. case b of Bound i \<Rightarrow> i | _ \<Rightarrow> 0) ts"
        have "ts = map Bound is"
          unfolding is_def map_map using bs by (induction ts) (auto elim!: is_Bound.elims)
        with t0 h0v have "?L \<le> ld (bnd_env Ts) \<tau>' w (trty T)" by (intro occ) auto
        moreover have "\<not> hrig env t" using hd Var hdt by (auto simp: hrig_def is_rigid_def)
        ultimately show ?thesis by simp
      next
        case False
        with rest Var nonrig show ?thesis by simp
      qed
    next
      case (Abs a A b)
      with rest nonrig show ?thesis by simp
    next
      case (App f' u')
      with head_of_in_not_App[of env f "Ok h"] hd show ?thesis by simp
    next
      case (Const c U)
      with rest spine show ?thesis by (simp add: is_rigid_def less_imp_le)
    next
      case (Free c U)
      with rest spine show ?thesis by (simp add: is_rigid_def less_imp_le)
    next
      case (Bound i)
      from ty App obtain U where "has_type V Ts f (U \<rightarrow>\<^sub>T T)" by (auto elim: has_type_elims)
      from head_of_in_typed[OF hd[simplified] refl wf ety this] Bound have "0 \<le> i"
        by (auto simp: has_type_Bound_iff)
      with Bound rest spine show ?thesis by (simp add: is_rigid_def less_imp_le)
    qed
  qed (use "1.hyps" rR in \<open>auto simp: return_def\<close>)
qed

text \<open>
  Hence the assignment of a rigid-headed term with a rigid occurrence of the (unbound) assigned
  variable \<open>v\<close> has no well-typed solution: \<^const>\<open>assignment\<close> fails with \<open>CANTUNIFY\<close> only on
  unsolvable pairs.
\<close>

theorem rigid_occurs_unsolvable:
  assumes gev: "okW (get_eta_var rb 0 t) (v, T)" and oc: "ok (rigid_occurs_term env v u) Rigid"
    and wf: "wf_env ar env" and ety: "env_typed V env" and sol: "solution V \<tau>' \<sigma> env"
    and vu: "vt_lookup (tenv env) v = None"
    and tyt: "has_type V (map snd rb) t U" and tyu: "has_type V (map snd rb) u U" and hr: "hrig env u"
    and ds: "dsolved \<sigma> (rb, t, u)"
  shows False
proof -
  note \<sigma> = solutionD[OF sol]
  let ?Ts = "map snd rb" and ?n = "length rb"
  from oc obtain s where ro: "rocc u env v [] = Some (Ok (Rigid, s))"
    by (auto simp: rigid_occurs_term_def)
  have trt: "tr t = dB.Var (code (AVar v)) \<degree>\<degree> map BVar (downs ?n)"
    using get_eta_var_tr[OF gev] by (simp add: comp_def)
  have "Abs_m ?n (\<sigma> (code (AVar v)) \<degree>\<degree> map BVar (downs ?n)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?n (mk_subst \<sigma> (tr u))"
    using dsolvedD[OF ds] trt by (simp add: tr_rlist_abs mk_subst_Abs_m)
  then have eq: "\<sigma> (code (AVar v)) \<degree>\<degree> map BVar (downs ?n) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
    by (rule Abs_m_equiv_reflect)
  have \<sigma>F: "no_loose_bound (\<sigma> (code (AVar v))) 0" "\<And>e'. (e', \<tau>') \<turnstile> \<sigma> (code (AVar v)) : tau V (code (AVar v))"
    by (rule closed_onD[OF \<sigma>(1)], simp, rule typed_onD[OF \<sigma>(2)], simp)
  obtain nF where nF: "\<beta>\<eta>cl (\<sigma> (code (AVar v))) nF" "normal nF" using normal_form_ex[OF \<sigma>F(2)] by blast
  have "(bnd_env ?Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr u) : trty U" by (rule has_type_subst[OF tyu \<sigma>(2)])
  then obtain w where w: "\<beta>\<eta>cl (mk_subst \<sigma> (tr u)) w" "normal w" "(bnd_env ?Ts, \<tau>') \<turnstile> w : trty U"
    by (rule nf_typed)
  have weq: "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)" by (rule equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w(1)]])
  from rocc_ld[OF ro refl wf ety sol vu nF tyu weq normal_no_redex[OF w(2)] w(3)] hr
  have lt: "ld E \<tau>' nF (trty (V v)) < ld (bnd_env ?Ts) \<tau>' w (trty U)" by simp
  have "ld (bnd_env ?Ts) \<tau>' w (trty U) = ld E \<tau>' nF (tau V (code (AVar v)))"
  proof (rule ld_bvars_occurrence[where \<sigma> = \<sigma> and F = "code (AVar v)" and \<tau> = "tau V", OF \<sigma>F nF])
    show "(bnd_env ?Ts, tau V) \<turnstile> dB.Var (code (AVar v)) \<degree>\<degree> map BVar (downs ?n) : trty U"
      using has_type_tr[OF tyt] trt by simp
    show "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v)) \<degree>\<degree> map BVar (downs ?n)"
      using equiv_trans[OF weq equiv_sym[OF eq]] .
  qed (use w normal_no_redex in auto)
  with lt show False by simp
qed

end
