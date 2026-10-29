section \<open>Completeness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex_Complete
  imports Unify_Match_Complete
begin

text \<open>
  Completeness of \<^const>\<open>add_ffpair\<close>: on flex-flex pairs solved by a well-typed solution \<open>\<sigma>\<close>, the
  treatment of the flex-flex pairs terminates without an exception, and an extension of \<open>\<sigma>\<close> by
  values for the new variables satisfies the resulting environment and solves the remaining
  pairs. The deletion of arguments in \<^const>\<open>clean_term\<close> does not lose solutions, since a banned
  bound variable that occurs rigidly in an argument persists in every instance.
\<close>

subsection \<open>Normalization terminates\<close>

text \<open>
  \<open>fhd t\<close>: the head of \<open>t\<close>, looking into abstractions in head position, also of redexes. A term
  whose \<open>fhd\<close> is a variable unbound in \<open>env0\<close> keeps such a head under normalization in an
  environment that binds the other variables only to such terms (\<open>flexb\<close>).
\<close>

fun fhd :: "pterm \<Rightarrow> pterm" where
  "fhd (Abs _ _ b) = fhd b"
| "fhd (f $ _) = fhd f"
| "fhd t = t"

definition fh :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "fh env0 t \<longleftrightarrow> (\<exists>w W. fhd t = Var w W \<and> vt_lookup (tenv env0) w = None)"

definition flexb :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "flexb env0 env \<longleftrightarrow>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> vt_lookup (tenv env0) x = None \<longrightarrow> fh env0 u)"

lemma fhd_subst_bound_aux: "is_Var (fhd b) \<Longrightarrow> fhd (subst_bound_aux u lev b) = fhd b"
  by (induction u lev b rule: subst_bound_aux.induct) (auto split: if_splits)

lemma fhd_subst_bound: "is_Var (fhd b) \<Longrightarrow> fhd (subst_bound u b) = fhd b"
  by (simp add: subst_bound_def fhd_subst_bound_aux)

lemma fhd_head_of: "is_Var (head_of t) \<Longrightarrow> fhd t = head_of t"
  by (induction t) auto

lemma fhd_no_beta: "\<not> could_beta_contract t \<Longrightarrow> is_Abs t \<or> fhd t = head_of t"
proof (induction t)
  case (App f u)
  then show ?case by (cases f) auto
qed auto

context
  fixes ar env W
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
begin

abbreviation inst :: "pterm \<Rightarrow> dB" where
  "inst t \<equiv> mk_subst (env_inst env) (tr t)"

text \<open>
  \<^const>\<open>norm_term1\<close> terminates on well-typed terms, with a well-typed result that is a
  \<open>\<beta>\<close>-reduct of the instance; the head variable of the result is unbound.
\<close>

lemma norm_term1_term:
  "has_type W Ts t T \<Longrightarrow> \<exists>t'. norm_term1 (tenv env) t = Some (Ok t') \<and> has_type W Ts t' T \<and>
    inst t \<rightarrow>\<^sub>\<beta>\<^sup>* inst t' \<and> (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and>
    (is_Abs t' \<or> fhd t' = head_of t') \<and>
    (\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t \<longrightarrow> fh env0 t')"
proof (induction t arbitrary: Ts T rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (inst t, card (reach env (vps t)))"]])
  case (1 t)
  let ?P = "\<lambda>t Ts T t'. norm_term1 (tenv env) t = Some (Ok t') \<and> has_type W Ts t' T \<and>
    inst t \<rightarrow>\<^sub>\<beta>\<^sup>* inst t' \<and> (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and>
    (is_Abs t' \<or> fhd t' = head_of t') \<and> (\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t \<longrightarrow> fh env0 t')"
  have red: "\<exists>t'. ?P u Us U t'"
    if "(sup beta subt)\<^sup>+\<^sup>+ (inst t) (inst u)" "has_type W Us u U" for u Us U
    using "1.IH"[OF _ that(2)] sn_lessI[OF inst_typable[OF ac wf ety "1.prems"] that(1)] by simp
  show ?case
  proof (cases t)
    case (Var x U)
    from "1.prems" Var have WU: "W x = U" by (auto elim: has_type_elims)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case None
      then have "norm_term1 (tenv env) t = Some (Ok t)" using Var by (subst norm_term1.simps) (simp add: lookup1_def return_def)
      then show ?thesis using "1.prems" None Var by auto
    next
      case (Some p)
      obtain U' u where p: "p = (U', u)" by (cases p)
      from env_typedD[OF ety Some[unfolded p]] WU have U': "U' = U" and tyu0: "has_type W [] u U" by auto
      from "1.prems" Var have TU: "T = U" by (auto elim: has_type_elims)
      have lk: "lk env x U = Some u" using Some p U' by (simp add: lk_def)
      have tyu: "has_type W Ts u U" using has_type_weaken[OF tyu0, of Ts] by simp
      have "inst t = inst u" using inst_bound[OF ac wf ety Some[unfolded p]] Var by simp
      with "1.IH"[OF _ tyu] reach_card_less[OF ac wf ety lk] Var obtain t' where t': "?P u Ts U t'" by auto
      have "norm_term1 (tenv env) t = Some (Ok t')"
        using t' Some p U' Var by (subst norm_term1.simps) (simp add: lookup1_def return_def)
      moreover have "fh env0 t'" if "flexb env0 env" "fh env0 t" for env0
      proof -
        from that(2) Var have "vt_lookup (tenv env0) x = None" by (auto simp: fh_def)
        with that(1) Some p have "fh env0 u" unfolding flexb_def by blast
        with t' that(1) show ?thesis by blast
      qed
      ultimately show ?thesis using t' \<open>inst t = inst u\<close> Var TU by auto
    qed
  next
    case (Abs a U b)
    from "1.prems" Abs obtain V where tyb: "has_type W (U # Ts) b V" and T: "T = U \<rightarrow>\<^sub>T V"
      by (auto elim: has_type_elims)
    have "\<exists>t'. ?P b (U # Ts) V t'" by (rule red[OF _ tyb]) (auto simp: Abs subt_def)
    then obtain b' where b': "?P b (U # Ts) V b'" by blast
    have "norm_term1 (tenv env) t = Some (Ok (Abs a U b'))"
      using b' Abs by (subst norm_term1.simps) (simp add: return_def)
    moreover have "inst t \<rightarrow>\<^sub>\<beta>\<^sup>* inst (Abs a U b')" using b' Abs by (simp add: rtrancl_beta_Abs)
    moreover have "fh env0 (Abs a U b')" if "flexb env0 env" "fh env0 t" for env0
      using b' that Abs by (simp add: fh_def)
    ultimately show ?thesis using b' T by (auto intro: has_type.Abs)
  next
    case (App f u)
    from "1.prems" App obtain U where tyf: "has_type W Ts f (U \<rightarrow>\<^sub>T T)" and tyu: "has_type W Ts u U"
      by (auto elim: has_type_elims)
    have pu: "proper u" by (rule has_type_proper[OF tyu])
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a U' body where f: "f = Abs a U' body" by (cases f) auto
      from tyf f have tyb: "has_type W (U # Ts) body T" by (auto elim: has_type_elims)
      have pb: "proper body" by (rule has_type_proper[OF tyb])
      have st: "inst t \<rightarrow>\<^sub>\<beta> inst (subst_bound u body)"
        using App f by (simp add: inst_subst_bound[OF ac wf ety pb pu])
      have "\<exists>t'. ?P (subst_bound u body) Ts T t'"
        by (rule red[OF _ has_type_subst_bound[OF tyb tyu]]) (use st in auto)
      then obtain t' where t': "?P (subst_bound u body) Ts T t'" by blast
      have "norm_term1 (tenv env) t = Some (Ok t')" using t' App f by (subst norm_term1.simps) simp
      moreover have "fh env0 t'" if "flexb env0 env" "fh env0 t" for env0
      proof -
        from that(2) App f have "fh env0 body" by (simp add: fh_def)
        then have "fh env0 (subst_bound u body)" by (auto simp: fh_def fhd_subst_bound)
        with t' that(1) show ?thesis by blast
      qed
      ultimately show ?thesis using t' st by (auto intro: converse_rtranclp_into_rtranclp)
    next
      case False
      have "\<exists>t'. ?P f Ts (U \<rightarrow>\<^sub>T T) t'" by (rule red[OF _ tyf]) (auto simp: App subt_def)
      then obtain nf where nf: "?P f Ts (U \<rightarrow>\<^sub>T T) nf" by blast
      have fhf: "fh env0 nf" if "flexb env0 env" "fh env0 t" for env0
        using nf that App by (simp add: fh_def)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a U' body where nfa: "nf = Abs a U' body" by (cases nf) auto
        from nf nfa have tyb: "has_type W (U # Ts) body T" by (auto elim: has_type_elims)
        have pb: "proper body" by (rule has_type_proper[OF tyb])
        have st: "beta\<^sup>+\<^sup>+ (inst t) (inst (subst_bound u body))"
        proof -
          have "inst t \<rightarrow>\<^sub>\<beta>\<^sup>* inst nf \<degree> inst u" using nf App by (simp add: rtrancl_beta_AppL)
          moreover have "inst nf \<degree> inst u \<rightarrow>\<^sub>\<beta> inst (subst_bound u body)"
            using nfa by (simp add: inst_subst_bound[OF ac wf ety pb pu])
          ultimately show ?thesis by (rule rtranclp_into_tranclp1)
        qed
        have "\<exists>t'. ?P (subst_bound u body) Ts T t'"
        proof (rule red[OF _ has_type_subst_bound[OF tyb tyu]])
          show "(sup beta subt)\<^sup>+\<^sup>+ (inst t) (inst (subst_bound u body))"
            using st by (induction rule: tranclp_induct) (auto intro: tranclp.trancl_into_trancl)
        qed
        then obtain t' where t': "?P (subst_bound u body) Ts T t'" by blast
        have "norm_term1 (tenv env) (f $ u) = Some (Ok t')"
          using t' nf nfa False by (subst norm_term1.simps) (cases f; simp)
        moreover have "fh env0 t'" if "flexb env0 env" "fh env0 t" for env0
        proof -
          from fhf[OF that] nfa have "fh env0 body" by (simp add: fh_def)
          then have "fh env0 (subst_bound u body)" by (auto simp: fh_def fhd_subst_bound)
          with t' that(1) show ?thesis by blast
        qed
        ultimately show ?thesis using t' tranclp_into_rtranclp[OF st] App by (auto intro: rtranclp_trans)
      next
        case nA: False
        have "\<exists>t'. ?P u Ts U t'" by (rule red[OF _ tyu]) (auto simp: App subt_def)
        then obtain nu where nu: "?P u Ts U nu" by blast
        have "norm_term1 (tenv env) (f $ u) = Some (Ok (nf $ nu))"
          using nf nu nA False by (subst norm_term1.simps) (cases f; cases nf; simp add: return_def)
        moreover have "has_type W Ts (nf $ nu) T" using nf nu by (auto intro: has_type.App)
        moreover have "inst t \<rightarrow>\<^sub>\<beta>\<^sup>* inst (nf $ nu)"
          using nf nu App by (simp add: rtrancl_beta_App)
        moreover have "fh env0 (nf $ nu)" if "flexb env0 env" "fh env0 t" for env0
          using fhf[OF that] by (simp add: fh_def)
        ultimately show ?thesis using nf nA App by auto
      qed
    qed
  qed (use "1.prems" in \<open>subst norm_term1.simps; auto simp: return_def\<close>)+
qed

text \<open>The same for \<^const>\<open>norm_term\<close>.\<close>

lemma norm_term_term:
  assumes "has_type W Ts t T"
  shows "\<exists>t'. norm_term env t = return t' \<and> has_type W Ts t' T \<and>
    inst t \<rightarrow>\<^sub>\<beta>\<^sup>* inst t' \<and> (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and>
    (is_Abs t' \<or> fhd t' = head_of t') \<and>
    (\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t \<longrightarrow> fh env0 t')"
proof (cases "env_is_empty env \<and> \<not> could_beta_contract t")
  case True
  then show ?thesis using assms fhd_no_beta[of t]
    by (auto simp: norm_term_def env_is_empty_def vt_is_empty_lookup)
next
  case False
  then show ?thesis using norm_term1_term[OF assms] wf_envD(1)[OF wf]
    by (simp add: norm_term_def return_def)
qed

end

subsection \<open>Rigid occurrences of bound variables persist\<close>

text \<open>
  The loose bound variables \<open>Z\<close> at depth \<open>d\<close>: the variables bound in between and the shifted \<open>Z\<close>.
\<close>

definition bshift :: "nat \<Rightarrow> nat set \<Rightarrow> nat set" where
  "bshift d Z = {i. i < d} \<union> (\<lambda>i. i + d) ` Z"

lemma bshift_Suc: "insert 0 (Suc ` bshift d Z) = bshift (Suc d) Z"
  by (auto simp: bshift_def image_iff less_Suc_eq_0_disj)

lemma bshift_0[simp]: "bshift 0 Z = Z"
  by (simp add: bshift_def)

lemma atom_apps_dep_onI:
  assumes "is_atom h" "loose_BVars h \<subseteq> Z" "\<forall>a\<in>set as. dep_on Z a"
  shows "dep_on Z (h \<degree>\<degree> as)"
proof -
  have "\<exists>rs. list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) as rs \<and> (\<forall>r\<in>set rs. loose_BVars r \<subseteq> Z)"
    using assms(3)
  proof (induction as)
    case (Cons a as)
    from Cons.prems have "\<forall>x\<in>set as. dep_on Z x" "dep_on Z a" by simp_all
    from Cons.IH[OF this(1)] obtain rs where rs: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) as rs" "\<forall>r\<in>set rs. loose_BVars r \<subseteq> Z"
      by blast
    from \<open>dep_on Z a\<close> obtain r where r: "a \<equiv>\<^sub>\<beta>\<^sub>\<eta> r" "loose_BVars r \<subseteq> Z" unfolding dep_on_def by blast
    have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (a # as) (r # rs)" using r(1) rs(1) by (simp only: list_all2_Cons)
    moreover have "\<forall>x\<in>set (r # rs). loose_BVars x \<subseteq> Z" using r(2) rs(2) by simp
    ultimately show ?case by blast
  qed simp
  then obtain rs where rs: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) as rs" "\<forall>r\<in>set rs. loose_BVars r \<subseteq> Z" by blast
  show ?thesis
  proof (rule dep_onI)
    show "h \<degree>\<degree> as \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> rs" by (rule equiv_list_app[OF equiv_refl rs(1)])
    show "loose_BVars (h \<degree>\<degree> rs) \<subseteq> Z" using assms(2) rs(2) by auto
  qed
qed

text \<open>
  A rigid occurrence of a banned bound variable (\<^const>\<open>rigid_bound\<close>) survives the instantiation
  by a rigid solution: an instance that only depends on \<open>Z\<close> has no such occurrence.
\<close>

lemma rigid_bound_dep:
  assumes \<sigma>: "closed_on UNIV \<sigma>" "rigid_subst \<sigma>"
  shows "rigid_bound lev banned t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> \<forall>j\<in>set banned. 0 \<le> j \<Longrightarrow>
    dep_on (bshift (nat_of_integer lev) Z) (mk_subst \<sigma> (tr t)) \<Longrightarrow> \<exists>j\<in>set banned. nat_of_integer j \<in> Z"
proof (induction lev banned t rule: rigid_bound.induct)
  case (1 lev banned t)
  obtain h args where sc: "strip_comb t = (h, args)" by (cases "strip_comb t")
  have t: "t = list_comb h args" by (rule strip_comb_list_comb[OF sc])
  have tr: "mk_subst \<sigma> (tr t) = mk_subst \<sigma> (tr h) \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma> (tr a)) args"
    by (simp add: t tr_list_comb comp_def)
  let ?Z = "bshift (nat_of_integer lev) Z"
  have rb: "rigid_bound lev banned t = (case h of
      Bound i \<Rightarrow> (i - lev) \<in> set banned \<or> (\<exists>a\<in>set args. rigid_bound lev banned a)
    | Var _ _ \<Rightarrow> False
    | Abs _ _ u \<Rightarrow> List.null args \<and> rigid_bound (lev + 1) banned u
    | _ \<Rightarrow> (\<exists>a\<in>set args. rigid_bound lev banned a))"
    by (subst rigid_bound.simps) (simp add: sc)
  have dargs: "dep_on ?Z (mk_subst \<sigma> (tr a))"
    if "is_atom (mk_subst \<sigma> (tr h))" "a \<in> set args" for a
    using atom_apps_dep_on(2)[OF that(1) "1.prems"(4)[unfolded tr]] that(2) by auto
  have nApp: "\<not> (\<exists>f u. h = f $ u)" using head_of_not_App[of t] fst_strip_comb[of t] sc by auto
  show ?case
  proof (cases h)
    case (Const c T)
    have at: "is_atom (mk_subst \<sigma> (tr h))" using rigid_substD[OF \<sigma>(2)] Const by simp
    from "1.prems"(1) rb Const obtain a where "a \<in> set args" "rigid_bound lev banned a" by auto
    from "1"(1)[OF sc[symmetric] refl Const this "1.prems"(2,3) dargs[OF at this(1)]] show ?thesis .
  next
    case (Free c T)
    have at: "is_atom (mk_subst \<sigma> (tr h))" using rigid_substD[OF \<sigma>(2)] Free by simp
    from "1.prems"(1) rb Free obtain a where "a \<in> set args" "rigid_bound lev banned a" by auto
    from "1"(2)[OF sc[symmetric] refl Free this "1.prems"(2,3) dargs[OF at this(1)]] show ?thesis .
  next
    case (Bound i)
    have at: "is_atom (mk_subst \<sigma> (tr h))" using Bound by simp
    from "1.prems"(1) rb Bound consider "i - lev \<in> set banned" | a where "a \<in> set args" "rigid_bound lev banned a"
      by auto
    then show ?thesis
    proof cases
      case 1
      have "loose_BVars (mk_subst \<sigma> (tr h)) \<subseteq> ?Z"
        by (rule atom_apps_dep_on(1)[OF at "1.prems"(4)[unfolded tr]])
      then have iZ: "nat_of_integer i \<in> ?Z" using Bound by simp
      have j0: "0 \<le> i - lev" using 1 "1.prems"(3) by auto
      then have "nat_of_integer (i - lev) = nat_of_integer i - nat_of_integer lev" "nat_of_integer lev \<le> nat_of_integer i"
        using "1.prems"(2) by (simp_all add: integer_reps nat_diff_distrib)
      with iZ have "nat_of_integer (i - lev) \<in> Z" by (auto simp: bshift_def)
      with 1 show ?thesis by blast
    next
      case 2
      from "1"(3)[OF sc[symmetric] refl Bound 2 "1.prems"(2,3) dargs[OF at 2(1)]] show ?thesis .
    qed
  next
    case (Abs x T u)
    from "1.prems"(1) rb Abs have nil: "args = []" and ru: "rigid_bound (lev + 1) banned u"
      by auto
    have "dep_on ?Z (dB.Abs (mk_subst \<sigma> (tr u)))" using "1.prems"(4) t nil Abs by simp
    from Abs_dep_on[OF this] have "dep_on (bshift (nat_of_integer (lev + 1)) Z) (mk_subst \<sigma> (tr u))"
      using "1.prems"(2) by (simp add: bshift_Suc integer_reps nat_add_distrib)
    from "1"(4)[OF sc[symmetric] refl Abs ru _ "1.prems"(3) this] "1.prems"(2) show ?thesis by simp
  qed (use "1.prems"(1) rb nApp in auto)
qed

text \<open>Dependencies reflect through lifting, for typed terms.\<close>

lemma lift_dep_reflect:
  assumes ty: "(E, \<tau>) \<turnstile> t : T" and dep: "dep_on (insert 0 (Suc ` Z)) (lift t 0)"
  shows "dep_on Z t"
proof -
  from normal_form_ex[OF ty] obtain nt where nt: "\<beta>\<eta>cl t nt" "normal nt" by blast
  have inj: "inj_on Suc (loose_BVars t)" by simp
  note rn = normal_form_rename[OF nt inj]
  from dep obtain r where r: "lift t 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> r" "loose_BVars r \<subseteq> insert 0 (Suc ` Z)"
    unfolding dep_on_def by blast
  have l: "lift t 0 = map_BVars Suc t" by (simp add: lift_map_BVars)
  have "r \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars Suc nt"
    using equiv_trans[OF equiv_sym[OF r(1)] \<beta>\<eta>cl_into_equiv[OF rn(1)[folded l]]] .
  then have "\<beta>\<eta>cl r (map_BVars Suc nt)" using rn(2) by (rule equiv_\<beta>\<eta>cl_normal)
  then have "loose_BVars (map_BVars Suc nt) \<subseteq> insert 0 (Suc ` Z)"
    using loose_BVars_\<beta>\<eta>cl r(2) by blast
  then have "loose_BVars nt \<subseteq> Z" by (auto simp: loose_BVars_map_BVars)
  then show ?thesis by (rule dep_onI[OF \<beta>\<eta>cl_into_equiv[OF nt(1)]])
qed

lemma dep_on_eta: "dep_on Z s \<Longrightarrow> dep_on (insert 0 (Suc ` Z)) (lift s 0 \<degree> BVar 0)"
proof -
  assume "dep_on Z s"
  moreover have "dB.Abs (lift s 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
    by (rule eta_into_equiv) (metis eta free_lift not_less_zero subst_lift)
  ultimately have "dep_on Z (dB.Abs (lift s 0 \<degree> BVar 0))" by (rule dep_on_equiv[rotated])
  then show ?thesis by (rule Abs_dep_on)
qed

lemma size_list_app_ge: "size h \<le> size (h \<degree>\<degree> A)"
  by (induction A arbitrary: h) (auto intro: le_trans[rotated])

lemma size_list_app_mem: "a \<in> set A \<Longrightarrow> size a < size (h \<degree>\<degree> A)"
proof (induction A arbitrary: h)
  case (Cons b A)
  show ?case
  proof (cases "a = b")
    case True
    then show ?thesis using size_list_app_ge[of "h \<degree> b" A] by simp
  next
    case False
    with Cons.prems have "a \<in> set A" by simp
    from Cons.IH[OF this, of "h \<degree> b"] show ?thesis by simp
  qed
qed simp

lemma lift_list_app: "lift (h \<degree>\<degree> A) k = lift h k \<degree>\<degree> map (\<lambda>t. lift t k) A"
  by (induction A arbitrary: h) simp_all

text \<open>
  An argument used by a \<open>\<beta>\<close>-normal body is preserved: if the body \<open>r\<close> has the loose bound variable
  \<open>k\<close> and all arguments have atomic heads, the application of \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>m. r\<close> to the arguments
  only depends on \<open>Z\<close> only if the argument for \<open>k\<close> does.
\<close>

lemma use_dep:
  "no_redex r \<Longrightarrow> loose_BVars r \<subseteq> {..<m} \<Longrightarrow> length ts = m \<Longrightarrow> k \<in> loose_BVars r \<Longrightarrow>
    dep_on Z (Abs_m m r \<degree>\<degree> ts) \<Longrightarrow> \<forall>i<m. \<exists>h A. is_atom h \<and> rev ts ! i = h \<degree>\<degree> A \<Longrightarrow>
    \<forall>i<m. \<exists>E T. (E, \<tau>) \<turnstile> rev ts ! i : T \<Longrightarrow> dep_on Z (rev ts ! k)"
proof (induction r arbitrary: m ts k Z rule: measure_induct_rule[of size])
  case (less r)
  note nr = less.prems(1) and lr = less.prems(2) and lts = less.prems(3) and kr = less.prems(4)
    and dep = less.prems(5) and at = less.prems(6) and ty = less.prems(7)
  have km: "k < m" using kr lr by auto
  have cl: "no_loose_bound (Abs_m m r) 0"
    using loose_BVars_no_loose_bound[OF lr] by (simp add: loose_bound_Abs_m)
  show ?case
  proof (cases "Unif_Occurs.is_Abs r")
    case True
    then obtain r' where r: "r = dB.Abs r'" by (cases r) auto
    let ?ts' = "map (\<lambda>t. lift t 0) ts @ [BVar 0]"
    have e1: "lift (Abs_m m r \<degree>\<degree> ts) 0 \<degree> BVar 0 = Abs_m m r \<degree>\<degree> ?ts'"
      using lift_closed[OF cl] by (simp add: lift_list_app)
    have e2: "Abs_m m r = Abs_m (Suc m) r'" using Abs_m_Suc'[of m r'] r by simp
    have "dep_on (insert 0 (Suc ` Z)) (Abs_m m r \<degree>\<degree> ?ts')"
      using dep_on_eta[OF dep] unfolding e1 .
    then have dep': "dep_on (insert 0 (Suc ` Z)) (Abs_m (Suc m) r' \<degree>\<degree> ?ts')" unfolding e2 .
    have rev': "rev ?ts' = BVar 0 # map (\<lambda>t. lift t 0) (rev ts)" by (simp add: rev_map)
    have "dep_on (insert 0 (Suc ` Z)) (rev ?ts' ! Suc k)"
    proof (rule less.IH[of r'])
      show "size r' < size r" by (simp add: r)
      show "no_redex r'" using nr by (simp add: r)
      show "loose_BVars r' \<subseteq> {..<Suc m}"
      proof
        fix i assume "i \<in> loose_BVars r'"
        with lr show "i \<in> {..<Suc m}" by (cases i) (auto simp: r)
      qed
      show "length ?ts' = Suc m" using lts by simp
      show "Suc k \<in> loose_BVars r'" using kr by (simp add: r)
      show "dep_on (insert 0 (Suc ` Z)) (Abs_m (Suc m) r' \<degree>\<degree> ?ts')" by (rule dep')
      show "\<forall>i<Suc m. \<exists>h A. is_atom h \<and> rev ?ts' ! i = h \<degree>\<degree> A"
      proof (intro allI impI)
        fix i assume i: "i < Suc m"
        show "\<exists>h A. is_atom h \<and> rev ?ts' ! i = h \<degree>\<degree> A"
        proof (cases i)
          case 0
          then show ?thesis using rev' by (intro exI[of _ "BVar 0"] exI[of _ "[]"]) simp
        next
          case (Suc i')
          with i at obtain h A where "is_atom h" "rev ts ! i' = h \<degree>\<degree> A" by auto
          moreover have "is_atom (lift h 0)" using \<open>is_atom h\<close> by (auto simp: is_atom_def)
          ultimately show ?thesis using Suc i lts rev'
            by (intro exI[of _ "lift h 0"] exI[of _ "map (\<lambda>t. lift t 0) A"]) (simp add: lift_list_app)
        qed
      qed
      show "\<forall>i<Suc m. \<exists>E T. (E, \<tau>) \<turnstile> rev ?ts' ! i : T"
      proof (intro allI impI)
        fix i assume i: "i < Suc m"
        show "\<exists>E T. (E, \<tau>) \<turnstile> rev ?ts' ! i : T"
        proof (cases i)
          case 0
          have "((\<lambda>_. Atom 0), \<tau>) \<turnstile> BVar 0 : Atom 0" by (rule typing.BVar) simp
          then show ?thesis using rev' 0 by auto
        next
          case (Suc i')
          with i ty obtain E T where "(E, \<tau>) \<turnstile> rev ts ! i' : T" by auto
          from lift_type[OF this, of 0 "Atom 0"] show ?thesis using Suc i lts rev' by auto
        qed
      qed
    qed
    then have "dep_on (insert 0 (Suc ` Z)) (lift (rev ts ! k) 0)" using rev' km lts by simp
    moreover from ty km obtain E T where "(E, \<tau>) \<turnstile> rev ts ! k : T" by auto
    ultimately show ?thesis using lift_dep_reflect by blast
  next
    case False
    from no_redex_atom_head[OF nr False] obtain h A where h: "is_atom h" "r = h \<degree>\<degree> A" by blast
    have nrA: "\<forall>a\<in>set A. no_redex a" using nr h no_redex_atom_apps by simp
    have lA: "\<forall>a\<in>set A. loose_BVars a \<subseteq> {..<m}" using lr h by auto
    have szA: "size a < size r" if "a \<in> set A" for a using size_list_app_mem[OF that] h by simp
    have IH: "dep_on Z (rev ts ! k)" if "a \<in> set A" "k \<in> loose_BVars a" "dep_on Z (Abs_m m a \<degree>\<degree> ts)" for a
      by (rule less.IH[OF szA[OF that(1)]]) (use that nrA lA lts at ty in auto)
    from h(1) consider j where "h = BVar j" | c where "h = dB.Var c" by (auto simp: is_atom_def)
    then show ?thesis
    proof cases
      case (1 j)
      have jm: "j < m" using lr h 1 by auto
      from at jm obtain g G where g: "is_atom g" "rev ts ! j = g \<degree>\<degree> G" by blast
      have e: "Abs_m m r \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> g \<degree>\<degree> (G @ map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A)"
        using Abs_m_apps_BVar_head[OF lts jm, of A] h 1 g(2) by simp
      have "dep_on Z (g \<degree>\<degree> (G @ map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A))"
        by (rule dep_on_equiv[OF equiv_sym[OF e] dep])
      note d = atom_apps_dep_on[OF g(1) this]
      show ?thesis
      proof (cases "k = j")
        case True
        have "dep_on Z (g \<degree>\<degree> G)" by (rule atom_apps_dep_onI[OF g(1) d(1)]) (use d(2) in auto)
        then show ?thesis using True g(2) by simp
      next
        case False
        with kr h 1 obtain a where "a \<in> set A" "k \<in> loose_BVars a" by auto
        with d(2) IH show ?thesis by auto
      qed
    next
      case (2 c)
      have e: "Abs_m m r \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var c \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A"
        using Abs_m_apps_closed_head[of "dB.Var c" ts m A] lts h 2 by simp
      have "dep_on Z (dB.Var c \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A)"
        by (rule dep_on_equiv[OF equiv_sym[OF e] dep])
      note d = atom_apps_dep_on[OF _ this]
      from kr h 2 obtain a where "a \<in> set A" "k \<in> loose_BVars a" by auto
      with d(2) IH show ?thesis by auto
    qed
  qed
qed

end
