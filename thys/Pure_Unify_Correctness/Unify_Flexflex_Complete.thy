section \<open>Completeness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex_Complete
  imports Unify_Match_Complete Pure_Pattern_Correctness.Match_Sound
begin

context csig
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

lemma fhd_list_comb[simp]: "fhd (list_comb h ts) = fhd h"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma head_of_list_comb_head[simp]: "head_of (list_comb h ts) = head_of h"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma fhd_types_abs[simp]: "fhd (types_abs Ts b) = fhd b"
  by (induction Ts) simp_all

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

abbreviation einst :: "pterm \<Rightarrow> dB" where
  "einst t \<equiv> mk_subst (env_inst env) (tr t)"

text \<open>
  \<^const>\<open>norm_term1\<close> terminates on well-typed terms, with a well-typed result that is a
  \<open>\<beta>\<close>-reduct of the instance; the head variable of the result is unbound.
\<close>

lemma norm_term1_term:
  "has_type W Ts t T \<Longrightarrow> \<exists>t'. norm_term1 (tenv env) t = Some (Ok t') \<and> has_type W Ts t' T \<and>
    einst t \<rightarrow>\<^sub>\<beta>\<^sup>* einst t' \<and> (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and>
    (is_Abs t' \<or> fhd t' = head_of t') \<and>
    (\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t \<longrightarrow> fh env0 t')"
proof (induction t arbitrary: Ts T rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (einst t, card (reach env (vps t)))"]])
  case (1 t)
  let ?P = "\<lambda>t Ts T t'. norm_term1 (tenv env) t = Some (Ok t') \<and> has_type W Ts t' T \<and>
    einst t \<rightarrow>\<^sub>\<beta>\<^sup>* einst t' \<and> (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and>
    (is_Abs t' \<or> fhd t' = head_of t') \<and> (\<forall>env0. flexb env0 env \<longrightarrow> fh env0 t \<longrightarrow> fh env0 t')"
  have red: "\<exists>t'. ?P u Us U t'"
    if "(sup beta subt)\<^sup>+\<^sup>+ (einst t) (einst u)" "has_type W Us u U" for u Us U
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
      have "einst t = einst u" using inst_bound[OF ac wf ety Some[unfolded p]] Var by simp
      with "1.IH"[OF _ tyu] reach_card_less[OF ac wf ety lk] Var obtain t' where t': "?P u Ts U t'" by auto
      have "norm_term1 (tenv env) t = Some (Ok t')"
        using t' Some p U' Var by (subst norm_term1.simps) (simp add: lookup1_def return_def)
      moreover have "fh env0 t'" if "flexb env0 env" "fh env0 t" for env0
      proof -
        from that(2) Var have "vt_lookup (tenv env0) x = None" by (auto simp: fh_def)
        with that(1) Some p have "fh env0 u" unfolding flexb_def by blast
        with t' that(1) show ?thesis by blast
      qed
      ultimately show ?thesis using t' \<open>einst t = einst u\<close> Var TU by auto
    qed
  next
    case (Abs a U b)
    from "1.prems" Abs obtain V where tyb: "has_type W (U # Ts) b V" and T: "T = U \<rightarrow>\<^sub>T V"
      by (auto elim: has_type_elims)
    have "\<exists>t'. ?P b (U # Ts) V t'" by (rule red[OF _ tyb]) (auto simp: Abs subt_def)
    then obtain b' where b': "?P b (U # Ts) V b'" by blast
    have "norm_term1 (tenv env) t = Some (Ok (Abs a U b'))"
      using b' Abs by (subst norm_term1.simps) (simp add: return_def)
    moreover have "einst t \<rightarrow>\<^sub>\<beta>\<^sup>* einst (Abs a U b')" using b' Abs by (simp add: rtrancl_beta_Abs)
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
      have st: "einst t \<rightarrow>\<^sub>\<beta> einst (subst_bound u body)"
        using App f by (simp add: Pattern_Size.csig.inst_subst_bound[OF ac wf ety pb pu])
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
        have st: "beta\<^sup>+\<^sup>+ (einst t) (einst (subst_bound u body))"
        proof -
          have "einst t \<rightarrow>\<^sub>\<beta>\<^sup>* einst nf \<degree> einst u" using nf App by (simp add: rtrancl_beta_AppL)
          moreover have "einst nf \<degree> einst u \<rightarrow>\<^sub>\<beta> einst (subst_bound u body)"
            using nfa by (simp add: Pattern_Size.csig.inst_subst_bound[OF ac wf ety pb pu])
          ultimately show ?thesis by (rule rtranclp_into_tranclp1)
        qed
        have "\<exists>t'. ?P (subst_bound u body) Ts T t'"
        proof (rule red[OF _ has_type_subst_bound[OF tyb tyu]])
          show "(sup beta subt)\<^sup>+\<^sup>+ (einst t) (einst (subst_bound u body))"
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
        moreover have "einst t \<rightarrow>\<^sub>\<beta>\<^sup>* einst (nf $ nu)"
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
    einst t \<rightarrow>\<^sub>\<beta>\<^sup>* einst t' \<and> (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None) \<and>
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

text \<open>
  Pruning: if a closed value applied to arguments with atomic heads only depends on \<open>Z\<close>, and the
  arguments not selected by \<open>ks\<close> do not, then the value is the abstraction of a closed term
  applied to the selected arguments.
\<close>

lemma prune_value:
  assumes closed: "no_loose_bound w0 0" and ty: "\<And>e. (e, \<tau>) \<turnstile> w0 : Ws \<Rrightarrow> U"
    and len: "length ts = length Ws" and dep: "dep_on Z (w0 \<degree>\<degree> ts)"
    and at: "\<exists>k<length Ws. k \<notin> set ks \<Longrightarrow> \<forall>i<length Ws. \<exists>h A. is_atom h \<and> rev ts ! i = h \<degree>\<degree> A"
    and tyts: "\<exists>k<length Ws. k \<notin> set ks \<Longrightarrow> \<forall>i<length Ws. \<exists>E T. (E, \<tau>) \<turnstile> rev ts ! i : T"
    and nodep: "\<And>k. k < length Ws \<Longrightarrow> k \<notin> set ks \<Longrightarrow> \<not> dep_on Z (rev ts ! k)"
    and ks: "\<forall>k\<in>set ks. k < length Ws"
  obtains w where "no_loose_bound w 0" "\<And>e. (e, \<tau>) \<turnstile> w : map (\<lambda>k. rev Ws ! k) ks \<Rrightarrow> U"
    "w0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length Ws) (w \<degree>\<degree> map BVar ks)"
proof -
  let ?m = "length Ws"
  obtain r where r: "\<beta>\<eta>cl (w0 \<degree>\<degree> map BVar (downs ?m)) r" "normal r" "(env_ext (\<lambda>_. Atom 0) Ws, \<tau>) \<turnstile> r : U"
    "loose_BVars r \<subseteq> {..<?m}"
    using typed_nf_args[OF closed ty refl] .
  have w0r: "w0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r"
  proof -
    have "w0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w0 \<degree>\<degree> map BVar (downs ?m))"
      using eta_expand_equiv[OF closed] by (rule equiv_sym)
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r" using r(1) by (intro equiv_Abs_m \<beta>\<eta>cl_into_equiv)
    finally show ?thesis .
  qed
  have "w0 \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r \<degree>\<degree> ts"
    by (rule equiv_list_app[OF w0r]) (simp add: list_all2_conv_all_nth equiv_refl)
  then have dep': "dep_on Z (Abs_m ?m r \<degree>\<degree> ts)" using dep by (rule dep_on_equiv[OF equiv_sym])
  have sub: "loose_BVars r \<subseteq> set ks"
  proof
    fix k assume k: "k \<in> loose_BVars r"
    then have km: "k < ?m" using r(4) by auto
    show "k \<in> set ks"
    proof (rule ccontr)
      assume nk: "k \<notin> set ks"
      with km have ex: "\<exists>k<?m. k \<notin> set ks" by blast
      have "dep_on Z (rev ts ! k)"
        by (rule use_dep[OF normal_no_redex[OF r(2)] r(4) len k dep']) (use at[OF ex] tyts[OF ex] len in auto)
      with nodep[OF km nk] show False by blast
    qed
  qed
  define w where "w = abst ks r"
  have "no_loose_bound w 0" unfolding w_def by (rule loose_BVars_abst[OF sub])
  moreover have "(e, \<tau>) \<turnstile> w : map (\<lambda>k. rev Ws ! k) ks \<Rrightarrow> U" for e
  proof -
    have "((\<lambda>_. Atom 0), \<tau>) \<turnstile> w : map (env_ext (\<lambda>_. Atom 0) Ws) ks \<Rrightarrow> U"
      unfolding w_def by (rule typing_abst[OF r(3) sub])
    moreover have "map (env_ext (\<lambda>_. Atom 0) Ws) ks = map (\<lambda>k. rev Ws ! k) ks"
      using ks by (auto simp: env_ext_nth rev_nth)
    ultimately show ?thesis using typing_closed[OF _ \<open>no_loose_bound w 0\<close>] by simp
  qed
  moreover have "w0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w \<degree>\<degree> map BVar ks)"
  proof -
    have "r = appb w ks" by (simp add: w_def appb_abst_self[OF sub])
    then have "Abs_m ?m r \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w \<degree>\<degree> map BVar ks)"
      by (auto intro: equiv_Abs_m equiv_sym[OF beta_into_equiv] appb_reduces)
    with w0r show ?thesis by (rule equiv_trans)
  qed
  ultimately show ?thesis by (rule that)
qed

subsection \<open>Deleting bound variables, completely\<close>

text \<open>The binder of a cleaned pair keeps the bound variables that occur in both terms.\<close>

lemma add_index_foldr:
  "foldr (add_index lt lu) xs ([], []) =
    (map fst (filter (\<lambda>(j, _). \<not> (j \<in> set lt \<and> j \<in> set lu)) xs),
     map snd (filter (\<lambda>(j, _). j \<in> set lt \<and> j \<in> set lu) xs))"
  by (induction xs) (auto simp: add_index_def split: prod.splits)

lemma filter_upt_nth_card:
  "i < n \<Longrightarrow> P i \<Longrightarrow> filter P [0..<n] ! card {j. j < i \<and> P j} = i"
proof (induction n)
  case (Suc n)
  have l: "length (filter P [0..<n]) = card {j. j < n \<and> P j}"
    by (simp add: length_filter_conv_card cong: conj_cong)
  show ?case
  proof (cases "i < n")
    case True
    have "card {j. j < i \<and> P j} < card {j. j < n \<and> P j}"
      by (rule psubset_card_mono) (use True Suc.prems(2) in auto)
    with Suc.IH[OF True Suc.prems(2)] l show ?thesis by (simp add: nth_append)
  next
    case False
    with Suc.prems have "i = n" by simp
    with Suc.prems l show ?thesis by (simp add: nth_append)
  qed
qed simp

lemma clean_binder_keeps:
  assumes "foldr (add_index lt lu) (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
  defines "K \<equiv> \<lambda>i. integer_of_nat i \<in> set lt \<and> integer_of_nat i \<in> set lu"
  shows "bset banned = {i. i < length rb \<and> \<not> K i}"
    "\<And>i. i < length rb \<Longrightarrow> K i \<Longrightarrow> squash (bset banned) i < length rb' \<and> rb' ! squash (bset banned) i = rb ! i"
proof -
  have z: "zip (upto_list (length rb)) rb = map (\<lambda>i. (integer_of_nat i, rb ! i)) [0..<length rb]"
    by (rule nth_equalityI) (simp_all add: upto_list_def)
  from assms(1) have b: "banned = map integer_of_nat (filter (\<lambda>i. \<not> K i) [0..<length rb])"
    and r: "rb' = map (\<lambda>i. rb ! i) (filter K [0..<length rb])"
    unfolding add_index_foldr z by (auto simp: filter_map comp_def K_def)
  show bs: "bset banned = {i. i < length rb \<and> \<not> K i}"
    by (auto simp: b bset_def image_iff)
  fix i assume i: "i < length rb" "K i"
  have "{..<i} - bset banned = {j. j < i \<and> K j}" using i(1) by (auto simp: bs)
  then have sq: "squash (bset banned) i = card {j. j < i \<and> K j}" by (simp add: squash_def)
  have "card {j. j < i \<and> K j} < card {j. j < length rb \<and> K j}"
    by (rule psubset_card_mono) (use i in auto)
  moreover have "length rb' = card {j. j < length rb \<and> K j}"
    by (simp add: r length_filter_conv_card cong: conj_cong)
  ultimately show "squash (bset banned) i < length rb' \<and> rb' ! squash (bset banned) i = rb ! i"
    using filter_upt_nth_card[of i "length rb" K, OF i] sq by (simp add: r)
qed

lemma change_bnos_cases:
  "(\<exists>evs. change_bnos banned lev x = Some (evs, UErr CHANGE_FAIL)) \<or> (\<exists>x'. okW (change_bnos banned lev x) x')"
  by (induction banned lev x rule: change_bnos.induct) (auto simp: bindW_def raiseW_def returnW_def)

text \<open>\<^const>\<open>change_bnos\<close> keeps the typing in the binder without the banned variables.\<close>

lemma shift_at_Suc_app: "shift_at (Suc k) f (Suc i) = Suc (shift_at k f i)"
  by (simp add: shift_at_def)

lemma change_bnos_typed:
  assumes "okW (change_bnos banned lev x) x'" "0 \<le> lev" "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j"
  shows "has_type V Ts x T \<Longrightarrow>
    (\<forall>i<length Ts. (i < nat_of_integer lev \<or> i - nat_of_integer lev \<notin> bset banned) \<longrightarrow>
      shift_at (nat_of_integer lev) (squash (bset banned)) i < length Ts' \<and>
      Ts' ! shift_at (nat_of_integer lev) (squash (bset banned)) i = Ts ! i) \<Longrightarrow>
    has_type V Ts' x' T"
  using assms
proof (induction banned lev x arbitrary: x' Ts Ts' T rule: change_bnos.induct)
  case (1 banned lev i)
  from "1.prems"(1) have i: "0 \<le> i" "nat_of_integer i < length Ts" "T = Ts ! nat_of_integer i"
    by (auto simp: has_type_Bound_iff)
  have pb: "proper (Bound i)" using i(1) by simp
  note cs = change_bnos_sound[OF "1.prems"(3) pb "1.prems"(4,5,6)]
  from "1.prems"(3) obtain i' where x': "x' = Bound i'" by (auto split: if_splits)
  from cs have tr: "BVar (nat_of_integer i') = BVar (shift_at (nat_of_integer lev) (squash (bset banned)) (nat_of_integer i))"
    and nb: "nat_of_integer lev \<le> nat_of_integer i \<longrightarrow> nat_of_integer i - nat_of_integer lev \<notin> bset banned"
    and pr: "proper (Bound i')"
    using x' by auto
  have "0 \<le> i'" using pr by simp
  with tr "1.prems"(2) i nb show ?case by (auto simp: x' has_type_Bound_iff not_le)
next
  case (2 banned lev a U t)
  from "2.prems"(3) obtain t' where t': "okW (change_bnos banned (lev + 1) t) t'" and x': "x' = Abs a U t'" by auto
  from "2.prems"(1) obtain T' where tyt: "has_type V (U # Ts) t T'" and T: "T = U \<rightarrow>\<^sub>T T'"
    by (auto elim: has_type_elims)
  have l: "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)" using "2.prems"(4) by (simp add: integer_reps)
  have "has_type V (U # Ts') t' T'"
  proof (rule "2.IH"[OF tyt _ t' _ "2.prems"(5,6)])
    show "\<forall>i<length (U # Ts). (i < nat_of_integer (lev + 1) \<or> i - nat_of_integer (lev + 1) \<notin> bset banned) \<longrightarrow>
        shift_at (nat_of_integer (lev + 1)) (squash (bset banned)) i < length (U # Ts') \<and>
        (U # Ts') ! shift_at (nat_of_integer (lev + 1)) (squash (bset banned)) i = (U # Ts) ! i"
    proof (intro allI impI)
      fix i assume "i < length (U # Ts)" "i < nat_of_integer (lev + 1) \<or> i - nat_of_integer (lev + 1) \<notin> bset banned"
      then show "shift_at (nat_of_integer (lev + 1)) (squash (bset banned)) i < length (U # Ts') \<and>
        (U # Ts') ! shift_at (nat_of_integer (lev + 1)) (squash (bset banned)) i = (U # Ts) ! i"
        using "2.prems"(2) l by (cases i) (auto simp: shift_at_Suc_app shift_at_def)
    qed
    show "0 \<le> lev + 1" using "2.prems"(4) by simp
  qed
  then show ?case by (simp add: x' T has_type.Abs)
next
  case (3 banned lev t u)
  from "3.prems"(3) obtain t' u' where t': "okW (change_bnos banned lev t) t'"
    and u': "okW (change_bnos banned lev u) u'" and x': "x' = t' $ u'" by auto
  from "3.prems"(1) obtain U where tyt: "has_type V Ts t (U \<rightarrow>\<^sub>T T)" and tyu: "has_type V Ts u U"
    by (auto elim: has_type_elims)
  from "3.IH"(1)[OF tyt "3.prems"(2) t' "3.prems"(4-6)] "3.IH"(2)[OF t' tyu "3.prems"(2) u' "3.prems"(4-6)]
  show ?case by (simp add: x' has_type.App)
qed (auto elim: has_type_elims intro: has_type.intros)

lemma flexargs_exists:
  "length js = length ts \<Longrightarrow> length ts = length Ts \<Longrightarrow>
    okW (flexargs js ts Ts) (map (\<lambda>k. Flarg (js ! k) (ts ! k) (Ts ! k)) [0..<length ts])"
proof (induction js ts Ts rule: list_induct3)
  case (Cons j js t ts T Ts)
  have "map (\<lambda>k. Flarg ((j # js) ! k) ((t # ts) ! k) ((T # Ts) ! k)) [0..<length (t # ts)] =
      Flarg j t T # map (\<lambda>k. Flarg (js ! k) (ts ! k) (Ts ! k)) [0..<length ts]"
    by (simp add: map_upt_Suc del: upt_Suc)
  with Cons show ?case by simp
qed simp

lemma change_arg_Flarg:
  "change_arg del banned (Flarg j t T) args =
    (if del \<and> rigid_bound 0 banned t then returnW args
     else do {t' \<leftarrow> change_bnos banned 0 t; returnW (Flarg j t' T # args)})"
  by (simp add: change_arg_def)

lemma foldrW_change_arg_cases:
  "(\<exists>evs. foldrW (change_arg del banned) fas acc = Some (evs, UErr CHANGE_FAIL)) \<or>
    (\<exists>ks. okW (foldrW (change_arg del banned) fas acc) (ks @ acc) \<and>
      list_all2 (\<lambda>a' a. fl_j a' = fl_j a \<and> fl_T a' = fl_T a \<and> okW (change_bnos banned 0 (fl_t a)) (fl_t a'))
        ks (filter (\<lambda>a. \<not> (del \<and> rigid_bound 0 banned (fl_t a))) fas))"
proof (induction fas)
  case Nil
  then show ?case by simp
next
  case (Cons a fas)
  obtain j t T where a: "a = Flarg j t T" by (cases a)
  let ?R = "\<lambda>a' a. fl_j a' = fl_j a \<and> fl_T a' = fl_T a \<and> okW (change_bnos banned 0 (fl_t a)) (fl_t a')"
  consider (err) evs where "foldrW (change_arg del banned) fas acc = Some (evs, UErr CHANGE_FAIL)"
    | (ok) ks evs0 where "foldrW (change_arg del banned) fas acc = Some (evs0, UOk (ks @ acc))"
      "list_all2 ?R ks (filter (\<lambda>a. \<not> (del \<and> rigid_bound 0 banned (fl_t a))) fas)"
    using Cons.IH by blast
  then show ?case
  proof cases
    case err
    then show ?thesis by (simp add: bindW_def)
  next
    case (ok ks evs0)
    show ?thesis
    proof (cases "del \<and> rigid_bound 0 banned t")
      case True
      have "okW (foldrW (change_arg del banned) (a # fas) acc) (ks @ acc)"
        using ok(1) True by (simp add: a change_arg_Flarg bindW_def returnW_def)
      with ok(2) True a show ?thesis by auto
    next
      case False
      consider (e) evs where "change_bnos banned 0 t = Some (evs, UErr CHANGE_FAIL)"
        | (o) t' evs1 where "change_bnos banned 0 t = Some (evs1, UOk t')"
        using change_bnos_cases[of banned 0 t] by blast
      then show ?thesis
      proof cases
        case (e evs)
        then show ?thesis using ok(1) False by (simp add: a change_arg_Flarg bindW_def)
      next
        case (o t' evs1)
        have "okW (foldrW (change_arg del banned) (a # fas) acc) ((Flarg j t' T # ks) @ acc)"
          using ok(1) False o by (simp add: a change_arg_Flarg bindW_def returnW_def)
        moreover have "okW (change_bnos banned 0 t) t'" using o by blast
        ultimately show ?thesis using ok(2) False a by (intro disjI2 exI[of _ "Flarg j t' T # ks"]) auto
      qed
    qed
  qed
qed

lemma squash_unsquash:
  assumes "B \<subseteq> {..<n}" "x < n - card B"
  shows "unsquash B x \<notin> B" "squash B (unsquash B x) = x"
proof -
  have fin: "finite B" using assms(1) finite_subset by blast
  have "squash B ` ({..<n} - B) \<subseteq> {..<n - card B}" using squash_bound[OF assms(1)] by auto
  moreover have "card (squash B ` ({..<n} - B)) = n - card B"
    using card_image[OF inj_on_subset[OF inj_on_squash, of "{..<n} - B" B]] assms(1)
    by (auto simp: card_Diff_subset fin)
  ultimately have "squash B ` ({..<n} - B) = {..<n - card B}" by (intro card_subset_eq) auto
  with assms(2) obtain y where y: "y \<notin> B" "x = squash B y" by auto
  then show "unsquash B x \<notin> B" "squash B (unsquash B x) = x" by (simp_all add: unsquash_squash)
qed

lemma map_BVars_squash_unsquash:
  assumes "B \<subseteq> {..<n}" "loose_BVars t \<subseteq> {..<n - card B}"
  shows "map_BVars (squash B) (map_BVars (unsquash B) t) = t"
proof -
  have "map_BVars (squash B) (map_BVars (unsquash B) t) = map_BVars (squash B \<circ> unsquash B) t"
    by (simp add: map_BVars_comp)
  also have "\<dots> = map_BVars id t"
    by (rule map_BVars_cong) (use assms squash_unsquash in auto)
  finally show ?thesis by (simp add: map_BVars_id)
qed

subsection \<open>Cleaning a flexible term\<close>

lemma flexargs_return:
  "length js = length ts \<Longrightarrow> length ts = length Ts \<Longrightarrow>
    flexargs js ts Ts = returnW (map (\<lambda>k. Flarg (js ! k) (ts ! k) (Ts ! k)) [0..<length ts])"
proof (induction js ts Ts rule: list_induct3)
  case (Cons j js t ts T Ts)
  then show ?case by (simp add: map_upt_Suc returnW_def bindW_def del: upt_Suc)
qed simp

lemma change_bnos_vars: "okW (change_bnos banned lev x) x' \<Longrightarrow> vars x' = vars x"
  by (induction banned lev x arbitrary: x' rule: change_bnos.induct) (auto split: if_splits)

lemma norm_term1_below:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> fresh_env env \<Longrightarrow> below (maxidx env) t \<Longrightarrow>
    below (maxidx env) t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  have te: "te = tenv env" and fr: "fresh_env env" and bt: "below (maxidx env) t" and t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup1 te xi T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t)
    | pterm.Abs a T body \<Rightarrow> nt te body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
        | _ \<Rightarrow> nt te f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  have bsub: "below (maxidx env) (subst_bound u b)" if "below (maxidx env) u" "below (maxidx env) b" for u b
    using vars_subst_bound[of u b] that by (auto simp: below_def)
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup1 te xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'" by auto
    from ok_lookup1[OF lk] consider "r' = None" | u where "r' = Some u" "vt_lookup te xi = Some (T, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest bt show ?thesis by auto
    next
      case 2
      with rest have "nt te u = Some (Ok t')" by simp
      moreover have "below (maxidx env) u" using fresh_envD[OF fr] 2 te by blast
      ultimately show ?thesis using "1.IH" te fr by blast
    qed
  next
    case (Abs a T body)
    with t' obtain b' where "nt te body = Some (Ok b')" "t' = pterm.Abs a T b'" by auto
    with "1.IH"[OF this(1) refl te fr] bt Abs show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      with t' App have "nt te (subst_bound u body) = Some (Ok t')" by simp
      from "1.IH"[OF this refl te fr bsub] bt App f show ?thesis by simp
    next
      case False
      with t' App obtain nf where nf: "nt te f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      have bnf0: "below (maxidx env) nf" using "1.IH"[OF nf refl te fr] bt App by simp
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have "nt te (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl te fr bsub] bt bnf0 App nfa show ?thesis by simp
      next
        case False
        with rest obtain nu where nu: "nt te u = Some (Ok nu)" and t'': "t' = nf $ nu"
          by (cases nf) auto
        from "1.IH"[OF nu refl te fr] bt bnf0 App t'' show ?thesis by simp
      qed
    qed
  qed (use t' bt in auto)
qed

lemma norm_term_below:
  "norm_term env t = return t' \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> fresh_env env \<Longrightarrow>
    below (maxidx env) t \<Longrightarrow> below (maxidx env) t'"
  by (cases "env_is_empty env \<and> \<not> could_beta_contract t")
    (auto simp: norm_term_def return_def intro: norm_term1_below)

lemma norm_term1_head:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> head_of t = Var x U \<Longrightarrow> vt_lookup te x = None \<Longrightarrow> head_of t' = Var x U"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  have ht: "head_of t = Var x U" and xn: "vt_lookup te x = None" and t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup1 te xi T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t)
    | pterm.Abs a T body \<Rightarrow> nt te body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
        | _ \<Rightarrow> nt te f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  show ?case
  proof (cases t)
    case (Var xi T)
    with ht have "xi = x" "T = U" by simp_all
    with t' xn Var show ?thesis by (auto simp: lookup1_def return_def)
  next
    case (App f u)
    from ht App have hf: "head_of f = Var x U" by simp
    then have nA: "\<not> is_Abs f" by (cases f) auto
    with t' App obtain nf where nf: "nt te f = Some (Ok nf)"
      and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
        | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
      by (cases f) auto
    from "1.IH"[OF nf refl hf xn] have hnf: "head_of nf = Var x U" .
    then have "\<not> is_Abs nf" by (cases nf) auto
    with rest obtain nu where "t' = nf $ nu" by (cases nf) auto
    with hnf show ?thesis by simp
  qed (use ht in auto)
qed

lemma norm_term_head:
  "norm_term env t = return t' \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> head_of t = Var x U \<Longrightarrow>
    vt_lookup (tenv env) x = None \<Longrightarrow> head_of t' = Var x U"
  by (cases "env_is_empty env \<and> \<not> could_beta_contract t")
    (auto simp: norm_term_def return_def intro: norm_term1_head)


lemma solution_tr_typed:
  "solution V \<tau>' \<sigma> env \<Longrightarrow> has_type V Ts a A \<Longrightarrow> (bnd_env Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr a) : trty A"
  by (rule typing_mk_subst[OF has_type_tr typed_on_mono[OF solutionD(2) FV_tr_range]])

lemma rigid_headed_atom:
  assumes "rigid_headed a" "rigid_subst \<sigma>"
  shows "\<exists>h A. is_atom h \<and> mk_subst \<sigma> (tr a) = h \<degree>\<degree> A"
proof -
  have a: "a = list_comb (head_of a) (snd (strip_comb a))" by (rule head_of_list_comb)
  have "is_atom (mk_subst \<sigma> (tr (head_of a)))"
    using assms rigid_substD[OF assms(2)] by (auto simp: rigid_headed_def split: pterm.splits)
  moreover have "mk_subst \<sigma> (tr a) = mk_subst \<sigma> (tr (head_of a)) \<degree>\<degree> map (\<lambda>x. mk_subst \<sigma> (tr x)) (snd (strip_comb a))"
    by (subst a) (simp add: tr_list_comb comp_def)
  ultimately show ?thesis by blast
qed

text \<open>
  \<^const>\<open>clean_term\<close> on a flexible term whose instance only depends on the non-banned bound
  variables: it gives up with \<open>CHANGE_FAIL\<close>, or it binds the head variable to an abstraction of a
  new variable applied to the kept arguments, for an extension of the solution.
\<close>

lemma clean_term_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env dps"
    and tyt: "has_type V (map snd rb) t B" and nfB: "\<not> is_funT B" and wt: "wf_tm ar rb t"
    and bt: "below (maxidx env) t" and ht: "head_of t = Var v T" and vn: "vt_lookup (tenv env) v = None"
    and bn: "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j" "bset banned \<subseteq> {..<length rb}"
    and rb': "length rb' = length rb - card (bset banned)"
      "\<And>i. i < length rb \<Longrightarrow> i \<notin> bset banned \<Longrightarrow>
        squash (bset banned) i < length rb' \<and> rb' ! squash (bset banned) i = rb ! i"
    and dep: "dep_on Z (mk_subst \<sigma> (tr t))" and Zb: "Z \<inter> bset banned = {}"
  shows "(\<exists>evs. clean_term banned env t = Some (evs, UErr CHANGE_FAIL)) \<or>
    (\<exists>env' t' V' \<sigma>'. okW (clean_term banned env t) (env', t') \<and> cinv ar V' \<tau>' \<sigma>' env' dps \<and>
      agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) V V' \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
      has_type V' (map snd rb') t' B \<and> below (maxidx env') t' \<and>
      (\<forall>x U. head_of t' = Var x U \<longrightarrow> vt_lookup (tenv env') x = None) \<and>
      (\<forall>x. vt_lookup (tenv env') x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v) \<and>
      (\<forall>x U. head_of t' = Var x U \<longrightarrow> x = v \<or> maxidx env < snd x) \<and>
      (\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
        flexb env0 env' \<and> fh env0 t'))"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note sol = cinvD(2)[OF inv]
  note \<sigma> = solutionD[OF sol]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  define ts where "ts = snd (strip_comb t)"
  let ?n = "length ts"
  have sc: "strip_comb t = (Var v T, ts)" using fst_strip_comb[of t] ht by (simp add: ts_def prod_eq_iff)
  have t_eq: "t = list_comb (Var v T) ts" using head_of_list_comb[of t] ht by (simp add: ts_def)
  have tyh: "has_type V (map snd rb) (Var v T) T" and Vv: "V v = T"
    using has_type_head_of[OF tyt] ht by (auto elim: has_type_elims intro: has_type.Var)
  from res_type_head(2)[OF tyt nfB tyh[folded ht]] obtain Ts where T: "T = foldr fun_type Ts B"
    and tyts: "list_all2 (has_type V (map snd rb)) ts Ts" by (auto simp: ts_def)
  have lTs: "length Ts = ?n" using list_all2_lengthD[OF tyts] by simp
  have aT: "arg_types T = Ts" "res_type T = B" using arg_res_type_fun[OF nfB, of Ts] T by simp_all
  have st: "strip_type env T = return (Ts, B)" using strip_type_arg_res[OF e] aT by simp
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
      else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) B);
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
    have rel0: "\<forall>i<length (map snd rb). (i < nat_of_integer 0 \<or> i - nat_of_integer 0 \<notin> bset banned) \<longrightarrow>
        shift_at (nat_of_integer 0) (squash (bset banned)) i < length (map snd rb') \<and>
        map snd rb' ! shift_at (nat_of_integer 0) (squash (bset banned)) i = map snd rb ! i"
      using rb'(2) by (auto simp: shift_at_def)
    have tsk: "has_type V (map snd rb) (ts ! k) (Ts ! k)" "below (maxidx env) (ts ! k)" if "k < ?n" for k
      using tyts that bt t_eq by (auto simp: list_all2_conv_all_nth below_list_comb)
    have tya: "has_type V (map snd rb') (fl_t a) (fl_T a) \<and> below (maxidx env) (fl_t a)" if "a \<in> set args" for a
    proof -
      from Pa[OF that] obtain k where k: "k < ?n" "fl_T a = Ts ! k" "okW (change_bnos banned 0 (ts ! k)) (fl_t a)"
        by blast
      have "has_type V (map snd rb') (fl_t a) (Ts ! k)"
        by (rule change_bnos_typed[OF k(3) _ bn(1,2) tsk(1)[OF k(1)] rel0]) simp
      moreover have "below (maxidx env) (fl_t a)"
        using tsk(2)[OF k(1)] change_bnos_vars[OF k(3)] by (simp add: below_def)
      ultimately show ?thesis using k(2) by simp
    qed
    have vm: "snd v \<le> maxidx env" using bt t_eq by (simp add: below_list_comb)
    have vn0: "vt_lookup (tenv env0) v = None" if "extends env env0" for env0
      by (rule extends_unbound[OF that vn])
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
      have "has_type V (map snd rb') (ts' ! i) (Ts ! i)" if "i < ?n" for i
        using tya[OF nth_mem[of i args]] argp[OF that] that la by (simp add: ts'_def)
      then have tyts': "list_all2 (has_type V (map snd rb')) ts' Ts"
        unfolding list_all2_conv_all_nth using la lTs by (simp add: ts'_def)
      have ok': "okW (clean_term banned env t) (env, list_comb (Var v T) ts')"
        using ok(1) True by (simp add: ct bindW_def Let_def returnW_def args_def ts'_def)
      have "has_type V (map snd rb') (list_comb (Var v T) ts') B"
        using tyts' Vv T by (auto simp: has_type_list_comb intro: has_type.Var)
      moreover have "below (maxidx env) (list_comb (Var v T) ts')"
        using tya vm by (auto simp: below_list_comb ts'_def)
      moreover have "fh env0 (list_comb (Var v T) ts')" if "extends env env0" for env0
        using vn0[OF that] by (simp add: fh_def)
      ultimately show ?thesis using ok' inv vn
        by (intro disjI2 exI[of _ env] exI[of _ "list_comb (Var v T) ts'"] exI[of _ V] exI[of _ \<sigma>])
          (auto simp: extends_refl)
    next
      case False
      note ei' = ei
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
      define sts where "sts = map (\<lambda>a. mk_subst \<sigma> (tr a)) ts"
      have rsts: "rev sts ! k = mk_subst \<sigma> (tr (ts ! (?n - 1 - k)))" if "k < ?n" for k
        using that by (simp add: sts_def rev_nth)
      have tyv: "(e, \<tau>') \<turnstile> \<sigma> (code (AVar v)) : map trty Ts \<Rrightarrow> trty B" for e
        using typed_onD[OF \<sigma>(2), of "code (AVar v)" e] Vv T by (simp add: trty_foldr)
      have dep': "dep_on Z (\<sigma> (code (AVar v)) \<degree>\<degree> sts)"
        using dep by (simp add: t_eq tr_list_comb sts_def comp_def)
      obtain w where w: "no_loose_bound w 0" "\<And>e. (e, \<tau>') \<turnstile> w : map (\<lambda>k. rev (map trty Ts) ! k) ks \<Rrightarrow> trty B"
        "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (map trty Ts)) (w \<degree>\<degree> map BVar ks)"
      proof (rule prune_value[of "\<sigma> (code (AVar v))" \<tau>' "map trty Ts" "trty B" sts Z ks])
        show "no_loose_bound (\<sigma> (code (AVar v))) 0" using closed_onD[OF \<sigma>(1)] by simp
        show "(e, \<tau>') \<turnstile> \<sigma> (code (AVar v)) : map trty Ts \<Rrightarrow> trty B" for e by (rule tyv)
        show "dep_on Z (\<sigma> (code (AVar v)) \<degree>\<degree> sts)" by (rule dep')
        show "\<forall>k\<in>set ks. k < length (map trty Ts)" using ksb lTs by simp
        show "length sts = length (map trty Ts)" using lTs by (simp add: sts_def)
        show "\<forall>i<length (map trty Ts). \<exists>h A. is_atom h \<and> rev sts ! i = h \<degree>\<degree> A"
          if "\<exists>k<length (map trty Ts). k \<notin> set ks"
        proof -
          from that lTs obtain k where "k < ?n" "k \<notin> set ks" by auto
          from nodel[OF this] have del: ?del by blast
          show ?thesis
          proof (intro allI impI)
            fix i assume "i < length (map trty Ts)"
            then have i: "i < ?n" using lTs by simp
            have "rigid_headed (ts ! (?n - 1 - i))" using del i by (simp add: list_all_length)
            from rigid_headed_atom[OF this \<sigma>(3)] show "\<exists>h A. is_atom h \<and> rev sts ! i = h \<degree>\<degree> A"
              using rsts[OF i] by simp
          qed
        qed
        show "\<forall>i<length (map trty Ts). \<exists>E T. (E, \<tau>') \<turnstile> rev sts ! i : T"
          if "\<exists>k<length (map trty Ts). k \<notin> set ks"
          using solution_tr_typed[OF sol tsk(1)] rsts lTs by (metis diff_less length_map less_imp_diff_less zero_less_one less_nat_zero_code not_gr_zero)
        show "\<not> dep_on Z (rev sts ! k)" if "k < length (map trty Ts)" "k \<notin> set ks" for k
        proof
          assume d: "dep_on Z (rev sts ! k)"
          from that lTs have k: "k < ?n" by simp
          from nodel[OF k that(2)] have "rigid_bound 0 banned (ts ! (?n - 1 - k))" by blast
          from rigid_bound_dep[OF \<sigma>(1,3) this _ bn(2)] d rsts[OF k]
          obtain j where "j \<in> set banned" "nat_of_integer j \<in> Z" by auto
          with Zb show False by (auto simp: bset_def)
        qed
      qed (rule that)
      define T' where "T' = foldr fun_type (map fl_T args) B"
      have "rev (map trty Ts) ! nat_of_integer (fl_j a) = trty (fl_T a)" if "a \<in> set args" for a
        using rk[OF that] lTs by (simp add: rev_map)
      then have mty: "map (\<lambda>k. rev (map trty Ts) ! k) ks = map trty (map fl_T args)"
        unfolding ks_def map_map by (intro map_cong) auto
      have wT': "(e, \<tau>') \<turnstile> w : trty T'" for e using w(2)[of e] mty by (simp add: T'_def trty_foldr)
      obtain env1 G where g: "genvar (fst v) env T' = (env1, G)" by (cases "genvar (fst v) env T'")
      define x' where "x' = (fst v, maxidx env + 1)"
      define \<sigma>1 where "\<sigma>1 = \<sigma>(code (AVar x') := w)"
      define V1 where "V1 = V(x' := T')"
      note ge = genvar_extend[OF inv g w(1) wT', folded x'_def, folded \<sigma>1_def V1_def]
      note gs = genvar_simps[OF g]
      note ei1 = env_invD[OF cinvD(1)[OF ge(1)]]
      note sol1 = cinvD(2)[OF ge(1)]
      have e1: "vt_is_empty (tyenv env1)" by (rule wf_envD(1)[OF ei1(2)])
      have x'n: "vt_lookup (tenv env1) x' = None"
      proof (rule ccontr)
        assume "vt_lookup (tenv env1) x' \<noteq> None"
        then obtain U u where "vt_lookup (tenv env) x' = Some (U, u)" using gs(1) by auto
        from fresh_envD[OF ei(4) this] show False by (simp add: x'_def)
      qed
      have vx': "v \<noteq> x'" using vm by (cases v) (auto simp: x'_def less_eq_integer.rep_eq plus_integer.rep_eq)
      define body where "body = list_comb G (map (Bound \<circ> fl_j) args)"
      have tybody: "has_type V1 (rev Ts) body B"
      proof -
        have "has_type V1 (rev Ts) G T'" using ge(5,8) by (simp add: has_type.Var)
        moreover have "list_all2 (has_type V1 (rev Ts)) (map (Bound \<circ> fl_j) args) (map fl_T args)"
          using rk lTs by (auto simp: list_all2_conv_all_nth has_type_Bound_iff)
        ultimately show ?thesis unfolding body_def T'_def has_type_list_comb by blast
      qed
      have tyabs: "has_type V1 [] (types_abs Ts body) T"
        using has_type_types_abs[of V1 Ts "[]" body B] tybody T by simp
      have vu_eq: "vupdate (v, T) (types_abs Ts body) env1 = update (v, T) (types_abs Ts body) env1"
        using nTs by (subst vupdate.simps) (cases Ts; simp)
      have vn1: "vt_lookup (tenv env1) v = None" using vn gs(1) by simp
      from update_unbound_ok[OF vn1, of T "types_abs Ts body"] obtain env2 where
        upd: "update (v, T) (types_abs Ts body) env1 = Some (Ok env2)" by blast
      have upd': "ok (update (v, T) (types_abs Ts body) env1) env2" using upd by simp
      have gT: "ground ar T" using wt t_eq wf_tm_list_comb[of ar rb "Var v T" ts] by (simp add: wf_tm_def)
      have gfold: "ground ar (foldr fun_type Us C) \<longleftrightarrow> (\<forall>A\<in>set Us. ground ar A) \<and> ground ar C" for Us C
        by (induction Us) auto
      have gTs: "\<forall>A\<in>set Ts. ground ar A" and gB: "ground ar B" using gT gfold[of Ts B] T by simp_all
      have "ground ar (fl_T a)" if "a \<in> set args" for a
      proof -
        from Pa[OF that] obtain k where "k < ?n" "fl_T a = Ts ! k" by blast
        with gTs lTs show ?thesis by simp
      qed
      then have gT': "ground ar T'" using gfold[of "map fl_T args" B] gB by (simp add: T'_def)
      have tabs: "typs_ok ar (types_abs Us b) \<longleftrightarrow> (\<forall>A\<in>set Us. ground ar A) \<and> typs_ok ar b" for Us b
        by (induction Us) auto
      have tyok: "typs_ok ar (types_abs Ts body)"
        using gTs gT' ge(5) by (simp add: tabs body_def typs_ok_list_comb)
      have wf2: "wf_env ar env2"
        by (rule ok_update_wf_env[OF upd' ei1(2) has_type_proper[OF tyabs] tyok gT])
          (use has_type_closed[OF tyabs] in simp)
      have mabs: "mk_subst \<sigma>1 (tr (types_abs Ts body)) = Abs_m (length Ts) (w \<degree>\<degree> map BVar ks)"
        using ge(5,7) by (simp add: tr_types_abs mk_subst_Abs_m body_def tr_list_comb ks_def comp_def)
      have eqv: "\<sigma>1 (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>1 (tr (types_abs Ts body))"
        using agree_Var[OF ge(2) vm] w(3) mabs by simp
      have V1v: "V1 v = T" using Vv vx' by (simp add: V1_def)
      have vm1: "snd v \<le> maxidx env1" using vm ge(4) by (simp add: less_eq_integer.rep_eq plus_integer.rep_eq)
      have babs: "below (maxidx env1) (types_abs Ts body)"
        using ge(4,5) by (simp add: body_def below_list_comb x'_def comp_def)
      note su = solution_update[OF sol1 ei1(4) ei1(3) upd' eqv V1v tyabs vm1 babs]
      have vpsb: "vps (types_abs Ts body) = {(x', T')}" using ge(5) by (simp add: body_def vps_list_comb)
      have ac2: "acyc env2"
        unfolding acyc_def
      proof (rule acyclic_update[OF dep_update[OF ok_update(2,1)[OF upd']]])
        have "lk env1 x' T' = None" using x'n by (simp add: lk_def)
        from reach_unbound[OF this] show "(v, T) \<notin> reach env1 (vps (types_abs Ts body))"
          using vx' vpsb by simp
        show "acyclic (dep env1)" using ei1(1) by (simp add: acyc_def)
      qed
      have inv2: "cinv ar V1 \<tau>' \<sigma>1 env2 dps"
        using ge(1) su ac2 wf2 by (simp add: cinv_def env_inv_def)
      have e2: "vt_is_empty (tyenv env2)" by (rule wf_envD(1)[OF wf2])
      have tyG: "has_type V1 (map snd rb') (list_comb G ts') B"
      proof -
        have "has_type V1 (map snd rb') G T'" using ge(5,8) by (simp add: has_type.Var)
        moreover have "list_all2 (has_type V1 (map snd rb')) ts' (map fl_T args)"
          unfolding list_all2_conv_all_nth ts'_def
          using tya[OF nth_mem] has_type_agreeV[OF _ _ ge(3)] by auto
        ultimately show ?thesis unfolding T'_def has_type_list_comb by blast
      qed
      from norm_term_term[OF ac2 wf2 su(2) tyG] obtain t'' where
        nt: "norm_term env2 (list_comb G ts') = return t''" "has_type V1 (map snd rb') t'' B"
        "\<forall>x U. head_of t'' = Var x U \<longrightarrow> vt_lookup (tenv env2) x = None"
        "\<forall>env0. flexb env0 env2 \<longrightarrow> fh env0 (list_comb G ts') \<longrightarrow> fh env0 t''"
        by blast
      have ok2: "okW (clean_term banned env t) (env2, t'')"
        using ok(1) False g[unfolded T'_def] vu_eq upd nt(1) unfolding ct
        by (simp add: bindW_def Let_def args_def ts'_def body_def liftM_def returnW_def return_def)
      have bG: "below (maxidx env2) (list_comb G ts')"
        using ge(4,5) su(4) tya below_mono[of "maxidx env" _ "maxidx env2"]
        by (auto simp: below_list_comb ts'_def x'_def less_eq_integer.rep_eq plus_integer.rep_eq)
      have bt'': "below (maxidx env2) t''" by (rule norm_term_below[OF nt(1) e2 su(3) bG])
      have tl2: "vt_lookup (tenv env2) x = (if x = v then Some (T, types_abs Ts body) else vt_lookup (tenv env) x)" for x
        using ok_update(2)[OF upd'] gs(1) by simp
      have nb: "\<forall>x. vt_lookup (tenv env2) x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v"
        using tl2 by auto
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
          proof (cases "x = v")
            case True
            with l tl2 have "u = types_abs Ts body" by simp
            then show ?thesis using fG by (simp add: fh_def body_def)
          next
            case False
            with l tl2 have "vt_lookup (tenv env) x = Some (U, u)" by simp
            with that(1) l(2) show ?thesis unfolding flexb_def by blast
          qed
        qed
        with nt(4) fG show ?thesis by blast
      qed
      have ext2: "extends env2 env" using ok_update_extends[OF upd'] ge(6) by (rule extends_trans)
      have mx: "maxidx env \<le> maxidx env2" using ge(4) su(4) by (simp add: less_eq_integer.rep_eq plus_integer.rep_eq)
      have hG: "head_of t'' = G"
        using norm_term_head[OF nt(1) e2, of x' T'] ge(5) x'n gs(1) tl2 vx' by simp
      have hd: "\<forall>x U. head_of t'' = Var x U \<longrightarrow> x = v \<or> maxidx env < snd x"
        using hG ge(5) by (simp add: x'_def less_integer.rep_eq plus_integer.rep_eq)
      show ?thesis
        using ok2 inv2 ge(2,3) mx ext2 nt(2,3) bt'' nb fl hd
        by (intro disjI2 exI[of _ env2] exI[of _ t''] exI[of _ V1] exI[of _ \<sigma>1]) blast
    qed
  qed
qed

subsection \<open>Flex-flex assignments\<close>

lemma update_complete:
  assumes inv: "env_inv ar V env" and sol: "solution V \<tau>' \<sigma> env" and xn: "vt_lookup (tenv env) x = None"
    and VT: "V x = T" and ty: "has_type V [] s T" and ws: "wf_tm ar [] s" and gT: "ground ar T"
    and bs: "below (maxidx env) s" and xm: "snd x \<le> maxidx env" and ac: "(x, T) \<notin> reach env (vps s)"
    and eq: "\<sigma> (code (AVar x)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr s)"
  shows "\<exists>env'. update (x, T) s env = return env' \<and> env_inv ar V env' \<and> solution V \<tau>' \<sigma> env' \<and>
    extends env' env \<and> maxidx env' = maxidx env \<and> tenv env' = vt_update (x, (T, s)) (tenv env)"
proof -
  note ei = env_invD[OF inv]
  from update_unbound_ok[OF xn, of T s] obtain env' where upd: "update (x, T) s env = Some (Ok env')" by blast
  have upd': "ok (update (x, T) s env) env'" using upd by simp
  note su = solution_update[OF sol ei(4) ei(3) upd' eq VT ty xm bs]
  have "acyc env'"
    unfolding acyc_def
    by (rule acyclic_update[OF dep_update[OF ok_update(2,1)[OF upd']] ac]) (use ei(1) in \<open>simp add: acyc_def\<close>)
  moreover have "wf_env ar env'" using ok_update_wf_env[OF upd' ei(2) _ _ gT] ws by (simp add: wf_tm_def)
  ultimately have "env_inv ar V env'" using su by (simp add: env_inv_def)
  then show ?thesis using upd su ok_update_extends[OF upd'] ok_update(2)[OF upd'] by (auto simp: return_def)
qed

text \<open>\<^const>\<open>vupdate\<close> on a binding that the solution satisfies and that closes no cycle.\<close>

lemma vupdate_complete:
  assumes inv: "env_inv ar V env" and sol: "solution V \<tau>' \<sigma> env" and vn: "vt_lookup (tenv env) v = None"
    and VT: "V v = T" and ty: "has_type V [] s T" and ws: "wf_tm ar [] s" and gT: "ground ar T"
    and bs: "below (maxidx env) s" and vm: "snd v \<le> maxidx env" and ac: "\<forall>U. (v, U) \<notin> reach env (vps s)"
    and eq: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr s)"
    and hs: "\<forall>w U. s = Var w U \<longrightarrow> vt_lookup (tenv env) w = None"
  shows "\<exists>env'. vupdate (v, T) s env = return env' \<and> env_inv ar V env' \<and> solution V \<tau>' \<sigma> env' \<and>
    extends env' env \<and> maxidx env' = maxidx env \<and>
    (\<forall>x U' u. vt_lookup (tenv env') x = Some (U', u) \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
      (x = v \<and> u = s) \<or> (\<exists>U. s = Var x U \<and> u = Var v U))"
proof -
  note ei = env_invD[OF inv]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  have plain: "?thesis" if "vupdate (v, T) s env = update (v, T) s env"
  proof -
    from update_complete[OF inv sol vn VT ty ws gT bs vm _ eq] ac obtain env' where
      u: "update (v, T) s env = return env'" "env_inv ar V env'" "solution V \<tau>' \<sigma> env'"
      "extends env' env" "maxidx env' = maxidx env" "tenv env' = vt_update (v, (T, s)) (tenv env)"
      by blast
    then show ?thesis using that by (intro exI[of _ env']) auto
  qed
  show ?thesis
  proof (cases s)
    case (Var w U)
    have U: "U = T" using ty Var by (auto elim: has_type_elims)
    have wn: "vt_lookup (tenv env) w = None" using hs Var by simp
    consider "v = w" | "v \<noteq> w" "indexname_less v w" | "v \<noteq> w" "\<not> indexname_less v w" by blast
    then show ?thesis
    proof cases
      case 1
      have "vupdate (v, T) s env = return env" using 1 Var by (subst vupdate.simps) simp
      then show ?thesis using inv sol by (intro exI[of _ env]) (auto simp: extends_refl)
    next
      case 2
      have lw: "lookup env w U = return None" by (rule lookup_unbound[OF e wn])
      have Vw: "V w = T" using ty Var U by (auto elim: has_type_elims)
      have wm: "snd w \<le> maxidx env" using bs Var by simp
      have "(w, T) \<notin> reach env (vps (Var v T))"
      proof -
        have "lk env v T = None" using vn by (simp add: lk_def)
        from reach_unbound[OF this] 2(1) show ?thesis by simp
      qed
      moreover have "\<sigma> (code (AVar w)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (Var v T))"
        using eq Var by (simp add: equiv_sym)
      moreover have "has_type V [] (Var v T) T" using VT by (simp add: has_type.Var)
      moreover have "wf_tm ar [] (Var v T)" using gT by (simp add: wf_tm_def)
      ultimately obtain env' where
        u: "update (w, T) (Var v T) env = return env'" "env_inv ar V env'" "solution V \<tau>' \<sigma> env'"
        "extends env' env" "maxidx env' = maxidx env" "tenv env' = vt_update (w, (T, Var v T)) (tenv env)"
        using update_complete[OF inv sol wn Vw _ _ gT _ wm] vm by fastforce
      have "vupdate (v, T) s env = return env'"
        using 2 Var U lw u(1) by (subst vupdate.simps) (simp add: bindW_def return_def)
      then show ?thesis using u Var U by (intro exI[of _ env']) auto
    next
      case 3
      have "vupdate (v, T) s env = update (v, T) s env" using 3 Var by (subst vupdate.simps) simp
      then show ?thesis by (rule plain)
    qed
  qed (rule plain, subst vupdate.simps, simp)+
qed

lemma fhd_rlist_abs[simp]: "fhd (rlist_abs rb u) = fhd u"
proof (induction rb arbitrary: u)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Abs a T u"] show ?case by simp
qed simp

lemma rlist_abs_Var: "rlist_abs rb u = Var w U \<Longrightarrow> rb = [] \<and> u = Var w U"
proof (induction rb arbitrary: u)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Abs a T u"] Cons.prems show ?case by simp
qed simp

lemma ground_foldr_iff: "ground ar (foldr fun_type Us C) \<longleftrightarrow> (\<forall>A\<in>set Us. ground ar A) \<and> ground ar C"
  by (induction Us) auto

text \<open>
  \<^const>\<open>ff_assign\<close> on a solved pair: it gives up with \<open>ASSIGN\<close>, or it binds the variable, and the
  solution is kept.
\<close>

lemma ff_assign_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env dps"
    and tyt: "has_type V (map snd rb) t B" and tyu: "has_type V (map snd rb) u B" and nfB: "\<not> is_funT B"
    and bok: "binders_ok ar rb" and wu: "wf_tm ar rb u" and bt: "below (maxidx env) t"
    and bu: "below (maxidx env) u" and ds: "dsolved \<sigma> (rb, t, u)"
    and ht: "\<forall>x U. head_of t = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
    and hu: "\<forall>x U. head_of u = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
  shows "(\<exists>evs. ff_assign alg env rb t u = Some (evs, UErr ASSIGN)) \<or>
    (\<exists>env'. okW (ff_assign alg env rb t u) env' \<and> cinv ar V \<tau>' \<sigma> env' dps \<and> extends env' env \<and>
      maxidx env' = maxidx env \<and>
      (\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fh env0 u \<longrightarrow> flexb env0 env'))"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note sol = cinvD(2)[OF inv]
  note \<sigma> = solutionD[OF sol]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  consider "get_eta_var rb 0 t = raiseW ASSIGN" | v T where "get_eta_var rb 0 t = returnW (v, T)"
    using get_eta_var_cases by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: ff_assign_def bindW_def raiseW_def)
  next
    case 2
    then have gev: "okW (get_eta_var rb 0 t) (v, T)" by (simp add: returnW_def)
    from get_eta_var_type[OF gev _ tyt] have T: "T = foldr fun_type (rev (map snd rb)) B"
      and Vv: "V v = T" and htv: "head_of t = Var v T"
      by (simp_all add: rev_nth)
    have vn: "vt_lookup (tenv env) v = None" using ht htv by simp
    have vm: "snd v \<le> maxidx env" using bt vps_head_of[OF htv] by (auto dest: below_vps)
    from occurs_terms_term[OF e ei(3), of "[u]" v] has_type_vtyped[OF tyu] obtain b
      where oc: "occurs_terms env v [u] = return b" by auto
    have okc: "ok (occurs_terms env v [u]) b" using oc by (simp add: return_def)
    have b: "b \<longleftrightarrow> occ_in env v (vps u)" using occurs_terms_correct[OF e ei(1) okc] by simp
    show ?thesis
    proof (cases b)
      case True
      then show ?thesis using 2 oc by (simp add: ff_assign_def bindW_def returnW_def return_def raiseW_def)
    next
      case False
      let ?s = "rlist_abs rb u"
      have bty: "body_type env T = return B" using body_type_base[OF e nfB] T by simp
      have fty: "fastype env rb u = return B" by (rule fastype_typed[OF e tyu])
      have tys: "has_type V [] ?s T" using has_type_rlist_abs[of V rb "[]" u B] tyu T by simp
      have ws: "wf_tm ar [] ?s"
        using wu bok by (simp add: wf_tm_def proper_rlist_abs typs_ok_rlist_abs no_loose_bound_tr_rlist_abs)
      have gB: "ground ar B" by (rule ground_has_type[OF e bok wu tyu])
      have gT: "ground ar T" using bok gB T by (auto simp: ground_foldr_iff binders_ok_def)
      have bs: "below (maxidx env) ?s" using bu by (simp add: below_rlist_abs)
      have nocc: "\<forall>U. (v, U) \<notin> reach env (vps ?s)" using False b by (auto simp: occ_in_def vps_rlist_abs)
      have eqv: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr ?s)"
      proof -
        have "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (dB.Var (code (AVar v)))"
          using mk_subst_equiv[OF conjunct1[OF get_eta_var_equiv[OF gev]] \<sigma>(1)] .
        then have "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))" by simp
        from equiv_trans[OF equiv_sym[OF this] dsolvedD[OF ds]] show ?thesis .
      qed
      have hs: "\<forall>w U. ?s = Var w U \<longrightarrow> vt_lookup (tenv env) w = None"
      proof (intro allI impI)
        fix w U assume "?s = Var w U"
        then have "rb = [] \<and> u = Var w U" by (rule rlist_abs_Var)
        then show "vt_lookup (tenv env) w = None" using hu by simp
      qed
      from vupdate_complete[OF cinvD(1)[OF inv] sol vn Vv tys ws gT bs vm nocc eqv hs] obtain env' where
        vu: "vupdate (v, T) ?s env = return env'" "env_inv ar V env'" "solution V \<tau>' \<sigma> env'"
        "extends env' env" "maxidx env' = maxidx env"
        "\<forall>x U' u'. vt_lookup (tenv env') x = Some (U', u') \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
          (x = v \<and> u' = ?s) \<or> (\<exists>U. ?s = Var x U \<and> u' = Var v U)"
        by blast
      have ok: "okW (ff_assign alg env rb t u) env'"
        using 2 oc False bty fty vu(1)
        by (simp add: ff_assign_def bindW_def returnW_def return_def cunify_types_same liftM_def)
      have inv': "cinv ar V \<tau>' \<sigma> env' dps" using inv vu(2,3,5) by (simp add: cinv_def)
      have "flexb env0 env'" if "flexb env0 env" "extends env env0" "fh env0 u" for env0
        unfolding flexb_def
      proof (intro allI impI)
        fix x U' u' assume l: "vt_lookup (tenv env') x = Some (U', u')" "vt_lookup (tenv env0) x = None"
        show "fh env0 u'"
        proof (cases "vt_lookup (tenv env) x")
          case None
          with vu(6) l(1) consider "x = v" "u' = ?s" | U where "?s = Var x U" "u' = Var v U" by blast
          then show ?thesis
          proof cases
            case 1
            then show ?thesis using that(3) by (simp add: fh_def)
          next
            case 2
            have "vt_lookup (tenv env0) v = None" by (rule extends_unbound[OF that(2) vn])
            with 2 show ?thesis by (simp add: fh_def)
          qed
        next
          case (Some p)
          with extendsD[OF vu(4) Some] l(1) have "vt_lookup (tenv env) x = Some (U', u')" by simp
          with that(1) l(2) show ?thesis unfolding flexb_def by blast
        qed
      qed
      then show ?thesis using ok inv' vu(4,5) by blast
    qed
  qed
qed

subsection \<open>Cleaning flex-flex pairs\<close>

lemma add_tpair_complete:
  "dsolved \<sigma> (rb, t, u) \<Longrightarrow> tsolved \<sigma> tps \<Longrightarrow> tsolved \<sigma> (add_tpair rb t u tps)"
  by (auto simp: add_tpair_def Let_def tsolved_def dsolved_def)

lemma add_tpair_below:
  "below m t \<Longrightarrow> below m u \<Longrightarrow> \<forall>(a, b)\<in>set tps. below m a \<and> below m b \<Longrightarrow>
    \<forall>(a, b)\<in>set (add_tpair rb t u tps). below m a \<and> below m b"
  by (auto simp: add_tpair_def Let_def below_rlist_abs)

text \<open>
  The remaining pairs are flex-flex pairs under a binder: typed terms of the same base type whose
  heads are variables that are unbound in the environment \<open>env0\<close> of the flex-flex phase.
\<close>

definition tpok :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> pterm \<times> pterm \<Rightarrow> bool" where
  "tpok ar V env0 m ab \<longleftrightarrow> (\<exists>rb a b B. ab = (rlist_abs rb a, rlist_abs rb b) \<and> binders_ok ar rb \<and>
    wf_tm ar rb a \<and> wf_tm ar rb b \<and> has_type V (map snd rb) a B \<and> has_type V (map snd rb) b B \<and>
    \<not> is_funT B \<and> below m a \<and> below m b \<and> fh env0 a \<and> fh env0 b)"

lemma tpok_mono: "tpok ar V env0 m ab \<Longrightarrow> agreeV m V V' \<Longrightarrow> m \<le> m' \<Longrightarrow> tpok ar V' env0 m' ab"
  unfolding tpok_def by (blast intro: has_type_agreeV below_mono)

lemma add_tpair_tpok:
  assumes "binders_ok ar rb" "wf_tm ar rb t" "wf_tm ar rb u" "has_type V (map snd rb) t B"
    "has_type V (map snd rb) u B" "\<not> is_funT B" "below m t" "below m u" "fh env0 t" "fh env0 u"
    "\<forall>ab\<in>set tps. tpok ar V env0 m ab"
  shows "\<forall>ab\<in>set (add_tpair rb t u tps). tpok ar V env0 m ab"
proof -
  have "tpok ar V env0 m (rlist_abs rb t, rlist_abs rb u)" unfolding tpok_def using assms(1-10) by blast
  with assms(11) show ?thesis by (auto simp: add_tpair_def Let_def)
qed

lemma loose_BVars_mk_subst_closed: "closed_on UNIV \<sigma> \<Longrightarrow> loose_BVars (mk_subst \<sigma> s) = loose_BVars s"
  by (induction s) (auto simp: closed_onD no_loose_bound_loose_BVars)

text \<open>The instances of the sides of a solved pair only depend on the bound variables of both.\<close>

lemma dsolved_dep:
  assumes "closed_on UNIV \<sigma>" "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
  shows "dep_on (loose_BVars (tr t) \<inter> loose_BVars (tr u)) (mk_subst \<sigma> (tr t))"
    "dep_on (loose_BVars (tr t) \<inter> loose_BVars (tr u)) (mk_subst \<sigma> (tr u))"
proof -
  from closure_confluent[OF assms(2)] obtain c where c: "\<beta>\<eta>cl (mk_subst \<sigma> (tr t)) c" "\<beta>\<eta>cl (mk_subst \<sigma> (tr u)) c"
    by blast
  have lc: "loose_BVars c \<subseteq> loose_BVars (tr t) \<inter> loose_BVars (tr u)"
    using loose_BVars_\<beta>\<eta>cl[OF c(1)] loose_BVars_\<beta>\<eta>cl[OF c(2)] loose_BVars_mk_subst_closed[OF assms(1)] by auto
  show "dep_on (loose_BVars (tr t) \<inter> loose_BVars (tr u)) (mk_subst \<sigma> (tr t))"
    by (rule dep_onI[OF \<beta>\<eta>cl_into_equiv[OF c(1)] lc])
  show "dep_on (loose_BVars (tr t) \<inter> loose_BVars (tr u)) (mk_subst \<sigma> (tr u))"
    by (rule dep_onI[OF \<beta>\<eta>cl_into_equiv[OF c(2)] lc])
qed

text \<open>Reflecting the renaming of the cleaned pair.\<close>

lemma unsquash_dsolved:
  assumes "B \<subseteq> {..<n}" "length rb' = n - card B" "closed_on UNIV \<sigma>"
    "wf_tm ar rb' t" "wf_tm ar rb' u"
    "map_BVars (unsquash B) (mk_subst \<sigma> (tr t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash B) (mk_subst \<sigma> (tr u))"
  shows "dsolved \<sigma> (rb', t, u)"
proof -
  have l: "loose_BVars (mk_subst \<sigma> (tr s)) \<subseteq> {..<n - card B}" if "wf_tm ar rb' s" for s
    using no_loose_bound_BVars[of "tr s" "length rb'"] that assms(2)
    by (auto simp: wf_tm_def loose_BVars_mk_subst_closed[OF assms(3)])
  from map_BVars_equiv[OF assms(6), of "squash B"]
  have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
    by (simp only: map_BVars_squash_unsquash[OF assms(1) l[OF assms(4)]]
      map_BVars_squash_unsquash[OF assms(1) l[OF assms(5)]])
  then show ?thesis by (simp add: dsolved_dsolvedB dsolvedB_unabs)
qed

lemma tsolved_agree:
  "tsolved \<sigma> tps \<Longrightarrow> \<forall>(a, b)\<in>set tps. below m a \<and> below m b \<Longrightarrow> agree m \<sigma> \<sigma>' \<Longrightarrow> tsolved \<sigma>' tps"
  unfolding tsolved_def
proof (intro ballI, clarify)
  fix a b assume s: "\<forall>(a, b)\<in>set tps. mk_subst \<sigma> (tr a) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr b)"
    and b: "\<forall>(a, b)\<in>set tps. below m a \<and> below m b" and ag: "agree m \<sigma> \<sigma>'" and ab: "(a, b) \<in> set tps"
  from bspec[OF s ab] bspec[OF b ab] mk_subst_agree[OF _ ag, of a] mk_subst_agree[OF _ ag, of b]
  show "mk_subst \<sigma>' (tr a) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr b)" by simp
qed

lemma tps_below_mono:
  "\<forall>(a, b)\<in>set tps. below m a \<and> below m b \<Longrightarrow> m \<le> m' \<Longrightarrow> \<forall>(a, b)\<in>set tps. below m' a \<and> below m' b"
  by (auto intro: below_mono)

text \<open>The runs of the handlers in \<^const>\<open>clean_ffpair\<close>.\<close>

lemma ff_handler_complete:
  fixes alg env2 rb' t' u' tps
  defines "H \<equiv> handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t' u'; returnW (env3, tps)})
    (\<lambda>e. case e of
      ASSIGN \<Rightarrow>
        handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u' t'; returnW (env3, tps)})
          (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
    | _ \<Rightarrow> raiseW e)"
  shows "okW (ff_assign alg env2 rb' t' u') env3 \<Longrightarrow> okW H (env3, tps)"
    "\<exists>evs. ff_assign alg env2 rb' t' u' = Some (evs, UErr ASSIGN) \<Longrightarrow>
      okW (ff_assign alg env2 rb' u' t') env3 \<Longrightarrow> okW H (env3, tps)"
    "\<exists>evs. ff_assign alg env2 rb' t' u' = Some (evs, UErr ASSIGN) \<Longrightarrow>
      \<exists>evs. ff_assign alg env2 rb' u' t' = Some (evs, UErr ASSIGN) \<Longrightarrow> okW H (env2, add_tpair rb' t' u' tps)"
  by (auto simp: H_def okW_handleW bindW_def)

lemma clean_ffpair_run:
  assumes fb: "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], []) =
    (banned, rb')"
  shows "\<exists>evs. clean_term banned env t = Some (evs, UErr CHANGE_FAIL) \<Longrightarrow>
      okW (clean_ffpair alg rb t u env tps) (env, add_tpair rb t u tps)"
    "okW (clean_term banned env t) (env1, t1) \<Longrightarrow> \<exists>evs. clean_term banned env1 u = Some (evs, UErr CHANGE_FAIL) \<Longrightarrow>
      okW (clean_ffpair alg rb t u env tps) (env, add_tpair rb t u tps)"
    "okW (clean_term banned env t) (env1, t1) \<Longrightarrow> okW (clean_term banned env1 u) (env2, u1) \<Longrightarrow>
      okW (handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t1 u1; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u1 t1; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t1 u1 tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) r \<Longrightarrow> okW (clean_ffpair alg rb t u env tps) r"
  by (auto simp: clean_ffpair_def Let_def fb okW_handleW bindW_def)

text \<open>
  \<^const>\<open>clean_ffpair\<close> on a solved flex-flex pair with different unbound head variables: an
  extension of the solution satisfies the resulting environment and solves the remaining pairs.
\<close>

lemma clean_ffpair_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env dps"
    and tyt: "has_type V (map snd rb) t B" and tyu: "has_type V (map snd rb) u B" and nfB: "\<not> is_funT B"
    and bok: "binders_ok ar rb" and wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u"
    and bt: "below (maxidx env) t" and bu: "below (maxidx env) u" and ds: "dsolved \<sigma> (rb, t, u)"
    and ht: "head_of t = Var v T" "vt_lookup (tenv env) v = None"
    and hu: "head_of u = Var w U" "vt_lookup (tenv env) w = None" and vw: "v \<noteq> w"
    and ts: "tsolved \<sigma> tps" and tb: "\<forall>(a, b)\<in>set tps. below (maxidx env) a \<and> below (maxidx env) b"
  shows "\<exists>env' tps' V' \<sigma>'. okW (clean_ffpair alg rb t u env tps) (env', tps') \<and> cinv ar V' \<tau>' \<sigma>' env' dps \<and>
    tsolved \<sigma>' tps' \<and> (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) V V' \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
    (\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
      flexb env0 env' \<and> ((\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab) \<longrightarrow>
        (\<forall>ab\<in>set tps'. tpok ar V' env0 (maxidx env') ab)))"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note \<sigma> = solutionD[OF cinvD(2)[OF inv]]
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  note cb = clean_binder[OF fb]
  note ck = clean_binder_keeps[OF fb]
  let ?B = "bset banned"
  let ?K = "\<lambda>i. integer_of_nat i \<in> set (loose_bnos t) \<and> integer_of_nat i \<in> set (loose_bnos u)"
  have pt: "proper t" "proper u" using wt wu by (simp_all add: wf_tm_def)
  have K: "?K i \<longleftrightarrow> i \<in> loose_BVars (tr t) \<and> i \<in> loose_BVars (tr u)" for i
    using set_loose_bnos[OF pt(1)] set_loose_bnos[OF pt(2)] by (auto simp: image_iff integer_eq_iff)
  let ?Z = "loose_BVars (tr t) \<inter> loose_BVars (tr u)"
  have bs: "?B = {i. i < length rb \<and> i \<notin> ?Z}" using ck(1) K by auto
  then have Zb: "?Z \<inter> ?B = {}" by blast
  have keep: "squash ?B i < length rb' \<and> rb' ! squash ?B i = rb ! i" if "i < length rb" "i \<notin> ?B" for i
    using ck(2)[of i] that K bs by auto
  have bok': "binders_ok ar rb'" using bok cb(5) by (auto simp: binders_ok_def)
  have wenv: "wf_env ar env" by (rule ei(2))
  have dsB: "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
    using ds by (simp add: dsolved_dsolvedB dsolvedB_unabs)
  note dep = dsolved_dep[OF \<sigma>(1) dsB]
  have fh0: "fh env0 t \<and> fh env0 u" if "extends env env0" for env0
    using ht hu extends_None[OF that] fhd_head_of[of t] fhd_head_of[of u] by (auto simp: fh_def)
  have tp0: "\<forall>ab\<in>set (add_tpair rb t u tps). tpok ar V env0 (maxidx env) ab"
    if "extends env env0" "\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab" for env0
    using add_tpair_tpok[OF bok wt wu tyt tyu nfB bt bu _ _ that(2)] fh0[OF that(1)] by blast
  have fallback: "\<exists>env' tps' V' \<sigma>'. okW (clean_ffpair alg rb t u env tps) (env', tps') \<and> cinv ar V' \<tau>' \<sigma>' env' dps \<and>
    tsolved \<sigma>' tps' \<and> (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) V V' \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
    (\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
      flexb env0 env' \<and> ((\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab) \<longrightarrow>
        (\<forall>ab\<in>set tps'. tpok ar V' env0 (maxidx env') ab)))"
    if "okW (clean_ffpair alg rb t u env tps) (env, add_tpair rb t u tps)"
    using that inv add_tpair_complete[OF ds ts] add_tpair_below[OF bt bu tb, of rb] tp0
    by (intro exI[where x=env] exI[where x="add_tpair rb t u tps"] exI[where x=V] exI[where x=\<sigma>]) auto
  have hwb: "snd w \<le> maxidx env"
  proof -
    have "below (maxidx env) (list_comb (head_of u) (snd (strip_comb u)))"
      using bu head_of_list_comb[of u] by simp
    then show ?thesis using hu(1) by (simp add: below_list_comb)
  qed
  from clean_term_complete[OF inv tyt nfB wt bt ht cb(1-4) keep dep(1) Zb]
  consider (f1) "\<exists>evs. clean_term banned env t = Some (evs, UErr CHANGE_FAIL)"
    | (c1) env1 t1 V1 \<sigma>1 where "okW (clean_term banned env t) (env1, t1)" "cinv ar V1 \<tau>' \<sigma>1 env1 dps"
      "agree (maxidx env) \<sigma> \<sigma>1" "agreeV (maxidx env) V V1" "maxidx env \<le> maxidx env1" "extends env1 env"
      "has_type V1 (map snd rb') t1 B" "below (maxidx env1) t1"
      "\<forall>x U. head_of t1 = Var x U \<longrightarrow> vt_lookup (tenv env1) x = None"
      "\<forall>x. vt_lookup (tenv env1) x \<noteq> None \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x = v"
      "\<forall>x U. head_of t1 = Var x U \<longrightarrow> x = v \<or> maxidx env < snd x"
      "\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
        flexb env0 env1 \<and> fh env0 t1"
    by blast
  then show ?thesis
  proof cases
    case f1
    then show ?thesis by (rule fallback[OF clean_ffpair_run(1)[OF fb]])
  next
    case (c1 env1 t1 V1 \<sigma>1)
    note ok1 = c1(1) and inv1 = c1(2) and ag1 = c1(3) and agV1 = c1(4) and mx1 = c1(5) and ext1 = c1(6)
      and ty1 = c1(7) and bt1 = c1(8) and hn1 = c1(9) and new1 = c1(10) and hd1 = c1(11) and fl1 = c1(12)
    have tyu1: "has_type V1 (map snd rb) u B" by (rule has_type_agreeV[OF tyu bu agV1])
    have bu1: "below (maxidx env1) u" by (rule below_mono[OF bu mx1])
    have hu1: "vt_lookup (tenv env1) w = None" using new1 hu(2) vw by blast
    have dep1: "dep_on ?Z (mk_subst \<sigma>1 (tr u))" using dep(2) mk_subst_agree[OF bu ag1] by simp
    from clean_term_complete[OF inv1 tyu1 nfB wu bu1 hu(1) hu1 cb(1-4) keep dep1 Zb]
    consider (f2) "\<exists>evs. clean_term banned env1 u = Some (evs, UErr CHANGE_FAIL)"
      | (c2) env2 u1 V2 \<sigma>2 where "okW (clean_term banned env1 u) (env2, u1)" "cinv ar V2 \<tau>' \<sigma>2 env2 dps"
        "agree (maxidx env1) \<sigma>1 \<sigma>2" "agreeV (maxidx env1) V1 V2" "maxidx env1 \<le> maxidx env2" "extends env2 env1"
        "has_type V2 (map snd rb') u1 B" "below (maxidx env2) u1"
        "\<forall>x U. head_of u1 = Var x U \<longrightarrow> vt_lookup (tenv env2) x = None"
        "\<forall>x. vt_lookup (tenv env2) x \<noteq> None \<longrightarrow> vt_lookup (tenv env1) x = None \<longrightarrow> x = w"
        "\<forall>env0. flexb env0 env1 \<longrightarrow> extends env1 env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env1 \<longrightarrow>
          flexb env0 env2 \<and> fh env0 u1"
      by blast
    then show ?thesis
    proof cases
      case f2
      then show ?thesis by (rule fallback[OF clean_ffpair_run(2)[OF fb ok1]])
    next
      case (c2 env2 u1 V2 \<sigma>2)
      note ok2 = c2(1) and inv2 = c2(2) and ag2 = c2(3) and agV2 = c2(4) and mx2 = c2(5) and ext2 = c2(6)
        and tyu2 = c2(7) and bu2 = c2(8) and hn2 = c2(9) and new2 = c2(10) and fl2 = c2(11)
      have wenv1: "wf_env ar env1" by (rule env_invD(2)[OF cinvD(1)[OF inv1]])
      note st = clean_term_sound[OF ok1 wenv wt cb(1-4)]
      note su = clean_term_sound[OF ok2 wenv1 wu cb(1-4)]
      have wt1: "wf_tm ar rb' t1" and wu1: "wf_tm ar rb' u1" using st su by blast+
      note \<sigma>2 = solutionD[OF cinvD(2)[OF inv2]]
      have mx12: "maxidx env \<le> maxidx env2" using mx1 mx2 by simp
      have ag02: "agree (maxidx env) \<sigma> \<sigma>2" by (rule agree_trans[OF ag1 ag2 mx1])
      have agV02: "agreeV (maxidx env) V V2" by (rule agreeV_trans[OF agV1 agV2 mx1])
      have ext02: "extends env2 env" by (rule extends_trans[OF ext2 ext1])
      have "mk_subst \<sigma>2 (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash ?B) (mk_subst \<sigma>2 (tr t1))"
        using st \<sigma>2(1) sat_extends[OF \<sigma>2(4) ext2] by blast
      moreover have "mk_subst \<sigma>2 (tr u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash ?B) (mk_subst \<sigma>2 (tr u1))"
        using su \<sigma>2(1,4) by blast
      moreover have "mk_subst \<sigma>2 (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>2 (tr u)"
        using dsB mk_subst_agree[OF bt ag02] mk_subst_agree[OF bu ag02] by simp
      ultimately have "map_BVars (unsquash ?B) (mk_subst \<sigma>2 (tr t1)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          map_BVars (unsquash ?B) (mk_subst \<sigma>2 (tr u1))"
        by (meson equiv_sym equiv_trans)
      note ds2 = unsquash_dsolved[OF cb(3) cb(4) \<sigma>2(1) wt1 wu1 this]
      have ty1': "has_type V2 (map snd rb') t1 B" by (rule has_type_agreeV[OF ty1 bt1 agV2])
      have bt1': "below (maxidx env2) t1" by (rule below_mono[OF bt1 mx2])
      have h1: "\<forall>x U. head_of t1 = Var x U \<longrightarrow> vt_lookup (tenv env2) x = None"
      proof (intro allI impI)
        fix x U assume h: "head_of t1 = Var x U"
        have "x \<noteq> w" using hd1 h vw hwb by force
        then show "vt_lookup (tenv env2) x = None" using hn1 h new2 by blast
      qed
      have ts2: "tsolved \<sigma>2 tps" by (rule tsolved_agree[OF ts tb ag02])
      have tb2: "\<forall>(a, b)\<in>set tps. below (maxidx env2) a \<and> below (maxidx env2) b"
        by (rule tps_below_mono[OF tb mx12])
      have fl: "flexb env0 env2 \<and> fh env0 t1 \<and> fh env0 u1"
        if "flexb env0 env" "extends env env0" "fresh_env env0" "maxidx env0 \<le> maxidx env" for env0
        using fl1 fl2 that extends_trans[OF ext1 that(2)] mx1 by fastforce
      have fin: "\<exists>env' tps' V' \<sigma>'. okW (clean_ffpair alg rb t u env tps) (env', tps') \<and> cinv ar V' \<tau>' \<sigma>' env' dps \<and>
        tsolved \<sigma>' tps' \<and> (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
        agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) V V' \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
        (\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
          flexb env0 env' \<and> ((\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab) \<longrightarrow>
        (\<forall>ab\<in>set tps'. tpok ar V' env0 (maxidx env') ab)))"
        if fa: "okW (clean_ffpair alg rb t u env tps) (env', tps')" "cinv ar V2 \<tau>' \<sigma>2 env' dps" "tsolved \<sigma>2 tps'"
          "\<forall>(a, b)\<in>set tps'. below (maxidx env2) a \<and> below (maxidx env2) b" "maxidx env' = maxidx env2"
          "extends env' env2" "tps' = tps \<or> tps' = add_tpair rb' t1 u1 tps"
          "\<forall>env0. flexb env0 env2 \<longrightarrow> extends env2 env0 \<longrightarrow> fh env0 t1 \<longrightarrow> fh env0 u1 \<longrightarrow> flexb env0 env'"
        for env' tps'
      proof -
        have tps': "\<forall>ab\<in>set tps'. tpok ar V2 env0 (maxidx env') ab"
          if "flexb env0 env" "extends env env0" "fresh_env env0" "maxidx env0 \<le> maxidx env"
            "\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab" for env0
        proof -
          from fl[OF that(1-4)] have f: "fh env0 t1" "fh env0 u1" by blast+
          have t2: "\<forall>ab\<in>set tps. tpok ar V2 env0 (maxidx env2) ab"
            using that(5) tpok_mono[OF _ agV02 mx12] by blast
          show ?thesis
            using fa(5,7) t2 add_tpair_tpok[OF bok' wt1 wu1 ty1' tyu2 nfB bt1' bu2 f t2] by auto
        qed
        show ?thesis
          using fa ag02 agV02 mx12 extends_trans[OF fa(6) ext02] fl extends_trans[OF ext02] tps'
          by (intro exI[where x=env'] exI[where x=tps'] exI[where x=V2] exI[where x=\<sigma>2]) auto
      qed
      note run = clean_ffpair_run(3)[OF fb ok1 ok2]
      from ff_assign_complete[OF inv2 ty1' tyu2 nfB bok' wu1 bt1' bu2 ds2 h1 hn2, of alg]
      consider (a1) env3 where "okW (ff_assign alg env2 rb' t1 u1) env3" "cinv ar V2 \<tau>' \<sigma>2 env3 dps"
          "extends env3 env2" "maxidx env3 = maxidx env2"
          "\<forall>env0. flexb env0 env2 \<longrightarrow> extends env2 env0 \<longrightarrow> fh env0 u1 \<longrightarrow> flexb env0 env3"
        | (r1) "\<exists>evs. ff_assign alg env2 rb' t1 u1 = Some (evs, UErr ASSIGN)"
        by blast
      then show ?thesis
      proof cases
        case (a1 env3)
        show ?thesis by (rule fin[OF run[OF ff_handler_complete(1)[OF a1(1)]] a1(2) ts2 tb2 a1(4) a1(3) disjI1[OF refl]])
          (use a1(5) in blast)
      next
        case r1
        from ff_assign_complete[OF inv2 tyu2 ty1' nfB bok' wt1 bu2 bt1' dsolved_sym[OF ds2] hn2 h1, of alg]
        consider (a2) env3 where "okW (ff_assign alg env2 rb' u1 t1) env3" "cinv ar V2 \<tau>' \<sigma>2 env3 dps"
            "extends env3 env2" "maxidx env3 = maxidx env2"
            "\<forall>env0. flexb env0 env2 \<longrightarrow> extends env2 env0 \<longrightarrow> fh env0 t1 \<longrightarrow> flexb env0 env3"
          | (r2) "\<exists>evs. ff_assign alg env2 rb' u1 t1 = Some (evs, UErr ASSIGN)"
          by blast
        then show ?thesis
        proof cases
          case (a2 env3)
          show ?thesis by (rule fin[OF run[OF ff_handler_complete(2)[OF r1 a2(1)]] a2(2) ts2 tb2 a2(4) a2(3) disjI1[OF refl]])
            (use a2(5) in blast)
        next
          case r2
          show ?thesis
            by (rule fin[OF run[OF ff_handler_complete(3)[OF r1 r2]] inv2
              add_tpair_complete[OF ds2 ts2] add_tpair_below[OF bt1' bu2 tb2]]) auto
        qed
      qed
    qed
  qed
qed

lemma has_type_Abs_funT: "has_type V Ts t B \<Longrightarrow> is_Abs t \<Longrightarrow> is_funT B"
  by (cases t) (auto elim: has_type_elims)

text \<open>
  \<^const>\<open>add_ffpair\<close> on a solved flex-flex pair whose heads are unbound in an environment
  \<open>env0\<close> from which \<open>env\<close> only adds flexible bindings: the normalized heads remain variables.
\<close>

theorem add_ffpair_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env [(rb, t0, u0)]"
    and tyt: "has_type V (map snd rb) t0 B" and tyu: "has_type V (map snd rb) u0 B" and nfB: "\<not> is_funT B"
    and fht: "fh env0 t0" and fhu: "fh env0 u0" and fb: "flexb env0 env" and ext0: "extends env env0"
    and fr0: "fresh_env env0" and mx0: "maxidx env0 \<le> maxidx env"
    and ts: "tsolved \<sigma> tps" and tb: "\<forall>(a, b)\<in>set tps. below (maxidx env) a \<and> below (maxidx env) b"
  shows "\<exists>env' tps' V' \<sigma>'. okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps') \<and>
    cinv ar V' \<tau>' \<sigma>' env' [] \<and> tsolved \<sigma>' tps' \<and>
    (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) V V' \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
    flexb env0 env' \<and> ((\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab) \<longrightarrow>
      (\<forall>ab\<in>set tps'. tpok ar V' env0 (maxidx env') ab))"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note \<sigma> = solutionD[OF cinvD(2)[OF inv]]
  have dp: "wf_dp ar (rb, t0, u0)" "below (maxidx env) t0" "below (maxidx env) u0" "dsolved \<sigma> (rb, t0, u0)"
    using cinvD(3)[OF inv, of "(rb, t0, u0)"] by simp_all
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  have bok: "binders_ok ar rb" and wt0: "wf_tm ar rb t0" and wu0: "wf_tm ar rb u0" using dp(1) by simp_all
  from norm_term_term[OF ei(1-3) tyt] obtain t where nt: "norm_term env t0 = return t"
    and tyt': "has_type V (map snd rb) t B" and hnt: "\<forall>x U. head_of t = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
    and at: "is_Abs t \<or> fhd t = head_of t" and fht': "fh env0 t"
    using fb fht by blast
  from norm_term_term[OF ei(1-3) tyu] obtain u where nu: "norm_term env u0 = return u"
    and tyu': "has_type V (map snd rb) u B" and hnu: "\<forall>x U. head_of u = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
    and au: "is_Abs u \<or> fhd u = head_of u" and fhu': "fh env0 u"
    using fb fhu by blast
  have "\<not> is_Abs t" "\<not> is_Abs u" using has_type_Abs_funT tyt' tyu' nfB by blast+
  with at au fht' fhu' obtain v T w U where ht: "head_of t = Var v T" and hu: "head_of u = Var w U"
    by (auto simp: fh_def)
  have vn: "vt_lookup (tenv env) v = None" and wn: "vt_lookup (tenv env) w = None" using hnt hnu ht hu by blast+
  have okt: "ok (norm_term env t0) t" and oku: "ok (norm_term env u0) u" using nt nu by (simp_all add: return_def)
  note tn = norm_term_wf_tm[OF okt ei(2) wt0] and un = norm_term_wf_tm[OF oku ei(2) wu0]
  have wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u" using tn un by blast+
  have bt: "below (maxidx env) t" and bu: "below (maxidx env) u"
    using norm_term_below[OF nt e ei(4) dp(2)] norm_term_below[OF nu e ei(4) dp(3)] .
  have ds: "dsolved \<sigma> (rb, t, u)"
    by (rule dsolved_env_equiv[OF env_equiv_rlist_abs env_equiv_rlist_abs \<sigma>(1,4) dp(4)])
      (use tn un env_equiv_sym in blast)+
  have run: "okW (add_ffpair alg (rb, t0, u0) (env, tps)) r"
    if "okW (if v = w then
            (if T = U then returnW (env, add_tpair rb t u tps)
             else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
          else if indexname_less v w then clean_ffpair alg rb u t env tps
          else clean_ffpair alg rb t u env tps) r" for r
    using that nt nu ht hu by (auto simp: add_ffpair_def)
  have flex: "flexb env0 env' \<and> ((\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab) \<longrightarrow>
      (\<forall>ab\<in>set tps'. tpok ar V' env0 (maxidx env') ab))"
    if "\<forall>env0'. flexb env0' env \<longrightarrow> extends env env0' \<longrightarrow> fresh_env env0' \<longrightarrow> maxidx env0' \<le> maxidx env \<longrightarrow>
      flexb env0' env' \<and> ((\<forall>ab\<in>set tps. tpok ar V env0' (maxidx env) ab) \<longrightarrow>
        (\<forall>ab\<in>set tps'. tpok ar V' env0' (maxidx env') ab))" for env' tps' V'
    using that fb ext0 fr0 mx0 by blast
  have inv': "cinv ar V \<tau>' \<sigma> env []" by (rule cinv_Nil[OF inv])
  show ?thesis
  proof (cases "v = w")
    case True
    have "V v = T" "V w = U"
      using has_type_head_of[OF tyt'] has_type_head_of[OF tyu'] ht hu by (auto elim: has_type_elims)
    then have TU: "T = U" using True by simp
    have "okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env, add_tpair rb t u tps)"
      by (rule run) (simp add: True TU)
    moreover have "\<forall>ab\<in>set (add_tpair rb t u tps). tpok ar V env0 (maxidx env) ab"
      if "\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab"
      by (rule add_tpair_tpok[OF bok wt wu tyt' tyu' nfB bt bu fht' fhu' that])
    ultimately show ?thesis using inv' add_tpair_complete[OF ds ts] add_tpair_below[OF bt bu tb, of rb] fb
      by (intro exI[where x=env] exI[where x="add_tpair rb t u tps"] exI[where x=V] exI[where x=\<sigma>]) auto
  next
    case False
    show ?thesis
    proof (cases "indexname_less v w")
      case True
      from False have wv: "w \<noteq> v" by simp
      from clean_ffpair_complete[OF inv' tyu' tyt' nfB bok wu wt bu bt dsolved_sym[OF ds] hu wn ht vn wv ts tb,
        of alg]
      obtain env' tps' V' \<sigma>' where c: "okW (clean_ffpair alg rb u t env tps) (env', tps')"
        "cinv ar V' \<tau>' \<sigma>' env' []" "tsolved \<sigma>' tps'"
        "\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b"
        "agree (maxidx env) \<sigma> \<sigma>'" "agreeV (maxidx env) V V'" "maxidx env \<le> maxidx env'" "extends env' env"
        "\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
          flexb env0 env' \<and> ((\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab) \<longrightarrow>
            (\<forall>ab\<in>set tps'. tpok ar V' env0 (maxidx env') ab))"
        by blast
      have "okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps')"
        using c(1) False True by (intro run) simp
      then show ?thesis using c(2-8) flex[OF c(9)]
        by (intro exI[where x=env'] exI[where x=tps'] exI[where x=V'] exI[where x=\<sigma>']) auto
    next
      case nl: False
      from clean_ffpair_complete[OF inv' tyt' tyu' nfB bok wt wu bt bu ds ht vn hu wn False ts tb, of alg]
      obtain env' tps' V' \<sigma>' where c: "okW (clean_ffpair alg rb t u env tps) (env', tps')"
        "cinv ar V' \<tau>' \<sigma>' env' []" "tsolved \<sigma>' tps'"
        "\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b"
        "agree (maxidx env) \<sigma> \<sigma>'" "agreeV (maxidx env) V V'" "maxidx env \<le> maxidx env'" "extends env' env"
        "\<forall>env0. flexb env0 env \<longrightarrow> extends env env0 \<longrightarrow> fresh_env env0 \<longrightarrow> maxidx env0 \<le> maxidx env \<longrightarrow>
          flexb env0 env' \<and> ((\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab) \<longrightarrow>
            (\<forall>ab\<in>set tps'. tpok ar V' env0 (maxidx env') ab))"
        by blast
      have "okW (add_ffpair alg (rb, t0, u0) (env, tps)) (env', tps')"
        using c(1) False nl by (intro run) simp
      then show ?thesis using c(2-8) flex[OF c(9)]
        by (intro exI[where x=env'] exI[where x=tps'] exI[where x=V'] exI[where x=\<sigma>']) auto
    qed
  qed
qed

lemma dsolved_agree:
  "dsolved \<sigma> (rb, t, u) \<Longrightarrow> below m t \<Longrightarrow> below m u \<Longrightarrow> agree m \<sigma> \<sigma>' \<Longrightarrow> dsolved \<sigma>' (rb, t, u)"
  by (simp add: dsolved_dsolvedB dsolvedB_unabs mk_subst_agree)

lemma flexb_refl[simp]: "flexb env env"
  by (simp add: flexb_def)

text \<open>The flex-flex phase: all pairs are added in turn, starting with no remaining pairs.\<close>

theorem foldrW_add_ffpair_complete:
  assumes "cinv ar V \<tau>' \<sigma> env ffs" "\<forall>dp\<in>set ffs. ff_shape V dp \<and> heads_unb env dp"
  shows "\<exists>env' tps' V' \<sigma>'. okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps') \<and>
    cinv ar V' \<tau>' \<sigma>' env' [] \<and> tsolved \<sigma>' tps' \<and>
    (\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> agreeV (maxidx env) V V' \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
    flexb env env' \<and> (\<forall>ab\<in>set tps'. tpok ar V' env (maxidx env') ab)"
  using assms
proof (induction ffs)
  case Nil
  then show ?case
    by (intro exI[where x=env] exI[where x="[]"] exI[where x=V] exI[where x=\<sigma>])
      (auto simp: tsolved_def intro: cinv_Nil)
next
  case (Cons dp ffs)
  obtain rb t0 u0 where dp: "dp = (rb, t0, u0)" by (cases dp)
  have "cinv ar V \<tau>' \<sigma> env ffs" using Cons.prems(1) by (simp add: cinv_def)
  from Cons.IH[OF this] Cons.prems(2) obtain env1 tps1 V1 \<sigma>1 where
    f: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env1, tps1)" and inv1: "cinv ar V1 \<tau>' \<sigma>1 env1 []"
    and ts1: "tsolved \<sigma>1 tps1" and tb1: "\<forall>(a, b)\<in>set tps1. below (maxidx env1) a \<and> below (maxidx env1) b"
    and ag1: "agree (maxidx env) \<sigma> \<sigma>1" and agV1: "agreeV (maxidx env) V V1" and mx1: "maxidx env \<le> maxidx env1"
    and ext1: "extends env1 env" and fb1: "flexb env env1" and tp1: "\<forall>ab\<in>set tps1. tpok ar V1 env (maxidx env1) ab"
    by auto
  have c: "wf_dp ar dp" "below (maxidx env) t0" "below (maxidx env) u0" "dsolved \<sigma> dp"
    using cinvD(3)[OF Cons.prems(1), of dp] dp by simp_all
  from Cons.prems(2) dp obtain B where nfB: "\<not> is_funT B"
    and tyt: "has_type V (map snd rb) t0 B" and tyu: "has_type V (map snd rb) u0 B"
    and vt: "is_Var (head_of t0)" and vu: "is_Var (head_of u0)" and hn: "heads_unb env dp"
    by (auto simp: ff_shape_def)
  obtain x T y U where "head_of t0 = Var x T" "head_of u0 = Var y U"
    using vt vu by (cases "head_of t0"; cases "head_of u0") auto
  moreover note hn[unfolded dp heads_unb_def prod.case]
  ultimately have "vt_lookup (tenv env) x = None" "vt_lookup (tenv env) y = None" by blast+
  then have fht: "fh env t0" and fhu: "fh env u0"
    using \<open>head_of t0 = Var x T\<close> \<open>head_of u0 = Var y U\<close> fhd_head_of[OF vt] fhd_head_of[OF vu]
    by (auto simp: fh_def)
  have tyt1: "has_type V1 (map snd rb) t0 B" and tyu1: "has_type V1 (map snd rb) u0 B"
    using has_type_agreeV[OF tyt c(2) agV1] has_type_agreeV[OF tyu c(3) agV1] .
  have inv1': "cinv ar V1 \<tau>' \<sigma>1 env1 [(rb, t0, u0)]"
    using inv1 c dp tyt1 tyu1 below_mono[OF c(2) mx1] below_mono[OF c(3) mx1] dsolved_agree[OF _ c(2,3) ag1]
    by (auto simp: cinv_def)
  note fr = env_invD(4)[OF cinvD(1)[OF Cons.prems(1)]]
  from add_ffpair_complete[OF inv1' tyt1 tyu1 nfB fht fhu fb1 ext1 fr mx1 ts1 tb1, of alg]
  obtain env' tps' V' \<sigma>' where a: "okW (add_ffpair alg (rb, t0, u0) (env1, tps1)) (env', tps')"
    "cinv ar V' \<tau>' \<sigma>' env' []" "tsolved \<sigma>' tps'"
    "\<forall>(a, b)\<in>set tps'. below (maxidx env') a \<and> below (maxidx env') b"
    "agree (maxidx env1) \<sigma>1 \<sigma>'" "agreeV (maxidx env1) V1 V'" "maxidx env1 \<le> maxidx env'"
    "extends env' env1" "flexb env env'" "\<forall>ab\<in>set tps'. tpok ar V' env (maxidx env') ab"
    using tp1 by blast
  have "okW (foldrW (add_ffpair alg) (dp # ffs) (env, [])) (env', tps')"
    using f a(1) dp by auto
  then show ?case using a(2-4,9,10) agree_trans[OF ag1 a(5) mx1] agreeV_trans[OF agV1 a(6) mx1] mx1 a(7)
      extends_trans[OF a(8) ext1]
    by (intro exI[where x=env'] exI[where x=tps'] exI[where x=V'] exI[where x=\<sigma>']) auto
qed

end

end
