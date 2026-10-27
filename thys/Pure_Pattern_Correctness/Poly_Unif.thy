section \<open>Polymorphic Unification Problems\<close>

theory Poly_Unif
  imports Poly_Inst
begin

subsection \<open>Types occurring in terms\<close>

fun tys :: "pterm \<Rightarrow> ptyp set" where
  "tys (Const _ T) = {T}"
| "tys (Free _ T) = {T}"
| "tys (Var _ T) = {T}"
| "tys (Bound _) = {}"
| "tys (Abs _ T t) = insert T (tys t)"
| "tys (s $ t) = tys s \<union> tys t"

definition etys :: "env \<Rightarrow> ptyp set" where
  "etys env = {T. \<exists>x U u. vt_lookup (tenv env) x = Some (U, u) \<and> (T = U \<or> T \<in> tys u)}"

lemma etysI: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> insert U (tys u) \<subseteq> etys env"
  unfolding etys_def by blast

lemma tys_incr_bv[simp]: "tys (incr_bv i l t) = tys t"
  by (induction i l t rule: incr_bv.induct) auto

lemma tys_incr_aux[simp]: "tys (incr_aux d t) = tys t"
  by (induction d t rule: incr_aux.induct) auto

lemma tys_incr[simp]: "tys (incr t) = tys t"
  by (simp add: incr_def)

lemma tys_subst_bound: "tys (subst_bound arg t) \<subseteq> tys arg \<union> tys t"
proof -
  have "tys (subst_bound_aux arg l t) \<subseteq> tys arg \<union> tys t" for l
    by (induction arg l t rule: subst_bound_aux.induct) (auto simp: incr_boundvars_def)
  then show ?thesis by (simp add: subst_bound_def)
qed

lemma tys_list_comb: "tys (list_comb h ts) = tys h \<union> (\<Union>t\<in>set ts. tys t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma tys_app[simp]: "tys (app h is) = tys h"
  by (induction "is" arbitrary: h) (auto simp: app_def)

lemma tys_strip_comb: "strip_comb s = (h, ts) \<Longrightarrow> tys s = tys h \<union> (\<Union>t\<in>set ts. tys t)"
  using strip_comb_list_comb tys_list_comb by metis

lemma tys_mkabs: "mkabs bs is t = Some (Ok u) \<Longrightarrow> tys u \<subseteq> tys t \<union> snd ` set bs"
proof (induction "is" arbitrary: u)
  case (Cons i "is")
  from Cons.prems obtain a T u0 where n: "nth bs i = Some (Ok (a, T))"
    and m: "mkabs bs is t = Some (Ok u0)" and u: "u = Abs a T u0"
    by (auto simp: bindM_def return_def split: option.splits res.splits prod.splits)
  have "(a, T) \<in> set bs" using n by (auto simp: ok_nth)
  then have "T \<in> snd ` set bs" by force
  with Cons.IH[OF m] u show ?case by auto
qed (simp add: return_def)

lemma tys_inst: "tys (inst \<rho> t) = tsubst \<rho> ` tys t"
  by (induction t) auto

lemma etys_instE: "etys (instE \<rho> env) = tsubst \<rho> ` etys env"
proof (intro equalityI subsetI)
  fix T assume "T \<in> etys (instE \<rho> env)"
  then obtain x U u where "vt_lookup (tenv env) x = Some (U, u)" "T = tsubst \<rho> U \<or> T \<in> tys (inst \<rho> u)"
    unfolding etys_def by auto
  then show "T \<in> tsubst \<rho> ` etys env" using etysI[of env x U u] by (auto simp: tys_inst)
next
  fix T assume "T \<in> tsubst \<rho> ` etys env"
  then obtain T0 x U u where "T = tsubst \<rho> T0" "vt_lookup (tenv env) x = Some (U, u)" "T0 = U \<or> T0 \<in> tys u"
    unfolding etys_def by blast
  then show "T \<in> etys (instE \<rho> env)" using etysI[of "instE \<rho> env" x "tsubst \<rho> U" "inst \<rho> u"]
    by (auto simp: tys_inst)
qed

lemma head_norm_tys:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> tys t' \<subseteq> tys t \<union> etys env"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  show ?case
  proof (cases t)
    case (Var xi T)
    from "1.hyps" Var obtain lr where lr: "lookup env xi T = Some lr"
      by (cases "lookup env xi T") (auto simp: bindM_def)
    show ?thesis
    proof (cases lr)
      case (Ok ro)
      show ?thesis
      proof (cases ro)
        case None
        then show ?thesis using "1.hyps" "1.prems" Var lr Ok by (auto simp: return_def)
      next
        case (Some u)
        from lr Ok Some obtain U where b: "vt_lookup (tenv env) xi = Some (U, u)"
          using lookup_SomeD by blast
        from "1.hyps" Var lr Ok Some have hu: "hn env u = Some r" by simp
        from "1.IH"[OF hu "1.prems"] etysI[OF b] show ?thesis by auto
      qed
    next
      case (Err e)
      then show ?thesis using "1.hyps" "1.prems" Var lr by auto
    qed
  next
    case (Abs a T body)
    from "1.hyps" Abs obtain rb where hb: "hn env body = Some rb"
      by (cases "hn env body") (auto simp: bindM_def)
    with "1.hyps" "1.prems" Abs obtain b where "rb = Ok b" "t' = Abs a T b"
      by (cases rb) (auto simp: bindM_def return_def)
    with "1.IH"[OF hb] Abs show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = Abs a T body" by (cases f) auto
      from "1.hyps" App f have h: "hn env (subst_bound u body) = Some r" by simp
      from "1.IH"[OF h "1.prems"] tys_subst_bound[of u body] App f show ?thesis by auto
    next
      case False
      have h: "bindM (hn env f) (\<lambda>nf. case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) = Some r"
        using "1.hyps" App False by (cases f) auto
      then obtain rf where hf: "hn env f = Some rf" by (cases "hn env f") (auto simp: bindM_def)
      from h hf "1.prems" obtain nf where rf: "rf = Ok nf" by (cases rf) auto
      note IHf = "1.IH"[OF hf rf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nf: "nf = Abs a T body" by (cases nf) auto
        from h hf rf nf have h2: "hn env (subst_bound u body) = Some r" by simp
        from "1.IH"[OF h2 "1.prems"] tys_subst_bound[of u body] IHf nf App show ?thesis by auto
      next
        case nA: False
        from h hf rf nA "1.prems" have "t' = nf $ u" by (cases nf) (auto simp: return_def)
        with IHf App show ?thesis by auto
      qed
    qed
  qed (use "1.hyps" "1.prems" in \<open>auto simp: return_def\<close>)
qed

lemma etys_genvar: "genvar a env T = (env', G) \<Longrightarrow> etys env' = etys env"
  by (simp add: etys_def genvar_simps)

lemma etys_update: "update (F, T) t env = Some (Ok env') \<Longrightarrow> etys env' \<subseteq> insert T (tys t \<union> etys env)"
  using ok_update[of F T t env env'] by (auto simp: etys_def)

text \<open>
  A property \<open>P\<close> of the types of a problem is preserved by the unification steps if it is closed
  under the construction of the types of new variables.
\<close>

definition tyclosed :: "(ptyp \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> bool" where
  "tyclosed P \<theta> \<longleftrightarrow> (\<forall>e T n is G. tyenv e = \<theta> \<longrightarrow> P T \<longrightarrow> type_of_G e T n is = Some (Ok G) \<longrightarrow> P G)"

lemma tyclosedD: "tyclosed P (tyenv e) \<Longrightarrow> P T \<Longrightarrow> type_of_G e T n is = Some (Ok G) \<Longrightarrow> P G"
  unfolding tyclosed_def by blast

lemma prvar_tys:
  assumes "prvar xs d bs env F Fty ts = Some (Ok (t', e'))" "P Fty" "\<forall>T\<in>etys env \<union> snd ` set bs. P T"
    "tyclosed P (tyenv env)"
  shows "(\<forall>T\<in>tys t' \<union> etys e'. P T) \<and> tyenv e' = tyenv env"
proof -
  from assms(1) obtain js js' Hty env1 H t where
    Hty: "type_of_G env Fty (ilength js) (mk_proj_list js') = Some (Ok Hty)"
    and g: "genvar (fst F) env Hty = (env1, H)" and t: "mk_hnf bs js H (mk_proj_list js') = Some (Ok t)"
    and u: "update (F, Fty) t env1 = Some (Ok e')" and t': "t' = app H (List.map_filter id js')"
    unfolding prvar_def Let_def
    by (auto simp: bindM_def return_def split: option.splits res.splits prod.splits)
  have PH: "P Hty" by (rule tyclosedD[OF assms(4,2) Hty])
  have H: "H = Var (fst F, maxidx env + 1) Hty" by (rule genvar_simps(4)[OF g])
  have "tys t \<subseteq> {Hty} \<union> snd ` set bs" using tys_mkabs[of bs js "app H (mk_proj_list js')" t] t H
    by (auto simp: mk_hnf_def)
  then show ?thesis
    using etys_update[OF u] etys_genvar[OF g] PH assms(2,3) t' H genvar_simps(2)[OF g] ok_update(3)[OF u]
    by (simp; blast)
qed

lemma mapAccM_tys:
  assumes "mapAccM g ts env = Some (Ok (ts', e'))"
    and "\<And>s env t' e'. s \<in> set ts \<Longrightarrow> g s env = Some (Ok (t', e')) \<Longrightarrow> \<forall>T\<in>tys s \<union> etys env. P T \<Longrightarrow>
      tyenv env = \<theta> \<Longrightarrow> (\<forall>T\<in>tys t' \<union> etys e'. P T) \<and> tyenv e' = \<theta>"
    and "\<forall>T\<in>(\<Union>t\<in>set ts. tys t) \<union> etys env. P T" "tyenv env = \<theta>"
  shows "(\<forall>T\<in>(\<Union>t\<in>set ts'. tys t) \<union> etys e'. P T) \<and> tyenv e' = \<theta>"
  using assms
proof (induction ts arbitrary: env ts')
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons s ts)
  from Cons.prems(1) obtain t1 e1 ys where g: "g s env = Some (Ok (t1, e1))"
    and m: "mapAccM g ts e1 = Some (Ok (ys, e'))" and ts': "ts' = t1 # ys"
    by (auto simp: bindM_def return_def split: option.splits res.splits prod.splits)
  from Cons.prems(2)[OF _ g] Cons.prems(3,4) have e1: "\<forall>T\<in>tys t1 \<union> etys e1. P T" "tyenv e1 = \<theta>"
    by auto
  have "(\<forall>T\<in>(\<Union>t\<in>set ys. tys t) \<union> etys e'. P T) \<and> tyenv e' = \<theta>"
    by (rule Cons.IH[OF m Cons.prems(2)]) (use Cons.prems(3) e1 in auto)
  with e1 ts' show ?case by auto
qed

lemma pr_tys:
  assumes "pr xs s env d bs = Some r"
  shows "r = Ok (t', e') \<Longrightarrow> \<forall>T\<in>tys s \<union> etys env \<union> snd ` set bs. P T \<Longrightarrow> tyclosed P (tyenv env) \<Longrightarrow>
    (\<forall>T\<in>tys t' \<union> etys e'. P T) \<and> tyenv e' = tyenv env"
  using assms
proof (induction xs s env d bs r arbitrary: t' e' rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d bs r)
  note P = "1.prems"(2) and cl = "1.prems"(3)
  have hr: "head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs) = Some r"
    unfolding pr_step_def prvar_def by (rule "1.hyps")
  with "1.prems"(1) obtain s0 where hn: "head_norm env s = Some (Ok s0)"
    and st: "pr_step prr xs s0 env d bs = Some (Ok (t', e'))"
    by (cases "head_norm env s") (auto simp: bindM_def split: res.splits)
  have P0: "\<forall>T\<in>tys s0 \<union> etys env \<union> snd ` set bs. P T" using head_norm_tys[OF hn refl] P by blast
  show ?case
  proof (cases "is_Abs s0")
    case True
    then obtain a T u where s0: "s0 = Abs a T u" by (cases s0) auto
    from st s0 obtain u' where r1: "prr xs u env (d + 1) ((a, T) # bs) = Some (Ok (u', e'))"
      and t': "t' = Abs a T u'"
      by (auto simp: pr_step_def bindM_def return_def split: option.splits res.splits prod.splits)
    have "\<forall>T'\<in>tys u \<union> etys env \<union> snd ` set ((a, T) # bs). P T'" using P0 s0 by auto
    from "1.IH"[OF r1 refl this cl] P0 s0 t' show ?thesis by auto
  next
    case False
    obtain hd ts where sc: "strip_comb s0 = (hd, ts)" by force
    note ts0 = tys_strip_comb[OF sc]
    show ?thesis
    proof (cases "is_Var hd")
      case True
      then obtain F Fty where hd: "hd = Var F Fty" by (cases hd) auto
      from st False sc hd have "prvar xs d bs env F Fty ts = Some (Ok (t', e'))"
        by (simp add: pr_step_def)
      from prvar_tys[OF this _ _ cl] P0 ts0 hd show ?thesis by auto
    next
      case nV: False
      show ?thesis
      proof (cases "is_Abs hd")
        case True
        with st False sc nV show ?thesis by (simp add: pr_step_def raise_def)
      next
        case nA: False
        define hm where "hm = (\<lambda>h. case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h)"
        have "pr_step prr xs s0 env d bs = hm hd \<bind>
            (\<lambda>h'. mapAccM (\<lambda>s env. prr xs s env d bs) ts env \<bind> (\<lambda>(ts', env'). return (list_comb h' ts', env')))"
          using False sc nV nA by (simp add: pr_step_def hm_def)
        with st obtain h' ts' where hh: "hm hd = Some (Ok h')"
          and m: "mapAccM (\<lambda>s env. prr xs s env d bs) ts env = Some (Ok (ts', e'))"
          and t': "t' = list_comb h' ts'"
          by (auto simp: bindM_def return_def split: option.splits res.splits prod.splits)
        have th: "tys h' \<subseteq> tys hd"
          using hh by (cases hd) (auto simp: hm_def trans_def bindM_def return_def split: option.splits res.splits)
        have "(\<forall>T\<in>(\<Union>t\<in>set ts'. tys t) \<union> etys e'. P T) \<and> tyenv e' = tyenv env"
        proof (rule mapAccM_tys[OF m])
          fix u e t'' e'' assume r: "prr xs u e d bs = Some (Ok (t'', e''))"
            and Pu: "\<forall>T\<in>tys u \<union> etys e. P T" and e: "tyenv e = tyenv env"
          have "\<forall>T\<in>tys u \<union> etys e \<union> snd ` set bs. P T" using Pu P0 by blast
          from "1.IH"[OF r refl this] cl e
          show "(\<forall>T\<in>tys t'' \<union> etys e''. P T) \<and> tyenv e'' = tyenv env" by simp
        qed (use P0 ts0 in auto)
        with th P0 ts0 t' show ?thesis by (auto simp: tys_list_comb)
      qed
    qed
  qed
qed

end
