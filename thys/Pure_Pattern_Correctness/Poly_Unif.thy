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

lemma proj_tys:
  "proj s env bs is = Some (Ok (t', e')) \<Longrightarrow> \<forall>T\<in>tys s \<union> etys env \<union> snd ` set bs. P T \<Longrightarrow>
    tyclosed P (tyenv env) \<Longrightarrow> (\<forall>T\<in>tys t' \<union> etys e'. P T) \<and> tyenv e' = tyenv env"
  unfolding proj_def using pr_tys[of "is" s env 0 bs _ t' e' P] by (auto simp: return_def split: if_splits)

lemma flexrigid_tys:
  assumes "flexrigid env bs F Fty is t = Some (Ok e')" "P Fty" "\<forall>T\<in>tys t \<union> etys env \<union> snd ` set bs. P T"
    "tyclosed P (tyenv env)"
  shows "(\<forall>T\<in>etys e'. P T) \<and> tyenv e' = tyenv env"
proof -
  from assms(1) obtain u env1 u' where p: "proj t env bs is = Some (Ok (u, env1))"
    and m: "mkabs bs is u = Some (Ok u')" and up: "update (F, Fty) u' env1 = Some (Ok e')"
    unfolding flexrigid_def
    by (auto simp: bindM_def return_def raise_def handle_def
        split: option.splits res.splits prod.splits if_splits exn.splits)
  from proj_tys[OF p assms(3,4)] have "\<forall>T\<in>tys u \<union> etys env1. P T" "tyenv env1 = tyenv env" by auto
  with etys_update[OF up] tys_mkabs[OF m] assms(2,3) ok_update(3)[OF up] show ?thesis by (simp; blast)
qed

lemma mk_new_hnf_tys:
  assumes "mk_new_hnf env bs is F Fty js = Some (Ok e')" "P Fty" "\<forall>T\<in>etys env \<union> snd ` set bs. P T"
    "tyclosed P (tyenv env)"
  shows "(\<forall>T\<in>etys e'. P T) \<and> tyenv e' = tyenv env"
proof -
  from assms(1) obtain Gty env1 G t where Gty: "type_of_G env Fty (ilength is) js = Some (Ok Gty)"
    and g: "genvar (fst F) env Gty = (env1, G)" and t: "mk_hnf bs is G js = Some (Ok t)"
    and up: "update (F, Fty) t env1 = Some (Ok e')"
    unfolding mk_new_hnf_def Let_def
    by (auto simp: bindM_def split: option.splits res.splits prod.splits)
  have PG: "P Gty" by (rule tyclosedD[OF assms(4,2) Gty])
  have "tys t \<subseteq> {Gty} \<union> snd ` set bs"
    using tys_mkabs[of bs "is" "app G js" t] t genvar_simps(4)[OF g] by (auto simp: mk_hnf_def)
  with etys_update[OF up] etys_genvar[OF g] have "etys e' \<subseteq> {Fty, Gty} \<union> etys env \<union> snd ` set bs"
    by blast
  with PG assms(2,3) genvar_simps(2)[OF g] ok_update(3)[OF up] show ?thesis by auto
qed

lemma flexflex1_tys:
  "flexflex1 env bs F Fty is js = Some (Ok e') \<Longrightarrow> P Fty \<Longrightarrow> \<forall>T\<in>etys env \<union> snd ` set bs. P T \<Longrightarrow>
    tyclosed P (tyenv env) \<Longrightarrow> (\<forall>T\<in>etys e'. P T) \<and> tyenv e' = tyenv env"
  unfolding flexflex1_def using mk_new_hnf_tys[of env bs "is" F Fty _ e' P]
  by (auto simp: return_def bindM_def split: if_splits option.splits res.splits)

lemma ff_tys:
  assumes "ff env bs F Fty is G Gty js = Some (Ok e')" "P Fty" "P Gty" "\<forall>T\<in>etys env \<union> snd ` set bs. P T"
    "tyclosed P (tyenv env)"
  shows "(\<forall>T\<in>etys e'. P T) \<and> tyenv e' = tyenv env"
proof (cases "subset js is")
  case True
  with assms(1) obtain ks t where m: "mkabs bs is (app (Var G Gty) ks) = Some (Ok t)"
    and up: "update (F, Fty) t env = Some (Ok e')"
    unfolding ff_def by (auto simp: bindM_def split: option.splits res.splits)
  from etys_update[OF up] tys_mkabs[OF m] assms(2-4) ok_update(3)[OF up] show ?thesis by (simp; blast)
next
  case False
  with assms(1) obtain ks' Hty env1 H tG tF env2 where
    Hty: "type_of_G env Fty (ilength is) ks' = Some (Ok Hty)"
    and g: "genvar (fst G) env Hty = (env1, H)"
    and tG: "(mapM (idx js) (inter js is) \<bind> (\<lambda>ks'. mkabs bs js (app H ks'))) = Some (Ok tG)"
    and tF: "(mapM (idx is) (inter js is) \<bind> (\<lambda>ks'. mkabs bs is (app H ks'))) = Some (Ok tF)"
    and u1: "update (F, Fty) tF env1 = Some (Ok env2)" and u2: "update (G, Gty) tG env2 = Some (Ok e')"
    unfolding ff_def Let_def by (auto simp: bindM_def split: option.splits res.splits prod.splits)
  have PH: "P Hty" by (rule tyclosedD[OF assms(5,2) Hty])
  have H: "H = Var (fst G, maxidx env + 1) Hty" by (rule genvar_simps(4)[OF g])
  from tG obtain k1 where "mkabs bs js (app H k1) = Some (Ok tG)"
    by (auto simp: bindM_def split: option.splits res.splits)
  from tys_mkabs[OF this] H have ttG: "tys tG \<subseteq> {Hty} \<union> snd ` set bs" by auto
  from tF obtain k2 where "mkabs bs is (app H k2) = Some (Ok tF)"
    by (auto simp: bindM_def split: option.splits res.splits)
  from tys_mkabs[OF this] H have ttF: "tys tF \<subseteq> {Hty} \<union> snd ` set bs" by auto
  from etys_update[OF u2] etys_update[OF u1] etys_genvar[OF g] ttG ttF PH assms(2-4)
    genvar_simps(2)[OF g] ok_update(3)[OF u1] ok_update(3)[OF u2]
  show ?thesis by (simp; blast)
qed

lemma flexflex2_tys:
  "flexflex2 env bs F Fty is G Gty js = Some (Ok e') \<Longrightarrow> P Fty \<Longrightarrow> P Gty \<Longrightarrow>
    \<forall>T\<in>etys env \<union> snd ` set bs. P T \<Longrightarrow> tyclosed P (tyenv env) \<Longrightarrow>
    (\<forall>T\<in>etys e'. P T) \<and> tyenv e' = tyenv env"
  unfolding flexflex2_def
  using ff_tys[of env bs F Fty "is" G Gty js e' P] ff_tys[of env bs G Gty js F Fty "is" e' P]
  by (cases "indexname_less G F") simp_all


subsection \<open>Well-formed types of problems\<close>

text \<open>
  The types of a problem are well-formed and their type variables are known to the type invariant
  \<^const>\<open>tinv\<close> (with the set \<open>A\<close> of type variables of the initial problem).
\<close>

definition tyw :: "(name \<Rightarrow> nat) \<Rightarrow> tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tyw ar \<theta> A T \<longleftrightarrow> tvars T \<subseteq> tvars_env \<theta> \<union> A \<and> wft ar T"

lemma tvars_env_textends: "textends \<theta> \<theta>' \<Longrightarrow> tvars_env \<theta> \<subseteq> tvars_env \<theta>'"
  unfolding tvars_env_def textends_def by blast

lemma tyw_textends: "textends \<theta> \<theta>' \<Longrightarrow> tyw ar \<theta> A T \<Longrightarrow> tyw ar \<theta>' A T"
  using tvars_env_textends by (fastforce simp: tyw_def)

lemma tyw_tcons: "tinv ar n \<theta> A \<Longrightarrow> tyw ar \<theta> A T \<Longrightarrow> tcons \<theta> T"
  by (simp add: tyw_def tinv_tcons)

lemma split_type_wft:
  "split_type T n Ts = Some (Ok (Ts', U)) \<Longrightarrow> wft ar T \<Longrightarrow> \<forall>X\<in>set Ts. wft ar X \<Longrightarrow>
    (\<forall>X\<in>set Ts'. wft ar X) \<and> wft ar U"
proof (induction T n Ts rule: split_type.induct)
  case (1 T n Ts)
  from "1.prems" show ?case
    by (subst (asm) split_type.simps)
      (use "1.IH" in \<open>fastforce simp: return_def raise_def split: if_splits ptyp.splits list.splits\<close>)
qed

lemma wft_foldr_fun: "wft ar (foldr fun_type Us U) \<longleftrightarrow> (\<forall>X\<in>set Us. wft ar X) \<and> wft ar U"
  by (induction Us) (auto simp: tarity_def)

lemma tyclosed_tyw: "tinv ar n \<theta> A \<Longrightarrow> tyclosed (tyw ar \<theta> A) \<theta>"
  unfolding tyclosed_def
proof (intro allI impI)
  fix e T m "is" G
  assume inv: "tinv ar n \<theta> A" and e: "tyenv e = \<theta>" and T: "tyw ar \<theta> A T"
    and G: "type_of_G e T m is = Some (Ok G)"
  have ac: "tacyc \<theta>" and tce: "tcons_env \<theta>" using inv by (simp_all add: tinv_tacyc tinv_tcons_env)
  have tc: "tcons \<theta> T" by (rule tyw_tcons[OF inv T])
  have ok: "tyok e" using ac tce e by (simp add: tyok_def)
  have "tvars G \<subseteq> tvars (tnorm \<theta> T)" using type_of_G_tvars[OF G ok] tc e by simp
  also have "\<dots> \<subseteq> tvars T \<union> tvars_env \<theta>" by (rule tvars_tnorm[OF ac])
  finally have tv: "tvars G \<subseteq> tvars_env \<theta> \<union> A" using T by (auto simp: tyw_def)
  from G obtain Ts U Us where st: "split_type (tnorm \<theta> T) m [] = Some (Ok (Ts, U))"
    and ms: "mapM (nth Ts) is = Some (Ok Us)" and GU: "G = foldr fun_type Us U"
    using e by (auto simp: type_of_G_def norm_type_ok[OF ac tce tc] bindM_def return_def
        split: option.splits res.splits prod.splits)
  have "wft ar (tnorm \<theta> T)" using T by (intro wft_tnorm[OF ac]) (auto simp: tyw_def intro: tinv_wft[OF inv])
  from split_type_wft[OF st this] mapM_nth_set[OF ms] have "wft ar G" by (auto simp: GU wft_foldr_fun)
  with tv show "tyw ar \<theta> A G" by (simp add: tyw_def)
qed


subsection \<open>Ground solutions\<close>

text \<open>
  The instances of a polymorphic problem are given by ground well-sorted solutions of its type
  environment.
\<close>

definition gsol :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> tyenv \<Rightarrow> tinst \<Rightarrow> bool" where
  "gsol alg ar \<theta> \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> tsol \<theta> \<rho> \<and> (\<forall>v S. ground ar (\<rho> v S))"

lemma ground_iff: "ground ar T \<longleftrightarrow> wft ar T \<and> tvars T = {}"
  by (induction T) (auto simp: tarity_def)

lemma ground_tsubst: "wft ar T \<Longrightarrow> (\<forall>v S. ground ar (\<rho> v S)) \<Longrightarrow> ground ar (tsubst \<rho> T)"
  by (induction T) (auto simp: tarity_def)

lemma gsol_textends: "textends \<theta> \<theta>' \<Longrightarrow> gsol alg ar \<theta>' \<rho> \<Longrightarrow> gsol alg ar \<theta> \<rho>"
  by (auto simp: gsol_def intro: tsol_textends)

text \<open>Turning a solution into a ground one with well-formed values.\<close>

fun clean :: "(name \<Rightarrow> nat) \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "clean ar (Type a Ts) = (if length Ts = tarity ar a then Type a (map (clean ar) Ts) else TFree STR '''' [])"
| "clean ar T = T"

lemma wft_clean: "wft ar (clean ar T)"
  by (induction T) auto

lemma tvars_clean: "tvars (clean ar T) \<subseteq> tvars T"
  by (induction T) auto

lemma clean_wft: "wft ar T \<Longrightarrow> clean ar T = T"
  by (induction T) (auto simp: map_idI)

lemma clean_tsubst: "wft ar U \<Longrightarrow> clean ar (tsubst \<rho> U) = tsubst (\<lambda>v S. clean ar (\<rho> v S)) U"
  by (induction U) auto

lemma tsubst_ground: "tvars T = {} \<Longrightarrow> tsubst \<rho> T = T"
  using tsubst_cong[of T \<rho> TVar] by simp

context wf_algebra
begin

lemma has_sort_clean: "has_sort alg T S \<Longrightarrow> has_sort alg (clean ar T) S"
proof (induction T arbitrary: S)
  case (Type a Ts)
  show ?case
  proof (cases "length Ts = tarity ar a")
    case True
    with Type show ?thesis by (fastforce dest: nth_mem)
  next
    case False
    have "S = []"
    proof (rule ccontr)
      assume "S \<noteq> []"
      then obtain c where "c \<in> set S" by (cases S) auto
      with Type.prems obtain Ss where "map_of (arities alg a) c = Some Ss" "length Ss = length Ts" by auto
      with arity_length False show False by simp
    qed
    then show ?thesis by simp
  qed
qed auto

lemma gsol_tstep:
  assumes ws: "wsinst alg \<rho>'" and sol: "tsol \<theta>' \<rho>'" and inv: "tinv ar n' \<theta>' A"
    and gr: "\<forall>v S. ground ar (\<rho> v S)" and ag: "tagree n \<rho> \<rho>'"
  obtains \<rho>'' where "gsol alg ar \<theta>' \<rho>''" "tagree n \<rho> \<rho>''"
proof -
  define \<rho>0 :: tinst where "\<rho>0 = (\<lambda>w S. TFree STR ''a'' S)"
  define \<rho>1 where "\<rho>1 = (\<lambda>v S. clean ar (tsubst \<rho>0 (\<rho>' v S)))"
  have g0: "tvars (tsubst \<rho>0 T) = {}" for T by (simp add: tvars_tsubst \<rho>0_def)
  have "wsinst alg \<rho>1"
    unfolding wsinst_def \<rho>1_def
  proof (intro allI has_sort_clean has_sort_tsubst)
    fix v S
    show "has_sort alg (\<rho>' v S) S" using ws unfolding wsinst_def by blast
    show "\<forall>(w, S')\<in>tvars (\<rho>' v S). has_sort alg (\<rho>0 w S') S'"
      by (auto simp: \<rho>0_def has_sort_TFree_iff simp del: has_sort.simps)
  qed
  moreover have "tsol \<theta>' \<rho>1"
    unfolding tsol_def
  proof (intro allI impI)
    fix v S U assume b: "vt_lookup \<theta>' v = Some (S, U)"
    have "\<rho>' v S = tsubst \<rho>' U" using sol b unfolding tsol_def by blast
    then show "\<rho>1 v S = tsubst \<rho>1 U"
      by (simp add: \<rho>1_def tsubst_tsubst clean_tsubst[OF tinv_wft[OF inv b]])
  qed
  moreover have "ground ar (\<rho>1 v S)" for v S
    using wft_clean tvars_clean[of ar "tsubst \<rho>0 (\<rho>' v S)"] g0 by (auto simp: \<rho>1_def ground_iff)
  moreover have "tagree n \<rho> \<rho>1"
    unfolding tagree_def
  proof (intro allI impI)
    fix v :: indexname and S assume "snd v \<le> n"
    then have "\<rho>' v S = \<rho> v S" using ag unfolding tagree_def by blast
    moreover have "wft ar (\<rho> v S)" "tvars (\<rho> v S) = {}" using gr[rule_format, of v S] by (simp_all add: ground_iff)
    ultimately show "\<rho>1 v S = \<rho> v S" by (simp add: \<rho>1_def tsubst_ground clean_wft)
  qed
  ultimately show ?thesis using that by (auto simp: gsol_def)
qed

end

end
