section \<open>Consistency\<close>

theory Thm_Consistency
  imports Thm_Type
begin

text \<open>
  The theorems of a signature hold in its models. So no theorem without hypotheses and flex-flex
  pairs, whose sort hypotheses are inhabited, proves \<open>\<And>P. P\<close> in a signature that has a model;
  the theory \<open>Thm_Model_ZFC\<close> gives one for every signature whose axioms are the equality axioms of
  \<open>Pure\<close>, which hold in every model that interprets \<open>Pure.eq\<close> as equality.
\<close>


subsection \<open>Good valuations exist\<close>

context pure_model
begin

definition pick_set :: "psort \<Rightarrow> 'u" where
  "pick_set S = (SOME A. une A \<and> (sort_ok alg S \<longrightarrow> sinh S \<longrightarrow> ssem S A))"

lemma pick_set: "une (pick_set S) \<and> (sort_ok alg S \<longrightarrow> sinh S \<longrightarrow> ssem S (pick_set S))"
proof -
  have "\<exists>A. une A \<and> (sort_ok alg S \<longrightarrow> sinh S \<longrightarrow> ssem S A)"
  proof (cases "sinh S")
    case True
    then show ?thesis by (auto simp: sinh_def)
  next
    case False
    then show ?thesis using une_ubool by blast
  qed
  then show ?thesis unfolding pick_set_def by (rule someI_ex)
qed

definition eta0 :: "'u tval" where
  "eta0 = (\<lambda>v S. pick_set S, \<lambda>a S. pick_set S)"

definition xi0 :: "'u vval" where
  "xi0 = (\<lambda>x T. SOME a. a \<in>\<^sub>u tsem eta0 T, \<lambda>x T. SOME a. a \<in>\<^sub>u tsem eta0 T)"

lemma good_t_eta0: "good_t eta0"
  using pick_set by (simp add: good_t_def eta0_def)

lemma good_eta0_xi0: "good eta0 xi0"
proof -
  have "(SOME a. a \<in>\<^sub>u tsem eta0 T) \<in>\<^sub>u tsem eta0 T" for T
    using tsem_ne[OF good_t_eta0, of T] by (auto simp: une_def intro: someI)
  then show ?thesis using good_t_eta0 by (simp add: good_def good_v_def xi0_def)
qed

lemma good_ex: "\<exists>\<eta> \<xi>. good \<eta> \<xi>"
  using good_eta0_xi0 by blast


subsection \<open>Truth of theorems\<close>

text \<open>A valid proposition without hypotheses and flex-flex pairs holds under every good valuation:\<close>

lemma valid_holds:
  assumes "valid Sh [] [] P" "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" "good \<eta> \<xi>"
  shows "holds_at \<eta> \<xi> P"
proof -
  have gs: "gsubst (\<lambda>x T. Var x T)" using wt_subst_Var by (simp add: gsubst_def)
  have "holds_at \<eta> \<xi> (ap TVar (\<lambda>x T. Var x T) P)"
    by (rule validD[OF assms(1) assms(2) assms(3) cinst_TVar inh_inst_TVar gs]) simp_all
  then show ?thesis by (simp add: ap_Var)
qed

text \<open>\<open>\<And>P. P\<close> holds under no valuation:\<close>

lemma not_holds_all_prop: "\<not> holds_at \<eta> \<xi> (all_const propT $ Abs x propT (Bound 0))"
proof -
  have tp: "tsem \<eta> propT = ubool" by (simp add: propT_def)
  have "sem \<eta> \<xi> (\<lambda>_. utrue) (all_const propT $ Abs x propT (Bound 0)) =
      ubval (\<forall>v. v \<in>\<^sub>u ubool \<longrightarrow> v = utrue)"
    by (subst sem_all) (simp_all add: tp push_def)
  moreover have "\<not> (\<forall>v. v \<in>\<^sub>u ubool \<longrightarrow> v = utrue)"
    using ubool_mem utrue_ufalse by blast
  ultimately show ?thesis by (simp add: holds_at_def)
qed

end


subsection \<open>No proof of \<open>\<And>P. P\<close>\<close>

text \<open>A sort is inhabited in a model (\<^const>\<open>pure_model.sinh\<close>):\<close>

definition m_sinh :: "'u model \<Rightarrow> psort \<Rightarrow> bool" where
  "m_sinh M S \<longleftrightarrow> (\<exists>A. (\<exists>a. m_mem M a A) \<and> (\<forall>cl\<in>set S. m_cls M cl A))"

lemma pure_model_sinh:
  "pure_model alg ar (m_mem M) (m_fun M) (m_app M) (m_lam M) (m_bool M) (m_true M) (m_false M)
    (m_tcon M) (m_cls M) (m_cval M) \<Longrightarrow>
  pure_model.sinh (m_mem M) (m_cls M) S \<longleftrightarrow> m_sinh M S"
  by (simp add: pure_model.sinh_def pure_model.ssem_def universe.une_def[OF pure_model.axioms(2)] m_sinh_def)

text \<open>
  The proposition of a theorem without hypotheses and flex-flex pairs, whose sort hypotheses are
  inhabited in a model of its signature, holds under every good valuation of the model:
\<close>

theorem pure_thm_holds:
  fixes th :: "'u pure_thm" and M :: "'u model"
  assumes sg: "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))" and M: "is_model (sign_of th) M"
    and h: "hyps_of th = []" and t: "th_tpairs (rep_of th) = []" and S: "\<forall>S\<in>shyps_of th. m_sinh M S"
    and g: "pure_model.good (sg_alg (sign_of th)) (sg_ar (sign_of th)) (m_mem M) (m_fun M) (m_bool M)
      (m_tcon M) (m_cls M) \<eta> \<xi>"
  shows "pure_model.holds_at (sg_alg (sign_of th)) (sg_consts (sign_of th)) (m_mem M) (m_fun M)
    (m_app M) (m_lam M) (m_bool M) (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M)
    \<eta> \<xi> (th_prop (rep_of th))"
proof -
  let ?c = "sign_of th"
  interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
    "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
    by (rule is_modelD[OF M])
  have "\<forall>M :: 'u model. is_model ?c M \<longrightarrow> valid_in ?c M (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using thm_ok_rep[of th] sg by (simp add: thm_ok_def)
  then have "valid_in ?c M (shyps_of th) [] [] (th_prop (rep_of th))" using M h t by simp
  then have v: "valid (shyps_of th) [] [] (th_prop (rep_of th))" by (simp add: valid_in_def)
  show ?thesis
    by (rule valid_holds[OF v _ g]) (use S pure_model_sinh[OF is_modelD[OF M]] in blast)
qed

theorem pure_thm_consistent:
  fixes th :: "'u pure_thm" and M :: "'u model"
  assumes "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))" and M: "is_model (sign_of th) M"
    and "hyps_of th = []" "th_tpairs (rep_of th) = []" "\<forall>S\<in>shyps_of th. m_sinh M S"
  shows "th_prop (rep_of th) \<noteq> all_const propT $ Abs x propT (Bound 0)"
proof
  let ?c = "sign_of th"
  interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
    "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
    by (rule is_modelD[OF M])
  assume P: "th_prop (rep_of th) = all_const propT $ Abs x propT (Bound 0)"
  obtain \<eta> \<xi> where g: "good \<eta> \<xi>" using good_ex by blast
  have "holds_at \<eta> \<xi> (th_prop (rep_of th))" by (rule pure_thm_holds[OF assms g])
  with not_holds_all_prop P show False by simp
qed

corollary pure_thm_consistent_no_shyps:
  fixes th :: "'u pure_thm" and M :: "'u model"
  assumes "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))" "is_model (sign_of th) M"
    "hyps_of th = []" "th_tpairs (rep_of th) = []" "shyps_of th = {}"
  shows "th_prop (rep_of th) \<noteq> all_const propT $ Abs x propT (Bound 0)"
  using pure_thm_consistent[of th M x] assms by simp


subsection \<open>The equality axioms of \<open>Pure\<close>\<close>

text \<open>
  The equality axioms hold in every model that interprets \<open>Pure.eq\<close> as equality
  (\<^const>\<open>pure_sig.eq_ok\<close>), if \<open>prop\<close> has no arguments.
\<close>

context pure_model
begin

lemma cert_ax_types:
  assumes "ar STR ''prop'' = 0"
  shows "cert_typ alg ar ax_aT" "cert_typ alg ar ax_bT" "cert_typ alg ar propT"
    "cert_typ alg ar (ax_aT \<rightarrow>\<^sub>T ax_bT)"
  using assms by (auto simp: ax_aT_def ax_bT_def propT_def cert_typ_def tarity_def sort_ok_def)

text \<open>The equality axioms are well-typed:\<close>

lemma typing_eq_const':
  assumes "eq_ok" "ar STR ''prop'' = 0" "cert_typ alg ar T"
  shows "e \<turnstile> Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) : T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT"
proof (rule typing.Const)
  from assms(1) obtain v S where "ctab STR ''Pure.eq'' = Some (TVar v S \<rightarrow>\<^sub>T TVar v S \<rightarrow>\<^sub>T propT)"
    by (auto simp: eq_ok_def)
  then show "const_typ_ok ctab STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT)"
    unfolding const_typ_ok_def by (auto intro!: exI[of _ "\<lambda>_ _. T"] simp: propT_def)
  show "cert_typ alg ar (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT)"
    using assms(2,3) by (auto simp: cert_typ_def tarity_def propT_def)
qed

lemma typing_implies':
  assumes "ar STR ''prop'' = 0"
  shows "e \<turnstile> implies : propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT"
  using assms by (auto simp: implies_def const_typ_ok_def cert_typ_def tarity_def propT_def)

lemma typing_all_const':
  assumes "ar STR ''prop'' = 0" "cert_typ alg ar T"
  shows "e \<turnstile> all_const T : (T \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT"
  using assms by (auto simp: all_const_def const_typ_ok_def cert_typ_def tarity_def propT_def)

lemma wf_equality_axiom:
  assumes eq: "eq_ok" and ar: "ar STR ''prop'' = 0" and a: "a \<in> eq_names"
  shows "wf_terms [] [] (equality_axiom a)"
proof -
  note ct = cert_ax_types[OF ar]
  have tv: "e \<turnstile> ax_var x T : T" if "cert_typ alg ar T" for e x T
    using that by (auto simp: ax_var_def)
  have teq: "e \<turnstile> ax_eq T s t : propT" if "cert_typ alg ar T" "e \<turnstile> s : T" "e \<turnstile> t : T" for e T s t
    using typing_eq_const'[OF eq ar that(1)] that(2,3) by (auto simp: ax_eq_def)
  have timp: "e \<turnstile> implies $ A $ B : propT" if "e \<turnstile> A : propT" "e \<turnstile> B : propT" for e A B
    using typing_implies'[OF ar] that by auto
  have tall: "e \<turnstile> all_const T $ Abs x T B : propT" if "cert_typ alg ar T" "e\<langle>0:T\<rangle> \<turnstile> B : propT" for e T x B
    using typing_all_const'[OF ar that(1)] that by auto
  have tb: "e\<langle>0:T\<rangle> \<turnstile> Bound 0 : T" for e T by (auto simp: shift_def)
  have tap: "e\<langle>0:ax_aT\<rangle> \<turnstile> ax_var n (ax_aT \<rightarrow>\<^sub>T ax_bT) $ Bound 0 : ax_bT" for e n
    using tv[OF ct(4)] tb by auto
  have tabs: "e \<turnstile> Abs x ax_aT (ax_var n (ax_aT \<rightarrow>\<^sub>T ax_bT) $ Bound 0) : ax_aT \<rightarrow>\<^sub>T ax_bT" for e x n
    using tap ct(1) by auto
  have tfx: "e \<turnstile> ax_var n (ax_aT \<rightarrow>\<^sub>T ax_bT) $ ax_var m ax_aT : ax_bT" for e n m
    using tv[OF ct(4)] tv[OF ct(1)] by auto
  have ty: "e \<turnstile> equality_axiom a : propT" for e
  proof -
    consider "a = STR ''reflexive''" | "a = STR ''symmetric''" | "a = STR ''transitive''"
      | "a = STR ''equal_intr''" | "a = STR ''equal_elim''" | "a = STR ''abstract_rule''"
      | "a = STR ''combination''"
      using a by (auto simp: eq_names_def)
    then show ?thesis
      by cases (auto simp: equality_axiom_def Let_def mk_implies_def
          intro!: teq timp tall tv ct tap tabs tfx)
  qed
  have "closed (equality_axiom a)"
    by (auto simp: equality_axiom_def Let_def closed_def ax_eq_def ax_var_def mk_implies_def
        implies_def all_const_def)
  with ty show ?thesis by (simp add: wf_terms_def gterm_def)
qed

text \<open>The values of the constants of \<open>Pure\<close>:\<close>

lemma sem_implies_const: "sem \<eta> \<xi> bv implies = imp_val"
  by (simp add: implies_def csem_def)

lemma sem_all_const: "sem \<eta> \<xi> bv (all_const T) = all_val (tsem \<eta> T)"
  by (simp add: all_const_def csem_def propT_def)

lemma sem_eq_const: "eq_ok \<Longrightarrow> sem \<eta> \<xi> bv (Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT)) = eq_val (tsem \<eta> T)"
  by (simp add: csem_eq)

lemma eq_val_app: "x \<in>\<^sub>u A \<Longrightarrow> y \<in>\<^sub>u A \<Longrightarrow> uapp (uapp (eq_val A) x) y = ubval (x = y)"
  by (simp add: eq_val_def uapp_ulam)

lemma imp_val_app: "p \<in>\<^sub>u ubool \<Longrightarrow> q \<in>\<^sub>u ubool \<Longrightarrow> uapp (uapp imp_val p) q = ubval (p = utrue \<longrightarrow> q = utrue)"
  by (simp add: imp_val_def uapp_ulam)

lemma all_val_app:
  assumes "\<And>a. a \<in>\<^sub>u A \<Longrightarrow> g a \<in>\<^sub>u ubool"
  shows "uapp (all_val A) (ulam A g) = ubval (\<forall>a. a \<in>\<^sub>u A \<longrightarrow> g a = utrue)"
proof -
  have "ulam A g \<in>\<^sub>u ufun A ubool" by (rule ulam_mem) (rule assms)
  then have "uapp (all_val A) (ulam A g) = ubval (\<forall>a. a \<in>\<^sub>u A \<longrightarrow> uapp (ulam A g) a = utrue)"
    by (simp add: all_val_def uapp_ulam)
  also have "\<dots> = ubval (\<forall>a. a \<in>\<^sub>u A \<longrightarrow> g a = utrue)"
    by (metis uapp_ulam)
  finally show ?thesis .
qed

lemma ubool_eq: "p \<in>\<^sub>u ubool \<Longrightarrow> q \<in>\<^sub>u ubool \<Longrightarrow> (p = utrue \<longleftrightarrow> q = utrue) \<Longrightarrow> p = q"
  using ubool_mem by blast

theorem equality_axiom_holds:
  assumes eq: "eq_ok" and ar: "ar STR ''prop'' = 0" and a: "a \<in> eq_names" and g: "good \<eta> \<xi>"
  shows "holds_at \<eta> \<xi> (equality_axiom a)"
proof -
  note ct = cert_ax_types[OF ar]
  let ?A = "tsem \<eta> ax_aT" and ?B = "tsem \<eta> ax_bT" and ?FT = "ax_aT \<rightarrow>\<^sub>T ax_bT"
  have ma: "fst \<xi> (x, 0) ax_aT \<in>\<^sub>u ?A" for x using goodD(2)[OF g ct(1)] .
  have mp: "fst \<xi> (x, 0) propT \<in>\<^sub>u ubool" for x using goodD(2)[OF g ct(3)] by (simp add: propT_def)
  have mf: "fst \<xi> (x, 0) ?FT \<in>\<^sub>u ufun ?A ?B" for x using goodD(2)[OF g ct(4)] by simp
  have mfa: "uapp (fst \<xi> (y, 0) ?FT) v \<in>\<^sub>u ?B" if "v \<in>\<^sub>u ?A" for y v by (rule uapp_mem[OF mf that])
  have lam: "ulam ?A (uapp (fst \<xi> (y, 0) ?FT)) = fst \<xi> (y, 0) ?FT" for y by (rule ulam_uapp[OF mf])
  note sims = holds_at_def equality_axiom_def Let_def ax_eq_def ax_var_def mk_implies_def
    sem_implies_const sem_all_const sem_eq_const[OF eq] csem_eq[OF eq] eq_val_app imp_val_app ma mp mf mfa lam
    push_def propT_def[symmetric]
  have tp: "tsem \<eta> propT = ubool" by (simp add: propT_def)
  consider "a = STR ''reflexive''" | "a = STR ''symmetric''" | "a = STR ''transitive''"
    | "a = STR ''equal_intr''" | "a = STR ''equal_elim''" | "a = STR ''abstract_rule''"
    | "a = STR ''combination''"
    using a by (auto simp: eq_names_def)
  then show ?thesis
  proof cases
    case 4
    then show ?thesis using ubool_eq[OF mp mp] by (auto simp: sims tp)
  next
    case 6
    have "(\<forall>v. v \<in>\<^sub>u ?A \<longrightarrow> uapp (fst \<xi> (STR ''f'', 0) ?FT) v = uapp (fst \<xi> (STR ''g'', 0) ?FT) v) \<longrightarrow>
        fst \<xi> (STR ''f'', 0) ?FT = fst \<xi> (STR ''g'', 0) ?FT"
      using ufun_ext[OF mf mf] by blast
    with 6 show ?thesis by (simp add: sims all_val_app)
  qed (simp_all add: sims tp)
qed

end

text \<open>
  A model that interprets \<open>Pure.eq\<close> as equality is a model of a signature whose axioms are
  equality axioms:
\<close>

theorem is_model_eq_axioms:
  assumes "pure_model (sg_alg c) (sg_ar c) (m_mem M) (m_fun M) (m_app M) (m_lam M) (m_bool M)
      (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M)"
    and eq: "pure_sig.eq_ok (sg_consts c)" and ar: "sg_ar c STR ''prop'' = 0"
    and ax: "\<And>a A. sg_axioms c a = Some A \<Longrightarrow> \<exists>b\<in>eq_names. A = equality_axiom b"
  shows "is_model c M"
proof -
  interpret pure_model "sg_alg c" "sg_ar c" "sg_consts c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
    "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
    by (rule assms(1))
  have "valid_in c M (tm_sorts A) [] [] A" if "sg_axioms c a = Some A" for a A
  proof -
    from ax[OF that] obtain b where b: "b \<in> eq_names" "A = equality_axiom b" by blast
    have "svalid (tm_sorts A) [] [] A"
      by (rule svalidI) (use equality_axiom_holds[OF eq ar b(1)] b(2) in blast)
    moreover have "wf_terms [] [] A" using wf_equality_axiom[OF eq ar b(1)] b(2) by simp
    ultimately show ?thesis using valid_svalid by (simp add: valid_in_def)
  qed
  with assms(1) show ?thesis by (simp add: is_model_def)
qed

end
