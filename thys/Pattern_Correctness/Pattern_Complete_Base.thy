section \<open>Completeness: Basic Notions\<close>

theory Pattern_Complete_Base
  imports Pattern_Normal
begin

subsection \<open>Computations without unification failures\<close>

text \<open>Completeness says that pattern unification never raises \<open>Unif\<close> on solvable problems.\<close>

abbreviation no_unif :: "'a M \<Rightarrow> bool" where
  "no_unif m \<equiv> xok (\<lambda>e. \<exists>tr. e = Unif tr) (\<lambda>_. True) m"

lemma no_unif_bindM: "no_unif m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> no_unif (f x)) \<Longrightarrow> no_unif (bindM m f)"
  by (rule xok_bindM)

lemma no_unif_handle:
  "(\<And>e. m = Some (Err e) \<Longrightarrow> no_unif (h e)) \<Longrightarrow> no_unif (handle m h)"
  by (auto simp: xok_def handle_def split: option.splits xres.splits)

text \<open>Model functions that raise neither \<open>Pattern\<close> nor \<open>Unif\<close>:\<close>

definition pu :: "(exn \<Rightarrow> bool) \<Rightarrow> bool" where
  "pu E \<longleftrightarrow> (\<forall>e. E e \<longrightarrow> e = Pattern \<or> (\<exists>tr. e = Unif tr))"

lemma pu_Unif: "pu (\<lambda>e. \<exists>tr. e = Unif tr)" and pu_Pattern: "pu (\<lambda>e. e = Pattern)"
  by (auto simp: pu_def)

context
  fixes E :: "exn \<Rightarrow> bool" assumes E: "pu E"
begin

lemma not_E [simp]: "\<not> E Match" "\<not> E TUnify" "\<not> E Type_Match" "\<not> E (Class_Error c)"
  "\<not> E (Type_Error s Ts ts)" "\<not> E (Term_Error s ts)" "\<not> E (Failure s)" "\<not> E Subscript"
  "\<not> E Unequal_Lengths" "\<not> E (Dup x)"
  using E by (auto simp: pu_def)

lemma xok_nth: "xok E (\<lambda>_. True) (nth xs i)"
  by (induction xs arbitrary: i) auto

lemma xok_zip_eq: "xok E (\<lambda>_. True) (zip_eq xs ys)"
  by (induction xs ys rule: zip_eq.induct) (auto intro!: xok_bindM)

lemma xok_mkabs: "xok E (\<lambda>_. True) (mkabs bs is t)"
  by (induction "is") (auto intro!: xok_bindM xok_nth split: prod.splits)

lemma xok_update_new: "xok E (\<lambda>_. True) (update_new kx t)"
  by (simp add: update_new_def)

lemma xok_update: "xok E (\<lambda>_. True) (update xT t env)"
  by (auto simp: update_def xok_update_new split: env.splits intro!: xok_bindM)

lemma xok_split_type: "xok E (\<lambda>_. True) (split_type T n Ts)"
  by (induction T n Ts rule: split_type.induct)
    (subst split_type.simps, auto split: ptyp.splits list.splits)

lemma xok_type_lookup: "xok E (\<lambda>_. True) (type_lookup \<theta> v S)"
  by (auto simp: type_lookup_def tvar_clash_def split: option.splits)

lemma xok_devar: "devar \<theta> T = Some r \<Longrightarrow> xok E (\<lambda>_. True) (Some r)"
proof (induction \<theta> T r rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  have IH: "xok E (\<lambda>_. True) (dv \<theta>' U)" for \<theta>' U by (rule xok_IH) (rule 1(1))
  have "xok E (\<lambda>_. True) (case T of TVar ixn S \<Rightarrow> do {r \<leftarrow> type_lookup \<theta> ixn S; case r of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T}
      | _ \<Rightarrow> return T)"
    by (auto split: ptyp.splits option.splits intro!: xok_bindM xok_type_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma xok_unified_aux: "unified_aux \<theta> T U = Some r \<Longrightarrow> xok E (\<lambda>_. True) (Some r)"
proof (induction \<theta> T U r rule: unified_aux.raw_induct[rotated, consumes 1])
  case (1 ua \<theta> T U r)
  have IH: "xok E (\<lambda>_. True) (ua \<theta>' T' U')" for \<theta>' T' U' by (rule xok_IH) (rule 1(1))
  have dv: "xok E (\<lambda>_. True) (devar \<theta> V)" for V by (rule xok_IH) (rule xok_devar)
  have "xok E (\<lambda>_. True) (do {
      V \<leftarrow> devar \<theta> T;
      V' \<leftarrow> devar \<theta> U;
      case (V, V') of
        (Type s Ts, Type s' Ts') \<Rightarrow>
          if s = s' then do {
            b \<leftarrow> allM (\<lambda>(T, T'). ua \<theta> T T') (zip Ts Ts');
            return (b \<and> length Ts = length Ts')}
          else return False
      | _ \<Rightarrow> return (V = V')
    })"
    by (auto split: ptyp.splits prod.splits intro!: xok_bindM xok_allM dv IH)
  then show ?case using 1(2) by simp
qed

lemma xok_unified: "xok E (\<lambda>_. True) (unified \<theta> T U)"
  by (auto simp: unified_def intro: xok_IH xok_unified_aux)

lemma xok_lookup: "xok E (\<lambda>_. True) (lookup env x T)"
  by (auto simp: lookup_def var_clash_def split: option.splits intro!: xok_bindM xok_unified)

lemma xok_head_norm: "head_norm env t = Some r \<Longrightarrow> xok E (\<lambda>_. True) (Some r)"
proof (induction env t r rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have IH: "xok E (\<lambda>_. True) (hn env' t')" for env' t' by (rule xok_IH) (rule 1(1))
  have "xok E (\<lambda>_. True) (case t of
      Var xi T \<Rightarrow> do {r \<leftarrow> lookup env xi T; case r of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t}
    | Abs a T body \<Rightarrow> do {body' \<leftarrow> hn env body; return (Abs a T body')}
    | f $ u \<Rightarrow>
        (case f of
          Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> do {
            nf \<leftarrow> hn env f;
            case nf of
              Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
            | _ \<Rightarrow> return (nf $ u)})
    | _ \<Rightarrow> return t)"
    by (auto split: pterm.splits option.splits intro!: xok_bindM xok_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma xok_head_norm': "xok E (\<lambda>_. True) (head_norm env t)"
  by (rule xok_IH) (rule xok_head_norm)

lemma xok_norm_type_aux: "norm_type_aux \<theta> T = Some r \<Longrightarrow> xok E (\<lambda>_. True) (Some r)"
proof (induction \<theta> T r rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nt \<theta> T r)
  have IH: "xok E (\<lambda>_. True) (nt \<theta>' U)" for \<theta>' U by (rule xok_IH) (rule 1(1))
  have "xok E (\<lambda>_. True) (case T of
      Type a Ts \<Rightarrow> do {Ts' \<leftarrow> mapM (nt \<theta>) Ts; return (Type a Ts')}
    | TFree _ _ \<Rightarrow> return T
    | TVar v S \<Rightarrow> do {r \<leftarrow> type_lookup \<theta> v S; case r of Some U \<Rightarrow> nt \<theta> U | None \<Rightarrow> return T})"
    by (auto split: ptyp.splits option.splits intro!: xok_bindM xok_mapM xok_type_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma xok_norm_type: "xok E (\<lambda>_. True) (norm_type \<theta> T)"
  by (auto simp: norm_type_def intro: xok_IH xok_norm_type_aux)

lemma xok_type_of_G: "xok E (\<lambda>_. True) (type_of_G env T n is)"
  by (auto simp: type_of_G_def intro!: xok_bindM xok_norm_type xok_split_type xok_mapM
      xok_nth split: prod.splits)

lemma xok_mk_ff_list: "xok E (\<lambda>_. True) (mk_ff_list is js)"
proof -
  have "xok E (\<lambda>_. True) (mk_ff_list_aux is js k)" for k
    by (induction "is" js k rule: mk_ff_list_aux.induct) (auto intro!: xok_bindM)
  then show ?thesis by (simp add: mk_ff_list_def)
qed

lemma xok_occurs: "occurs F t env = Some r \<Longrightarrow> xok E (\<lambda>_. True) (Some r)"
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 oc F t env r)
  have IH: "xok E (\<lambda>_. True) (oc F' t' env')" for F' t' env' by (rule xok_IH) (rule 1(1))
  have "xok E (\<lambda>_. True) (case t of
      Var G T \<Rightarrow> do {r \<leftarrow> lookup env G T; case r of Some u \<Rightarrow> oc F u env | None \<Rightarrow> return (F = G)}
    | t1 $ t2 \<Rightarrow> do {b \<leftarrow> oc F t1 env; if b then return True else oc F t2 env}
    | Abs _ _ u \<Rightarrow> oc F u env
    | _ \<Rightarrow> return False)"
    by (auto split: pterm.splits option.splits intro!: xok_bindM xok_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma xok_occurs': "xok E (\<lambda>_. True) (occurs F t env)"
  by (rule xok_IH) (rule xok_occurs)

lemma xok_devar': "xok E (\<lambda>_. True) (devar \<theta> T)"
  by (rule xok_IH) (rule xok_devar)

end

lemmas no_unif_nth = xok_nth[OF pu_Unif] and
  no_unif_zip_eq = xok_zip_eq[OF pu_Unif] and
  no_unif_mkabs = xok_mkabs[OF pu_Unif] and
  no_unif_update_new = xok_update_new[OF pu_Unif] and
  no_unif_update = xok_update[OF pu_Unif] and
  no_unif_split_type = xok_split_type[OF pu_Unif] and
  no_unif_type_lookup = xok_type_lookup[OF pu_Unif] and
  no_unif_devar = xok_devar[OF pu_Unif] and
  no_unif_unified_aux = xok_unified_aux[OF pu_Unif] and
  no_unif_unified = xok_unified[OF pu_Unif] and
  no_unif_lookup = xok_lookup[OF pu_Unif] and
  no_unif_head_norm = xok_head_norm[OF pu_Unif] and
  no_unif_head_norm' = xok_head_norm'[OF pu_Unif] and
  no_unif_norm_type_aux = xok_norm_type_aux[OF pu_Unif] and
  no_unif_norm_type = xok_norm_type[OF pu_Unif] and
  no_unif_type_of_G = xok_type_of_G[OF pu_Unif] and
  no_unif_mk_ff_list = xok_mk_ff_list[OF pu_Unif] and
  no_unif_occurs = xok_occurs[OF pu_Unif] and
  no_unif_occurs' = xok_occurs'[OF pu_Unif]

lemma no_unif_mk_new_hnf: "no_unif (mk_new_hnf env bs is F T js)"
  by (auto simp: mk_new_hnf_def mk_hnf_def intro!: no_unif_bindM no_unif_type_of_G no_unif_mkabs
      no_unif_update split: prod.splits)

lemma no_unif_ints_of: "no_unif (ints_of ts)"
  by (induction ts rule: ints_of.induct) (auto intro!: no_unif_bindM)

lemma no_unif_ints_of': "no_unif (ints_of' env ts)"
  by (auto simp: ints_of'_def intro!: no_unif_bindM xok_mapM no_unif_head_norm' no_unif_ints_of)

lemma no_unif_idx: "j \<in> set xs \<Longrightarrow> no_unif (idx xs j)"
  by (induction xs) auto

lemma no_unif_mapM_idx: "set ks \<subseteq> set xs \<Longrightarrow> no_unif (mapM (idx xs) ks)"
  by (rule xok_mapM) (auto intro: no_unif_idx)

lemma no_unif_try_trans: "no_unif (try_trans xs d i)"
  by (auto simp: try_trans_def intro!: no_unif_handle)


subsection \<open>Agreement of solutions\<close>

text \<open>Extended solutions agree with the given one on the old variables, those of index at most
  \<^const>\<open>maxidx\<close>.\<close>

definition sagree :: "integer \<Rightarrow> vsubst \<Rightarrow> vsubst \<Rightarrow> bool" where
  "sagree n \<sigma> \<sigma>' \<longleftrightarrow> (\<forall>x T. snd x \<le> n \<longrightarrow> \<sigma>' x T = \<sigma> x T)"

lemma sagree_refl [simp]: "sagree n \<sigma> \<sigma>"
  by (simp add: sagree_def)

lemma sagree_trans: "sagree n \<sigma>1 \<sigma>2 \<Longrightarrow> sagree n' \<sigma>2 \<sigma>3 \<Longrightarrow> n \<le> n' \<Longrightarrow> sagree n \<sigma>1 \<sigma>3"
  by (simp add: sagree_def)

definition tbelow :: "integer \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "tbelow n A \<longleftrightarrow> (\<forall>p\<in>A. snd (fst p) \<le> n)"

lemma vars_typs: "(x, T) \<in> vars t \<Longrightarrow> T \<in> typs t"
  by (induction t) auto

lemma inst_agree: "tagree n \<rho> \<rho>' \<Longrightarrow> tbelow n (ttvars t) \<Longrightarrow> inst \<rho>' t = inst \<rho> t"
  by (rule inst_cong, rule tagree_tsubst) (auto simp: tbelow_def ttvars_def)

lemma vars_inst: "vars (inst \<rho> t) = (\<lambda>(x, T). (x, tsubst \<rho> T)) ` vars t"
  by (induction t) auto

context pure_sig
begin

lemma ap_agree:
  assumes "tagree n \<rho> \<rho>'" "sagree n \<sigma> \<sigma>'" "tbelow n (ttvars t)" "below n (vars t)"
  shows "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t"
proof -
  have "vsubst \<sigma>' (inst \<rho> t) = vsubst \<sigma> (inst \<rho> t)"
    by (rule vsubst_cong) (use assms(2,4) in \<open>auto simp: vars_inst sagree_def below_def\<close>)
  then show ?thesis unfolding ap_def inst_agree[OF assms(1,3)] .
qed

subsection \<open>Types\<close>

lemma wft_tsubstD: "wft ar (tsubst \<rho> U) \<Longrightarrow> wft ar U"
  by (induction U) auto

lemma typing_typs: "e \<turnstile> t : T \<Longrightarrow> U \<in> typs t \<Longrightarrow> cert_typ alg ar U"
  by (induction rule: typing.induct) auto

lemma typs_inst: "typs (inst \<rho> t) = tsubst \<rho> ` typs t"
  by (induction t) auto

lemma typing_inst_wft: "e \<turnstile> inst \<rho> t : T \<Longrightarrow> U \<in> typs t \<Longrightarrow> wft ar U"
  using typing_typs[of e "inst \<rho> t" T "tsubst \<rho> U"] by (auto simp: typs_inst cert_typ_def intro: wft_tsubstD)

text \<open>
  The invariant of the type environment (\<^const>\<open>tinv\<close>), for a set \<open>A\<close> of type variables of the
  problem, which also contains the type variables of the bindings.
\<close>

definition tvinv :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> bool" where
  "tvinv A env \<longleftrightarrow> tinv ar (maxidx env) (tyenv env) A \<and>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
      tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A)"

lemma tvinvD:
  assumes "tvinv A env"
  shows "tinv ar (maxidx env) (tyenv env) A"
    and "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
  using assms unfolding tvinv_def by blast+

lemma tvinv_tbelow: "tvinv A env \<Longrightarrow> B \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> tbelow (maxidx env) B"
  unfolding tbelow_def by (meson subsetD tinv_idx tvinvD(1))

lemma unify_types_complete:
  assumes inv: "tvinv A env"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar T"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar U"
    and \<rho>: "wsinst alg \<rho>" "tsol (tyenv env) \<rho>" "tsubst \<rho> T = tsubst \<rho> U"
  shows "no_unif (unify_types alg T U env)"
    and "ok (unify_types alg T U env) env' \<Longrightarrow>
      \<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and> tvinv A env' \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
proof -
  let ?r = "unify_types alg T U env"
  have "no_unif ?r \<and> (ok ?r env' \<longrightarrow>
      (\<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and> tvinv A env' \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')))"
  proof (cases "T = U")
    case True
    then show ?thesis using \<rho> inv by (auto simp: unify_types_def)
  next
    case False
    note ua = unify_aux_ok[OF tvinvD(1)[OF inv] U(1) T(1) U(2) T(2)]
    from ua show ?thesis
    proof (elim disjE exE conjE)
      fix \<theta>' n' assume r: "unify_aux alg U T (tyenv env, maxidx env) = return (\<theta>', n')"
        and st: "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> U = tsubst \<rho> T) (tyenv env) (maxidx env) \<theta>' n'"
      have r': "?r = return (Envir n' (tenv env) \<theta>')"
        using False r by (simp add: unify_types_def type_unify_def)
      obtain \<rho>' where \<rho>': "wsinst alg \<rho>'" "tsol \<theta>' \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
        using tstepD(5)[OF st \<rho>(1,2)] \<rho>(3) by auto
      have tv: "tvars_env (tyenv env) \<subseteq> tvars_env \<theta>'" by (rule tvars_env_textends[OF tstepD(1)[OF st]])
      have "tvinv A (Envir n' (tenv env) \<theta>')"
        unfolding tvinv_def using tstepD(3)[OF st] tvinvD(2)[OF inv] tv by fastforce
      with \<rho>' tv show ?thesis by (auto simp: r')
    next
      assume r: "unify_aux alg U T (tyenv env, maxidx env) = raise TUnify"
        and no: "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> U \<noteq> tsubst \<rho> T"
      with \<rho> show ?thesis by auto
    qed
  qed
  then show "no_unif ?r"
    and "ok ?r env' \<Longrightarrow> \<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      tvinv A env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    by blast+
qed

end

end
