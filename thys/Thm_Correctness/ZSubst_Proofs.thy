section \<open>Validity of the tight proofs of instantiation\<close>

theory ZSubst_Proofs
  imports ZRule_Proofs
begin

text \<open>A tight type is canonical if it is the encoding of its decoding:\<close>

definition zcanon :: "ztyp \<Rightarrow> bool" where
  "zcanon T \<longleftrightarrow> ztyp_of (typ_of T) = T"

lemma zcanon_ztyp_of: "tnoneg T \<Longrightarrow> zcanon (ztyp_of T)"
  by (simp add: zcanon_def typ_of_ztyp_of_tnoneg)

lemma map_eq_selfD: "map f xs = xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x = x"
  by (induction xs) auto

lemma zcanon_zsubst_type:
  assumes "zcanon T" and tv: "\<And>v U. tv v = Some U \<Longrightarrow> zcanon U"
  shows "zcanon (zsubst_type tv T)"
  using assms(1)
proof (induction T)
  case (ZTVar v S)
  then show ?case using tv[of "(v, S)"] by (cases "tv (v, S)") (auto simp: zcanon_def)
next
  case (ZFun T U)
  then show ?case by (auto simp: zcanon_def)
next
  case (ZType1 c T)
  then show ?case by (auto simp: zcanon_def)
next
  case (ZType c Ts)
  have IH: "ztyp_of (typ_of (zsubst_type tv T)) = zsubst_type tv T" if "T \<in> set Ts" "ztyp_of (typ_of T) = T" for T
    using ZType.IH[OF that(1)] that(2) by (simp add: zcanon_def)
  from ZType.prems show ?case
  proof (cases Ts rule: remdups_adj.cases)
    case (3 T U Ws)
    show ?thesis
    proof (cases Ws)
      case Nil
      with 3 ZType.prems IH show ?thesis by (auto simp: zcanon_def split: if_splits)
    next
      case (Cons W Ws')
      with 3 ZType.prems IH show ?thesis by (auto simp: zcanon_def intro!: map_idI dest: map_eq_selfD)
    qed
  qed (auto simp: zcanon_def split: if_splits)
qed (simp_all add: zcanon_def)

lemma lookup_zvar_map_of: "lookup_zvar xs v = map_of xs v"
  by (induction xs) (auto simp: prod_eq_iff)

lemma lookup_var_subst_map_of: "Pure_Subst_Rules.lookup_var xs v = map_of xs v"
  by (induction xs) (auto simp: prod_eq_iff)

text \<open>The lookup of a tight variable of canonical type is the lookup of its decoding:\<close>

lemma lookup_zinst:
  assumes zi: "list_all2 (\<lambda>((v, T), t) e. \<exists>t'. zterm_of ta t = return t' \<and> e = ((v, ztyp_of T), t')) insts zinst"
    and kt: "\<forall>((v, T), t)\<in>set insts. tnoneg T" and c: "zcanon U"
  shows "(lookup_zvar zinst (x, U) = None \<longleftrightarrow> map_of insts (x, typ_of U) = None) \<and>
    (\<forall>z. lookup_zvar zinst (x, U) = Some z \<longrightarrow> (\<exists>t. map_of insts (x, typ_of U) = Some t \<and> zterm_of ta t = return z))"
  using zi kt
proof (induction rule: list_all2_induct)
  case (Cons a insts e zinst)
  obtain v T t where a: "a = ((v, T), t)" by (cases a) auto
  from Cons.hyps(1) a obtain t' where t': "zterm_of ta t = return t'" and e: "e = ((v, ztyp_of T), t')" by auto
  have tT: "tnoneg T" using Cons.prems a by simp
  have "(v, ztyp_of T) = (x, U) \<longleftrightarrow> (v, T) = (x, typ_of U)"
    using c tT by (auto simp: zcanon_def typ_of_ztyp_of_tnoneg)
  with Cons show ?case by (auto simp: a e lookup_zvar_map_of t')
qed simp

lemma typ_of_zsubst_instT:
  assumes "\<forall>((v, S), T)\<in>set instT. snd v \<noteq> -1 \<and> tnoneg T"
  shows "typ_of (zsubst_type (map_of (map (\<lambda>(v, T). (v, ztyp_of T)) instT)) Z) =
    tsubst (tab_inst (map (\<lambda>(v, T). (v, (T, -1))) instT)) (typ_of Z)"
proof (induction Z)
  case (ZTVar v S)
  have m1: "map_of (map (\<lambda>(v, T). (v, ztyp_of T)) instT) = map_option ztyp_of \<circ> map_of instT"
    and m2: "map_of (map (\<lambda>(v, T). (v, (T, -1 :: integer))) instT) = map_option (\<lambda>T. (T, -1)) \<circ> map_of instT"
    by (simp_all add: map_of_map[symmetric] case_prod_beta')
  show ?case
  proof (cases "map_of instT (v, S)")
    case None
    then show ?thesis by (simp add: m1 m2 tab_inst_def)
  next
    case (Some T)
    from map_of_SomeD[OF Some] assms have "snd v \<noteq> -1" "tnoneg T" by auto
    with Some show ?thesis by (simp add: m1 m2 tab_inst_def typ_of_ztyp_of_tnoneg)
  qed
qed (simp_all add: propT_def)

context prf_model
begin

lemma erase_zdec_zinst:
  assumes ty: "\<And>Z. typ_of (ty Z) = tsubst \<rho>0 (typ_of Z)"
    and zi: "list_all2 (\<lambda>((v, T), t) e. \<exists>t'. zterm_of ta t = return t' \<and> e = ((v, ztyp_of T), t')) insts zinst"
    and kt: "\<forall>((v, T), t)\<in>set insts. snd v \<noteq> -1 \<and> tnoneg T \<and> noneg t"
    and c: "\<forall>(x, T)\<in>zvars t. zcanon (ty T)"
  shows "erase (zdec (zsubst_term ty (lookup_zvar zinst) t)) =
    erase (vsubst (tab_subst (map (\<lambda>(v, t). (v, (remove_types t, -1))) insts)) (inst \<rho>0 (zdec t)))"
  using c
proof (induction t)
  case (ZVar x T)
  have kt': "\<forall>((v, T), t)\<in>set insts. tnoneg T" using kt by auto
  note lk = lookup_zinst[OF zi kt' ZVar.prems[simplified], of x]
  have m: "map_of (map (\<lambda>(v, t). (v, (remove_types t, -1 :: integer))) insts) =
      map_option (\<lambda>t. (remove_types t, -1)) \<circ> map_of insts"
    by (simp add: map_of_map[symmetric] case_prod_beta')
  show ?case
  proof (cases "snd x = -1")
    case True
    have "lookup_zvar zinst (x, ty T) = None"
    proof (rule ccontr)
      assume "lookup_zvar zinst (x, ty T) \<noteq> None"
      then have "map_of insts (x, typ_of (ty T)) \<noteq> None" using lk by (cases x) auto
      then obtain t where "((x, typ_of (ty T)), t) \<in> set insts" by (auto dest: map_of_SomeD)
      with kt True show False by auto
    qed
    with True show ?thesis by (cases x) (simp add: ty)
  next
    case False
    show ?thesis
    proof (cases "lookup_zvar zinst (x, ty T)")
      case None
      with lk have "map_of insts (x, typ_of (ty T)) = None" by (cases x) auto
      with None False show ?thesis by (simp add: ty tab_subst_def lookup_var_subst_map_of m)
    next
      case (Some z)
      with lk obtain t where t: "map_of insts (x, typ_of (ty T)) = Some t" and z: "zterm_of ta t = return z"
        by (cases x) auto
      have "noneg t" using map_of_SomeD[OF t] kt by auto
      then have "erase (zdec z) = erase t" using zdec_zterm_of[OF z] by (metis erase_remove_types)
      with Some t False show ?thesis by (simp add: ty tab_subst_def lookup_var_subst_map_of m)
    qed
  qed
next
  case (ZAbs a T t)
  then show ?case by simp
next
  case (ZApp t u)
  then show ?case by simp
next
  case (ZOfclass T c)
  then show ?case by (simp add: Proof_Judgment.of_class_def)
qed simp_all

end

context prf_model
begin

theorem zinstantiate_proof_valid:
  fixes instT :: instT and insts :: inst
  defines "\<rho>0 \<equiv> tab_inst (map (\<lambda>(v, T). (v, (T, -1))) instT)"
    and "\<sigma>0 \<equiv> tab_subst (map (\<lambda>(v, t). (v, (t, -1))) insts)"
  assumes p: "zvalid ax H tps pf \<phi>" and \<rho>0: "cinst \<rho>0" and \<sigma>0: "wt_subst \<sigma>0"
    and uniq: "\<And>x T U. (x, T) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (zprf_tr pf)) (inst \<rho>0 \<phi>) \<Longrightarrow>
      (x, U) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (zprf_tr pf)) (inst \<rho>0 \<phi>) \<Longrightarrow> T = U"
    and cert: "\<And>x T. (x, T) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (zprf_tr pf)) (inst \<rho>0 \<phi>) \<Longrightarrow> cert_typ alg ar T"
    and kT: "\<forall>((v, S), T)\<in>set instT. snd v \<noteq> -1 \<and> tnoneg T"
    and kt: "\<forall>((v, T), t)\<in>set insts. snd v \<noteq> -1 \<and> tnoneg T \<and> noneg t"
    and c: "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. zcanon T) (\<lambda>_. True) pf" and zc: "zconsts_ok pf"
    and z: "zinstantiate_proof ztargs instT insts pf = return q"
  shows "zvalid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps) q (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
proof -
  let ?ty = "zsubst_type (map_of (map (\<lambda>(v, T). (v, ztyp_of T)) instT))"
  let ?\<sigma>r = "tab_subst (map (\<lambda>(v, t). (v, (remove_types t, -1))) insts)"
  from z obtain zinst where zi0: "mapM (\<lambda>((v, T), t). do {t' \<leftarrow> zterm_of ztargs t; return ((v, ztyp_of T), t')})
      insts = return zinst"
    and m: "map_zproof ?ty (\<lambda>t. return (zsubst_term ?ty (lookup_zvar zinst) t)) pf = return q"
    by (auto simp: zinstantiate_proof_def bindZ_eq_returnZ Let_def)
  have zi: "list_all2 (\<lambda>((v, T), t) e. \<exists>t'. zterm_of ztargs t = return t' \<and> e = ((v, ztyp_of T), t')) insts zinst"
    using zi0[unfolded mapZ_eq_returnZ] by (rule list_all2_mono) (auto simp: bindZ_eq_returnZ split: prod.splits)
  obtain w where w: "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax H tps w \<phi>" using p by (rule zvalidE)
  have tw: "prf_terms w = prf_terms (zprf_tr pf)" using arg_cong[OF w(1), of prf_terms] by simp
  have pv: "prf_vars X (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) w) Y =
      prf_vars X (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (zprf_tr pf)) Y" for X Y
    by (simp add: prf_vars_def prf_terms_map_proof_terms tw)
  have v: "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps)
      (instantiate_proof instT insts w) (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
    by (rule instantiate_proof_valid[OF w(2) \<rho>0[unfolded \<rho>0_def] \<sigma>0[unfolded \<sigma>0_def], folded \<rho>0_def \<sigma>0_def])
      (use uniq cert in \<open>simp_all only: pv\<close>)
  have ip: "instantiate_proof instT insts w = map_proof_terms (\<lambda>t. vsubst ?\<sigma>r (inst \<rho>0 t)) (tsubst \<rho>0) w"
    by (simp add: instantiate_proof_def inst_m_fst instT_m_fst \<rho>0_def Let_def)
  have tyZ: "typ_of (?ty Z) = tsubst \<rho>0 (typ_of Z)" for Z
    unfolding \<rho>0_def by (rule typ_of_zsubst_instT[OF kT])
  have cv: "zcanon (?ty T)" if "zcanon T" for T
    by (rule zcanon_zsubst_type[OF that]) (use kT in \<open>fastforce simp: map_of_map[symmetric] case_prod_beta'
      intro!: zcanon_ztyp_of dest!: map_of_SomeD\<close>)
  let ?w = "prf_reclass (zprf_tr q) (pclass_map (tsubst \<rho>0) w)"
  have "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps) ?w (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
  proof (rule prf_valid_aeq[OF v])
    fix \<rho> \<sigma>
    have "prf_aeq (map_proof_terms (\<lambda>t. ap \<rho> \<sigma> (vsubst ?\<sigma>r (inst \<rho>0 t))) (\<lambda>T. tsubst \<rho> (tsubst \<rho>0 T)) w)
        (prf_ap \<rho> \<sigma> ?w)"
    proof (rule map_zproof_aeq_gen[OF m _ _ w(1) zc])
      show "zprf_all (\<lambda>t. \<forall>t'. return (zsubst_term ?ty (lookup_zvar zinst) t) = return t' \<longrightarrow>
          ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (vsubst ?\<sigma>r (inst \<rho>0 (zdec t))))
        (\<lambda>Z. tsubst \<rho> (typ_of (?ty Z)) = tsubst \<rho> (tsubst \<rho>0 (typ_of Z))) pf"
      proof (rule zprf_all_mono[OF c])
        fix t assume ct: "\<forall>(x, T)\<in>zvars t. zcanon T"
        have "erase (zdec (zsubst_term ?ty (lookup_zvar zinst) t)) = erase (vsubst ?\<sigma>r (inst \<rho>0 (zdec t)))"
          by (rule erase_zdec_zinst[OF tyZ zi kt]) (use ct cv in auto)
        from erase_ap_cong[OF this, of \<rho> \<sigma>]
        show "\<forall>t'. return (zsubst_term ?ty (lookup_zvar zinst) t) = return t' \<longrightarrow>
            ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (vsubst ?\<sigma>r (inst \<rho>0 (zdec t)))"
          by simp
      qed (simp add: tyZ)
    qed simp
    then show "prf_aeq (prf_ap \<rho> \<sigma> (instantiate_proof instT insts w)) (prf_ap \<rho> \<sigma> ?w)"
      by (simp add: ip prf_ap_def map_proof_terms_comp comp_def)
  qed
  then show ?thesis by (rule zvalidI[rotated]) simp
qed

end

subsection \<open>Generalization of free variables by substitution\<close>

lemma clean_index_aux_ge: "clean_index_aux xs i = (ys, j) \<Longrightarrow> i \<le> j"
proof (induction xs i arbitrary: ys j rule: clean_index_aux.induct)
  case (1 xs i)
  show ?case
  proof (cases "xs \<noteq> [] \<and> last xs = CHR ''_''")
    case True
    with "1.prems" have "clean_index_aux (butlast xs) (i + 1) = (ys, j)" by (simp add: clean_index_aux.simps)
    from "1.IH"[OF True this] show ?thesis by simp
  next
    case False
    with "1.prems" show ?thesis by (simp add: clean_index_aux.simps)
  qed
qed

lemma clean_index_ge: "gi \<le> snd (clean_index (x, gi))"
proof -
  obtain ys j where e: "clean_index_aux (String.explode x) gi = (ys, j)"
    by (cases "clean_index_aux (String.explode x) gi")
  then show ?thesis using clean_index_aux_ge[OF e] by (simp add: clean_index_def)
qed

text \<open>
  The substitution of the free variables \<open>FS\<close> by \<open>val\<close>, and of their fresh names \<open>c ` FS\<close> back by
  them:
\<close>

definition tauG :: "name set \<Rightarrow> (name \<Rightarrow> name) \<Rightarrow> (name \<Rightarrow> ptyp \<Rightarrow> pterm) \<Rightarrow> name \<Rightarrow> ptyp \<Rightarrow> pterm" where
  "tauG FS c val y V = (if y \<in> FS then val y V else if y \<in> c ` FS then Free (the_inv_into FS c y) V else Free y V)"

lemma lift_tauG: "(\<And>y V. closed (val y V)) \<Longrightarrow> (\<lambda>y V. lift (tauG FS c val y V) 0) = tauG FS c val"
  by (auto simp: fun_eq_iff tauG_def lift_closed0)

lemma fsubst_tauG_frename:
  assumes c: "inj_on c FS" "c ` FS \<inter> FS = {}" and s: "fnames s \<inter> c ` FS = {}" and cl: "\<And>y V. closed (val y V)"
  shows "fsubst (tauG FS c val) (frename (\<lambda>a V. if a \<in> FS then c a else a) s) = s"
  using s
proof (induction s)
  case (Free y V)
  show ?case
  proof (cases "y \<in> FS")
    case True
    then have "c y \<notin> FS" "c y \<in> c ` FS" using c(2) by auto
    with True the_inv_into_f_f[OF c(1) True] show ?thesis by (simp add: tauG_def)
  next
    case False
    with Free.prems show ?thesis by (auto simp: tauG_def)
  qed
next
  case (Abs a T t)
  then show ?case by (simp add: lift_tauG[OF cl])
qed (simp_all add: Int_Un_distrib2)

context prf_sig
begin

lemma fsubst_ap_gen:
  assumes c: "inj_on c (set frees)" "c ` set frees \<inter> set frees = {}"
    and val: "val = (\<lambda>y V. \<sigma> (clean_index (y, gi)) V)" and cl: "closed_subst \<sigma>"
    and t: "fnames t \<inter> c ` set frees = {}"
    and tv: "\<And>v U. (v, U) \<in> vars t \<Longrightarrow> fnames (\<sigma> v (tsubst \<rho> U)) \<inter> c ` set frees = {}"
  shows "fsubst (tauG (set frees) c val) (ap \<rho> (\<lambda>v U. frename (\<lambda>a V. if a \<in> set frees then c a else a) (\<sigma> v U)) t) =
    ap \<rho> \<sigma> (generalize_term [] frees gi t)"
  using t tv
proof (induction t)
  case (Free y U)
  have "y \<notin> c ` set frees" using Free.prems by simp
  then show ?case by (simp add: ap_def tauG_def val)
next
  case (Var v U)
  have "fnames (\<sigma> v (tsubst \<rho> U)) \<inter> c ` set frees = {}" using Var.prems(2) by simp
  from fsubst_tauG_frename[OF c this, of val] cl show ?case by (simp add: ap_def val closed_substD)
next
  case (Abs a T t)
  have cv: "closed (val y V)" for y V using cl by (simp add: val closed_substD)
  from Abs show ?case by (simp add: ap_def lift_tauG[OF cv])
next
  case (App t u)
  then show ?case by (simp add: ap_def Int_Un_distrib2)
qed (simp_all add: ap_def)

lemma prf_fsubst_prf_ap_map:
  assumes "\<And>t. t \<in> prf_terms p \<Longrightarrow> fsubst \<tau> (ap \<rho> \<sigma>' t) = ap \<rho> \<sigma> (g t)" and l: "(\<lambda>y V. lift (\<tau> y V) 0) = \<tau>"
  shows "prf_fsubst \<tau> (prf_ap \<rho> \<sigma>' p) = prf_ap \<rho> \<sigma> (map_proof_terms g (\<lambda>T. T) p)"
  using assms(1)
proof (induction p)
  case (Abst a T q)
  then show ?case by (simp add: prf_ap_def l option.map_ident)
next
  case (AbsP a t q)
  then show ?case by (cases t) (simp_all add: prf_ap_def option.map_ident)
next
  case (PAppt q t)
  then show ?case by (cases t) (simp_all add: prf_ap_def option.map_ident)
next
  case (PThm x)
  then show ?case by (cases x) (simp add: prf_ap_def option.map_ident)
qed (simp_all add: prf_ap_def option.map_ident)

end

context prf_model
begin

text \<open>
  Substituting schematic variables of index \<open>gi\<close> for free variables that occur neither in the
  hypotheses, nor in the flex-flex pairs, nor in the closures of the atoms keeps proofs valid:
\<close>

theorem prf_valid_subst_frees:
  assumes p: "prf_valid ax H tps q P" and fH: "finite H"
    and H: "\<And>h. h \<in> H \<Longrightarrow> fnames h \<inter> set frees = {}"
    and nt: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> fnames t \<inter> set frees = {} \<and> fnames u \<inter> set frees = {}"
    and tw: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> closed t \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T)"
    and na: "\<And>A. A \<in> prf_atoms q \<Longrightarrow> fnames (close A) \<inter> set frees = {}"
  shows "prf_valid ax H tps (map_proof_terms (generalize_term [] frees gi) (\<lambda>T. T) q) (generalize_term [] frees gi P)"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  let ?FS = "set frees"
  define TS where "TS = insert P (prf_terms q \<union> fst ` set tps \<union> snd ` set tps)"
  have fTS: "finite TS" by (simp add: TS_def)
  define N0 where "N0 = (\<Union>t\<in>TS. fnames t) \<union> (\<Union>t\<in>TS. \<Union>(v, U)\<in>vars t. fnames (\<sigma> v (tsubst \<rho> U))) \<union>
    (\<Union>h\<in>H. fnames h) \<union> (\<Union>A\<in>prf_atoms q. fnames (close A)) \<union> ?FS"
  have "finite N0" using fTS fH by (auto simp: N0_def)
  then obtain c :: "name \<Rightarrow> name" where c: "inj_on c ?FS" "c ` ?FS \<inter> N0 = {}"
    using fresh_inj[OF finite_set[of frees] _ infinite_literal] by blast
  have c2: "c ` ?FS \<inter> ?FS = {}" using c(2) by (auto simp: N0_def)
  let ?f = "\<lambda>a (V :: ptyp). if a \<in> ?FS then c a else a"
  define \<sigma>' where "\<sigma>' = (\<lambda>v U. frename ?f (\<sigma> v U))"
  define val where "val = (\<lambda>y V. \<sigma> (clean_index (y, gi)) V)"
  let ?\<tau> = "tauG ?FS c val"
  note \<sigma>c = closed_substD[OF gsubstD(2)[OF \<sigma>]]
  have \<sigma>t: "cert_typ alg ar U \<Longrightarrow> \<exists>e. e \<turnstile> \<sigma> v U : U" for v U
    using wt_subst_typing[OF gsubstD(1)[OF \<sigma>]] by blast
  have \<sigma>': "gsubst \<sigma>'"
    using \<sigma>c \<sigma>t by (fastforce simp: gsubst_def wt_subst_def closed_subst_def closed_def \<sigma>'_def intro: typing_frename)
  have TSn: "fnames t \<inter> c ` ?FS = {}" if "t \<in> TS" for t using that c(2) by (auto simp: N0_def)
  have TSv: "fnames (\<sigma> v (tsubst \<rho> U)) \<inter> c ` ?FS = {}" if "t \<in> TS" "(v, U) \<in> vars t" for t v U
    using that c(2) by (auto simp: N0_def)
  have tTS: "t \<in> TS \<and> u \<in> TS" if "(t, u) \<in> set tps" for t u using that by (force simp: TS_def)
  have sol': "ap \<rho> \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u" if tu: "(t, u) \<in> set tps" for t u
  proof -
    have e: "ap \<rho> \<sigma>' s = frename ?f (ap \<rho> \<sigma> s)" if s: "fnames s \<inter> ?FS = {}" for s
    proof -
      have "?f x (tsubst \<rho> U) = x" if "(x, U) \<in> pfrees s" for x U
        using that s by (force simp: Generalize_Correct.fnames_pfrees)
      then show ?thesis using ap_frename[of s ?f \<rho> \<sigma>] by (simp add: \<sigma>'_def)
    qed
    from tw[OF tu] obtain U where ct: "closed t" and tt: "\<And>e. e \<turnstile> t : U" by blast
    have "gterm (ap \<rho> \<sigma> t) (tsubst \<rho> U)" by (rule gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma> ct tt])
    then have "wt (ap \<rho> \<sigma> t)" unfolding gterm_def wt_def by blast
    from conv_frename[OF this sol[OF tu]] e[of t] e[of u] nt[OF tu] show ?thesis by simp
  qed
  have pr: "prf_ok ax H e [] (prf_ap \<rho> \<sigma>' q) (ap \<rho> \<sigma>' P)" by (rule prf_validD[OF p \<rho> \<sigma>' sol'])
  have cv: "closed (val y V)" for y V using \<sigma>c by (simp add: val_def)
  have "prf_ok ax H e (map (fsubst ?\<tau>) []) (prf_fsubst ?\<tau> (prf_ap \<rho> \<sigma>' q)) (fsubst ?\<tau> (ap \<rho> \<sigma>' P))"
  proof (rule prf_ok_fsubst[where N = "?FS \<union> c ` ?FS", OF _ pr])
    show "fnames h \<inter> (?FS \<union> c ` ?FS) = {}" if "h \<in> H" for h
      using H[OF that] that c(2) by (auto simp: N0_def)
    show "e \<turnstile> ?\<tau> x U : U" if "cert_typ alg ar U" for x U
    proof -
      have "e \<turnstile> \<sigma> v U : U" for v using \<sigma>t[OF that, of v] \<sigma>c[of v U] typing_closed by blast
      then show ?thesis using that by (auto simp: tauG_def val_def)
    qed
    show "?\<tau> x U = Free x U" if "x \<notin> ?FS \<union> c ` ?FS" for x U using that by (simp add: tauG_def)
    show "\<forall>A\<in>prf_atoms (prf_ap \<rho> \<sigma>' q). fnames (close A) \<inter> (?FS \<union> c ` ?FS) = {}"
      using na c(2) by (auto simp: prf_ap_def N0_def)
  qed
  moreover have tm: "fsubst ?\<tau> (ap \<rho> \<sigma>' t) = ap \<rho> \<sigma> (generalize_term [] frees gi t)" if "t \<in> TS" for t
    unfolding \<sigma>'_def
    by (rule fsubst_ap_gen[OF c(1) c2 val_def gsubstD(2)[OF \<sigma>] TSn[OF that] TSv[OF that]])
  moreover have "prf_fsubst ?\<tau> (prf_ap \<rho> \<sigma>' q) = prf_ap \<rho> \<sigma> (map_proof_terms (generalize_term [] frees gi) (\<lambda>T. T) q)"
    by (rule prf_fsubst_prf_ap_map[OF _ lift_tauG[OF cv]]) (use tm in \<open>auto simp: TS_def\<close>)
  ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> (map_proof_terms (generalize_term [] frees gi) (\<lambda>T. T) q))
      (ap \<rho> \<sigma> (generalize_term [] frees gi P))"
    using tm[of P] by (simp add: TS_def)
qed

end

subsection \<open>Tight generalization\<close>

lemma typ_of_zsubst_gen:
  assumes "tfrees \<noteq> [] \<Longrightarrow> gi \<noteq> -1"
  shows "typ_of (zsubst_type (\<lambda>((a, i), S). if i = -1 \<and> a \<in> set tfrees then Some (ZTVar (a, gi) S) else None) Z) =
    generalizeT tfrees gi (typ_of Z)"
proof (induction Z)
  case (ZTVar v S)
  obtain a i where v: "v = (a, i)" by (cases v)
  show ?case using assms by (cases "tfrees = []") (auto simp: v)
qed (simp_all add: propT_def)

context prf_model
begin

lemma erase_zdec_zgen:
  assumes ty: "\<And>Z. typ_of (ty Z) = generalizeT tfrees gi (typ_of Z)" and gi: "frees \<noteq> [] \<Longrightarrow> 0 \<le> gi"
  shows "erase (zdec (zsubst_term ty (\<lambda>((x, i), T). if i = -1 \<and> x \<in> set frees then Some (ZVar (clean_index (x, gi)) T)
      else None) t)) = erase (generalize_term tfrees frees gi (zdec t))"
proof (induction t)
  case (ZVar xi T)
  obtain x i where xi: "xi = (x, i)" by (cases xi)
  have "snd (clean_index (x, gi)) \<noteq> -1" if "x \<in> set frees" using that gi clean_index_ge[of gi x] by force
  then show ?case by (auto simp: xi ty)
qed (auto simp: ty Proof_Judgment.of_class_def)

theorem zgeneralize_proof_valid:
  assumes ok: "okT (generalize tfrees frees gi hs th0) th"
    and p: "zvalid ax (set hs) (th_tpairs th0) pf (th_prop th0)"
    and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)" and mx: "-1 \<le> th_maxidx th0"
    and nt: "\<And>t u. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> fnames t \<inter> set frees = {} \<and> fnames u \<inter> set frees = {}"
    and ntf: "\<And>t u. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow>
      \<not> tf_in (tf_set tfrees) t \<and> \<not> tf_in (tf_set tfrees) u"
    and np: "prf_nolb 0 (zprf_tr pf)" and zc: "zconsts_ok pf" and eqc: "zeq_close_ok"
    and z: "zgeneralize_proof tfrees frees gi pf = return q"
  shows "zvalid ax (set hs) (th_tpairs th) q (th_prop th)"
proof -
  let ?A = "tf_set tfrees" and ?g = "\<lambda>a (S :: psort). (a, gi)"
  let ?\<phi> = "gen_atom ?A ?g"
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  let ?gen = "generalize_term tfrees frees gi" and ?genT = "generalizeT tfrees gi"
  let ?ty = "zsubst_type (\<lambda>((a, i), S). if i = -1 \<and> a \<in> set tfrees then Some (ZTVar (a, gi) S) else None)"
  let ?var = "\<lambda>((x, i), T). if i = -1 \<and> x \<in> set frees then Some (ZVar (clean_index (x, gi)) T) else None"
  have gen: "?gen t = generalize_term [] frees gi (tmap ?\<phi> t)" for t by (rule generalize_term_split)
  have genT: "?genT = map_atyps ?\<phi>" by (rule ext) (rule generalizeT_gen_atom)
  have genF: "?gen = generalize_term [] frees gi \<circ> tmap ?\<phi>" by (rule ext) (simp add: gen)
  have tid: "?gen t = t \<and> ?gen u = u" if "(t, u) \<in> set ?tps" for t u
    using ntf[OF that] nt[OF that] by (auto simp: gen tmap_gen_atom_id intro!: generalize_term_id)
  have ni: "\<not> gi \<le> th_maxidx th0" and nb: "\<And>h. h \<in> set hs \<Longrightarrow> \<not> bad_term tfrees frees h"
    and th: "th_tpairs th = map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps" "th_prop th = ?gen ?P"
    if "\<not> (tfrees = [] \<and> frees = [])"
    using ok that by (auto simp: generalize_def returnW_def raiseW_def Let_def mk_rep_def split: if_splits)
  have gi0: "0 \<le> gi" if "\<not> (tfrees = [] \<and> frees = [])" using ni[OF that] mx by (simp add: integer_less_eq_iff)
  have T: "th_tpairs th = ?tps" and Pth: "th_prop th = ?gen ?P"
  proof -
    have "th_tpairs th = ?tps \<and> th_prop th = ?gen ?P"
    proof (cases "tfrees = [] \<and> frees = []")
      case True
      then have "?gen t = t" for t using generalize_term_id[of frees t gi] by (simp add: gen)
      with ok True show ?thesis by (simp add: generalize_def returnW_def)
    next
      case False
      have "map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps = ?tps" by (rule map_idI) (auto dest: tid)
      with th[OF False] show ?thesis by simp
    qed
    then show "th_tpairs th = ?tps" "th_prop th = ?gen ?P" by simp_all
  qed
  have hs: "\<not> tf_in ?A h \<and> fnames h \<inter> set frees = {}" if "h \<in> set hs" for h
  proof (cases "tfrees = [] \<and> frees = []")
    case True
    then show ?thesis by (simp add: tf_in_def)
  next
    case False
    from bad_term_tf_in[OF nb[OF False that]] bad_term_frees show ?thesis
      by (fastforce simp: Generalize_Correct.fnames_pfrees)
  qed
  have hw: "wtp h \<and> vars h = {} \<and> ttvars h = {}" if "h \<in> set hs" for h using wt that by (simp add: wt_thm_def)
  have tw: "closed t \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T)" "closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> u : T)" if "(t, u) \<in> set ?tps" for t u
    using wt that by (fastforce simp: wt_thm_def)+
  have cl: "prf_valid ax (set hs) ?tps (map_proof_terms ?gen ?genT w) (?gen ?P)"
    if w: "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax (set hs) ?tps w ?P" for w
  proof -
    have aw: "fnames (close A) = {} \<and> \<not> tf_in ?A (close A)" if "A \<in> prf_atoms w" for A
      using that arg_cong[OF w(1), of prf_atoms] zeq_close_okD[OF eqc] by (fastforce simp: tf_in_def)
    have v1: "prf_valid ax (set hs) ?tps (map_proof_terms (tmap ?\<phi>) (map_atyps ?\<phi>) w) (tmap ?\<phi> ?P)"
    proof (rule prf_valid_gen_tfrees[OF w(2)])
      show "wtp ?P" using wt by (simp add: wt_thm_def)
      show "closed h \<and> vars h = {} \<and> ttvars h = {} \<and> \<not> tf_in ?A h" if "h \<in> set hs" for h
        using hw[OF that] hs[OF that] wtpD(1) by blast
      show "prf_nolb 0 w" using arg_cong[OF w(1), of "prf_nolb 0"] np by simp
    qed (use ntf aw in auto)
    have "prf_valid ax (set hs) ?tps (map_proof_terms (generalize_term [] frees gi) (\<lambda>T. T)
        (map_proof_terms (tmap ?\<phi>) (map_atyps ?\<phi>) w)) (generalize_term [] frees gi (tmap ?\<phi> ?P))"
      by (rule prf_valid_subst_frees[OF v1]) (use hs nt tw aw in auto)
    then show ?thesis by (simp add: map_proof_terms_comp genF genT comp_def)
  qed
  obtain w where w: "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax (set hs) ?tps w ?P" using p by (rule zvalidE)
  let ?w = "prf_reclass (zprf_tr q) (pclass_map ?genT w)"
  have m: "map_zproof ?ty (\<lambda>t. return (zsubst_term ?ty ?var t)) pf = return q"
    using z by (simp add: zgeneralize_proof_def Let_def)
  have gi': "gi \<noteq> -1" if "tfrees \<noteq> []" using gi0 that by fastforce
  have gi'': "0 \<le> gi" if "frees \<noteq> []" using gi0 that by fastforce
  have tyof: "typ_of (?ty Z) = ?genT (typ_of Z)" for Z by (rule typ_of_zsubst_gen[OF gi'])
  have "prf_valid ax (set hs) ?tps ?w (?gen ?P)"
  proof (rule prf_valid_aeq[OF cl[OF w]])
    fix \<rho> \<sigma>
    have "prf_aeq (map_proof_terms (\<lambda>t. ap \<rho> \<sigma> (?gen t)) (\<lambda>T. tsubst \<rho> (?genT T)) w) (prf_ap \<rho> \<sigma> ?w)"
    proof (rule map_zproof_aeq_gen[OF m _ _ w(1) zc])
      show "zprf_all (\<lambda>t. \<forall>t'. return (zsubst_term ?ty ?var t) = return t' \<longrightarrow>
          ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (?gen (zdec t)))
        (\<lambda>Z. tsubst \<rho> (typ_of (?ty Z)) = tsubst \<rho> (?genT (typ_of Z))) pf"
      proof (rule zprf_all_true)
        fix t
        have "erase (ap \<rho> \<sigma> (zdec (zsubst_term ?ty ?var t))) = erase (ap \<rho> \<sigma> (?gen (zdec t)))"
          by (rule erase_ap_cong[OF erase_zdec_zgen[OF tyof gi'']])
        then show "\<forall>t'. return (zsubst_term ?ty ?var t) = return t' \<longrightarrow> ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (?gen (zdec t))"
          by simp
      qed (simp add: tyof)
    qed simp
    then show "prf_aeq (prf_ap \<rho> \<sigma> (map_proof_terms ?gen ?genT w)) (prf_ap \<rho> \<sigma> ?w)"
      by (simp add: prf_ap_def map_proof_terms_comp comp_def)
  qed
  then show ?thesis unfolding T Pth by (rule zvalidI[rotated]) simp
qed

end

end
