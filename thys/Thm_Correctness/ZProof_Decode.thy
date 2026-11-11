section \<open>Decoding tight terms and proofs\<close>

theory ZProof_Decode
  imports Proof_Bicompose "Pure_Thm.Pure_Rules"
begin

text \<open>
  The tight terms of \<open>ZTerm\<close> do not carry the types of constants: a constant is converted with
  the instances of the type variables of its declared type (\<open>Consts.typargs\<close>). Decoding
  recovers the term from these type arguments and the declared types of the signature. The
  conversion \<^const>\<open>zterm_of\<close> is parametric in the type arguments of constants; here they are
  computed from the declared types (\<open>ztargs\<close>). With fix \<open>zterm-ofclass\<close>, only proper class
  membership propositions become \<open>OFCLASS\<close>, so that decoding inverts the conversion on all
  well-typed terms. A tight proof stands for the classic proof with the decoded terms and types as
  annotations (\<open>zprf_tr\<close>).
\<close>

lemma ex_returnZ [simp]: "(\<exists>z. return x = return z \<and> P z) \<longleftrightarrow> P x"
  by (auto simp: return_def)

lemma returnZ_inj [simp]: "return x = return y \<longleftrightarrow> x = y"
  by (simp add: return_def)


subsection \<open>The monad\<close>

lemma bindZ_eq_returnZ: "bindM m f = return y \<longleftrightarrow> (\<exists>x. m = return x \<and> f x = return y)"
  by (auto simp: bindM_def return_def split: option.splits xres.splits)

lemma liftMZ_eq_returnZ: "liftMZ m = return x \<longleftrightarrow> ok m x"
  by (auto simp: liftMZ_def return_def split: option.splits xres.splits)

lemma liftOZ_eq_returnZ: "liftOZ m = return x \<longleftrightarrow> m = Some x"
  by (auto simp: liftOZ_def return_def)

lemma mapZ_eq_returnZ: "mapM f xs = return ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = return y) xs ys"
  by (induction xs arbitrary: ys) (auto simp: bindZ_eq_returnZ list_all2_Cons1)

text \<open>The same with \<^const>\<open>return\<close> unfolded:\<close>

lemmas Z_ok_simps = bindZ_eq_returnZ[unfolded return_def] liftMZ_eq_returnZ[unfolded return_def]
  liftOZ_eq_returnZ[unfolded return_def] mapZ_eq_returnZ[unfolded return_def]



subsection \<open>Types\<close>

lemma typ_of_ztyp_of: "\<forall>(v, S)\<in>tvars T. snd v \<noteq> -1 \<Longrightarrow> typ_of (ztyp_of T) = T"
proof (induction T rule: ztyp_of.induct)
  case (3 c)
  then show ?case by (simp add: propT_def)
next
  case (6 c T U V Ts)
  have h: "typ_of (ztyp_of X) = X" if X: "X \<in> set (T # U # V # Ts)" for X
  proof -
    have "\<forall>a\<in>tvars X. case a of (v, S) \<Rightarrow> snd v \<noteq> -1" using "6.prems" X by auto
    with X "6.IH"[of X] show ?thesis by auto
  qed
  have "map (typ_of \<circ> ztyp_of) (T # U # V # Ts) = T # U # V # Ts" by (rule map_idI) (simp add: h)
  then show ?case by (simp del: list.map add: comp_def)
qed auto

lemma set_dedup [simp]: "set (dedup xs) = set xs"
  by (induction xs rule: dedup.induct) auto

lemma distinct_dedup: "distinct (dedup xs)"
  by (induction xs rule: dedup.induct) auto

lemma set_typ_tvars [simp]: "set (typ_tvars T) = tvars T"
  by (induction T rule: typ_tvars.induct) auto

lemma map_of_zip_map_self: "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> map_of (zip xs (map f xs)) x = Some (f x)"
  by (induction xs) auto

lemma tsubst_inj_tvars:
  "tsubst \<rho> U = tsubst \<rho>' U \<Longrightarrow> (v, S) \<in> tvars U \<Longrightarrow> \<rho> v S = \<rho>' v S"
proof (induction U)
  case (Type a Ts)
  then obtain T where T: "T \<in> set Ts" "(v, S) \<in> tvars T" by auto
  from Type.prems(1) have "\<forall>T\<in>set Ts. tsubst \<rho> T = tsubst \<rho>' T" by (simp add: map_eq_conv)
  with T Type.IH show ?case by blast
qed auto


subsection \<open>Type arguments of constants\<close>

text \<open>The type parameters of a declared type, in the order of their first occurrence.\<close>

definition tparams :: "ptyp \<Rightarrow> (indexname \<times> psort) list" where
  "tparams U = dedup (typ_tvars U)"

lemma set_tparams: "set (tparams U) = tvars U"
  by (simp add: tparams_def)

text \<open>The instance of a type parameter of \<open>U\<close> in an instance \<open>T\<close> of \<open>U\<close>.\<close>

definition targ :: "ptyp \<Rightarrow> ptyp \<Rightarrow> indexname \<times> psort \<Rightarrow> ptyp" where
  "targ U T p = (THE X. \<exists>\<rho>. T = tsubst \<rho> U \<and> \<rho> (fst p) (snd p) = X)"

lemma targ_eq: "T = tsubst \<rho> U \<Longrightarrow> (v, S) \<in> tvars U \<Longrightarrow> targ U T (v, S) = \<rho> v S"
  unfolding targ_def by (rule the_equality) (auto dest: tsubst_inj_tvars)

definition zeq_vars :: "(name \<times> name list) list" where
  "zeq_vars = [(STR ''reflexive'', [STR ''x'']), (STR ''symmetric'', [STR ''x'', STR ''y'']),
    (STR ''transitive'', [STR ''x'', STR ''y'', STR ''z'']), (STR ''equal_intr'', [STR ''A'', STR ''B'']),
    (STR ''equal_elim'', [STR ''A'', STR ''B'']), (STR ''abstract_rule'', [STR ''f'', STR ''g'']),
    (STR ''combination'', [STR ''f'', STR ''g'', STR ''x'', STR ''y''])]"

definition zv_lookup_name :: "'a zvtab \<Rightarrow> indexname \<Rightarrow> 'a option" where
  "zv_lookup_name t xi =
    (if \<exists>!T. zv_lookup t (xi, T) \<noteq> None then zv_lookup t (xi, THE T. zv_lookup t (xi, T) \<noteq> None)
     else None)"

definition zeq_tr :: "name \<Rightarrow> (name \<Rightarrow> pterm option) \<Rightarrow> prf" where
  "zeq_tr n look =
    (case find (\<lambda>(a, xs). n = STR ''Pure.'' + a) zeq_vars of
      Some (a, xs) \<Rightarrow>
        (case those (map look xs) of
          Some ts \<Rightarrow> foldl (\<lambda>p t. PAppt p (Some t)) (equality_axm a) ts
        | None \<Rightarrow> MinProof)
    | None \<Rightarrow> MinProof)"

text \<open>The proof constants of the equality axioms, and the translation of the other axioms:\<close>

definition zeq_const :: "name \<Rightarrow> zterm \<Rightarrow> bool" where
  "zeq_const n A \<longleftrightarrow> (\<exists>a\<in>fst ` set zeq_vars. n = STR ''Pure.'' + a \<and> A = fst (zequality_axiom a))"

text \<open>The variables of a term in the order of their first occurrence (\<open>Proofterm.variables_of\<close>):\<close>

fun term_atoms :: "pterm \<Rightarrow> pterm list" where
  "term_atoms (t $ u) = term_atoms t @ term_atoms u"
| "term_atoms (Abs _ _ b) = term_atoms b"
| "term_atoms t = [t]"

definition term_variables :: "pterm \<Rightarrow> pterm list" where
  "term_variables t = rev (fold (\<lambda>a acc. case a of Var _ _ \<Rightarrow> List.insert a acc | Free _ _ \<Rightarrow> List.insert a acc
    | _ \<Rightarrow> acc) (term_atoms t) [])"

definition zax_tr :: "name \<Rightarrow> pterm \<Rightarrow> (indexname \<Rightarrow> pterm option) \<Rightarrow> prf" where
  "zax_tr n A look =
    foldl PAppt (PAxm n A None) (map (\<lambda>v. case v of Var xi _ \<Rightarrow> look xi | _ \<Rightarrow> None) (term_variables A))"

text \<open>
  Proof boxes of theorems are translated like axioms, to classic proof boxes of their propositions,
  without type arguments; the data of the box (serial, name, body), which the proof judgment does
  not inspect, is left unspecified.
\<close>

definition zthm_head :: "pterm \<Rightarrow> thm_header \<times> thm_body" where
  "zthm_head A = (Thm_Header undefined A None, undefined)"

definition zthm_tr :: "pterm \<Rightarrow> (indexname \<Rightarrow> pterm option) \<Rightarrow> prf" where
  "zthm_tr A look =
    foldl PAppt (PThm (zthm_head A)) (map (\<lambda>v. case v of Var xi _ \<Rightarrow> look xi | _ \<Rightarrow> None) (term_variables A))"

lemma hd_set_types_Thm_Header [simp]: "hd_set_types (Thm_Header i A Ts) Us = Thm_Header i A Us"
  by (simp add: hd_set_types_def)

context pure_sig
begin

text \<open>
  \<open>Consts.typargs\<close>: \<open>Pure.imp\<close> has none, \<open>Pure.all\<close> the type of its bound variable; other
  constants the instances of the type parameters of their declared type, if the type is an
  instance of it (otherwise \<open>Type.raw_match\<close> raises an exception).
\<close>

definition ztargs :: ztypargs where
  "ztargs c T =
    (if c = STR ''Pure.imp'' then return []
     else if c = STR ''Pure.all'' then
       (case T of Type _ [Type _ [U, _], _] \<Rightarrow> return [U] | _ \<Rightarrow> raise (Type_Error STR ''typargs'' [T] []))
     else case ctab c of
       None \<Rightarrow> raise (Type_Error STR ''typargs'' [T] [])
     | Some U \<Rightarrow>
         if \<exists>\<rho>. T = tsubst \<rho> U then return (map (targ U T) (tparams U))
         else raise (Type_Error STR ''typargs'' [T] []))"

text \<open>The type of a constant with given type arguments.\<close>

definition zconst_typ :: "name \<Rightarrow> ptyp list \<Rightarrow> ptyp" where
  "zconst_typ c Us =
    (if c = STR ''Pure.imp'' then imp_type
     else if c = STR ''Pure.all'' then (case Us of [U] \<Rightarrow> (U \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT | _ \<Rightarrow> dummyT)
     else case ctab c of
       None \<Rightarrow> dummyT
     | Some U \<Rightarrow> tsubst (\<lambda>v S. case map_of (zip (tparams U) Us) (v, S) of Some X \<Rightarrow> X | None \<Rightarrow> dummyT) U)"

lemma ztargs_const_typ_ok:
  assumes "const_typ_ok ctab c T"
  shows "\<exists>Us. ztargs c T = return Us \<and> zconst_typ c Us = T \<and> (\<forall>U\<in>set Us. tvars U \<subseteq> tvars T)"
proof (cases "c = STR ''Pure.imp''")
  case True
  with assms show ?thesis by (simp add: ztargs_def zconst_typ_def const_typ_ok_def imp_type_def propT_def)
next
  case ni: False
  show ?thesis
  proof (cases "c = STR ''Pure.all''")
    case True
    with assms obtain U where T: "T = (U \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT"
      by (auto simp: const_typ_ok_def propT_def)
    then show ?thesis using True ni by (simp add: ztargs_def zconst_typ_def propT_def)
  next
    case na: False
    with ni assms obtain U \<rho> where U: "ctab c = Some U" and T: "T = tsubst \<rho> U"
      by (auto simp: const_typ_ok_def)
    let ?Us = "map (targ U T) (tparams U)"
    have "zconst_typ c ?Us = tsubst \<rho> U"
      unfolding zconst_typ_def using ni na U
    proof (simp, intro tsubst_cong)
      fix v S assume vS: "(v, S) \<in> tvars U"
      then have "map_of (zip (tparams U) ?Us) (v, S) = Some (targ U T (v, S))"
        by (intro map_of_zip_map_self) (simp_all add: tparams_def distinct_dedup)
      with targ_eq[OF T vS] show "(case map_of (zip (tparams U) ?Us) (v, S) of None \<Rightarrow> dummyT | Some X \<Rightarrow> X) = \<rho> v S"
        by simp
    qed
    moreover have "tvars X \<subseteq> tvars T" if "X \<in> set ?Us" for X
    proof -
      from that obtain v S where vS: "(v, S) \<in> tvars U" "X = targ U T (v, S)"
        by (auto simp: set_tparams)
      then have "X = \<rho> v S" using targ_eq[OF T] by simp
      then show ?thesis using vS(1) T by (auto simp: tvars_tsubst)
    qed
    ultimately show ?thesis using ni na U T by (auto simp: ztargs_def)
  qed
qed


subsection \<open>Decoding\<close>

fun zdec :: "zterm \<Rightarrow> pterm" where
  "zdec (ZVar xi T) = (if snd xi = -1 then Free (fst xi) (typ_of T) else Var xi (typ_of T))"
| "zdec (ZBound i) = Bound i"
| "zdec (ZConst0 c) = Const c (zconst_typ c [])"
| "zdec (ZConst1 c T) = Const c (zconst_typ c [typ_of T])"
| "zdec (ZConst c Ts) = Const c (zconst_typ c (map typ_of Ts))"
| "zdec (ZAbs a T t) = Abs a (typ_of T) (zdec t)"
| "zdec (ZApp t u) = zdec t $ zdec u"
| "zdec (ZOfclass T c) = of_class (typ_of T) c"

text \<open>
  The conversion of a well-typed term without schematic (type) variables of index \<open>-1\<close> never
  raises an exception, and decoding inverts it.
\<close>

lemma zterm_of_zdec:
  assumes "e \<turnstile> t : T" "\<forall>v\<in>vars t. snd (fst v) \<noteq> -1" "\<forall>U\<in>typs t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
  shows "\<exists>z. zterm_of ztargs t = return z \<and> zdec z = t"
  using assms
proof (induction rule: typing.induct)
  case (Const c T e)
  from ztargs_const_typ_ok[OF Const.hyps(1)] obtain Us where u: "ztargs c T = return Us" "zconst_typ c Us = T"
    "\<forall>U\<in>set Us. tvars U \<subseteq> tvars T"
    by blast
  have r1: "typ_of (ztyp_of X) = X" if "X \<in> set Us" for X
  proof (rule typ_of_ztyp_of)
    show "\<forall>(v, S)\<in>tvars X. snd v \<noteq> -1" using that u(3) Const.prems(2) by fastforce
  qed
  then have r: "map typ_of (map ztyp_of Us) = Us" by (auto intro!: map_idI)
  show ?case
  proof (cases Us rule: remdups_adj.cases)
    case 1
    then show ?thesis using u by simp
  next
    case (2 U)
    then show ?thesis using u r by simp
  next
    case (3 U V Ws)
    then show ?thesis using u r by simp
  qed
next
  case (Free T e x)
  then show ?case by (simp add: typ_of_ztyp_of)
next
  case (Var T e x)
  then show ?case by (cases x) (simp add: typ_of_ztyp_of)
next
  case (Bound i e T)
  then show ?case by simp
next
  case (Abs T e t U a)
  then show ?case by (auto simp: typ_of_ztyp_of)
next
  case (App e s T U t)
  have ps: "\<forall>v\<in>vars s. snd (fst v) \<noteq> -1" "\<forall>U\<in>typs s. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
    and pt: "\<forall>v\<in>vars t. snd (fst v) \<noteq> -1" "\<forall>U\<in>typs t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
    using App.prems by auto
  from App.IH(1)[OF ps] obtain zs where zs: "zterm_of ztargs s = return zs" "zdec zs = s" by blast
  from App.IH(2)[OF pt] obtain zt where zt: "zterm_of ztargs t = return zt" "zdec zt = t" by blast
  show ?case
  proof (cases "\<exists>T' c. match_of_class (s $ t) = Some (T', c) \<and> s $ t = mk_of_class T' c")
    case True
    then obtain T' c where m: "match_of_class (s $ t) = Some (T', c)" and e: "s $ t = mk_of_class T' c"
      by blast
    then have t: "t = Const STR ''Pure.type'' (Type STR ''itself'' [T'])" by (simp add: mk_of_class_def)
    have "typ_of (ztyp_of T') = T'" using pt(2) t by (intro typ_of_ztyp_of) auto
    then show ?thesis using m e by (simp add: of_class_def mk_of_class_def class_suffix_def propT_def)
  next
    case False
    then show ?thesis using zs zt by (auto split: option.splits)
  qed
qed


subsection \<open>Tight proofs\<close>

text \<open>
  The proof constants of the equality axioms (\<^const>\<open>zaxiom_proof\<close>) are translated to the
  classic axioms (\<^const>\<open>equality_axm\<close>) applied to the instances of their variables, in the
  order of their quantification in the closure of the axiom (\<open>Logic.close_form\<close>). The
  instances are looked up by the names of the variables (index \<open>-1\<close>), since their types are
  instantiated. The proof constants of other axioms (\<open>ZTerm.axiom_proof\<close>) are translated to the
  classic axioms with their propositions, without type arguments, applied to the instances of their
  variables, in the order of their quantification in the closure of the axiom
  (\<open>Proofterm.forall_intr_variables_term\<close>), looked up by name; the proof boxes of theorems
  likewise to classic proof boxes (\<^const>\<open>zthm_tr\<close>); oracles have no translation.
\<close>

definition zconst_tr :: "zproof_const \<Rightarrow> prf" where
  "zconst_tr c =
    (case c of ((ZAxiom n, A), (_, tab)) \<Rightarrow>
      if zeq_const n A then zeq_tr n (\<lambda>x. map_option zdec (zv_lookup_name tab (x, -1)))
      else zax_tr n (zdec A) (\<lambda>xi. map_option zdec (zv_lookup_name tab xi))
    | ((ZThm _, A), (_, tab)) \<Rightarrow> zthm_tr (zdec A) (\<lambda>xi. map_option zdec (zv_lookup_name tab xi))
    | _ \<Rightarrow> MinProof)"

fun zprf_tr :: "zproof \<Rightarrow> prf" where
  "zprf_tr ZNop = MinProof"
| "zprf_tr (ZConstp c) = zconst_tr c"
| "zprf_tr (ZBoundp i) = PBound i"
| "zprf_tr (ZAbst a T p) = Abst a (Some (typ_of T)) (zprf_tr p)"
| "zprf_tr (ZAbsp a t p) = AbsP a (Some (zdec t)) (zprf_tr p)"
| "zprf_tr (ZAppt p t) = PAppt (zprf_tr p) (Some (zdec t))"
| "zprf_tr (ZAppp p q) = PAppp (zprf_tr p) (zprf_tr q)"
| "zprf_tr (ZHyp t) = Hyp (zdec t)"
| "zprf_tr (OFCLASSp T c) = PClass (typ_of T) c"

end

text \<open>A map of classic proofs that maps the terms of applications maps the translations:\<close>

lemma those_map_option: "those (map (\<lambda>x. map_option g (f x)) xs) = map_option (map g) (those (map f xs))"
  by (induction xs) (auto simp: option.map_comp comp_def split: option.splits)

lemma foldl_PAppt_map:
  assumes "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))"
  shows "F (foldl (\<lambda>p t. PAppt p (Some t)) p0 ts) = foldl (\<lambda>p t. PAppt p (Some t)) (F p0) (map g ts)"
  by (induction ts arbitrary: p0) (simp_all add: assms)

lemma zeq_tr_map:
  assumes "F MinProof = MinProof" "\<And>a. F (equality_axm a) = equality_axm a"
    "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))"
  shows "F (zeq_tr n look) = zeq_tr n (\<lambda>x. map_option g (look x))"
  by (simp add: zeq_tr_def those_map_option foldl_PAppt_map[OF assms(3)] assms(1,2)
      split: option.splits prod.splits)

lemma foldl_PAppt_map_option:
  assumes "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))" "\<And>p. F (PAppt p None) = PAppt (F p) None"
  shows "F (foldl PAppt p0 us) = foldl PAppt (F p0) (map (map_option g) us)"
proof (induction us arbitrary: p0)
  case (Cons u us)
  have "F (PAppt p0 u) = PAppt (F p0) (map_option g u)" by (cases u) (simp_all add: assms)
  with Cons show ?case by simp
qed simp

lemma zax_tr_map:
  assumes "F (PAxm n A None) = PAxm n A None"
    "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))" "\<And>p. F (PAppt p None) = PAppt (F p) None"
  shows "F (zax_tr n A look) = zax_tr n A (\<lambda>x. map_option g (look x))"
proof -
  have m: "map (map_option g) (map (\<lambda>v. case v of Var xi _ \<Rightarrow> look xi | _ \<Rightarrow> None) (term_variables A)) =
      map (\<lambda>v. case v of Var xi _ \<Rightarrow> map_option g (look xi) | _ \<Rightarrow> None) (term_variables A)"
    by (simp add: map_eq_conv split: pterm.splits)
  show ?thesis unfolding zax_tr_def foldl_PAppt_map_option[OF assms(2,3)] assms(1) m by (rule HOL.refl)
qed

lemma zthm_tr_map:
  assumes "F (PThm (zthm_head A)) = PThm (zthm_head A)"
    "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))" "\<And>p. F (PAppt p None) = PAppt (F p) None"
  shows "F (zthm_tr A look) = zthm_tr A (\<lambda>x. map_option g (look x))"
proof -
  have m: "map (map_option g) (map (\<lambda>v. case v of Var xi _ \<Rightarrow> look xi | _ \<Rightarrow> None) (term_variables A)) =
      map (\<lambda>v. case v of Var xi _ \<Rightarrow> map_option g (look xi) | _ \<Rightarrow> None) (term_variables A)"
    by (simp add: map_eq_conv split: pterm.splits)
  show ?thesis unfolding zthm_tr_def foldl_PAppt_map_option[OF assms(2,3)] assms(1) m by (rule HOL.refl)
qed

lemma zv_lookup_zv_map [simp]: "zv_lookup (zv_map f t) k = map_option f (zv_lookup t k)"
  by transfer simp

lemma zv_map_ident [simp]: "zv_map (\<lambda>x. x) t = t"
  by transfer (simp add: comp_def option.map_ident)

lemma zv_lookup_name_zv_map [simp]: "zv_lookup_name (zv_map f t) xi = map_option f (zv_lookup_name t xi)"
  by (simp add: zv_lookup_name_def)

text \<open>
  The names of the variables of the instances of proof constants are distinct (the constants of
  the equality axioms are built so, and maps of the types of the variables keep this):
\<close>

definition ztab_names_ok :: "'a zvtab \<Rightarrow> bool" where
  "ztab_names_ok t \<longleftrightarrow> (\<forall>k1 k2. zv_lookup t k1 \<noteq> None \<longrightarrow> zv_lookup t k2 \<noteq> None \<longrightarrow> fst k1 = fst k2 \<longrightarrow> k1 = k2)"

fun zconsts_ok :: "zproof \<Rightarrow> bool" where
  "zconsts_ok (ZConstp (c, instT, tab)) = ztab_names_ok tab"
| "zconsts_ok (ZAbst a T p) = zconsts_ok p"
| "zconsts_ok (ZAbsp a t p) = zconsts_ok p"
| "zconsts_ok (ZAppt p t) = zconsts_ok p"
| "zconsts_ok (ZAppp p q) = (zconsts_ok p \<and> zconsts_ok q)"
| "zconsts_ok _ = True"

lemma zv_lookup_name_Some:
  assumes "ztab_names_ok t" "zv_lookup t (xi, T) = Some v"
  shows "zv_lookup_name t xi = Some v"
proof -
  have u: "\<exists>!T. zv_lookup t (xi, T) \<noteq> None"
  proof (rule ex1I[of _ T])
    show "zv_lookup t (xi, T) \<noteq> None" using assms(2) by simp
    fix T' assume "zv_lookup t (xi, T') \<noteq> None"
    with assms(1,2) have "(xi, T') = (xi, T)" unfolding ztab_names_ok_def by fastforce
    then show "T' = T" by simp
  qed
  then have "(THE T. zv_lookup t (xi, T) \<noteq> None) = T"
    using assms(2) by (intro the1_equality) auto
  with u assms(2) show ?thesis by (simp add: zv_lookup_name_def)
qed

lemma zv_lookup_name_None:
  "ztab_names_ok t \<Longrightarrow> zv_lookup_name t xi = None \<longleftrightarrow> (\<forall>T. zv_lookup t (xi, T) = None)"
  by (metis option.distinct(1) zv_lookup_name_Some zv_lookup_name_def not_None_eq)

lemma zv_lookup_nameD: "zv_lookup_name t xi = Some v \<Longrightarrow> \<exists>T. zv_lookup t (xi, T) = Some v"
  by (auto simp: zv_lookup_name_def split: if_splits)

lemma ztab_names_ok_zv_map [simp]: "ztab_names_ok (zv_map f t) = ztab_names_ok t"
  by (simp add: ztab_names_ok_def)

subsection \<open>Instances of proof constants\<close>

lemma zv_dest_spec: "distinct (map fst (zv_dest t)) \<and> set (zv_dest t) = {(k, x). zv_lookup t k = Some x}"
proof -
  have "finite {(k, x). zv_lookup t k = Some x}"
  proof transfer
    fix m :: "indexname \<times> ztyp \<Rightarrow> 'a option" assume "finite (dom m)"
    moreover have "{(k, x). m k = Some x} \<subseteq> (\<lambda>k. (k, the (m k))) ` dom m" by force
    ultimately show "finite {(k, x). m k = Some x}" by (rule finite_surj)
  qed
  then obtain xs where xs: "set xs = {(k, x). zv_lookup t k = Some x}" "distinct xs"
    using finite_distinct_list by blast
  have "inj_on fst (set xs)" using xs(1) by (auto simp: inj_on_def)
  with xs have "distinct (map fst xs) \<and> set xs = {(k, x). zv_lookup t k = Some x}"
    by (simp add: distinct_map)
  then show ?thesis unfolding zv_dest_def by (rule someI)
qed

lemma zv_lookup_zv_update: "zv_lookup (zv_update (k, x) t) k' = (if k' = k then Some x else zv_lookup t k')"
  by transfer simp

lemma zv_lookup_zv_empty [simp]: "zv_lookup zv_empty k = None"
  by transfer simp

lemma zv_insert_list_distinct:
  assumes "distinct (map fst xs)" "\<And>k. k \<in> fst ` set xs \<Longrightarrow> zv_lookup t k = None"
  shows "\<exists>t'. zv_insert_list xs t = Some t' \<and> (\<forall>k. zv_lookup t' k = (case map_of xs k of Some x \<Rightarrow> Some x | None \<Rightarrow> zv_lookup t k))"
  using assms
proof (induction xs arbitrary: t)
  case (Cons kx xs)
  obtain k x where kx: "kx = (k, x)" by (cases kx)
  have "zv_lookup (zv_update (k, x) t) k' = None" if "k' \<in> fst ` set xs" for k'
    using Cons.prems that kx by (auto simp: zv_lookup_zv_update)
  from Cons.IH[of "zv_update (k, x) t"] Cons.prems this obtain t' where
    "zv_insert_list xs (zv_update (k, x) t) = Some t'"
    "\<forall>k'. zv_lookup t' k' = (case map_of xs k' of Some x \<Rightarrow> Some x | None \<Rightarrow> zv_lookup (zv_update (k, x) t) k')"
    by (auto simp: kx)
  moreover have "zv_lookup t k = None" using Cons.prems kx by simp
  moreover have "map_of xs k = None" using Cons.prems(1) kx by (simp add: map_of_eq_None_iff)
  ultimately show ?case by (auto simp: kx zv_lookup_zv_update split: option.splits)
qed simp

lemma map_insts_names:
  assumes m: "map_insts typ term (instT, tab) = return (instT', tab')" and ok: "ztab_names_ok tab"
  shows "ztab_names_ok tab'" "zv_lookup_name tab' xi = None \<longleftrightarrow> zv_lookup_name tab xi = None"
    "zv_lookup_name tab xi = Some t \<Longrightarrow> \<exists>t'. term t = return t' \<and> zv_lookup_name tab' xi = Some t'"
proof -
  let ?d = "zv_dest tab"
  from m obtain xs where xs: "mapM (\<lambda>((x, T), t). do {t' \<leftarrow> term t; return ((x, typ T), t')}) ?d = return xs"
    and mk: "make_inst xs = return tab'"
    by (auto simp: map_insts_def bindZ_eq_returnZ)
  have l2: "list_all2 (\<lambda>(k, t) (k', t'). k' = (fst k, typ (snd k)) \<and> term t = return t') ?d xs"
    using xs unfolding mapZ_eq_returnZ
    by (rule list_all2_mono) (auto simp: bindZ_eq_returnZ split: prod.splits)
  have ds: "distinct (map fst ?d)" "set ?d = {(k, x). zv_lookup tab k = Some x}" using zv_dest_spec[of tab] by simp_all
  have fx: "map fst xs = map (\<lambda>k. (fst k, typ (snd k))) (map fst ?d)"
    using l2 by (induction rule: list_all2_induct) auto
  have inj: "inj_on (\<lambda>k. (fst k, typ (snd k))) (fst ` set ?d)"
    using ok ds(2) by (auto simp: inj_on_def ztab_names_ok_def)
  have "distinct (map (\<lambda>k. (fst k, typ (snd k))) (map fst ?d))"
    by (rule distinct_map[THEN iffD2]) (simp add: ds(1) inj)
  then have dx: "distinct (map fst xs)" by (simp only: fx)
  from zv_insert_list_distinct[OF dx zv_lookup_zv_empty] obtain t0 where
    t0: "zv_insert_list xs zv_empty = Some t0"
      "\<forall>k. zv_lookup t0 k = (case map_of xs k of Some x \<Rightarrow> Some x | None \<Rightarrow> zv_lookup zv_empty k)"
    by blast
  have t0': "\<forall>k. zv_lookup t0 k = map_of xs k"
  proof
    fix k show "zv_lookup t0 k = map_of xs k" using spec[OF t0(2), of k] by (cases "map_of xs k") auto
  qed
  have tab': "tab' = t0" using mk t0(1) by (simp add: make_inst_def return_def)
  have xsl: "\<exists>x. (k, x) \<in> set ?d \<and> (\<forall>t'. term x = return t' \<longrightarrow> map_of xs (fst k, typ (snd k)) = Some t')"
    if "(k, x) \<in> set ?d" for k x
  proof -
    from that obtain i where i: "i < length ?d" "?d ! i = (k, x)" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF l2 i(1)] i obtain t' where xi: "xs ! i = ((fst k, typ (snd k)), t')" "term x = return t'"
      by (cases "xs ! i") auto
    have "i < length xs" using i(1) list_all2_lengthD[OF l2] by simp
    then have "map_of xs (fst k, typ (snd k)) = Some t'" using dx xi(1)
      by (metis map_of_is_SomeI nth_mem)
    with xi(2) that show ?thesis by auto
  qed
  have keys': "zv_lookup tab' k' \<noteq> None \<longleftrightarrow> (\<exists>k. k' = (fst k, typ (snd k)) \<and> zv_lookup tab k \<noteq> None)" for k'
  proof -
    have "zv_lookup tab' k' \<noteq> None \<longleftrightarrow> k' \<in> set (map fst xs)" by (simp add: tab' t0' map_of_eq_None_iff)
    also have "\<dots> \<longleftrightarrow> (\<exists>k. k' = (fst k, typ (snd k)) \<and> zv_lookup tab k \<noteq> None)" using ds(2) by (force simp: fx)
    finally show ?thesis .
  qed
  show ok': "ztab_names_ok tab'"
    unfolding ztab_names_ok_def
  proof (intro allI impI)
    fix k1 k2 assume "zv_lookup tab' k1 \<noteq> None" "zv_lookup tab' k2 \<noteq> None" "fst k1 = fst k2"
    then obtain j1 j2 where j: "k1 = (fst j1, typ (snd j1))" "zv_lookup tab j1 \<noteq> None"
      "k2 = (fst j2, typ (snd j2))" "zv_lookup tab j2 \<noteq> None" using keys' by blast
    with \<open>fst k1 = fst k2\<close> have "fst j1 = fst j2" by simp
    with j(2,4) ok have "j1 = j2" unfolding ztab_names_ok_def by blast
    with j(1,3) show "k1 = k2" by simp
  qed
  have "(\<forall>T. zv_lookup tab' (xi, T) = None) \<longleftrightarrow> (\<forall>T. zv_lookup tab (xi, T) = None)"
  proof
    assume a: "\<forall>T. zv_lookup tab' (xi, T) = None"
    show "\<forall>T. zv_lookup tab (xi, T) = None"
    proof (rule ccontr)
      assume "\<not> (\<forall>T. zv_lookup tab (xi, T) = None)"
      then obtain T where "zv_lookup tab (xi, T) \<noteq> None" by blast
      then have "zv_lookup tab' (xi, typ T) \<noteq> None" using keys'[of "(xi, typ T)"] by fastforce
      then show False by (simp add: a)
    qed
  next
    assume a: "\<forall>T. zv_lookup tab (xi, T) = None"
    show "\<forall>T. zv_lookup tab' (xi, T) = None"
    proof (rule ccontr)
      assume "\<not> (\<forall>T. zv_lookup tab' (xi, T) = None)"
      then obtain T where "zv_lookup tab' (xi, T) \<noteq> None" by blast
      then obtain k where "(xi, T) = (fst k, typ (snd k))" "zv_lookup tab k \<noteq> None" using keys' by blast
      then have "zv_lookup tab (xi, snd k) \<noteq> None" by (cases k) auto
      then show False by (simp add: a)
    qed
  qed
  then show "zv_lookup_name tab' xi = None \<longleftrightarrow> zv_lookup_name tab xi = None"
    by (simp add: zv_lookup_name_None[OF ok] zv_lookup_name_None[OF ok'])
  assume "zv_lookup_name tab xi = Some t"
  then obtain T where T: "zv_lookup tab (xi, T) = Some t" by (blast dest: zv_lookup_nameD)
  then have "((xi, T), t) \<in> set ?d" using ds(2) by simp
  from xsl[OF this] obtain x where x: "((xi, T), x) \<in> set ?d"
    "\<forall>t'. term x = return t' \<longrightarrow> map_of xs (xi, typ T) = Some t'" by auto
  from x(1) ds(2) have "zv_lookup tab (xi, T) = Some x" by simp
  with T have "x = t" by simp
  from x(1) obtain t' where "term t = return t'"
    using l2 \<open>x = t\<close> by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
  with x(2) \<open>x = t\<close> have "zv_lookup tab' (xi, typ T) = Some t'" by (simp add: tab' t0')
  with \<open>term t = return t'\<close> show "\<exists>t'. term t = return t' \<and> zv_lookup_name tab' xi = Some t'"
    using zv_lookup_name_Some[OF ok'] by blast
qed

lemma map_insts_values:
  assumes m: "map_insts typ term (instT, tab) = return (instT', tab')" and ok: "ztab_names_ok tab"
    and l: "zv_lookup tab' k = Some t'"
  shows "\<exists>k0 t. zv_lookup tab k0 = Some t \<and> term t = return t'"
proof -
  obtain xi T where k: "k = (xi, T)" by (cases k)
  have ok': "ztab_names_ok tab'" by (rule map_insts_names(1)[OF m ok])
  have n': "zv_lookup_name tab' xi = Some t'" using zv_lookup_name_Some[OF ok'] l k by simp
  then obtain t where n: "zv_lookup_name tab xi = Some t" using map_insts_names(2)[OF m ok, of xi] by auto
  from map_insts_names(3)[OF m ok n] n' have "term t = return t'" by auto
  moreover from zv_lookup_nameD[OF n] obtain U where "zv_lookup tab (xi, U) = Some t" by blast
  ultimately show ?thesis by blast
qed

text \<open>Instances mapped by a total function:\<close>

lemma map_insts_return:
  assumes ok: "ztab_names_ok tab"
  shows "\<exists>tab'. map_insts typ (\<lambda>t. return (f t)) (instT, tab) = return (zt_map typ instT, tab') \<and>
    ztab_names_ok tab' \<and> (\<forall>xi. zv_lookup_name tab' xi = map_option f (zv_lookup_name tab xi))"
proof -
  let ?d = "zv_dest tab"
  let ?xs = "map (\<lambda>((x, T), t). ((x, typ T), f t)) ?d"
  have ds: "distinct (map fst ?d)" "set ?d = {(k, x). zv_lookup tab k = Some x}"
    using zv_dest_spec[of tab] by simp_all
  have m: "mapM (\<lambda>((x, T), t). return ((x, typ T), f t)) ?d = return ?xs"
    unfolding mapZ_eq_returnZ list.rel_map by (rule list.rel_refl) auto
  have fx: "map fst ?xs = map (\<lambda>k. (fst k, typ (snd k))) (map fst ?d)" by (auto split: prod.splits)
  have inj: "inj_on (\<lambda>k. (fst k, typ (snd k))) (fst ` set ?d)"
    using ok ds(2) by (auto simp: inj_on_def ztab_names_ok_def)
  have "distinct (map (\<lambda>k. (fst k, typ (snd k))) (map fst ?d))"
    by (rule distinct_map[THEN iffD2]) (simp add: ds(1) inj)
  then have dx: "distinct (map fst ?xs)" by (simp only: fx)
  from zv_insert_list_distinct[OF dx zv_lookup_zv_empty] obtain t0 where
    "zv_insert_list ?xs zv_empty = Some t0" by blast
  then have mi: "map_insts typ (\<lambda>t. return (f t)) (instT, tab) = return (zt_map typ instT, t0)"
    by (simp add: map_insts_def m make_inst_def)
  have "zv_lookup_name t0 xi = map_option f (zv_lookup_name tab xi)" for xi
  proof (cases "zv_lookup_name tab xi")
    case None
    then show ?thesis using map_insts_names(2)[OF mi ok, of xi] by simp
  next
    case (Some t)
    then show ?thesis using map_insts_names(3)[OF mi ok Some] by simp
  qed
  with mi map_insts_names(1)[OF mi ok] show ?thesis by blast
qed

context pure_sig
begin

lemma zconst_tr_map_tab:
  assumes "F MinProof = MinProof" "\<And>a. F (equality_axm a) = equality_axm a"
    "\<And>p u. F (PAppt p (Some u)) = PAppt (F p) (Some (g u))"
    "\<And>xi. zv_lookup_name tab' xi = map_option f (zv_lookup_name tab xi)"
    "\<And>k t. zv_lookup tab k = Some t \<Longrightarrow> g (zdec t) = zdec (f t)"
    "\<And>n A. F (PAxm n A None) = PAxm n A None" "\<And>p. F (PAppt p None) = PAppt (F p) None"
    "\<And>A. F (PThm (zthm_head A)) = PThm (zthm_head A)"
  shows "F (zconst_tr (c, instT, tab)) = zconst_tr (c, instT', tab')"
proof -
  obtain nm A where c: "c = (nm, A)" by (cases c)
  have l: "map_option g (map_option zdec (zv_lookup_name tab xi)) =
      map_option zdec (zv_lookup_name tab' xi)" for xi
  proof (cases "zv_lookup_name tab xi")
    case (Some t)
    from zv_lookup_nameD[OF Some] obtain T where "zv_lookup tab (xi, T) = Some t" by blast
    with Some assms(4,5) show ?thesis by simp
  qed (simp add: assms(4))
  show ?thesis
  proof (cases nm)
    case (ZAxiom n)
    show ?thesis
    proof (cases "zeq_const n A")
      case True
      have "F (zeq_tr n (\<lambda>x. map_option zdec (zv_lookup_name tab (x, -1)))) =
          zeq_tr n (\<lambda>x. map_option g (map_option zdec (zv_lookup_name tab (x, -1))))"
        by (rule zeq_tr_map[OF assms(1-3)])
      then show ?thesis using True by (simp add: zconst_tr_def c ZAxiom l)
    next
      case False
      have "F (zax_tr n (zdec A) (\<lambda>xi. map_option zdec (zv_lookup_name tab xi))) =
          zax_tr n (zdec A) (\<lambda>xi. map_option g (map_option zdec (zv_lookup_name tab xi)))"
        by (rule zax_tr_map[OF assms(6,3,7)])
      then show ?thesis using False by (simp add: zconst_tr_def c ZAxiom l)
    qed
  next
    case (ZThm n)
    have "F (zthm_tr (zdec A) (\<lambda>xi. map_option zdec (zv_lookup_name tab xi))) =
        zthm_tr (zdec A) (\<lambda>xi. map_option g (map_option zdec (zv_lookup_name tab xi)))"
      by (rule zthm_tr_map[OF assms(8,3,7)])
    then show ?thesis by (simp add: zconst_tr_def c ZThm l)
  qed (simp_all add: zconst_tr_def c assms(1))
qed

lemma zconst_tr_map:
  assumes "F MinProof = MinProof" "\<And>a. F (equality_axm a) = equality_axm a"
    "\<And>p u. F (PAppt p (Some u)) = PAppt (F p) (Some (g u))"
    "\<And>k t. zv_lookup tab k = Some t \<Longrightarrow> g (zdec t) = zdec (f t)"
    "\<And>n A. F (PAxm n A None) = PAxm n A None" "\<And>p. F (PAppt p None) = PAppt (F p) None"
    "\<And>A. F (PThm (zthm_head A)) = PThm (zthm_head A)"
  shows "F (zconst_tr (c, instT, tab)) = zconst_tr (c, instT, zv_map f tab)"
  by (rule zconst_tr_map_tab[where F = F and g = g and tab' = "zv_map f tab" and f = f and tab = tab])
    (use assms in simp_all)

end

end
