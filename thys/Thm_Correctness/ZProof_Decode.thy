section \<open>Decoding tight terms and proofs\<close>

theory ZProof_Decode
  imports Proof_Bicompose "Pure_Thm.Pure_ZTerm"
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

fun zprf_tr :: "zproof \<Rightarrow> prf" where
  "zprf_tr ZNop = MinProof"
| "zprf_tr (ZConstp c) = MinProof"
| "zprf_tr (ZBoundp i) = PBound i"
| "zprf_tr (ZAbst a T p) = Abst a (Some (typ_of T)) (zprf_tr p)"
| "zprf_tr (ZAbsp a t p) = AbsP a (Some (zdec t)) (zprf_tr p)"
| "zprf_tr (ZAppt p t) = PAppt (zprf_tr p) (Some (zdec t))"
| "zprf_tr (ZAppp p q) = PAppp (zprf_tr p) (zprf_tr q)"
| "zprf_tr (ZHyp t) = Hyp (zdec t)"
| "zprf_tr (OFCLASSp T c) = PClass (typ_of T) c"

end

text \<open>
  Proof constants do not occur in the tight proofs of the theorems built here (the classic
  translation has no counterpart for their instantiations).
\<close>

fun zconst_free :: "zproof \<Rightarrow> bool" where
  "zconst_free (ZConstp c) = False"
| "zconst_free (ZAbst a T p) = zconst_free p"
| "zconst_free (ZAbsp a t p) = zconst_free p"
| "zconst_free (ZAppt p t) = zconst_free p"
| "zconst_free (ZAppp p q) = (zconst_free p \<and> zconst_free q)"
| "zconst_free _ = True"

end
