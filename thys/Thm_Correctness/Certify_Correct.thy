section \<open>Certified terms and types are well formed\<close>

theory Certify_Correct
  imports Thm_Example "Pure_Thm.Pure_Certify"
begin

text \<open>
  The rules of \<^const>\<open>derivable\<close> take certified terms and types with the premises
  \<^const>\<open>cterm_ok\<close> and \<^const>\<open>ctyp_ok\<close>. This theory shows that the models of
  \<open>Thm.global_cterm_of\<close> and \<open>Thm.global_ctyp_of\<close> (theory \<^theory_text>\<open>Pure_Certify\<close>) establish
  them: a result of certification is a closed term with certified types, well-typed over the
  signature with the returned type, with indices from \<open>0\<close> to its maximal index, and its sorts
  are the finitely many sorts of the term, which are sorts over the classes of the signature
  (\<^const>\<open>csorts_ok\<close>).

  The parts of the signature that certification reads are related to the signature of the
  correctness theories by three assumptions. \<open>tsig_ok\<close>: the declared number of arguments of a
  type constructor is its arity, and the right-hand side of a type abbreviation (that is not
  syntactic) is a type over the logical type constructors, with their numbers of arguments,
  declared classes and indices from \<open>0\<close> (\<open>typ_logical\<close>: a type that certification returns as it
  is). \<open>consts_ok\<close>: the type schemes of the constants have no free type variables, and \<open>Pure.imp\<close>
  and \<open>Pure.all\<close> have their types (if the table has them: the typing judgment gives these two
  constants their types by itself). \<open>abbrs_ok\<close>: the right-hand side of an abbreviation of a
  constant is a closed term of the type of the constant, without schematic variables, with
  indices of type variables from \<open>0\<close>. The right-hand sides are results of certification
  themselves, so the last assumption is an invariant of the table: \<open>abbrs_ok_update\<close> below.
\<close>

fun typ_logical :: "algebra \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> ptyp \<Rightarrow> bool" where
  "typ_logical alg td (Type c Ts) \<longleftrightarrow>
    td c = Some (Logical_Type (len Ts)) \<and> (\<forall>T\<in>set Ts. typ_logical alg td T)"
| "typ_logical alg td (TFree a S) \<longleftrightarrow> cert_sort alg S"
| "typ_logical alg td (TVar v S) \<longleftrightarrow> 0 \<le> snd v \<and> cert_sort alg S"

definition tsig_ok :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> bool" where
  "tsig_ok alg ar td \<longleftrightarrow>
    (\<forall>a n. td a = Some (Logical_Type n) \<longrightarrow> n = of_nat (tarity ar a)) \<and>
    (\<forall>a vs U. td a = Some (Abbreviation vs U False) \<longrightarrow> typ_logical alg td U)"

lemma tsig_okD: "tsig_ok alg ar td \<Longrightarrow> \<forall>a vs U. td a = Some (Abbreviation vs U False) \<longrightarrow> typ_logical alg td U"
  by (simp add: tsig_ok_def)

definition consts_ok :: "(name \<Rightarrow> ptyp option) \<Rightarrow> bool" where
  "consts_ok ctab \<longleftrightarrow> (\<forall>c U. ctab c = Some U \<longrightarrow> no_tfrees U) \<and>
    (\<forall>U. ctab STR ''Pure.imp'' = Some U \<longrightarrow>
      U = Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' []) \<and>
    (\<forall>U. ctab STR ''Pure.all'' = Some U \<longrightarrow>
      (\<exists>v S. U = (TVar v S \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []))"

definition abbrs_ok :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (name \<Rightarrow> ptyp option) \<Rightarrow> (name \<Rightarrow> pterm option) \<Rightarrow> bool" where
  "abbrs_ok alg ar ctab abbrs \<longleftrightarrow>
    (\<forall>c rhs U. abbrs c = Some rhs \<longrightarrow> ctab c = Some U \<longrightarrow>
      closed rhs \<and> (\<forall>e. signature.typing (cert_typ alg ar) (const_typ_ok ctab) e rhs U) \<and>
      vars rhs = {} \<and> (\<forall>T\<in>typs rhs. tnn T))"


subsection \<open>Lists\<close>

lemma len_of_nat: "len xs = of_nat (length xs)"
  by (induction xs) auto

lemma len_eq_of_nat: "len xs = of_nat n \<longleftrightarrow> length xs = n"
  by (simp add: len_of_nat)

lemma len_map [simp]: "len (map f xs) = len xs"
  by (induction xs) auto

lemma those_map_Some: "those_map f xs = Some ys \<Longrightarrow> list_all2 (\<lambda>x y. f x = Some y) xs ys"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma those_map_id: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = Some x) \<Longrightarrow> those_map f xs = Some xs"
  by (induction xs) auto

lemma nth_opt_Some: "nth_opt bs i = Some T \<longleftrightarrow> (\<exists>n<length bs. i = of_nat n \<and> T = bs ! n)"
proof (induction bs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  show ?case
  proof (cases "i = 0")
    case True
    then show ?thesis by auto
  next
    case False
    show ?thesis
    proof (cases "i < 0")
      case True
      then have "i \<noteq> of_nat n" for n :: nat by (metis not_less of_nat_0_le_iff)
      with True False show ?thesis by simp
    next
      case nn: False
      have "(\<exists>n<length (b # bs). i = of_nat n \<and> T = (b # bs) ! n) \<longleftrightarrow>
          (\<exists>n<length bs. i - 1 = of_nat n \<and> T = bs ! n)" (is "?L \<longleftrightarrow> ?R")
      proof
        assume ?L
        then obtain n where n: "n < length (b # bs)" "i = of_nat n" "T = (b # bs) ! n" by blast
        with False obtain m where m: "n = Suc m" by (cases n) auto
        with n show ?R by (intro exI[of _ m]) auto
      next
        assume ?R
        then obtain n where n: "n < length bs" "i - 1 = of_nat n" "T = bs ! n" by blast
        then have "i = of_nat (Suc n)" by simp
        with n show ?L by (intro exI[of _ "Suc n"]) auto
      qed
      with False nn Cons.IH[of "i - 1"] show ?thesis by simp
    qed
  qed
qed


subsection \<open>Types\<close>

lemma inst_frees_logical:
  assumes "\<forall>T\<in>snd ` set tab. typ_logical alg td T"
  shows "typ_logical alg td U \<Longrightarrow> typ_logical alg td (inst_frees tab U)"
proof (induction U)
  case (TFree a S)
  show ?case
  proof (cases "S = [] \<and> map_of tab a \<noteq> None")
    case True
    then obtain T where T: "map_of tab a = Some T" by blast
    then have "T \<in> snd ` set tab" by (force dest: map_of_SomeD)
    with assms True T show ?thesis by auto
  next
    case False
    with TFree show ?thesis by (auto split: option.splits)
  qed
qed auto

lemma cert_sort_ok: "cert_sort alg S \<Longrightarrow> sort_ok alg S"
  by (auto simp: cert_sort_def sort_ok_def class_mem_def list_all_iff)

text \<open>A certified type is a type over the logical type constructors:\<close>

lemma certify_typ_logical:
  "certify_typ alg td T = Some T' \<Longrightarrow>
    \<forall>a vs U. td a = Some (Abbreviation vs U False) \<longrightarrow> typ_logical alg td U \<Longrightarrow> typ_logical alg td T'"
proof (induction alg td T arbitrary: T' rule: certify_typ.induct)
  case (1 alg td c args)
  note ab = "1.prems"(2)
  from "1.prems"(1) obtain decl where d: "td c = Some decl" by (auto split: option.splits)
  show ?case
  proof (cases decl)
    case (Logical_Type n)
    with "1.prems"(1) d obtain args' where l: "len args = n"
      and a: "those_map (certify_typ alg td) args = Some args'" and T': "T' = Type c args'"
      by (auto split: if_splits)
    note la = those_map_Some[OF a]
    have ok: "typ_logical alg td U'" if "U' \<in> set args'" for U'
    proof -
      from that obtain i where i: "i < length args'" "U' = args' ! i" by (auto simp: in_set_conv_nth)
      with la have "args ! i \<in> set args" "certify_typ alg td (args ! i) = Some U'"
        by (auto simp: list_all2_conv_all_nth)
      then show ?thesis using "1.IH"(1)[OF d Logical_Type _ _ ] l ab by auto
    qed
    have "len args' = n" using la l by (simp add: len_of_nat list_all2_lengthD)
    with ok d show ?thesis by (simp add: T' Logical_Type)
  next
    case (Abbreviation vs U syntactic)
    with "1.prems"(1) d obtain args' where l: "len args = len vs" and ns: "\<not> syntactic"
      and a: "those_map (certify_typ alg td) args = Some args'"
      and T': "T' = inst_frees (zip vs args') U"
      by (auto split: if_splits)
    note la = those_map_Some[OF a]
    have ok: "typ_logical alg td U'" if "U' \<in> set args'" for U'
    proof -
      from that obtain i where i: "i < length args'" "U' = args' ! i" by (auto simp: in_set_conv_nth)
      with la have "args ! i \<in> set args" "certify_typ alg td (args ! i) = Some U'"
        by (auto simp: list_all2_conv_all_nth)
      then show ?thesis using "1.IH"(2)[OF d Abbreviation _ _ ] l ns ab by auto
    qed
    have U: "typ_logical alg td U" using ab[rule_format, of c vs U] d ns by (simp add: Abbreviation)
    have sub: "snd ` set (zip vs args') \<subseteq> set args'" by (auto dest: set_zip_rightD)
    show ?thesis unfolding T' by (rule inst_frees_logical) (use ok sub U in auto)
  next
    case Nonterminal
    with "1.prems"(1) d show ?thesis by simp
  qed
next
  case (2 alg td a S)
  then show ?case by (auto split: if_splits)
next
  case (3 alg td x i S)
  then show ?case by (auto split: if_splits)
qed

text \<open>Certification returns such a type as it is; in particular, a second certification of
  a certified type is the identity.\<close>

lemma typ_logical_fix: "typ_logical alg td T \<Longrightarrow> certify_typ alg td T = Some T"
proof (induction T)
  case (Type c Ts)
  then have "those_map (certify_typ alg td) Ts = Some Ts" by (intro those_map_id) auto
  with Type.prems show ?case by simp
next
  case (TVar v S)
  then show ?case by (cases v) auto
qed auto

lemma certify_typ_idem:
  "certify_typ alg td T = Some T' \<Longrightarrow> tsig_ok alg ar td \<Longrightarrow> certify_typ alg td T' = Some T'"
  by (rule typ_logical_fix[OF certify_typ_logical[OF _ tsig_okD]])

lemma typ_logical_ok: "typ_logical alg td T \<Longrightarrow> tsig_ok alg ar td \<Longrightarrow> cert_typ alg ar T \<and> tnn T"
proof (induction T)
  case (Type c Ts)
  from Type.prems have "len Ts = of_nat (tarity ar c)" unfolding tsig_ok_def by auto
  then have "length Ts = tarity ar c" by (simp add: len_eq_of_nat)
  with Type show ?case by (fastforce simp: cert_typ_def tnn_def)
next
  case (TFree a S)
  then show ?case by (auto simp: cert_typ_def tnn_def cert_sort_ok)
next
  case (TVar v S)
  then show ?case by (auto simp: cert_typ_def tnn_def cert_sort_ok)
qed

lemma certify_typ_ok:
  "certify_typ alg td T = Some T' \<Longrightarrow> tsig_ok alg ar td \<Longrightarrow> cert_typ alg ar T' \<and> tnn T'"
  by (rule typ_logical_ok[OF certify_typ_logical[OF _ tsig_okD]])


subsection \<open>Terms\<close>

lemma certify_types_ok:
  assumes ts: "tsig_ok alg ar td"
  shows "certify_types alg td t = Some t' \<Longrightarrow>
    (\<forall>T\<in>typs t'. typ_logical alg td T) \<and> (check_vars t \<longrightarrow> (\<forall>x i T. ((x, i), T) \<in> vars t' \<longrightarrow> 0 \<le> i))"
proof (induction t arbitrary: t')
  case (Var v T)
  obtain x i where v: "v = (x, i)" by (cases v)
  from Var show ?case using certify_typ_logical[OF _ tsig_okD[OF ts]] by (auto simp: v)
next
  case (Abs a T t)
  from Abs.prems obtain T' u where T': "certify_typ alg td T = Some T'"
    and u: "certify_types alg td t = Some u" and t': "t' = Abs a T' u"
    by (auto split: option.splits)
  from Abs.IH[OF u] certify_typ_logical[OF T' tsig_okD[OF ts]] show ?case by (simp add: t')
next
  case (App t u)
  from App.prems obtain t1 u1 where t1: "certify_types alg td t = Some t1"
    and u1: "certify_types alg td u = Some u1" and t': "t' = t1 $ u1"
    by (auto split: option.splits)
  from App.IH(1)[OF t1] App.IH(2)[OF u1] show ?case by (auto simp: t'; blast)
qed (use certify_typ_logical[OF _ tsig_okD[OF ts]] in auto)

lemma certify_types_vars: "certify_types alg td t = Some t' \<Longrightarrow> vars t = {} \<Longrightarrow> vars t' = {}"
  by (induction t arbitrary: t') (auto split: option.splits)

text \<open>Matching: the instance is the pattern under the bindings.\<close>

definition rho_of :: "tyenv \<Rightarrow> tinst" where
  "rho_of \<theta> v S = (case vt_lookup \<theta> v of Some (S', T) \<Rightarrow> T | None \<Rightarrow> TVar v S)"

definition tyext :: "tyenv \<Rightarrow> tyenv \<Rightarrow> bool" where
  "tyext \<theta> \<theta>' \<longleftrightarrow> (\<forall>v x. vt_lookup \<theta> v = Some x \<longrightarrow> vt_lookup \<theta>' v = Some x)"

lemma tyext_refl [simp]: "tyext \<theta> \<theta>"
  and tyext_trans: "tyext \<theta> \<theta>' \<Longrightarrow> tyext \<theta>' \<theta>'' \<Longrightarrow> tyext \<theta> \<theta>''"
  by (auto simp: tyext_def)

lemma raw_match_sound:
  "raw_match U T \<theta> = Some \<theta>' \<Longrightarrow> tyext \<theta> \<theta>' \<and> (\<forall>\<theta>''. tyext \<theta>' \<theta>'' \<longrightarrow> tsubst (rho_of \<theta>'') U = T)"
  "raw_matches Us Ts \<theta> = Some \<theta>' \<Longrightarrow>
    tyext \<theta> \<theta>' \<and> (\<forall>\<theta>''. tyext \<theta>' \<theta>'' \<longrightarrow> map (tsubst (rho_of \<theta>'')) Us = Ts)"
proof (induction U T \<theta> and Us Ts \<theta> arbitrary: \<theta>' and \<theta>' rule: raw_match_raw_matches.induct)
  case (1 v S T subs)
  show ?case
  proof (cases "vt_lookup subs v")
    case None
    with "1.prems" have \<theta>': "\<theta>' = vt_update (v, (S, T)) subs" by simp
    have "tyext subs \<theta>'" using None by (auto simp: \<theta>' tyext_def)
    moreover have "tsubst (rho_of \<theta>'') (TVar v S) = T" if "tyext \<theta>' \<theta>''" for \<theta>''
    proof -
      have "vt_lookup \<theta>'' v = Some (S, T)"
        using that[unfolded tyext_def, rule_format, of v "(S, T)"] by (simp add: \<theta>')
      then show ?thesis by (simp add: rho_of_def)
    qed
    ultimately show ?thesis by blast
  next
    case (Some p)
    obtain S' U where p: "p = (S', U)" by (cases p)
    with "1.prems" Some have e: "S = S'" "U = T" "\<theta>' = subs" by (auto split: if_splits)
    have "tsubst (rho_of \<theta>'') (TVar v S) = T" if "tyext \<theta>' \<theta>''" for \<theta>''
    proof -
      have "vt_lookup \<theta>'' v = Some (S, T)"
        using that[unfolded tyext_def, rule_format, of v "(S, T)"] Some p e by simp
      then show ?thesis by (simp add: rho_of_def)
    qed
    then show ?thesis by (simp add: e)
  qed
next
  case (2 a Ts b Us subs)
  then show ?case by (auto split: if_splits)
next
  case (3 a S b S' subs)
  then show ?case by (auto split: if_splits)
next
  case (8 T Ts U Us subs)
  from "8.prems" obtain s where s: "raw_match T U subs = Some s" and r: "raw_matches Ts Us s = Some \<theta>'"
    by (auto split: option.splits)
  note A = "8.IH"(1)[OF s] and B = "8.IH"(2)[OF s r]
  have "tyext subs \<theta>'" using A B tyext_trans by blast
  moreover have "map (tsubst (rho_of \<theta>'')) (T # Ts) = U # Us" if "tyext \<theta>' \<theta>''" for \<theta>''
    using A B that tyext_trans by auto
  ultimately show ?case by blast
qed auto

lemma raw_instance_tsubst: "raw_instance T U \<Longrightarrow> \<exists>\<rho>. T = tsubst \<rho> U"
proof -
  assume "raw_instance T U"
  then obtain \<theta> where "raw_match U T vt_empty = Some \<theta>" by (auto simp: raw_instance_def)
  from raw_match_sound(1)[OF this] have "tsubst (rho_of \<theta>) U = T" by simp
  then show ?thesis by metis
qed

text \<open>\<open>Type.could_match\<close> is a filter: it holds whenever the matching succeeds.\<close>

lemma raw_match_could_match:
  "raw_match U T \<theta> \<noteq> None \<Longrightarrow> could_match U T"
  "raw_matches Us Ts \<theta> \<noteq> None \<Longrightarrow> could_matches Us Ts"
  by (induction U T \<theta> and Us Ts \<theta> rule: raw_match_raw_matches.induct)
    (auto split: option.splits if_splits)

lemma raw_instance_iff: "raw_instance T U \<longleftrightarrow> raw_match U T vt_empty \<noteq> None"
  using raw_match_could_match(1) by (auto simp: raw_instance_def)

text \<open>The types of the bindings are subterms of the instance.\<close>

definition tyenv_ran :: "tyenv \<Rightarrow> ptyp set" where
  "tyenv_ran \<theta> = {T. \<exists>v S. vt_lookup \<theta> v = Some (S, T)}"

lemma tyenv_ran_empty [simp]: "tyenv_ran vt_empty = {}"
  by (simp add: tyenv_ran_def)

lemma rho_of_ran: "rho_of \<theta> v S = TVar v S \<or> rho_of \<theta> v S \<in> tyenv_ran \<theta>"
proof (cases "vt_lookup \<theta> v")
  case None
  then show ?thesis by (simp add: rho_of_def)
next
  case (Some p)
  obtain S' T where p: "p = (S', T)" by (cases p)
  with Some have "T \<in> tyenv_ran \<theta>" unfolding tyenv_ran_def by blast
  with Some p show ?thesis by (simp add: rho_of_def)
qed

lemma raw_match_ran:
  assumes sub: "\<And>a Ts T. Q (Type a Ts) \<Longrightarrow> T \<in> set Ts \<Longrightarrow> Q T"
  shows "raw_match U T \<theta> = Some \<theta>' \<Longrightarrow> Q T \<Longrightarrow> \<forall>X\<in>tyenv_ran \<theta>. Q X \<Longrightarrow> \<forall>X\<in>tyenv_ran \<theta>'. Q X"
    and "raw_matches Us Ts \<theta> = Some \<theta>' \<Longrightarrow> \<forall>T\<in>set Ts. Q T \<Longrightarrow> \<forall>X\<in>tyenv_ran \<theta>. Q X \<Longrightarrow>
      \<forall>X\<in>tyenv_ran \<theta>'. Q X"
proof (induction U T \<theta> and Us Ts \<theta> arbitrary: \<theta>' and \<theta>' rule: raw_match_raw_matches.induct)
  case (1 v S T subs)
  have "tyenv_ran \<theta>' \<subseteq> insert T (tyenv_ran subs)"
  proof (cases "vt_lookup subs v")
    case None
    with "1.prems"(1) have "\<theta>' = vt_update (v, (S, T)) subs" by simp
    then show ?thesis by (auto simp: tyenv_ran_def split: if_splits)
  next
    case (Some p)
    with "1.prems"(1) have "\<theta>' = subs" by (cases p) (auto split: if_splits)
    then show ?thesis by blast
  qed
  with "1.prems"(2,3) show ?case by blast
next
  case (2 a Ts b Us subs)
  from "2.prems"(1) have e: "a = b" and m: "raw_matches Ts Us subs = Some \<theta>'" by (auto split: if_splits)
  from "2.prems"(2) sub have "\<forall>T\<in>set Us. Q T" by blast
  with "2.IH"[OF _ m] e "2.prems"(3) show ?case by simp
next
  case (3 a S b S' subs)
  then show ?case by (auto split: if_splits)
next
  case (8 T Ts U Us subs)
  from "8.prems"(1) obtain s where s: "raw_match T U subs = Some s" and r: "raw_matches Ts Us s = Some \<theta>'"
    by (auto split: option.splits)
  from "8.IH"(1)[OF s] "8.prems"(2,3) have "\<forall>X\<in>tyenv_ran s. Q X" by simp
  with "8.IH"(2)[OF s r] "8.prems"(2) show ?case by simp
qed auto

text \<open>\<open>Envir.subst_term_types\<close> is the instantiation with the bindings.\<close>

lemma subst_typ0_tsubst: "subst_typ0 \<theta> T = Some T' \<Longrightarrow> T' = tsubst (rho_of \<theta>) T"
proof (induction T arbitrary: T')
  case (Type a Ts)
  from Type.prems obtain Ts' where s: "those_map (subst_typ0 \<theta>) Ts = Some Ts'" and T': "T' = Type a Ts'"
    by auto
  have "Ts' = map (tsubst (rho_of \<theta>)) Ts"
  proof (rule nth_equalityI)
    show l: "length Ts' = length (map (tsubst (rho_of \<theta>)) Ts)"
      using those_map_Some[OF s] by (simp add: list_all2_lengthD)
    fix i assume "i < length Ts'"
    with l those_map_Some[OF s] have "Ts ! i \<in> set Ts" "subst_typ0 \<theta> (Ts ! i) = Some (Ts' ! i)"
      by (auto simp: list_all2_conv_all_nth)
    from Type.IH[OF this] l \<open>i < length Ts'\<close> show "Ts' ! i = map (tsubst (rho_of \<theta>)) Ts ! i" by simp
  qed
  then show ?case by (simp add: T')
next
  case (TVar v S)
  then show ?case by (auto simp: rho_of_def split: option.splits if_splits)
qed auto

lemma subst_term_types_inst: "subst_term_types \<theta> t = Some t' \<Longrightarrow> t' = inst (rho_of \<theta>) t"
  by (induction t arbitrary: t') (auto split: option.splits dest: subst_typ0_tsubst)

lemma ctnn_tsubst:
  "cert_typ alg ar T \<and> tnn T \<Longrightarrow> (\<And>v S. (v, S) \<in> tvars T \<Longrightarrow> cert_typ alg ar (\<rho> v S) \<and> tnn (\<rho> v S)) \<Longrightarrow>
    cert_typ alg ar (tsubst \<rho> T) \<and> tnn (tsubst \<rho> T)"
  by (induction T) (fastforce simp: cert_typ_def tnn_def)+

lemma sorts_ok_tvars: "sorts_ok alg T \<Longrightarrow> (v, S) \<in> tvars T \<Longrightarrow> sort_ok alg S"
  by (induction T) auto

lemma (in signature) typing_typs_ok: "e \<turnstile> t : T \<Longrightarrow> U \<in> typs t \<Longrightarrow> ty_ok U"
  by (induction rule: typing.induct) auto

lemma (in signature) typing_const_mono:
  "e \<turnstile> t : T \<Longrightarrow> (\<And>c T. const_ok c T \<Longrightarrow> cok c T) \<Longrightarrow> signature.typing ty_ok cok e t T"
  by (induction rule: typing.induct) (auto intro!: signature.typing.intros)

lemma typs_inst_image: "typs (inst \<rho> t) = tsubst \<rho> ` typs t"
  by (induction t) auto

text \<open>The instance of the right-hand side of an abbreviation: its variables and types.\<close>

lemma expand_atom_typs:
  assumes ab: "abbrs_ok alg ar ctab abbrs" and a: "abbrs c = Some rhs" and c: "ctab c = Some U"
    and T: "cert_typ alg ar T" "tnn T" and x: "expand_atom T U rhs = Some r"
  obtains \<rho> where "r = inst \<rho> rhs" "tsubst \<rho> U = T" "\<And>v S. sort_ok alg S \<Longrightarrow> cert_typ alg ar (\<rho> v S)"
    "vars r = {}" "\<forall>V\<in>typs r. cert_typ alg ar V \<and> tnn V"
proof -
  from x obtain \<theta> where m: "raw_match U T vt_empty = Some \<theta>" and s: "subst_term_types \<theta> rhs = Some r"
    by (auto simp: expand_atom_def split: option.splits)
  define \<rho> where "\<rho> = rho_of \<theta>"
  have r: "r = inst \<rho> rhs" unfolding \<rho>_def by (rule subst_term_types_inst[OF s])
  have TU: "tsubst \<rho> U = T" using raw_match_sound(1)[OF m] by (simp add: \<rho>_def)
  have ran: "\<forall>X\<in>tyenv_ran \<theta>. cert_typ alg ar X \<and> tnn X"
    by (rule raw_match_ran(1)[where Q = "\<lambda>X. cert_typ alg ar X \<and> tnn X", OF _ m])
      (use T in \<open>fastforce simp: cert_typ_def tnn_def\<close>)+
  have ci: "cert_typ alg ar (\<rho> v S)" if "sort_ok alg S" for v S
    using rho_of_ran[of \<theta> v S] ran that by (auto simp: \<rho>_def cert_typ_def)
  from ab a c have rhs: "\<And>e. signature.typing (cert_typ alg ar) (const_typ_ok ctab) e rhs U"
    "vars rhs = {}" "\<forall>T\<in>typs rhs. tnn T"
    by (auto simp: abbrs_ok_def)
  have v: "vars r = {}" by (simp add: r vars_inst rhs(2))
  have "cert_typ alg ar V \<and> tnn V" if "V \<in> typs r" for V
  proof -
    from that obtain W where W: "W \<in> typs rhs" "V = tsubst \<rho> W" by (auto simp: r typs_inst_image)
    have cW: "cert_typ alg ar W \<and> tnn W" using signature.typing_typs_ok[OF rhs(1) W(1)] rhs(3) W(1) by blast
    have "cert_typ alg ar (\<rho> v S) \<and> tnn (\<rho> v S)" if "(v, S) \<in> tvars W" for v S
      using rho_of_ran[of \<theta> v S] ran cW that by (fastforce simp: \<rho>_def tnn_def cert_typ_def dest: sorts_ok_tvars)
    with cW show ?thesis unfolding W(2) by (intro ctnn_tsubst) auto
  qed
  with r TU ci v show ?thesis by (intro that) auto
qed

lemma certify_const_ok:
  assumes co: "consts_ok ctab" and c: "ctab c = Some U" and i: "raw_instance T U"
  shows "const_typ_ok ctab c T"
proof -
  from raw_instance_tsubst[OF i] obtain \<rho> where T: "T = tsubst \<rho> U" by blast
  from co c have nf: "no_tfrees U" by (auto simp: consts_ok_def)
  show ?thesis
  proof (cases "c = STR ''Pure.imp''")
    case True
    with co c have "U = Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' []"
      by (auto simp: consts_ok_def)
    with True T show ?thesis by (simp add: const_typ_ok_def)
  next
    case ni: False
    show ?thesis
    proof (cases "c = STR ''Pure.all''")
      case True
      with co c obtain v S where "U = (TVar v S \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []"
        by (auto simp: consts_ok_def)
      with True T show ?thesis by (simp add: const_typ_ok_def)
    next
      case False
      with ni c nf T show ?thesis by (auto simp: const_typ_ok_def)
    qed
  qed
qed

text \<open>The constants of a term are declared, at instances of their type schemes: what the
  function \<open>term\<close> of \<open>Consts.certify\<close> checks.\<close>

fun consts_inst :: "(name \<Rightarrow> ptyp option) \<Rightarrow> pterm \<Rightarrow> bool" where
  "consts_inst ctab (Const c T) \<longleftrightarrow> (case ctab c of None \<Rightarrow> False | Some U \<Rightarrow> raw_instance T U)"
| "consts_inst ctab (Abs _ _ t) \<longleftrightarrow> consts_inst ctab t"
| "consts_inst ctab (t $ u) \<longleftrightarrow> consts_inst ctab t \<and> consts_inst ctab u"
| "consts_inst ctab _ \<longleftrightarrow> True"

lemma certify_plain_fix:
  "\<forall>T\<in>typs t. typ_logical alg td T \<Longrightarrow>
    certify_plain alg td ctab t = (if consts_inst ctab t then Some t else None)"
  by (induction t) (auto simp: typ_logical_fix split: option.splits)

lemma typ_of_closed: "typ_of bs t = Some T \<Longrightarrow> \<not> loose_bvar t (of_nat (length bs))"
proof (induction t arbitrary: bs T)
  case (Bound i)
  then show ?case by (auto simp: nth_opt_Some)
next
  case (Abs a U t)
  from Abs.prems obtain V where "typ_of (U # bs) t = Some V" by auto
  from Abs.IH[OF this] show ?case by (simp add: add.commute)
next
  case (App t u)
  then show ?case by (auto split: option.splits)
qed auto

subsection \<open>The expansion of abbreviations\<close>

text \<open>The result has the variables of the term, and its types are certified.\<close>

lemma betapplys_vars_typs:
  "vars (betapplys t us) \<subseteq> vars t \<union> \<Union>(vars ` set us) \<and> typs (betapplys t us) \<subseteq> typs t \<union> \<Union>(typs ` set us)"
proof (induction us arbitrary: t)
  case (Cons u us)
  have "vars (betapply t u) \<subseteq> vars t \<union> vars u \<and> typs (betapply t u) \<subseteq> typs t \<union> typs u"
  proof (cases t)
    case (Abs a U b)
    then show ?thesis using vars_subst[of b u 0] typs_subst[of b u 0] by (auto simp: subst_bound_subst)
  qed simp_all
  with Cons.IH[of "betapply t u"] show ?case by auto
qed simp

lemma expand_term_vars:
  assumes ts: "tsig_ok alg ar td" and ab: "abbrs_ok alg ar ctab abbrs"
  shows "expand_term alg td ctab abbrs t args = Some r \<Longrightarrow> \<forall>T\<in>typs t. typ_logical alg td T \<Longrightarrow>
    \<forall>a\<in>set args. \<forall>V\<in>typs a. cert_typ alg ar V \<and> tnn V \<Longrightarrow>
    vars r \<subseteq> vars t \<union> \<Union>(vars ` set args) \<and> (\<forall>V\<in>typs r. cert_typ alg ar V \<and> tnn V)"
proof (induction t arbitrary: args r)
  case (Const c T)
  from Const.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Const.prems(1) fx obtain U where U: "ctab c = Some U" and ri: "raw_instance T U"
    by (auto split: option.splits if_splits)
  show ?case
  proof (cases "abbrs c")
    case None
    with Const.prems(1) fx U ri have r: "r = list_comb (Const c T) args" by simp
    show ?thesis using okT Const.prems(3) by (auto simp: r list_comb_apps vars_apps typs_apps)
  next
    case (Some rhs)
    with Const.prems(1) fx U ri obtain r0 where x: "expand_atom T U rhs = Some r0"
      and r: "r = betapplys r0 args"
      by auto
    from expand_atom_typs[OF ab Some U _ _ x] okT
    have "vars r0 = {}" "\<forall>V\<in>typs r0. cert_typ alg ar V \<and> tnn V" by metis+
    with betapplys_vars_typs[of r0 args] Const.prems(3) show ?thesis unfolding r by blast
  qed
next
  case (Free x T)
  from Free.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Free.prems(1) fx have r: "r = list_comb (Free x T) args" by simp
  show ?case using okT Free.prems(3) by (auto simp: r list_comb_apps vars_apps typs_apps)
next
  case (Var v T)
  from Var.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Var.prems(1) fx have r: "r = list_comb (Var v T) args" by simp
  show ?case using okT Var.prems(3) by (auto simp: r list_comb_apps vars_apps typs_apps)
next
  case (Bound i)
  then show ?case by (auto simp: list_comb_apps vars_apps typs_apps)
next
  case (Abs a T t)
  from Abs.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Abs.prems(1) fx obtain t' where t': "expand_term alg td ctab abbrs t [] = Some t'"
    and r: "r = list_comb (Abs a T t') args"
    by auto
  from Abs.IH[OF t'] Abs.prems(2)
  have "vars t' \<subseteq> vars t" "\<forall>V\<in>typs t'. cert_typ alg ar V \<and> tnn V" by auto
  then show ?case using okT Abs.prems(3) by (auto simp: r list_comb_apps vars_apps typs_apps)
next
  case (App f u)
  from App.prems(1) obtain u' where u': "expand_term alg td ctab abbrs u [] = Some u'"
    and f: "expand_term alg td ctab abbrs f (u' # args) = Some r"
    by (auto split: option.splits)
  from App.IH(2)[OF u'] App.prems(2)
  have u: "vars u' \<subseteq> vars u" "\<forall>V\<in>typs u'. cert_typ alg ar V \<and> tnn V" by auto
  from App.IH(1)[OF f] App.prems(2,3) u(2)
  have "vars r \<subseteq> vars f \<union> \<Union>(vars ` set (u' # args))" "\<forall>V\<in>typs r. cert_typ alg ar V \<and> tnn V" by auto
  with u(1) show ?case by auto
qed

context pure_sig
begin

lemma abbrs_okD:
  assumes "abbrs_ok alg ar ctab abbrs" "abbrs c = Some rhs" "ctab c = Some U"
  shows "closed rhs" "e \<turnstile> rhs : U"
  using assms by (auto simp: abbrs_ok_def)

lemma loose_bvar_beta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar t k \<Longrightarrow> loose_bvar s k"
  by (induction rule: rtranclp_induct) (auto dest: loose_bvar_beta)

text \<open>The instance of the right-hand side of an abbreviation is closed and has the type of
  the constant.\<close>

lemma expand_atom_typing:
  assumes ab: "abbrs_ok alg ar ctab abbrs" and a: "abbrs c = Some rhs" and c: "ctab c = Some U"
    and T: "cert_typ alg ar T" "tnn T" and x: "expand_atom T U rhs = Some r"
  shows "closed r" "e \<turnstile> r : T"
proof -
  from expand_atom_typs[OF ab a c T x] obtain \<rho> where r: "r = inst \<rho> rhs" and TU: "tsubst \<rho> U = T"
    and ci: "\<And>v S. sort_ok alg S \<Longrightarrow> cert_typ alg ar (\<rho> v S)"
    by metis
  note rhs = abbrs_okD[OF ab a c]
  show cl: "closed r" using rhs(1) by (simp add: r closed_def)
  have "cert_inst \<rho>" using ci by (simp add: cert_inst_def)
  from typing_inst[OF rhs(2) cert_inst_inst_ok[OF this]]
  have "(\<lambda>j. tsubst \<rho> (e j)) \<turnstile> r : T" for e by (simp add: r TU)
  from typing_closed[OF this cl] show "e \<turnstile> r : T" .
qed

lemma shift_env_nth:
  assumes "\<forall>n<length bs. e (of_nat n) = bs ! n" and n: "n < length (U # bs)"
  shows "(e\<langle>0:U\<rangle>) (of_nat n) = (U # bs) ! n"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc m)
  with n assms(1) have "e (of_nat m) = bs ! m" by simp
  moreover have "(of_nat (Suc m) :: integer) > 0" by (metis of_nat_0_less_iff zero_less_Suc)
  ultimately show ?thesis using Suc by (simp add: shift_def)
qed

text \<open>The result is closed (up to the level of the term) and has the type of the term.\<close>

lemma expand_term_loose:
  assumes ts: "tsig_ok alg ar td" and ab: "abbrs_ok alg ar ctab abbrs"
  shows "expand_term alg td ctab abbrs t args = Some r \<Longrightarrow> \<forall>T\<in>typs t. typ_logical alg td T \<Longrightarrow>
    0 \<le> k \<Longrightarrow> \<not> loose_bvar t k \<Longrightarrow> \<forall>a\<in>set args. \<not> loose_bvar a k \<Longrightarrow> \<not> loose_bvar r k"
proof (induction t arbitrary: args r k)
  case (Const c T)
  from Const.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Const.prems(1) fx obtain U where U: "ctab c = Some U" and ri: "raw_instance T U"
    by (auto split: option.splits if_splits)
  show ?case
  proof (cases "abbrs c")
    case None
    with Const.prems(1) fx U ri have r: "r = list_comb (Const c T) args" by simp
    show ?thesis using Const.prems(5) by (simp add: r list_comb_apps loose_bvar_apps)
  next
    case (Some rhs)
    with Const.prems(1) fx U ri obtain r0 where x: "expand_atom T U rhs = Some r0"
      and r: "r = betapplys r0 args"
      by auto
    have "closed r0" by (rule expand_atom_typing(1)[OF ab Some U _ _ x]) (use okT in auto)
    then have "\<not> loose_bvar r0 k" using Const.prems(3) by (auto simp: closed_def dest: loose_bvar_mono)
    then have "\<not> loose_bvar (list_comb r0 args) k"
      using Const.prems(5) by (simp add: list_comb_apps loose_bvar_apps)
    then show ?thesis
      unfolding r using loose_bvar_beta_reds[OF betapplys_beta_reds Const.prems(3)] by blast
  qed
next
  case (Free x T)
  from Free.prems(2) have "certify_typ alg td T = Some T" by (simp add: typ_logical_fix)
  with Free.prems show ?case by (auto simp: list_comb_apps loose_bvar_apps)
next
  case (Var v T)
  from Var.prems(2) have "certify_typ alg td T = Some T" by (simp add: typ_logical_fix)
  with Var.prems show ?case by (auto simp: list_comb_apps loose_bvar_apps)
next
  case (Bound i)
  then show ?case by (auto simp: list_comb_apps loose_bvar_apps)
next
  case (Abs a T t)
  from Abs.prems(2) have fx: "certify_typ alg td T = Some T" by (simp add: typ_logical_fix)
  from Abs.prems(1) fx obtain t' where t': "expand_term alg td ctab abbrs t [] = Some t'"
    and r: "r = list_comb (Abs a T t') args"
    by auto
  have "\<not> loose_bvar t' (k + 1)" by (rule Abs.IH[OF t']) (use Abs.prems in auto)
  then show ?case using Abs.prems(5) by (simp add: r list_comb_apps loose_bvar_apps)
next
  case (App f u)
  from App.prems(1) obtain u' where u': "expand_term alg td ctab abbrs u [] = Some u'"
    and f: "expand_term alg td ctab abbrs f (u' # args) = Some r"
    by (auto split: option.splits)
  have "\<not> loose_bvar u' k" by (rule App.IH(2)[OF u']) (use App.prems in auto)
  then show ?case by (intro App.IH(1)[OF f]) (use App.prems in auto)
qed

lemma expand_term_typing:
  assumes ts: "tsig_ok alg ar td" and co: "consts_ok ctab" and ab: "abbrs_ok alg ar ctab abbrs"
  shows "expand_term alg td ctab abbrs t args = Some r \<Longrightarrow> \<forall>T\<in>typs t. typ_logical alg td T \<Longrightarrow>
    typ_of bs t = Some (As \<Rrightarrow> B) \<Longrightarrow> e \<tturnstile> args : As \<Longrightarrow> \<forall>n<length bs. e (of_nat n) = bs ! n \<Longrightarrow>
    e \<turnstile> r : B"
proof (induction t arbitrary: args r bs As B e)
  case (Const c T)
  from Const.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Const.prems(3) have T: "T = As \<Rrightarrow> B" by simp
  from Const.prems(1) fx obtain U where U: "ctab c = Some U" and ri: "raw_instance T U"
    by (auto split: option.splits if_splits)
  show ?case
  proof (cases "abbrs c")
    case None
    with Const.prems(1) fx U ri have r: "r = list_comb (Const c T) args" by simp
    have "e \<turnstile> Const c T : As \<Rrightarrow> B" using certify_const_ok[OF co U ri] okT T by auto
    then show ?thesis unfolding r list_comb_apps by (rule list_app_typeI[OF _ Const.prems(4)])
  next
    case (Some rhs)
    with Const.prems(1) fx U ri obtain r0 where x: "expand_atom T U rhs = Some r0"
      and r: "r = betapplys r0 args"
      by auto
    have "e \<turnstile> r0 : T" by (rule expand_atom_typing(2)[OF ab Some U _ _ x]) (use okT in auto)
    then have "e \<turnstile> r0 \<degree>\<degree> args : B" unfolding T by (rule list_app_typeI[OF _ Const.prems(4)])
    then show ?thesis
      unfolding r using subject_reduction_beta'[OF betapplys_beta_reds] by (simp add: list_comb_apps)
  qed
next
  case (Free x T)
  from Free.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Free.prems(1) fx have r: "r = list_comb (Free x T) args" by simp
  from Free.prems(3) okT have "e \<turnstile> Free x T : As \<Rrightarrow> B" by auto
  then show ?case unfolding r list_comb_apps by (rule list_app_typeI[OF _ Free.prems(4)])
next
  case (Var v T)
  from Var.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Var.prems(1) fx have r: "r = list_comb (Var v T) args" by simp
  from Var.prems(3) okT have "e \<turnstile> Var v T : As \<Rrightarrow> B" by auto
  then show ?case unfolding r list_comb_apps by (rule list_app_typeI[OF _ Var.prems(4)])
next
  case (Bound i)
  from Bound.prems(1) have r: "r = list_comb (Bound i) args" by simp
  from Bound.prems(3) obtain n where "n < length bs" "i = of_nat n" "As \<Rrightarrow> B = bs ! n"
    by (auto simp: nth_opt_Some)
  with Bound.prems(5) have "e \<turnstile> Bound i : As \<Rrightarrow> B" by auto
  then show ?case unfolding r list_comb_apps by (rule list_app_typeI[OF _ Bound.prems(4)])
next
  case (Abs a T t)
  from Abs.prems(2) have lg: "typ_logical alg td T" by simp
  note fx = typ_logical_fix[OF lg] and okT = typ_logical_ok[OF lg ts]
  from Abs.prems(1) fx obtain t' where t': "expand_term alg td ctab abbrs t [] = Some t'"
    and r: "r = list_comb (Abs a T t') args"
    by auto
  from Abs.prems(3) obtain V where V: "typ_of (T # bs) t = Some V" and TV: "As \<Rrightarrow> B = T \<rightarrow>\<^sub>T V" by auto
  have "e\<langle>0:T\<rangle> \<turnstile> t' : V"
  proof (rule Abs.IH[OF t'])
    show "typ_of (T # bs) t = Some ([] \<Rrightarrow> V)" using V by simp
    show "e\<langle>0:T\<rangle> \<tturnstile> [] : []" by simp
    show "\<forall>n<length (T # bs). (e\<langle>0:T\<rangle>) (of_nat n) = (T # bs) ! n"
      using shift_env_nth[OF Abs.prems(5)] by blast
  qed (use Abs.prems(2) in auto)
  with okT have "e \<turnstile> Abs a T t' : As \<Rrightarrow> B" unfolding TV by auto
  then show ?case unfolding r list_comb_apps by (rule list_app_typeI[OF _ Abs.prems(4)])
next
  case (App f u)
  from App.prems(1) obtain u' where u': "expand_term alg td ctab abbrs u [] = Some u'"
    and f: "expand_term alg td ctab abbrs f (u' # args) = Some r"
    by (auto split: option.splits)
  from App.prems(3) obtain U where tf: "typ_of bs f = Some (U \<rightarrow>\<^sub>T (As \<Rrightarrow> B))" and tu: "typ_of bs u = Some U"
    by (auto split: option.splits ptyp.splits list.splits if_splits)
  have "e \<turnstile> u' : U"
  proof (rule App.IH(2)[OF u' _ _ _ App.prems(5)])
    show "typ_of bs u = Some ([] \<Rrightarrow> U)" using tu by simp
    show "e \<tturnstile> [] : []" by simp
  qed (use App.prems(2) in auto)
  show ?case
  proof (rule App.IH(1)[OF f _ _ _ App.prems(5)])
    show "typ_of bs f = Some ((U # As) \<Rrightarrow> B)" using tf by simp
    show "e \<tturnstile> (u' # args) : (U # As)" using \<open>e \<turnstile> u' : U\<close> App.prems(4) by simp
  qed (use App.prems(2) in auto)
qed

lemma typ_of_typing:
  assumes co: "consts_ok ctab"
  shows "typ_of bs t = Some T \<Longrightarrow> \<forall>U\<in>typs t. cert_typ alg ar U \<Longrightarrow> consts_inst ctab t \<Longrightarrow>
    \<forall>n<length bs. e (of_nat n) = bs ! n \<Longrightarrow> e \<turnstile> t : T"
proof (induction t arbitrary: bs T e)
  case (Const c U)
  then show ?case using certify_const_ok[OF co] by (auto split: option.splits)
next
  case (Bound i)
  then obtain n where "n < length bs" "i = of_nat n" "T = bs ! n" by (auto simp: nth_opt_Some)
  with Bound.prems(4) show ?case by auto
next
  case (Abs a U t)
  from Abs.prems(1) obtain V where V: "typ_of (U # bs) t = Some V" and T: "T = U \<rightarrow>\<^sub>T V" by auto
  have "(e\<langle>0:U\<rangle>) (of_nat n) = (U # bs) ! n" if "n < length (U # bs)" for n
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    with that Abs.prems(4) have "e (of_nat m) = bs ! m" by simp
    moreover have "(of_nat (Suc m) :: integer) > 0" by (metis of_nat_0_less_iff zero_less_Suc)
    ultimately show ?thesis using Suc by (simp add: shift_def)
  qed
  then have "e\<langle>0:U\<rangle> \<turnstile> t : V" using Abs.IH[OF V] Abs.prems(2,3) by simp
  with Abs.prems(2) show ?case by (auto simp: T)
next
  case (App t u)
  from App.prems(1) obtain T1 where t: "typ_of bs t = Some (T1 \<rightarrow>\<^sub>T T)" and u: "typ_of bs u = Some T1"
    by (auto split: option.splits ptyp.splits list.splits if_splits)
  from App.IH(1)[OF t] App.IH(2)[OF u] App.prems(2-) show ?case by auto
qed auto

text \<open>The result of \<open>Sign.certify_term\<close>, with the maximal index that \<open>Thm.global_cterm_of\<close> records:\<close>

theorem certify_term_wf:
  assumes ts: "tsig_ok alg ar td" and co: "consts_ok ctab" and ab: "abbrs_ok alg ar ctab abbrs"
    and c: "certify_term alg td ctab abbrs tm = Some (t, T)"
  shows "cterm_wf (CTerm t T (maxidx_of_term t))"
proof -
  from c obtain t0 where cv: "check_vars tm" and ct: "certify_types alg td tm = Some t0"
    and ty: "typ_of [] t0 = Some T" and cc: "consts_certify alg td ctab abbrs t0 = Some t"
    by (auto simp: certify_term_def split: if_splits option.splits)
  note ok = certify_types_ok[OF ts ct]
  then have lg: "\<forall>U\<in>typs t0. typ_logical alg td U" by blast
  have v0: "\<forall>v\<in>vars t0. 0 \<le> snd (fst v)" using ok cv by fastforce
  have cl0: "closed t0" using typ_of_closed[OF ty] by (simp add: closed_def)
  have main: "closed t \<and> (\<forall>e. e \<turnstile> t : T) \<and> (\<forall>v\<in>vars t. 0 \<le> snd (fst v)) \<and>
    (\<forall>V\<in>typs t. cert_typ alg ar V \<and> tnn V)"
  proof (cases "need_expand abbrs t0")
    case True
    with cc have x: "expand_term alg td ctab abbrs t0 [] = Some t" by (simp add: consts_certify_def)
    have "e \<turnstile> t : T" for e
      by (rule expand_term_typing[OF ts co ab x lg, where bs = "[]" and As = "[]"]) (use ty in auto)
    moreover have "closed t"
      unfolding closed_def by (rule expand_term_loose[OF ts ab x lg]) (use cl0 in \<open>auto simp: closed_def\<close>)
    moreover from expand_term_vars[OF ts ab x lg]
    have "vars t \<subseteq> vars t0" "\<forall>V\<in>typs t. cert_typ alg ar V \<and> tnn V" by auto
    ultimately show ?thesis using v0 by blast
  next
    case False
    with cc lg have t: "t = t0" and ci: "consts_inst ctab t0"
      by (auto simp: consts_certify_def certify_plain_fix split: if_splits)
    have "e \<turnstile> t0 : T" for e
      by (rule typ_of_typing[OF co ty _ ci]) (use lg typ_logical_ok[OF _ ts] in auto)
    then show ?thesis using cl0 v0 lg typ_logical_ok[OF _ ts] by (auto simp: t)
  qed
  have "ibelow (maxidx_of_term t) t"
    unfolding ibelow_def maxidx_of_term_def using maxidx_term_vars maxidx_term_ttvars by blast
  moreover have "-1 \<le> maxidx_of_term t" unfolding maxidx_of_term_def by (rule maxidx_term_ge)
  moreover have "\<forall>v\<in>ttvars t. 0 \<le> snd (fst v)" using main by (fastforce simp: ttvars_def tnn_def)
  ultimately show ?thesis using main by (simp add: cterm_wf_def)
qed

end

text \<open>The types of the result are certified (this needs no assumption on the sort algebra):\<close>

lemma certify_term_typs:
  assumes ts: "tsig_ok alg ar td" and ab: "abbrs_ok alg ar ctab abbrs"
    and c: "certify_term alg td ctab abbrs tm = Some (t, T)"
  shows "\<forall>V\<in>typs t. cert_typ alg ar V \<and> tnn V" and "vars tm = {} \<Longrightarrow> vars t = {}"
proof -
  from c obtain t0 where ct: "certify_types alg td tm = Some t0"
    and cc: "consts_certify alg td ctab abbrs t0 = Some t"
    by (auto simp: certify_term_def split: if_splits option.splits)
  from certify_types_ok[OF ts ct] have lg: "\<forall>U\<in>typs t0. typ_logical alg td U" by blast
  have "(\<forall>V\<in>typs t. cert_typ alg ar V \<and> tnn V) \<and> vars t \<subseteq> vars t0"
  proof (cases "need_expand abbrs t0")
    case True
    with cc have x: "expand_term alg td ctab abbrs t0 [] = Some t" by (simp add: consts_certify_def)
    from expand_term_vars[OF ts ab x lg] show ?thesis by auto
  next
    case False
    with cc lg have "t = t0" by (auto simp: consts_certify_def certify_plain_fix split: if_splits)
    with lg typ_logical_ok[OF _ ts] show ?thesis by auto
  qed
  then show "\<forall>V\<in>typs t. cert_typ alg ar V \<and> tnn V" and "vars tm = {} \<Longrightarrow> vars t = {}"
    using certify_types_vars[OF ct] by auto
qed

text \<open>
  The assumption on the abbreviations is an invariant of the table. \<open>Consts.abbreviate\<close>
  declares a constant with the type of a certified term without schematic variables, and
  with the result of \<open>Consts.certify\<close> for that term as its right-hand side: these are the two
  components of the result of \<open>Sign.certify_term\<close>.
\<close>

lemma (in pure_sig) abbrs_ok_update:
  assumes ts: "tsig_ok alg ar td" and co: "consts_ok ctab" and ab: "abbrs_ok alg ar ctab abbrs"
    and c: "certify_term alg td ctab abbrs tm = Some (n, U)" and nv: "vars tm = {}"
    and fresh: "ctab c = None"
  shows "abbrs_ok alg ar (ctab(c \<mapsto> U)) (abbrs(c \<mapsto> n))"
  unfolding abbrs_ok_def
proof (intro allI impI)
  fix d rhs V
  assume a: "(abbrs(c \<mapsto> n)) d = Some rhs" and t: "(ctab(c \<mapsto> U)) d = Some V"
  have mono: "signature.typing (cert_typ alg ar) (const_typ_ok (ctab(c \<mapsto> U))) e s S" if "e \<turnstile> s : S" for e s S
    by (rule typing_const_mono[OF that]) (use fresh in \<open>auto simp: const_typ_ok_def split: if_splits\<close>)
  have "closed rhs \<and> (\<forall>e. e \<turnstile> rhs : V) \<and> vars rhs = {} \<and> (\<forall>T\<in>typs rhs. tnn T)"
  proof (cases "d = c")
    case True
    with a t have e: "rhs = n" "V = U" by auto
    from certify_term_wf[OF ts co ab c] certify_term_typs[OF ts ab c] nv show ?thesis
      by (auto simp: e cterm_wf_def)
  next
    case False
    with a t ab fresh show ?thesis by (auto simp: abbrs_ok_def)
  qed
  with mono show "closed rhs \<and> (\<forall>e. signature.typing (cert_typ alg ar) (const_typ_ok (ctab(c \<mapsto> U))) e rhs V) \<and>
    vars rhs = {} \<and> (\<forall>T\<in>typs rhs. tnn T)"
    by blast
qed


subsection \<open>The premises of the rules\<close>

text \<open>
  A certified term as \<open>Thm.global_cterm_of\<close> makes it satisfies the premises on certified terms
  of the rules of \<^const>\<open>derivable\<close>, and it records the sorts of its term (as \<open>match_cterms_ok\<close>
  assumes).
\<close>

theorem global_cterm_of_ok:
  assumes ts: "tsig_ok (sg_alg c) (sg_ar c) td" and co: "consts_ok (sg_consts c)"
    and ab: "abbrs_ok (sg_alg c) (sg_ar c) (sg_consts c) abbrs"
    and g: "global_cterm_of (sg_alg c) td (sg_consts c) abbrs tm = Some (r, Ss)"
  shows "cterm_ok \<lparr>cd_rep = r, cd_sorts = set Ss, cd_sign = c\<rparr>"
    and "csorts_ok c (cd_sorts \<lparr>cd_rep = r, cd_sorts = set Ss, cd_sign = c\<rparr>)"
    and "tm_sorts (ct_t r) = set Ss"
proof -
  from g obtain t T where ce: "certify_term (sg_alg c) td (sg_consts c) abbrs tm = Some (t, T)"
    and r: "r = CTerm t T (maxidx_of_term t)" and Ss: "Ss = insert_term_sorts t []"
    by (auto simp: global_cterm_of_def)
  show "cterm_ok \<lparr>cd_rep = r, cd_sorts = set Ss, cd_sign = c\<rparr>"
    unfolding cterm_ok_def using pure_sig.certify_term_wf[OF _ ts co ab ce] by (simp add: r)
  show sorts: "tm_sorts (ct_t r) = set Ss" unfolding r Ss set_insert_term_sorts_tm by simp
  from certify_term_typs[OF ts ab ce] have "\<forall>U\<in>typs t. sorts_ok (sg_alg c) U" by (simp add: cert_typ_def)
  then have "\<forall>S\<in>tm_sorts t. sort_ok (sg_alg c) S" using sorts_ok_tsorts by (fastforce simp: tm_sorts_typs)
  with sorts show "csorts_ok c (cd_sorts \<lparr>cd_rep = r, cd_sorts = set Ss, cd_sign = c\<rparr>)"
    by (simp add: csorts_ok_def r)
qed

theorem global_ctyp_of_ok:
  assumes ts: "tsig_ok (sg_alg c) (sg_ar c) td"
    and g: "global_ctyp_of (sg_alg c) td T = Some (T', m, Ss)"
  shows "ctyp_ok \<lparr>cty_T = T', cty_maxidx = m, cty_sorts = set Ss, cty_sign = c\<rparr>"
    and "csorts_ok c (cty_sorts \<lparr>cty_T = T', cty_maxidx = m, cty_sorts = set Ss, cty_sign = c\<rparr>)"
proof -
  from g have ce: "certify_typ (sg_alg c) td T = Some T'" and m: "m = maxidx_typ T' (-1)"
    and Ss: "Ss = insert_typ_sorts T' []"
    by (auto simp: global_ctyp_of_def)
  note ok = certify_typ_ok[OF ce ts]
  have "-1 \<le> m" unfolding m by (rule maxidx_typ_ge)
  moreover have "0 \<le> snd (fst w) \<and> snd (fst w) \<le> m" if "w \<in> tvars T'" for w
    using that ok maxidx_typ_tvars[OF that, of "-1"] by (auto simp: m tnn_def)
  moreover have "tsorts T' \<subseteq> set Ss" by (simp add: Ss typ_sorts_tsorts)
  ultimately show "ctyp_ok \<lparr>cty_T = T', cty_maxidx = m, cty_sorts = set Ss, cty_sign = c\<rparr>"
    using ok by (simp add: ctyp_ok_def)
  have "\<forall>S\<in>tsorts T'. sort_ok (sg_alg c) S" using ok sorts_ok_tsorts by (fastforce simp: cert_typ_def)
  then show "csorts_ok c (cty_sorts \<lparr>cty_T = T', cty_maxidx = m, cty_sorts = set Ss, cty_sign = c\<rparr>)"
    by (simp add: csorts_ok_def Ss typ_sorts_tsorts)
qed


subsection \<open>An example\<close>

text \<open>
  The signature \<^const>\<open>pure0\<close> of theory \<^theory_text>\<open>Thm_Example\<close> with the declarations of its two type
  constructors satisfies the assumptions, and the certified term of the derivations there is
  what the model of \<open>Thm.global_cterm_of\<close> returns for the free variable \<open>A\<close>.
\<close>

definition td0 :: "name \<Rightarrow> tdecl option" where
  "td0 a = (if a = STR ''fun'' then Some (Logical_Type 2)
    else if a = STR ''prop'' then Some (Logical_Type 0) else None)"

lemma tsig_ok0: "tsig_ok alg0 (\<lambda>_. 0) td0"
  by (auto simp: tsig_ok_def td0_def tarity_def split: if_splits)

lemma abbrs_ok0: "abbrs_ok alg ar ctab (\<lambda>_. None)"
  by (simp add: abbrs_ok_def)

lemma consts_ok0: "consts_ok ctab0"
  by (auto simp: consts_ok_def ctab0_def ax_aT_def propT_def split: if_splits)

lemma not_qualified_A: "\<not> is_qualified STR ''A''"
  unfolding is_qualified_def by eval

lemma global_cterm_of_A0: "global_cterm_of alg0 td0 ctab0 (\<lambda>_. None) A0 = Some (CTerm A0 propT (-1), [])"
  by (simp add: global_cterm_of_def certify_term_def consts_certify_def A0_def propT_def td0_def
      not_qualified_A maxidx_of_term_def)

corollary "cterm_ok ctA"
proof -
  have "global_cterm_of (sg_alg pure0) td0 (sg_consts pure0) (\<lambda>_. None) A0 = Some (CTerm A0 propT (-1), [])"
    using global_cterm_of_A0 by simp
  from global_cterm_of_ok(1)[OF _ _ abbrs_ok0 this] tsig_ok0 consts_ok0 show ?thesis
    by (simp add: ctA_def)
qed

end
