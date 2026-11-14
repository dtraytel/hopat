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
  are the finitely many sorts of the term.

  The parts of the signature that certification reads are related to the signature of the
  correctness theories by two assumptions. \<open>tsig_ok\<close>: the declared number of arguments of a
  type constructor is its arity, and the right-hand side of a type abbreviation is a certified
  type without schematic type variables. \<open>consts_ok\<close>: the type schemes of the constants have
  no free type variables, and \<open>Pure.imp\<close> and \<open>Pure.all\<close> have their types (if the table has them: the
  typing judgment gives these two constants their types by itself).
\<close>

definition tsig_ok :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (name \<Rightarrow> tdecl option) \<Rightarrow> bool" where
  "tsig_ok alg ar td \<longleftrightarrow>
    (\<forall>a n. td a = Some (Logical_Type n) \<longrightarrow> n = of_nat (tarity ar a)) \<and>
    (\<forall>a vs U s. td a = Some (Abbreviation vs U s) \<longrightarrow> cert_typ alg ar U \<and> tvars U = {})"

definition consts_ok :: "(name \<Rightarrow> ptyp option) \<Rightarrow> bool" where
  "consts_ok ctab \<longleftrightarrow> (\<forall>c U. ctab c = Some U \<longrightarrow> no_tfrees U) \<and>
    (\<forall>U. ctab STR ''Pure.imp'' = Some U \<longrightarrow>
      U = Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' []) \<and>
    (\<forall>U. ctab STR ''Pure.all'' = Some U \<longrightarrow>
      (\<exists>v S. U = (TVar v S \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []))"


subsection \<open>Lists\<close>

lemma len_of_nat: "len xs = of_nat (length xs)"
  by (induction xs) auto

lemma len_eq_of_nat: "len xs = of_nat n \<longleftrightarrow> length xs = n"
  by (simp add: len_of_nat)

lemma those_map_Some: "those_map f xs = Some ys \<Longrightarrow> list_all2 (\<lambda>x y. f x = Some y) xs ys"
  by (induction xs arbitrary: ys) (auto split: option.splits)

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

lemma inst_frees_ok:
  assumes "\<forall>T\<in>snd ` set tab. wft ar T \<and> sorts_ok alg T"
  shows "wft ar U \<Longrightarrow> sorts_ok alg U \<Longrightarrow> wft ar (inst_frees tab U) \<and> sorts_ok alg (inst_frees tab U)"
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

lemma tvars_inst_frees: "tvars (inst_frees tab U) \<subseteq> tvars U \<union> (\<Union>T\<in>snd ` set tab. tvars T)"
proof (induction U)
  case (TFree a S)
  show ?case
  proof (cases "S = [] \<and> map_of tab a \<noteq> None")
    case True
    then obtain T where T: "map_of tab a = Some T" by blast
    then have "T \<in> snd ` set tab" by (force dest: map_of_SomeD)
    with True T show ?thesis by auto
  next
    case False
    then show ?thesis by (auto split: option.splits)
  qed
qed auto

lemma cert_sort_ok: "cert_sort alg S \<Longrightarrow> sort_ok alg S"
  by (auto simp: cert_sort_def sort_ok_def class_mem_def list_all_iff)

lemma certify_typ_ok:
  "certify_typ alg td T = Some T' \<Longrightarrow> tsig_ok alg ar td \<Longrightarrow> cert_typ alg ar T' \<and> tnn T'"
proof (induction alg td T arbitrary: T' rule: certify_typ.induct)
  case (1 alg td c args)
  note ts = "1.prems"(2)
  from "1.prems"(1) obtain decl where d: "td c = Some decl" by (auto split: option.splits)
  show ?case
  proof (cases decl)
    case (Logical_Type n)
    with "1.prems"(1) d obtain args' where l: "len args = n"
      and a: "those_map (certify_typ alg td) args = Some args'" and T': "T' = Type c args'"
      by (auto split: if_splits)
    note la = those_map_Some[OF a]
    have ok: "cert_typ alg ar U' \<and> tnn U'" if "U' \<in> set args'" for U'
    proof -
      from that obtain i where i: "i < length args'" "U' = args' ! i" by (auto simp: in_set_conv_nth)
      with la have "args ! i \<in> set args" "certify_typ alg td (args ! i) = Some U'"
        by (auto simp: list_all2_conv_all_nth)
      then show ?thesis using "1.IH"(1)[OF d Logical_Type _ _ ] l ts by auto
    qed
    have "n = of_nat (tarity ar c)" using ts d unfolding tsig_ok_def Logical_Type by blast
    with l have "length args = tarity ar c" by (simp add: len_eq_of_nat)
    then have "length args' = tarity ar c" using la by (simp add: list_all2_lengthD)
    with ok show ?thesis by (auto simp: T' cert_typ_def)
  next
    case (Abbreviation vs U syntactic)
    with "1.prems"(1) d obtain args' where l: "len args = len vs" and ns: "\<not> syntactic"
      and a: "those_map (certify_typ alg td) args = Some args'"
      and T': "T' = inst_frees (zip vs args') U"
      by (auto split: if_splits)
    note la = those_map_Some[OF a]
    have ok: "cert_typ alg ar U' \<and> tnn U'" if "U' \<in> set args'" for U'
    proof -
      from that obtain i where i: "i < length args'" "U' = args' ! i" by (auto simp: in_set_conv_nth)
      with la have "args ! i \<in> set args" "certify_typ alg td (args ! i) = Some U'"
        by (auto simp: list_all2_conv_all_nth)
      then show ?thesis using "1.IH"(2)[OF d Abbreviation _ _ ] l ns ts by auto
    qed
    have U: "cert_typ alg ar U" "tvars U = {}" using ts d unfolding tsig_ok_def Abbreviation by blast+
    have sub: "snd ` set (zip vs args') \<subseteq> set args'" by (auto dest: set_zip_rightD)
    have "wft ar T' \<and> sorts_ok alg T'" unfolding T'
      by (rule inst_frees_ok) (use ok sub U in \<open>auto simp: cert_typ_def\<close>)
    moreover have "tnn T'"
      using tvars_inst_frees[of "zip vs args'" U] ok sub U(2) unfolding T' tnn_def by fastforce
    ultimately show ?thesis by (simp add: cert_typ_def)
  next
    case Nonterminal
    with "1.prems"(1) d show ?thesis by simp
  qed
next
  case (2 alg td a S)
  then show ?case by (auto simp: cert_typ_def cert_sort_ok split: if_splits)
next
  case (3 alg td x i S)
  then show ?case by (auto simp: cert_typ_def cert_sort_ok split: if_splits)
qed


subsection \<open>Terms\<close>

lemma certify_types_ok:
  assumes ts: "tsig_ok alg ar td"
  shows "certify_types alg td t = Some t' \<Longrightarrow>
    (\<forall>T\<in>typs t'. cert_typ alg ar T \<and> tnn T) \<and> (check_vars t \<longrightarrow> (\<forall>x i T. ((x, i), T) \<in> vars t' \<longrightarrow> 0 \<le> i))"
proof (induction t arbitrary: t')
  case (Var v T)
  obtain x i where v: "v = (x, i)" by (cases v)
  from Var show ?case using certify_typ_ok[OF _ ts] by (auto simp: v)
next
  case (Abs a T t)
  from Abs.prems obtain T' u where T': "certify_typ alg td T = Some T'"
    and u: "certify_types alg td t = Some u" and t': "t' = Abs a T' u"
    by (auto split: option.splits)
  from Abs.IH[OF u] certify_typ_ok[OF T' ts] show ?case by (simp add: t')
next
  case (App t u)
  from App.prems obtain t1 u1 where t1: "certify_types alg td t = Some t1"
    and u1: "certify_types alg td u = Some u1" and t': "t' = t1 $ u1"
    by (auto split: option.splits)
  from App.IH(1)[OF t1] App.IH(2)[OF u1] show ?case by (auto simp: t'; blast)
qed (use certify_typ_ok[OF _ ts] in auto)

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

context pure_sig
begin

lemma typ_of_typing:
  assumes co: "consts_ok ctab"
  shows "typ_of bs t = Some T \<Longrightarrow> \<forall>U\<in>typs t. cert_typ alg ar U \<Longrightarrow> certify_consts ctab t \<Longrightarrow>
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
  assumes ts: "tsig_ok alg ar td" and co: "consts_ok ctab"
    and c: "certify_term alg td ctab abbr tm = Some (t, T)"
  shows "cterm_wf (CTerm t T (maxidx_of_term t))"
proof -
  from c have cv: "check_vars tm" and ct: "certify_types alg td tm = Some t"
    and ty: "typ_of [] t = Some T" and cc: "certify_consts ctab t"
    by (auto simp: certify_term_def split: if_splits option.splits)
  note ok = certify_types_ok[OF ts ct]
  have cl: "closed t" using typ_of_closed[OF ty] by (simp add: closed_def)
  have "e \<turnstile> t : T" for e by (rule typ_of_typing[OF co ty _ cc]) (use ok in auto)
  moreover have "ibelow (maxidx_of_term t) t"
    unfolding ibelow_def maxidx_of_term_def using maxidx_term_vars maxidx_term_ttvars by blast
  moreover have "-1 \<le> maxidx_of_term t" unfolding maxidx_of_term_def by (rule maxidx_term_ge)
  moreover have "\<forall>v\<in>vars t. 0 \<le> snd (fst v)" using ok cv by fastforce
  moreover have "\<forall>v\<in>ttvars t. 0 \<le> snd (fst v)" using ok by (fastforce simp: ttvars_def tnn_def)
  ultimately show ?thesis using cl by (simp add: cterm_wf_def)
qed

end


subsection \<open>The premises of the rules\<close>

text \<open>
  A certified term as \<open>Thm.global_cterm_of\<close> makes it satisfies the premises on certified terms
  of the rules of \<^const>\<open>derivable\<close>, and it records the sorts of its term (as \<open>match_cterms_ok\<close>
  assumes).
\<close>

theorem global_cterm_of_ok:
  assumes ts: "tsig_ok (sg_alg c) (sg_ar c) td" and co: "consts_ok (sg_consts c)"
    and g: "global_cterm_of (sg_alg c) td (sg_consts c) abbr tm = Some (r, Ss)"
  shows "cterm_ok \<lparr>cd_rep = r, cd_sorts = set Ss, cd_sign = c\<rparr>"
    and "finite (cd_sorts \<lparr>cd_rep = r, cd_sorts = set Ss, cd_sign = c\<rparr>)"
    and "tm_sorts (ct_t r) = set Ss"
proof -
  from g obtain t T where ce: "certify_term (sg_alg c) td (sg_consts c) abbr tm = Some (t, T)"
    and r: "r = CTerm t T (maxidx_of_term t)" and Ss: "Ss = insert_term_sorts t []"
    by (auto simp: global_cterm_of_def)
  show "cterm_ok \<lparr>cd_rep = r, cd_sorts = set Ss, cd_sign = c\<rparr>"
    unfolding cterm_ok_def using pure_sig.certify_term_wf[OF _ ts co ce] by (simp add: r)
  show "finite (cd_sorts \<lparr>cd_rep = r, cd_sorts = set Ss, cd_sign = c\<rparr>)" by simp
  show "tm_sorts (ct_t r) = set Ss" unfolding r Ss set_insert_term_sorts_tm by simp
qed

theorem global_ctyp_of_ok:
  assumes ts: "tsig_ok (sg_alg c) (sg_ar c) td"
    and g: "global_ctyp_of (sg_alg c) td T = Some (T', m, Ss)"
  shows "ctyp_ok \<lparr>cty_T = T', cty_maxidx = m, cty_sorts = set Ss, cty_sign = c\<rparr>"
    and "finite (cty_sorts \<lparr>cty_T = T', cty_maxidx = m, cty_sorts = set Ss, cty_sign = c\<rparr>)"
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
  show "finite (cty_sorts \<lparr>cty_T = T', cty_maxidx = m, cty_sorts = set Ss, cty_sign = c\<rparr>)" by simp
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

lemma consts_ok0: "consts_ok ctab0"
  by (auto simp: consts_ok_def ctab0_def ax_aT_def propT_def split: if_splits)

lemma not_qualified_A: "\<not> is_qualified STR ''A''"
  unfolding is_qualified_def by eval

lemma global_cterm_of_A0: "global_cterm_of alg0 td0 ctab0 (\<lambda>_. False) A0 = Some (CTerm A0 propT (-1), [])"
  by (simp add: global_cterm_of_def certify_term_def A0_def propT_def td0_def not_qualified_A
      maxidx_of_term_def)

corollary "cterm_ok ctA"
  using global_cterm_of_ok(1)[of pure0 td0 "\<lambda>_. False" A0, OF _ _ global_cterm_of_A0[folded pure0_sel]]
    tsig_ok0 consts_ok0
  by (simp add: ctA_def)

end
