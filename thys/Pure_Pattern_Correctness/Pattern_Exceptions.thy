section \<open>Exceptions and Typing of Results\<close>

theory Pattern_Exceptions
  imports Pattern_Unif_Complete
begin

text \<open>
  Without assuming a solution, we show for well-typed inputs: \<^const>\<open>unify\<close> raises only the
  exceptions \<open>Unif\<close> and \<open>Pattern\<close>, it raises \<open>Pattern\<close> only if an input is not a pattern, and its
  results are again well-typed environments.
\<close>

subsection \<open>Exceptions\<close>

definition exn_ok :: "exn \<Rightarrow> bool" where
  "exn_ok e \<longleftrightarrow> e = Pattern \<or> (\<exists>u. e = Unif u)"

definition fails_ok :: "'a M \<Rightarrow> bool" where
  "fails_ok m \<longleftrightarrow> (\<forall>e. m = Some (Err e) \<longrightarrow> exn_ok e)"

definition no_exn :: "'a M \<Rightarrow> bool" where
  "no_exn m \<longleftrightarrow> (\<forall>e. m \<noteq> Some (Err e))"

lemma exn_ok_simps[simp]: "exn_ok Pattern" "exn_ok (Unif u)"
  by (simp_all add: exn_ok_def)

lemma fails_ok_simps[simp]:
  "fails_ok (return x)" "fails_ok None" "fails_ok (Some (Ok x))" "fails_ok (raise e) \<longleftrightarrow> exn_ok e"
  "fails_ok (Some (Err e)) \<longleftrightarrow> exn_ok e"
  by (simp_all add: fails_ok_def return_def raise_def)

lemma no_exn_simps[simp]:
  "no_exn (return x)" "no_exn None" "no_exn (Some (Ok x))" "\<not> no_exn (raise e)" "\<not> no_exn (Some (Err e))"
  by (simp_all add: no_exn_def return_def raise_def)

lemma no_exn_fails_ok: "no_exn m \<Longrightarrow> fails_ok m"
  by (auto simp: no_exn_def fails_ok_def)

lemma no_exn_SomeD: "no_exn (Some r) \<Longrightarrow> \<exists>x. r = Ok x"
  by (cases r) (simp_all add: no_exn_def)

lemma fails_ok_bindM: "fails_ok m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> fails_ok (f x)) \<Longrightarrow> fails_ok (bindM m f)"
  by (auto simp: fails_ok_def bindM_def split: option.splits res.splits)

lemma no_exn_bindM: "no_exn m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> no_exn (f x)) \<Longrightarrow> no_exn (bindM m f)"
  by (auto simp: no_exn_def bindM_def split: option.splits res.splits)

lemma no_exn_mapM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_exn (f x)) \<Longrightarrow> no_exn (mapM f xs)"
  by (induction xs) (auto intro!: no_exn_bindM)

lemma fails_ok_mapM: "(\<And>x. x \<in> set xs \<Longrightarrow> fails_ok (f x)) \<Longrightarrow> fails_ok (mapM f xs)"
  by (induction xs) (auto intro!: fails_ok_bindM)

lemma no_exn_someI: "(\<And>r. m = Some r \<Longrightarrow> no_exn (Some r)) \<Longrightarrow> no_exn m"
  by (cases m) (auto simp: no_exn_def)

lemma fails_ok_someI: "(\<And>r. m = Some r \<Longrightarrow> fails_ok (Some r)) \<Longrightarrow> fails_ok m"
  by (cases m) (auto simp: fails_ok_def)


subsection \<open>Head normalisation of well-typed terms\<close>

lemma lookup_typed:
  assumes "wf_env ar env" "env_typed V env" "V x = T"
  shows "\<exists>r. lookup env x T = return r"
proof (cases "vt_lookup (tenv env) x")
  case (Some p)
  obtain U u where p: "p = (U, u)" by force
  with Some env_typedD[OF assms(2)] assms(3) have "U = T" by simp
  with Some p show ?thesis by (auto simp: lookup_def unified_empty[OF wf_envD(1)[OF assms(1)]])
qed (auto simp: lookup_def)

lemma head_norm_no_exn_aux:
  assumes "head_norm env t = Some r"
  shows "wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> has_type V Ts t T \<Longrightarrow> \<exists>t'. r = Ok t' \<and> has_type V Ts t' T"
  using assms
proof (induction env t r arbitrary: Ts T rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have wf: "wf_env ar env" and ty: "env_typed V env" and tyt: "has_type V Ts t T"
    and h: "(case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) = Some r"
    using 1 by simp_all
  note IH = "1.IH"[OF _ wf ty]
  show ?case
  proof (cases t)
    case (Var xi U)
    from tyt Var have VU: "V xi = U" and TU: "T = U" by (auto elim: has_type_elims)
    from lookup_typed[OF wf ty VU] obtain r' where lk: "lookup env xi U = return r'" by blast
    from h Var lk have rest: "(case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) = Some r"
      by (cases r') (simp_all add: return_def bindM_def)
    show ?thesis
    proof (cases r')
      case None
      with rest tyt show ?thesis by (auto simp: return_def)
    next
      case (Some u)
      from lk have "ok (lookup env xi U) r'" by (simp add: return_def)
      from ok_lookup[OF wf_envD(1)[OF wf] this] Some have "vt_lookup (tenv env) xi = Some (U, u)" by simp
      from env_typedD[OF ty this] have "has_type V Ts u U"
        using has_type_weaken[of V "[]" u U Ts] by simp
      moreover have "hn env u = Some r" using rest Some by simp
      ultimately show ?thesis using IH TU by blast
    qed
  next
    case (Abs a U body)
    from tyt Abs obtain W where T: "T = U \<rightarrow>\<^sub>T W" and tb: "has_type V (U # Ts) body W"
      by (auto elim: has_type_elims)
    from h Abs have "hn env body \<bind> (\<lambda>body'. return (pterm.Abs a U body')) = Some r" by simp
    then show ?thesis
    proof (rule bindM_SomeE)
      fix e assume "hn env body = Some (Err e)"
      with IH[OF _ tb] show ?thesis by auto
    next
      fix b' assume "hn env body = Some (Ok b')" "return (pterm.Abs a U b') = Some r"
      with IH[OF _ tb] T show ?thesis by (auto simp: return_def intro: has_type.Abs)
    qed
  next
    case (App f u)
    from tyt App obtain U where tf: "has_type V Ts f (U \<rightarrow>\<^sub>T T)" and tu: "has_type V Ts u U"
      by (auto elim: has_type_elims)
    have beta: "has_type V Ts (subst_bound u body) T" if "has_type V Ts (pterm.Abs a W body) (U \<rightarrow>\<^sub>T T)"
      for a W body
      using that tu by (auto elim!: has_type_elims intro: has_type_subst_bound)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a W body where f: "f = pterm.Abs a W body" by (cases f) auto
      with h App have "hn env (subst_bound u body) = Some r" by simp
      from IH[OF this beta] tf f show ?thesis by simp
    next
      case False
      with h App have hf: "hn env f \<bind> (\<lambda>nf. case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) = Some r"
        by (cases f) auto
      then show ?thesis
      proof (rule bindM_SomeE)
        fix e assume "hn env f = Some (Err e)"
        with IH[OF _ tf] show ?thesis by auto
      next
        fix nf assume nf: "hn env f = Some (Ok nf)"
          and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
            | _ \<Rightarrow> return (nf $ u)) = Some r"
        from IH[OF nf tf] have tnf: "has_type V Ts nf (U \<rightarrow>\<^sub>T T)" by simp
        show ?thesis
        proof (cases "is_Abs nf")
          case True
          then obtain a W body where nfa: "nf = pterm.Abs a W body" by (cases nf) auto
          with rest have "hn env (subst_bound u body) = Some r" by simp
          from IH[OF this beta] tnf nfa show ?thesis by simp
        next
          case False
          with rest tnf tu show ?thesis by (cases nf) (auto simp: return_def intro: has_type.App)
        qed
      qed
    qed
  qed (use h tyt in \<open>auto simp: return_def\<close>)
qed

lemma head_norm_no_exn:
  "wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> has_type V Ts t T \<Longrightarrow> no_exn (head_norm env t)"
  using head_norm_no_exn_aux by (fastforce simp: no_exn_def)

lemma ints_of_res: "ints_of ts = Some r \<Longrightarrow> r = Err Pattern \<or> (\<exists>is. r = Ok is)"
  by (induction ts arbitrary: r rule: ints_of.induct)
    (auto simp: bindM_def return_def raise_def split: option.splits res.splits if_splits)

lemma ints_of'_res:
  assumes "ints_of' env ts = Some r" "wf_env ar env" "env_typed V env" "\<forall>t\<in>set ts. \<exists>U. has_type V Ts t U"
  shows "r = Err Pattern \<or> (\<exists>is. r = Ok is)"
proof -
  have "no_exn (mapM (head_norm env) ts)"
    using assms(4) by (intro no_exn_mapM) (auto intro: head_norm_no_exn[OF assms(2,3)])
  with assms(1) show ?thesis
    by (auto simp: ints_of'_def no_exn_def bindM_def dest: ints_of_res split: option.splits res.splits)
qed

lemma ints_of'_Bounds:
  assumes "distinct is" "\<forall>i\<in>set is. 0 \<le> i"
  shows "ints_of' env (map Bound is) = return is"
proof -
  have "mapM (head_norm env) (map Bound is) = return (map Bound is)"
    by (induction "is") (simp_all add: head_norm.simps[of env "Bound _"])
  moreover have "ints_of (map Bound is) = return is"
    using assms by (induction "is") auto
  ultimately show ?thesis by (simp add: ints_of'_def)
qed


subsection \<open>The occurs checks on well-typed terms\<close>

lemma occurs_no_exn:
  assumes "occurs F t env = Some r"
  shows "wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> has_type V Ts t T \<Longrightarrow> \<exists>b. r = Ok b"
  using assms
proof (induction F t env r arbitrary: Ts T rule: occurs.raw_induct[rotated, consumes 1])
  case (1 occ F t env r)
  have wf: "wf_env ar env" and ty: "env_typed V env" and tyt: "has_type V Ts t T"
    and h: "(case t of
      pterm.Var G T \<Rightarrow> lookup env G T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G))
    | t1 $ t2 \<Rightarrow> occ F t1 env \<bind> (\<lambda>b. if b then return True else occ F t2 env)
    | pterm.Abs _ _ u \<Rightarrow> occ F u env
    | _ \<Rightarrow> return False) = Some r"
    using 1 by simp_all
  note IH = "1.IH"[OF _ wf ty]
  show ?case
  proof (cases t)
    case (Var G U)
    from tyt Var have VU: "V G = U" by (auto elim: has_type_elims)
    from lookup_typed[OF wf ty VU] obtain r' where lk: "lookup env G U = return r'" by blast
    from h Var lk have rest: "(case r' of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G)) = Some r"
      by (cases r') (simp_all add: return_def bindM_def)
    show ?thesis
    proof (cases r')
      case (Some u)
      from lk have "ok (lookup env G U) r'" by (simp add: return_def)
      from ok_lookup[OF wf_envD(1)[OF wf] this] Some have "vt_lookup (tenv env) G = Some (U, u)" by simp
      from env_typedD[OF ty this] have "has_type V [] u U" by simp
      with rest Some IH show ?thesis by auto
    qed (use rest in \<open>auto simp: return_def\<close>)
  next
    case (Abs a U body)
    from tyt Abs obtain W where "has_type V (U # Ts) body W" by (auto elim: has_type_elims)
    with h Abs IH show ?thesis by auto
  next
    case (App t1 t2)
    from tyt App obtain U where t1: "has_type V Ts t1 (U \<rightarrow>\<^sub>T T)" and t2: "has_type V Ts t2 U"
      by (auto elim: has_type_elims)
    from h App have "occ F t1 env \<bind> (\<lambda>b. if b then return True else occ F t2 env) = Some r" by simp
    with IH[OF _ t1] IH[OF _ t2] show ?thesis
      by (auto simp: bindM_def return_def split: option.splits res.splits if_splits)
  qed (use h in \<open>auto simp: return_def\<close>)
qed

lemma rigid_occurs_no_exn:
  assumes "rigid_occurs F t env = Some r"
  shows "wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> has_type V Ts t T \<Longrightarrow> \<exists>b. r = Ok b"
  using assms
proof (induction F t env r arbitrary: Ts T rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t env r)
  have wf: "wf_env ar env" and ty: "env_typed V env" and tyt: "has_type V Ts t T"
    using 1 by simp_all
  note IH = "1.IH"[OF _ wf ty]
  define B where "B = (\<lambda>t'. case t' of
        pterm.Abs _ _ u \<Rightarrow> ro F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              pterm.Var G _ \<Rightarrow>
                if G = F then
                  handle (ints_of' env ts \<bind> (\<lambda>_. return True))
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | pterm.Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts)))"
  from "1.hyps" have "head_norm env t \<bind> B = Some r" by (simp add: B_def)
  then show ?case
  proof (rule bindM_SomeE)
    fix e assume "head_norm env t = Some (Err e)"
    with head_norm_no_exn_aux[OF _ wf ty tyt] show ?thesis by auto
  next
    fix t' assume hn: "head_norm env t = Some (Ok t')" and Bt: "B t' = Some r"
    from head_norm_no_exn_aux[OF hn wf ty tyt] have tyt': "has_type V Ts t' T" by simp
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain a U u where t'a: "t' = pterm.Abs a U u" by (cases t') auto
      from tyt' t'a obtain W where "has_type V (U # Ts) u W" by (auto elim: has_type_elims)
      with Bt t'a IH show ?thesis by (auto simp: B_def)
    next
      case nA: False
      obtain h ts where sc: "strip_comb t' = (h, ts)" by force
      from tyt' strip_comb_list_comb[OF sc] obtain Us where tyts: "list_all2 (has_type V Ts) ts Us"
        by (auto simp: has_type_list_comb)
      have tyts': "\<forall>u\<in>set ts. \<exists>U. has_type V Ts u U"
        using tyts by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
      have rest: "(case h of
          pterm.Var G _ \<Rightarrow>
            if G = F then
              handle (ints_of' env ts \<bind> (\<lambda>_. return True))
                (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
            else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts) = Some r"
        using Bt sc nA unfolding B_def by (cases t') simp_all
      have ex: "\<exists>b. r = Ok b" if "existsM (\<lambda>u. ro F u env) ts = Some r"
        using that tyts'
      proof (induction ts arbitrary: r)
        case (Cons u us)
        from Cons.prems obtain U where tu: "has_type V Ts u U" by auto
        from Cons.prems(1) have "ro F u env \<bind> (\<lambda>b. if b then return True else existsM (\<lambda>u. ro F u env) us) =
          Some r" by simp
        then show ?case
        proof (rule bindM_SomeE)
          fix e assume a: "ro F u env = Some (Err e)"
          from IH[OF a tu] show ?thesis by simp
        next
          fix b assume "(if b then return True else existsM (\<lambda>u. ro F u env) us) = Some r"
          with Cons.IH Cons.prems(2) show ?thesis by (cases b) (auto simp: return_def)
        qed
      qed (auto simp: return_def)
      show ?thesis
      proof (cases h)
        case (Var G U)
        show ?thesis
        proof (cases "G = F")
          case True
          from rest Var True have hd: "handle (ints_of' env ts \<bind> (\<lambda>_. return True))
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) = Some r" by simp
          then obtain ri where ri: "ints_of' env ts = Some ri"
            by (cases "ints_of' env ts") (simp_all add: handle_def bindM_def)
          from ints_of'_res[OF ri wf ty tyts'] hd ri show ?thesis
            by (auto simp: handle_def bindM_def return_def raise_def)
        qed (use rest Var in \<open>auto simp: return_def\<close>)
      qed (use rest ex in \<open>auto simp: return_def\<close>)
    qed
  qed
qed


subsection \<open>Variables reachable through bindings\<close>

text \<open>\<open>occv env x y\<close>: the unbound variable \<open>x\<close> is reachable from \<open>y\<close> through the bindings of \<open>env\<close>.\<close>

inductive occv :: "env \<Rightarrow> indexname \<Rightarrow> indexname \<Rightarrow> bool" for env where
  occv_refl: "vt_lookup (tenv env) x = None \<Longrightarrow> occv env x x"
| occv_step: "vt_lookup (tenv env) y = Some (U, u) \<Longrightarrow> z \<in> vars u \<Longrightarrow> occv env x z \<Longrightarrow> occv env x y"

definition occt :: "env \<Rightarrow> indexname \<Rightarrow> pterm \<Rightarrow> bool" where
  "occt env x t \<longleftrightarrow> (\<exists>y\<in>vars t. occv env x y)"

lemma occt_mono: "occt env x t \<Longrightarrow> vars t \<subseteq> vars t' \<Longrightarrow> occt env x t'"
  by (auto simp: occt_def)

lemma occt_simps[simp]:
  "occt env x (s $ t) \<longleftrightarrow> occt env x s \<or> occt env x t" "occt env x (Abs a T t) \<longleftrightarrow> occt env x t"
  "occt env x (Const c T) \<longleftrightarrow> False" "occt env x (Free c T) \<longleftrightarrow> False" "occt env x (Bound i) \<longleftrightarrow> False"
  by (auto simp: occt_def)

lemma vars_list_comb: "vars (list_comb h ts) = vars h \<union> \<Union> (vars ` set ts)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma occv_unbound: "occv env x y \<Longrightarrow> vt_lookup (tenv env) y = None \<Longrightarrow> x = y"
  by (auto elim: occv.cases)

lemma occurs_False_occt:
  assumes "occurs F t env = Some r"
  shows "r = Ok False \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> \<not> occt env F t"
  using assms
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 occ F t env r)
  from "1.hyps" "1.prems"(1) have h: "(case t of
      pterm.Var G T \<Rightarrow> lookup env G T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G))
    | t1 $ t2 \<Rightarrow> occ F t1 env \<bind> (\<lambda>b. if b then return True else occ F t2 env)
    | pterm.Abs _ _ u \<Rightarrow> occ F u env
    | _ \<Rightarrow> return False) = Some (Ok False)"
    by simp
  note IH = "1.IH"[OF _ refl "1.prems"(2)]
  show ?case
  proof (cases t)
    case (Var G U)
    from h Var obtain r' where lk: "ok (lookup env G U) r'"
      and rest: "(case r' of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G)) = Some (Ok False)"
      by (auto elim!: bindM_SomeE)
    from ok_lookup[OF "1.prems"(2) lk]
    consider "r' = None" "vt_lookup (tenv env) G = None" | u where "r' = Some u" "vt_lookup (tenv env) G = Some (U, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest have "F \<noteq> G" by (simp add: return_def)
      with 1 Var show ?thesis by (auto simp: occt_def dest: occv_unbound)
    next
      case 2
      with rest have "\<not> occt env F u" by (intro IH) simp
      with 2 Var show ?thesis by (auto simp: occt_def elim: occv.cases)
    qed
  next
    case (App t1 t2)
    from h App obtain b where o1: "occ F t1 env = Some (Ok b)"
      and o2: "(if b then return True else occ F t2 env) = Some (Ok False)"
      by (auto elim!: bindM_SomeE)
    from o2 have "\<not> b" and "occ F t2 env = Some (Ok False)" by (auto simp: return_def split: if_splits)
    with o1 App IH show ?thesis by auto
  next
    case (Abs a U u)
    with h IH show ?thesis by auto
  qed (simp_all add: occt_def)
qed

lemma vars_subst_bound: "vars (subst_bound u t) \<subseteq> vars u \<union> vars t"
  using vars_subst_bound_aux by (simp add: subst_bound_def)

lemma head_norm_occt:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> occt env x t' \<Longrightarrow> occt env x t"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  from "1.hyps" "1.prems"(1) have h: "(case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) = Some (Ok t')"
    by simp
  note IH = "1.IH"[OF _ refl "1.prems"(2)]
  have occ: "occt env x t'" by (rule "1.prems"(3))
  show ?case
  proof (cases t)
    case (Var xi U)
    from h Var obtain r' where lk: "ok (lookup env xi U) r'"
      and rest: "(case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) = Some (Ok t')"
      by (auto elim!: bindM_SomeE)
    from ok_lookup[OF "1.prems"(2) lk]
    consider "r' = None" | u where "r' = Some u" "vt_lookup (tenv env) xi = Some (U, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest occ show ?thesis by (simp add: return_def)
    next
      case 2
      with rest have "hn env u = Some (Ok t')" by simp
      from IH[OF this occ] obtain z where "z \<in> vars u" "occv env x z" by (auto simp: occt_def)
      with 2 Var show ?thesis by (auto simp: occt_def intro: occv_step)
    qed
  next
    case (Abs a U body)
    with h obtain b' where "hn env body = Some (Ok b')" "t' = pterm.Abs a U b'"
      by (auto elim!: bindM_SomeE simp: return_def)
    with IH occ Abs show ?thesis by auto
  next
    case (App f u)
    have beta: "occt env x t" if "occt env x (subst_bound u body)" "occt env x (pterm.Abs a W body) \<Longrightarrow> occt env x f"
      for a W body
      using that vars_subst_bound[of u body] App by (auto simp: occt_def)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a W body where f: "f = pterm.Abs a W body" by (cases f) auto
      with h App have "hn env (subst_bound u body) = Some (Ok t')" by simp
      from beta[OF IH[OF this occ]] f show ?thesis by simp
    next
      case False
      with h App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) =
          Some (Ok t')"
        by (cases f) (auto elim!: bindM_SomeE)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a W body where nfa: "nf = pterm.Abs a W body" by (cases nf) auto
        with rest have "hn env (subst_bound u body) = Some (Ok t')" by simp
        from beta[OF IH[OF this occ]] IH[OF nf] nfa show ?thesis by simp
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) (simp_all add: return_def)
        with occ IH[OF nf] App show ?thesis by auto
      qed
    qed
  qed (use h occ in \<open>simp_all add: return_def\<close>)
qed

text \<open>Extending an environment by bindings to new variables only: reachability changes only by new variables.\<close>

definition new_ok :: "env \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> bool" where
  "new_ok env env' s \<longleftrightarrow> extends env' env \<and> maxidx env \<le> maxidx env' \<and>
    (\<forall>y U u. vt_lookup (tenv env') y = Some (U, u) \<longrightarrow> vt_lookup (tenv env) y = None \<longrightarrow>
      (occt env y s \<or> maxidx env < snd y) \<and> (\<forall>z\<in>vars u. maxidx env < snd z))"

lemma new_okI:
  "extends env' env \<Longrightarrow> maxidx env \<le> maxidx env' \<Longrightarrow>
    (\<And>y U u. vt_lookup (tenv env') y = Some (U, u) \<Longrightarrow> vt_lookup (tenv env) y = None \<Longrightarrow>
      (occt env y s \<or> maxidx env < snd y) \<and> (\<forall>z\<in>vars u. maxidx env < snd z)) \<Longrightarrow> new_ok env env' s"
  unfolding new_ok_def by blast

lemma new_okD:
  assumes "new_ok env env' s"
  shows "extends env' env" "maxidx env \<le> maxidx env'"
    "vt_lookup (tenv env') y = Some (U, u) \<Longrightarrow> vt_lookup (tenv env) y = None \<Longrightarrow> occt env y s \<or> maxidx env < snd y"
    "vt_lookup (tenv env') y = Some (U, u) \<Longrightarrow> vt_lookup (tenv env) y = None \<Longrightarrow> z \<in> vars u \<Longrightarrow> maxidx env < snd z"
  using assms unfolding new_ok_def by blast+

lemma extendsD: "extends env' env \<Longrightarrow> vt_lookup (tenv env) x = Some b \<Longrightarrow> vt_lookup (tenv env') x = Some b"
  unfolding extends_def by blast

lemma extends_None: "extends env' env \<Longrightarrow> vt_lookup (tenv env') x = None \<Longrightarrow> vt_lookup (tenv env) x = None"
  using extendsD[of env' env x] by (cases "vt_lookup (tenv env) x") auto

lemma occv_extend:
  assumes "occv env' x y" "new_ok env env' s" "fresh_env env"
  shows "occv env x y \<or> maxidx env < snd x"
  using assms(1)
proof (induction rule: occv.induct)
  case (occv_refl x)
  have "vt_lookup (tenv env) x = None" by (rule extends_None[OF new_okD(1)[OF assms(2)] occv_refl])
  then show ?case by (simp add: occv.occv_refl)
next
  case (occv_step y U u z x)
  show ?case
  proof (cases "vt_lookup (tenv env) y")
    case None
    have zf: "maxidx env < snd z" by (rule new_okD(4)[OF assms(2) occv_step(1) None occv_step(2)])
    from occv_step(4) show ?thesis
    proof
      assume "occv env x z"
      moreover have "vt_lookup (tenv env) z = None"
        using zf fresh_envD[OF assms(3)] by (cases "vt_lookup (tenv env) z") fastforce+
      ultimately show ?thesis using zf occv_unbound by blast
    qed simp
  next
    case (Some b)
    with extendsD[OF new_okD(1)[OF assms(2)] Some] occv_step(1) have "b = (U, u)" by simp
    with Some occv_step(2,4) show ?thesis by (auto intro: occv.occv_step)
  qed
qed

lemma occt_extend: "occt env' x t \<Longrightarrow> new_ok env env' s \<Longrightarrow> fresh_env env \<Longrightarrow> occt env x t \<or> maxidx env < snd x"
  using occv_extend unfolding occt_def by blast

lemma new_ok_refl: "new_ok env env s"
  by (rule new_okI) simp_all

lemma new_ok_mono: "new_ok env env' s \<Longrightarrow> vars s \<subseteq> vars s' \<Longrightarrow> new_ok env env' s'"
  by (rule new_okI) (auto dest: new_okD intro: occt_mono)

lemma new_ok_trans:
  assumes "new_ok env e1 s" "new_ok e1 e2 s'" "fresh_env env" "vars s' \<subseteq> vars s"
  shows "new_ok env e2 s"
proof (rule new_okI)
  show "extends e2 env" using new_okD(1)[OF assms(1)] new_okD(1)[OF assms(2)] by (rule extends_trans[rotated])
  have m: "maxidx env \<le> maxidx e1" by (rule new_okD(2)[OF assms(1)])
  then show "maxidx env \<le> maxidx e2" using new_okD(2)[OF assms(2)] by simp
  fix y U u assume y2: "vt_lookup (tenv e2) y = Some (U, u)" and y0: "vt_lookup (tenv env) y = None"
  show "(occt env y s \<or> maxidx env < snd y) \<and> (\<forall>z\<in>vars u. maxidx env < snd z)"
  proof (cases "vt_lookup (tenv e1) y")
    case None
    have o: "occt e1 y s' \<or> maxidx e1 < snd y" by (rule new_okD(3)[OF assms(2) y2 None])
    have f: "maxidx e1 < snd z" if "z \<in> vars u" for z by (rule new_okD(4)[OF assms(2) y2 None that])
    from o have "occt env y s \<or> maxidx env < snd y"
    proof
      assume "occt e1 y s'"
      from occt_extend[OF this assms(1,3)] show ?thesis using occt_mono[OF _ assms(4)] by blast
    qed (use m in simp)
    with f m show ?thesis by fastforce
  next
    case (Some b)
    from extendsD[OF new_okD(1)[OF assms(2)] Some] y2 have "b = (U, u)" by simp
    with Some have "vt_lookup (tenv e1) y = Some (U, u)" by simp
    from new_okD(3,4)[OF assms(1) this y0] show ?thesis by blast
  qed
qed


subsection \<open>Typing of new variables and bindings\<close>

definition ty_ext :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "ty_ext ar V env V' env' \<longleftrightarrow> agreeV (maxidx env) V V' \<and> env_typed V' env' \<and> fresh_env env' \<and>
    wf_env ar env' \<and> maxidx env \<le> maxidx env' \<and> extends env' env"

lemma ty_ext_refl: "env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow> wf_env ar env \<Longrightarrow> ty_ext ar V env V env"
  by (simp add: ty_ext_def)

lemma ty_ext_trans: "ty_ext ar V e V1 e1 \<Longrightarrow> ty_ext ar V1 e1 V2 e2 \<Longrightarrow> ty_ext ar V e V2 e2"
  unfolding ty_ext_def by (meson agreeV_trans extends_trans order_trans)

lemma typed_new_var:
  assumes fr: "fresh_env env" and ety: "env_typed V env" and G: "genvar a env Gty = (env1, G)"
  defines "V' \<equiv> V((a, maxidx env + 1) := Gty)"
  shows "agreeV (maxidx env) V V'" "env_typed V' env1" "fresh_env env1" "maxidx env1 = maxidx env + 1"
    "G = pterm.Var (a, maxidx env + 1) Gty" "V' (a, maxidx env + 1) = Gty" "tenv env1 = tenv env"
proof -
  note G' = genvar_simps[OF G]
  show agV: "agreeV (maxidx env) V V'" by (auto simp: agreeV_def V'_def)
  show "env_typed V' env1" using env_typed_agreeV[OF ety fr agV] by (simp add: env_typed_def G')
  show "fresh_env env1"
    unfolding fresh_env_def G'(1,3)
  proof (intro allI impI)
    fix x U u assume "vt_lookup (tenv env) x = Some (U, u)"
    from fresh_envD[OF fr this] show "snd x \<le> maxidx env + 1 \<and> below (maxidx env + 1) u"
      by (auto intro: below_mono)
  qed
  show "maxidx env1 = maxidx env + 1" "G = pterm.Var (a, maxidx env + 1) Gty" "V' (a, maxidx env + 1) = Gty"
    "tenv env1 = tenv env"
    by (simp_all add: G' V'_def)
qed

lemma typed_update:
  assumes fr: "fresh_env env" and ety: "env_typed V env" and upd: "ok (update (F, T) t env) env'"
    and ty: "V F = T" "has_type V [] t T" and Fm: "snd F \<le> maxidx env" and tm: "below (maxidx env) t"
  shows "env_typed V env'" "fresh_env env'" "maxidx env' = maxidx env"
proof -
  note u = ok_update[OF upd]
  show "env_typed V env'"
    unfolding env_typed_def u(2)
  proof (intro allI impI)
    fix x U u' assume "vt_lookup (vt_update (F, T, t) (tenv env)) x = Some (U, u')"
    then show "V x = U \<and> has_type V [] u' U"
      using env_typedD[OF ety] ty by (auto split: if_splits)
  qed
  show "fresh_env env'"
    unfolding fresh_env_def u(2) u(4)
  proof (intro allI impI)
    fix x U u' assume "vt_lookup (vt_update (F, T, t) (tenv env)) x = Some (U, u')"
    then show "snd x \<le> maxidx env \<and> below (maxidx env) u'"
      using fresh_envD[OF fr] Fm tm by (auto split: if_splits)
  qed
  show "maxidx env' = maxidx env" by (rule u(4))
qed

lemma update_unbound: "vt_lookup (tenv env) F = None \<Longrightarrow> \<exists>env'. update (F, T) t env = return env'"
  by (cases env) (auto simp: update_def update_new_def vt_defined_lookup)

lemma new_ok_occt: "new_ok env env' s0 \<Longrightarrow> (\<And>y. occt env y s0 \<Longrightarrow> occt env y s) \<Longrightarrow> new_ok env env' s"
  by (rule new_okI) (auto dest: new_okD)

lemma new_ok_update:
  assumes "ok (update (F, T) t env) env'" "occt env F s" "\<forall>z\<in>vars t. maxidx env < snd z"
  shows "new_ok env env' s"
proof (rule new_okI)
  note u = ok_update[OF assms(1)]
  show "extends env' env" by (rule ok_update_extends[OF assms(1)])
  show "maxidx env \<le> maxidx env'" using u(4) by simp
  fix y U u assume "vt_lookup (tenv env') y = Some (U, u)" "vt_lookup (tenv env) y = None"
  with u(2) have "y = F" "u = t" by (auto split: if_splits)
  with assms(2,3) show "(occt env y s \<or> maxidx env < snd y) \<and> (\<forall>z\<in>vars u. maxidx env < snd z)" by simp
qed


subsection \<open>Auxiliary functions\<close>

lemma head_norm_head_unbound:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> fst (strip_comb t') = pterm.Var F U \<Longrightarrow>
    vt_lookup (tenv env) F = None"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  from "1.hyps" "1.prems"(1) have h: "(case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) = Some (Ok t')"
    by simp
  note IH = "1.IH"[OF _ refl "1.prems"(2)]
  have hd: "fst (strip_comb t') = pterm.Var F U" by (rule "1.prems"(3))
  show ?case
  proof (cases t)
    case (Var xi T)
    from h Var obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "(case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) = Some (Ok t')"
      by (auto elim!: bindM_SomeE)
    from ok_lookup[OF "1.prems"(2) lk]
    consider "r' = None" "vt_lookup (tenv env) xi = None" | u where "r' = Some u"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest Var have "t' = pterm.Var xi T" by (simp add: return_def)
      with 1 hd show ?thesis by (simp add: strip_comb_def)
    next
      case 2
      with rest IH hd show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with h hd show ?thesis by (auto elim!: bindM_SomeE simp: return_def strip_comb_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a W body where f: "f = pterm.Abs a W body" by (cases f) auto
      with h App IH hd show ?thesis by simp
    next
      case False
      with h App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) =
          Some (Ok t')"
        by (cases f) (auto elim!: bindM_SomeE)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a W body where nfa: "nf = pterm.Abs a W body" by (cases nf) auto
        with rest IH hd show ?thesis by simp
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) (simp_all add: return_def)
        with hd IH[OF nf] show ?thesis by (simp add: strip_comb_App)
      qed
    qed
  next
    case (Const c T)
    with h have "t' = Const c T" by (simp add: return_def)
    with hd show ?thesis by (simp add: strip_comb_def)
  next
    case (Free c T)
    with h have "t' = Free c T" by (simp add: return_def)
    with hd show ?thesis by (simp add: strip_comb_def)
  next
    case (Bound i)
    with h have "t' = Bound i" by (simp add: return_def)
    with hd show ?thesis by (simp add: strip_comb_def)
  qed
qed

lemma idx_res: "(\<exists>k. idx is j = return k) \<or> idx is j = raise (Unif No_Trace)"
  by (induction "is") auto

lemma try_trans_no_exn: "\<exists>r. try_trans xs d i = return r"
  using idx_res[of xs "i - d"]
  by (auto simp: try_trans_def handle_def bindM_def return_def raise_def)

lemma trans_res: "trans xs d i = Some r \<Longrightarrow> (\<exists>j. r = Ok j) \<or> (\<exists>u. r = Err (Unif u))"
  using idx_res[of xs "i - d"]
  by (auto simp: trans_def bindM_def return_def raise_def split: if_splits)

lemma nth_ok: "0 \<le> i \<Longrightarrow> nat_of_integer i < length xs \<Longrightarrow> nth xs i = return (xs ! nat_of_integer i)"
  using ok_nth[of xs i "xs ! nat_of_integer i"] by (simp add: return_def)

lemma mapM_nth_ok:
  "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length Ts \<Longrightarrow> mapM (nth Ts) ks = return (map (\<lambda>k. Ts ! nat_of_integer k) ks)"
  by (induction ks) (simp_all add: nth_ok)

lemma type_of_G_ok:
  assumes "vt_is_empty (tyenv env)" "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length Us"
  shows "type_of_G env (foldr fun_type Us U) (integer_of_nat (length Us)) ks =
    return (foldr fun_type (map (\<lambda>k. rev Us ! nat_of_integer k) ks) U)"
  using assms mapM_nth_ok[of ks "rev Us"]
  by (simp add: type_of_G_def norm_type_def split_type_foldr)

lemma mapM_return:
  "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. f x = return y) \<Longrightarrow> \<exists>ys. mapM f xs = return ys \<and> list_all2 (\<lambda>x y. f x = return y) xs ys"
proof (induction xs)
  case (Cons a xs)
  from Cons.prems obtain y where y: "f a = return y" by auto
  from Cons obtain ys where ys: "mapM f xs = return ys" "list_all2 (\<lambda>x y. f x = return y) xs ys" by auto
  show ?case using y ys by (intro exI[of _ "y # ys"]) (simp add: return_def bindM_def)
qed (simp add: return_def)

lemma mkabs_ok:
  "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders \<Longrightarrow> \<exists>u. mkabs binders is t = return u"
  by (induction "is") (auto simp: nth_ok split: prod.splits)

lemma mapAccM_inv:
  assumes "mapAccM f xs e = Some r" "P g e"
    and "\<And>x g e r. x \<in> set xs \<Longrightarrow> P g e \<Longrightarrow> f x e = Some r \<Longrightarrow>
      fails_ok (Some r) \<and> (N \<longrightarrow> r \<noteq> Err Pattern) \<and>
      (\<forall>y e1. r = Ok (y, e1) \<longrightarrow> (\<exists>g1. P g1 e1 \<and> R g1 e1 g e \<and> Q x y g1 e1))"
    and mono: "\<And>x y g1 e1 g2 e2. Q x y g1 e1 \<Longrightarrow> R g2 e2 g1 e1 \<Longrightarrow> Q x y g2 e2"
    and trans: "\<And>g1 e1 g2 e2 g3 e3. R g2 e2 g1 e1 \<Longrightarrow> R g3 e3 g2 e2 \<Longrightarrow> R g3 e3 g1 e1"
    and refl: "\<And>g e. R g e g e"
  shows "fails_ok (Some r) \<and> (N \<longrightarrow> r \<noteq> Err Pattern) \<and> (\<forall>ys e'. r = Ok (ys, e') \<longrightarrow>
    (\<exists>g'. P g' e' \<and> R g' e' g e \<and> list_all2 (\<lambda>x y. Q x y g' e') xs ys))"
  using assms(1-3)
proof (induction xs arbitrary: g e r)
  case Nil
  then show ?case using refl by (auto simp: return_def)
next
  case (Cons x xs)
  have step: "fails_ok (Some r) \<and> (N \<longrightarrow> r \<noteq> Err Pattern) \<and>
      (\<forall>y e1. r = Ok (y, e1) \<longrightarrow> (\<exists>g1. P g1 e1 \<and> R g1 e1 g e \<and> Q x' y g1 e1))"
    if "x' \<in> set xs" "P g e" "f x' e = Some r" for x' g e r
    using Cons.prems(3)[OF _ that(2,3)] that(1) by simp
  from Cons.prems(1) have "f x e \<bind> (\<lambda>(y, s1). mapAccM f xs s1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2))) = Some r"
    by simp
  then show ?case
  proof (rule bindM_SomeE)
    fix ex assume "f x e = Some (Err ex)" "r = Err ex"
    with Cons.prems(3)[of x g e "Err ex"] Cons.prems(2) show ?thesis by simp
  next
    fix ye1 assume fx: "f x e = Some (Ok ye1)"
      and rest: "(\<lambda>(y, s1). mapAccM f xs s1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2))) ye1 = Some r"
    obtain y e1 where ye1: "ye1 = (y, e1)" by force
    from Cons.prems(3)[of x g e, OF _ Cons.prems(2) fx] ye1 obtain g1 where
      g1: "P g1 e1" "R g1 e1 g e" "Q x y g1 e1" by auto
    have IH: "fails_ok (Some r') \<and> (N \<longrightarrow> r' \<noteq> Err Pattern) \<and> (\<forall>ys e'. r' = Ok (ys, e') \<longrightarrow>
        (\<exists>g'. P g' e' \<and> R g' e' g1 e1 \<and> list_all2 (\<lambda>x y. Q x y g' e') xs ys))"
      if "mapAccM f xs e1 = Some r'" for r'
      by (rule Cons.IH[OF that g1(1)], rule step, assumption+)
    from rest ye1 have "mapAccM f xs e1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2)) = Some r" by simp
    then show ?thesis
    proof (rule bindM_SomeE)
      fix ex assume m: "mapAccM f xs e1 = Some (Err ex)" and r: "r = Err ex"
      from IH[OF m] r show ?thesis by blast
    next
      fix yse2 assume m: "mapAccM f xs e1 = Some (Ok yse2)"
        and r: "(\<lambda>(ys, s2). return (y # ys, s2)) yse2 = Some r"
      obtain ys e2 where yse2: "yse2 = (ys, e2)" by force
      from IH[OF m] yse2 obtain g2 where g2: "P g2 e2" "R g2 e2 g1 e1" "list_all2 (\<lambda>x y. Q x y g2 e2) xs ys"
        by blast
      from r yse2 have "r = Ok (y # ys, e2)" by (simp add: return_def)
      with g2 g1 show ?thesis by (auto intro: mono trans)
    qed
  qed
qed


subsection \<open>Projections\<close>

lemma pr_exn:
  assumes "pr xs s env d binders = Some r"
  shows "wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow> env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow>
    proper s \<Longrightarrow> typs_ok ar s \<Longrightarrow> has_type V (map snd binders) s T \<Longrightarrow> below (maxidx env) s \<Longrightarrow>
    0 \<le> d \<Longrightarrow> nat_of_integer d \<le> length binders \<Longrightarrow>
    \<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer d + nat_of_integer x < length binders \<Longrightarrow>
    fails_ok (Some r) \<and> (ppat s \<and> env_ppat env \<longrightarrow> r \<noteq> Err Pattern) \<and>
    (\<forall>s' env'. r = Ok (s', env') \<longrightarrow> (\<exists>V'. ty_ext ar V env V' env' \<and> below (maxidx env') s' \<and>
      has_type V' (pctx (map snd binders) (nat_of_integer d) xs) s' T) \<and> new_ok env env' s \<and>
      (ppat s \<longrightarrow> env_ppat env \<longrightarrow> env_ppat env'))"
  using assms
proof (induction xs s env d binders r arbitrary: V T rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d binders r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env" and ps: "proper s" "typs_ok ar s" and ty: "has_type V (map snd binders) s T"
    and bs: "below (maxidx env) s" and d0: "0 \<le> d" and dl: "nat_of_integer d \<le> length binders"
    and xsb: "\<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer d + nat_of_integer x < length binders"
    using "1.prems" by simp_all
  let ?Bs = "map snd binders"
  let ?Ts = "pctx (map snd binders) (nat_of_integer d) xs"
  let ?N = "ppat s \<and> env_ppat env"
  have xs0: "\<forall>x\<in>set xs. 0 \<le> x" using xsb by simp
  have vt: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wf])
  from "1.hyps" have "head_norm env s \<bind> (\<lambda>s0. (if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty \<Rightarrow> do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}
            | _ \<Rightarrow> raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')}))) = Some r"
    by (simp only:)
  then show ?case
  proof (rule bindM_SomeE)
    fix e assume "head_norm env s = Some (Err e)"
    with head_norm_no_exn_aux[OF _ wf ety ty] show ?thesis by auto
  next
    fix s0 assume hn: "head_norm env s = Some (Ok s0)" and rest: "(if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty \<Rightarrow> do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}
            | _ \<Rightarrow> raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')})) = Some r"
    from head_norm_sound[OF hn refl wf ps]
    have s0: "proper s0" "typs_ok ar s0" by auto
    have ty0: "has_type V ?Bs s0 T" by (rule head_norm_typed[OF hn refl wf ety ty])
    have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF hn refl wf fr bs])
    have pp0: "ppat s0" if "?N" using head_norm_ppat[OF hn wf] that by blast
    have occ0: "occt env y s" if "occt env y s0" for y by (rule head_norm_occt[OF hn refl vt that])
    show ?thesis
    proof (cases "is_Abs s0")
      case True
      then obtain a U t where s0a: "s0 = pterm.Abs a U t" by (cases s0) auto
      from rest True s0a have prt: "prr xs t env (d + 1) ((a, U) # binders) \<bind>
          (\<lambda>(t', env'). return (pterm.Abs a U t', env')) = Some r"
        by simp
      from ty0 s0a obtain W where T: "T = U \<rightarrow>\<^sub>T W" and tyt: "has_type V (U # ?Bs) t W"
        by (auto elim: has_type_elims)
      have bt: "below (maxidx env) t" using bs0 s0a by simp
      have pt: "proper t" "typs_ok ar t" and gU: "ground ar U" using s0 s0a by simp_all
      have bok': "binders_ok ar ((a, U) # binders)" using bok gU by (simp add: binders_ok_def)
      have nd: "nat_of_integer (d + 1) = Suc (nat_of_integer d)" using d0 by (simp add: nat_of_integer_add)
      have d1: "0 \<le> d + 1" "nat_of_integer (d + 1) \<le> length ((a, U) # binders)"
        "\<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer (d + 1) + nat_of_integer x < length ((a, U) # binders)"
        using d0 dl xsb by (simp_all add: nd)
      have tyt1: "has_type V (map snd ((a, U) # binders)) t W" using tyt by simp
      have ppt: "ppat t \<and> env_ppat env" if "?N" using pp0[OF that] that s0a by (auto dest: ppat_AbsD)
      note IH = "1.IH"[OF _ wf bok' ety fr pt tyt1 bt d1]
      from prt show ?thesis
      proof (rule bindM_SomeE)
        fix e assume "prr xs t env (d + 1) ((a, U) # binders) = Some (Err e)" "r = Err e"
        with IH ppt show ?thesis by fastforce
      next
        fix te assume pr1: "prr xs t env (d + 1) ((a, U) # binders) = Some (Ok te)"
          and r: "(\<lambda>(t', env'). return (pterm.Abs a U t', env')) te = Some r"
        obtain t' env' where te: "te = (t', env')" by force
        from IH[OF pr1[unfolded te]] obtain V' where ext: "ty_ext ar V env V' env'"
          and bt': "below (maxidx env') t'"
          and tyt': "has_type V' (pctx (map snd ((a, U) # binders)) (nat_of_integer (d + 1)) xs) t' W"
          and nw: "new_ok env env' t" and ep: "ppat t \<longrightarrow> env_ppat env \<longrightarrow> env_ppat env'"
          by auto
        from r te have "r = Ok (pterm.Abs a U t', env')" by (simp add: return_def)
        moreover have "has_type V' ?Ts (pterm.Abs a U t') T"
          using tyt' by (simp add: nd pctx_Suc T has_type.Abs)
        moreover have "new_ok env env' s" using nw s0a occ0 by (auto intro: new_ok_occt)
        moreover have "?N \<longrightarrow> env_ppat env'" using ep ppt by blast
        ultimately show ?thesis using ext bt' by auto
      qed
    next
      case False
      obtain h ts where hts: "strip_comb s0 = (h, ts)" by force
      note s0_eq = strip_comb_list_comb[OF hts]
      have nAh: "\<not> is_Abs h" using head_norm_head[OF hn refl False] hts by simp
      show ?thesis
      proof (cases "is_Var h")
        case True
        then obtain F Fty where h: "h = pterm.Var F Fty" by (cases h) auto
        define DO where "DO = do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}"
        from rest False hts h have rv: "DO = Some r" by (simp add: DO_def)
        have pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
          using s0 s0_eq by (auto simp: proper_list_comb typs_ok_list_comb)
        from ty0 s0_eq obtain Us0 where tyts: "list_all2 (has_type V ?Bs) ts Us0"
          by (auto simp: has_type_list_comb)
        have tyts': "\<forall>u\<in>set ts. \<exists>U. has_type V ?Bs u U"
          using tyts by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
        have gFty: "ground ar Fty" using s0 s0_eq h by (simp add: typs_ok_list_comb)
        have Fm: "snd F \<le> maxidx env" using bs0 s0_eq h by (simp add: below_list_comb)
        have Funb: "vt_lookup (tenv env) F = None"
          using head_norm_head_unbound[OF hn refl vt] hts h by simp
        obtain ri where ri: "ints_of' env ts = Some ri"
          using rv by (cases "ints_of' env ts") (simp_all add: DO_def bindM_def)
        from ints_of'_res[OF ri wf ety tyts'] show ?thesis
        proof
          assume riP: "ri = Err Pattern"
          have "\<not> ?N"
          proof
            assume "?N"
            from ppat_strip_flex[OF hts[unfolded h] pp0[OF this]] obtain iss
              where "ts = map Bound iss" "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i" by blast
            with ri riP show False by (simp add: ints_of'_Bounds return_def)
          qed
          with rv ri riP show ?thesis by (auto simp: DO_def bindM_def)
        next
          assume "\<exists>js. ri = Ok js"
          then obtain js where js: "ok (ints_of' env ts) js" using ri by blast
          note ints = ints_of'_sound[OF js wf pts]
          have tyapp: "has_type V ?Bs (app (pterm.Var F Fty) js) T"
            using has_type_ints_of'[OF js wf ety] ty0 s0_eq h by simp
          note tj = has_type_app_Var[OF tyapp]
          define UsJ where "UsJ = map (\<lambda>i. ?Bs ! nat_of_integer i) js"
          have lenUsJ: "length UsJ = length js" by (simp add: UsJ_def)
          have UsJ_alt: "UsJ = map (\<lambda>i. snd (binders ! nat_of_integer i)) js"
            unfolding UsJ_def by (rule map_cong[OF refl]) (use tj(1) in auto)
          have FtyJ: "Fty = foldr fun_type UsJ T" using tj(3) by (simp add: UsJ_def)
          from mapM_return[of js "try_trans xs d", OF try_trans_no_exn] obtain js' where
            js'm: "mapM (try_trans xs d) js = return js'"
            and js'r: "list_all2 (\<lambda>j opt. try_trans xs d j = return opt) js js'"
            by blast
          have js'2: "list_all2 (\<lambda>j opt. ok (try_trans xs d j) opt) js js'"
            using js'r by (simp add: return_def)
          then have len': "length js' = length js" by (simp add: list_all2_lengthD)
          let ?ks = "mk_proj_list js'" and ?ls = "List.map_filter id js'"
          have tt: "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and> 0 \<le> l \<and>
              nat_of_integer l < nat_of_integer d + length xs \<and>
              bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer j)) js js'"
          proof -
            have "js' ! p = None \<or> (\<exists>l. js' ! p = Some l \<and> 0 \<le> l \<and>
              nat_of_integer l < nat_of_integer d + length xs \<and>
              bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer (js ! p))"
              if p: "p < length js" for p
            proof -
              from js'2 p have "ok (try_trans xs d (js ! p)) (js' ! p)" by (simp add: list_all2_conv_all_nth)
              from ok_try_trans[OF this d0 _ xs0] ints(2) p show ?thesis by auto
            qed
            with len' show ?thesis by (simp add: list_all2_conv_all_nth)
          qed
          have ks_b: "\<forall>k\<in>set ?ks. 0 \<le> k \<and> nat_of_integer k < length js"
            using mk_proj_list_ren(2)[of "nats js" js'] len' by simp
          define Hty where "Hty = foldr fun_type (map (\<lambda>k. rev UsJ ! nat_of_integer k) ?ks) T"
          have HtyE: "type_of_G env Fty (ilength js) ?ks = return Hty"
            using type_of_G_ok[OF vt, of ?ks UsJ T] ks_b lenUsJ by (simp add: FtyJ ilength_eq Hty_def)
          obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
          let ?H = "(fst F, maxidx env + 1)"
          define V' where "V' = V(?H := Hty)"
          note nv = typed_new_var[OF fr ety G, folded V'_def]
          from mkabs_ok[of js binders "app H ?ks"] tj(1) obtain t
            where tE: "mkabs binders js (app H ?ks) = return t" by auto
          have t: "ok (mkabs binders js (app H ?ks)) t" using tE by (simp add: return_def)
          from update_unbound[of env1 F Fty t] Funb nv(7) obtain env''
            where uE: "update (F, Fty) t env1 = return env''" by auto
          have env': "ok (update (F, Fty) t env1) env''" using uE by (simp add: return_def)
          have rr: "r = Ok (app H ?ls, env'')"
            using rv js js'm HtyE G tE uE
            by (simp add: DO_def Let_def mk_hnf_def return_def bindM_def)
          have F_ne: "F \<noteq> ?H" using Fm by (cases F) auto
          have tyt: "has_type V' [] t Fty"
          proof -
            have "has_type V' (rev UsJ) (app H ?ks) T"
              unfolding has_type_app using ks_b lenUsJ nv(5,6) Hty_def
              by (auto intro: has_type.Var)
            then have "has_type V' (rev (map (\<lambda>i. snd (binders ! nat_of_integer i)) js)) (app H ?ks) T"
              by (simp add: UsJ_alt)
            from has_type_mkabs0[OF t _ this] tj(1) show ?thesis by (simp add: FtyJ UsJ_alt)
          qed
          have VF: "V' F = Fty" using tj(2) F_ne by (simp add: V'_def)
          have below_t: "below (maxidx env1) t" using vars_mkabs[OF t] by (simp add: below_def vars_app nv(4,5))
          have Fm1: "snd F \<le> maxidx env1" using Fm nv(4) by simp
          note up = typed_update[OF nv(3) nv(2) env' VF tyt Fm1 below_t]
          have Hg: "ground ar Hty" using type_of_G_ground[OF _ vt gFty] HtyE by (simp add: return_def)
          have wf1: "wf_env ar env1" by (rule genvar_wf_env[OF G wf])
          have wf': "wf_env ar env''"
            by (rule binding_sound(2)[OF t[unfolded nv(5)] env' wf1 gFty Hg bok ks_b])
          have ext: "ty_ext ar V env V' env''"
            unfolding ty_ext_def using nv(1,4) up wf' ok_update_extends[OF env'] genvar_extends[OF G]
            by (auto intro: extends_trans)
          have ls_b: "\<forall>l\<in>set ?ls. 0 \<le> l \<and> nat_of_integer l < nat_of_integer d + length xs"
            using tt by (fastforce simp: set_map_filter_id list_all2_conv_all_nth in_set_conv_nth)
          have lenTs: "length ?Ts = nat_of_integer d + length xs" using dl by (simp add: length_pctx)
          have "map (\<lambda>l. ?Ts ! nat_of_integer l) ?ls =
              map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip (map (\<lambda>j. ?Bs ! nat_of_integer j) js) js'))"
          proof (rule map_filter_bren)
            show "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and>
                ?Ts ! nat_of_integer l = ?Bs ! nat_of_integer j)) js js'"
              using tt by (rule list_all2_mono) (use dl in \<open>auto simp: pctx_nth\<close>)
          qed
          also have "\<dots> = map (\<lambda>k. rev UsJ ! nat_of_integer k) ?ks"
            using mk_proj_list_rev[of UsJ js'] lenUsJ len' by (simp add: UsJ_def)
          finally have tyls: "map (\<lambda>l. ?Ts ! nat_of_integer l) ?ls = map (\<lambda>k. rev UsJ ! nat_of_integer k) ?ks" .
          have tys': "has_type V' ?Ts (app H ?ls) T"
            unfolding has_type_app using ls_b lenTs nv(5,6) Hty_def tyls
            by (auto intro: has_type.Var)
          have bs': "below (maxidx env'') (app H ?ls)" using up(3) nv(4,5) by (simp add: below_app)
          have nw: "new_ok env env'' s"
          proof (rule new_okI)
            show "extends env'' env" using ok_update_extends[OF env'] genvar_extends[OF G] by (rule extends_trans)
            show "maxidx env \<le> maxidx env''" using up(3) nv(4) by simp
            fix y U u assume y2: "vt_lookup (tenv env'') y = Some (U, u)" and y0: "vt_lookup (tenv env) y = None"
            from y2 y0 ok_update(2)[OF env'] nv(7) have yF: "y = F" "u = t" by (auto split: if_splits)
            have "occt env F s0" using Funb s0_eq h by (auto simp: occt_def vars_list_comb intro: occv_refl)
            then have "occt env y s" using yF occ0 by simp
            moreover have "\<forall>z\<in>vars u. maxidx env < snd z"
              using vars_mkabs[OF t] yF by (simp add: vars_app nv(5))
            ultimately show "(occt env y s \<or> maxidx env < snd y) \<and> (\<forall>z\<in>vars u. maxidx env < snd z)" by simp
          qed
          have "env_ppat env''" if "?N"
          proof -
            have dks: "distinct ?ks"
              using mk_proj_list_aux_sorted[of js' "ilength js' - 1"]
              by (auto simp: mk_proj_list_def intro: distinct_sorted_gt)
            have "ppat t" using ppat_mkabs[OF t] nv(5) dks ks_b by (auto intro: ppat.ppat_flex)
            then show ?thesis using env_ppat_update[OF env'] env_ppat_genvar[OF G] that by simp
          qed
          then show ?thesis using rr ext tys' bs' nw by auto
        qed
      next
        case notVar: False
        have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF hts])
        define hm where "hm = (case h of Bound i \<Rightarrow> trans xs d i \<bind> (\<lambda>j. return (Bound j)) | _ \<Rightarrow> return h)"
        from rest False hts notVar nAh have rr: "hm \<bind> (\<lambda>h'.
            mapAccM (\<lambda>s env. prr xs s env d binders) ts env \<bind>
            (\<lambda>(ts', env'). return (list_comb h' ts', env'))) = Some r"
          by (simp add: hm_def)
        from ty0 s0_eq obtain Us where tyh: "has_type V ?Bs h (foldr fun_type Us T)"
          and tyts: "list_all2 (has_type V ?Bs) ts Us"
          by (auto simp: has_type_list_comb)
        have pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
          using s0 s0_eq by (auto simp: proper_list_comb typs_ok_list_comb)
        have bts: "\<forall>t\<in>set ts. below (maxidx env) t" using bs0 s0_eq by (simp add: below_list_comb)
        have ppts: "\<forall>t\<in>set ts. ppat t" if "?N"
          using ppat_spine[OF pp0[OF that, unfolded s0_eq] nApp False[unfolded s0_eq]] notVar by auto
        have lenTs: "length ?Ts = nat_of_integer d + length xs" using dl by (simp add: length_pctx)
        have hd: "\<forall>e. hm = Some (Err e) \<longrightarrow> (\<exists>u. e = Unif u)"
          "\<And>h'. ok hm h' \<Longrightarrow> (\<forall>m. below m h') \<and> (\<forall>V0. has_type V0 ?Ts h' (foldr fun_type Us T))"
        proof -
          have "(\<forall>e. hm = Some (Err e) \<longrightarrow> (\<exists>u. e = Unif u)) \<and> (\<forall>h'. ok hm h' \<longrightarrow>
            (\<forall>m. below m h') \<and> (\<forall>V0. has_type V0 ?Ts h' (foldr fun_type Us T)))"
          proof (cases h)
            case (Bound i)
            from tyh Bound have i: "0 \<le> i" "nat_of_integer i < length ?Bs"
              "foldr fun_type Us T = ?Bs ! nat_of_integer i"
              by (simp_all add: has_type_Bound_iff)
            have "\<forall>e. hm = Some (Err e) \<longrightarrow> (\<exists>u. e = Unif u)"
            proof (intro allI impI)
              fix e assume "hm = Some (Err e)"
              then obtain rt where "trans xs d i = Some rt" "rt = Err e"
                by (auto simp: hm_def Bound bindM_def return_def split: option.splits res.splits)
              with trans_res show "\<exists>u. e = Unif u" by blast
            qed
            moreover have "(\<forall>m. below m h') \<and> (\<forall>V0. has_type V0 ?Ts h' (foldr fun_type Us T))"
              if "ok hm h'" for h'
            proof -
              from that obtain j where j: "ok (trans xs d i) j" "h' = Bound j"
                by (auto simp: hm_def Bound)
              note tj = ok_trans[OF j(1) d0 i(1) xs0]
              have "?Ts ! nat_of_integer j = ?Bs ! nat_of_integer i"
                using pctx_nth[OF _ conjunct1[OF conjunct2[OF tj]]] dl tj by simp
              then show ?thesis using tj i(3) lenTs by (auto simp: j(2) has_type_Bound_iff)
            qed
            ultimately show ?thesis by blast
          next
            case (Const c U)
            with tyh show ?thesis by (auto simp: hm_def return_def elim: has_type_elims intro: has_type.Const)
          next
            case (Free c U)
            with tyh show ?thesis by (auto simp: hm_def return_def elim: has_type_elims intro: has_type.Free)
          qed (use notVar nAh nApp in auto)
          then show "\<forall>e. hm = Some (Err e) \<longrightarrow> (\<exists>u. e = Unif u)"
            "\<And>h'. ok hm h' \<Longrightarrow> (\<forall>m. below m h') \<and> (\<forall>V0. has_type V0 ?Ts h' (foldr fun_type Us T))"
            by blast+
        qed
        define P where "P = (\<lambda>g e. ty_ext ar V env g e \<and> new_ok env e s0 \<and> (?N \<longrightarrow> env_ppat e))"
        define R where "R = (\<lambda>g2 e2 (g1 :: indexname \<Rightarrow> ptyp) e1. agreeV (maxidx e1) g1 g2 \<and> maxidx e1 \<le> maxidx e2)"
        define Q where "Q = (\<lambda>x y g e. below (maxidx e) y \<and> (\<forall>U. has_type V ?Bs x U \<longrightarrow> has_type g ?Ts y U))"
        have mc: "fails_ok (Some rm) \<and> (?N \<longrightarrow> rm \<noteq> Err Pattern) \<and> (\<forall>ys e'. rm = Ok (ys, e') \<longrightarrow>
            (\<exists>g'. P g' e' \<and> R g' e' V env \<and> list_all2 (\<lambda>x y. Q x y g' e') ts ys))"
          if m: "mapAccM (\<lambda>s env. prr xs s env d binders) ts env = Some rm" for rm
        proof (rule mapAccM_inv[OF m, of P V ?N R Q])
          show "P V env" using ety fr wf by (simp add: P_def ty_ext_refl new_ok_refl)
        next
          fix x g e r1
          assume x: "x \<in> set ts" and Pg: "P g e" and pr1: "prr xs x e d binders = Some r1"
          from Pg have ext1: "ty_ext ar V env g e" and nw1: "new_ok env e s0" and ep1: "?N \<longrightarrow> env_ppat e"
            by (simp_all add: P_def)
          note e1 = ext1[unfolded ty_ext_def]
          from tyts x obtain U where tyx: "has_type V ?Bs x U"
            by (metis in_set_conv_nth list_all2_conv_all_nth)
          have bx: "below (maxidx env) x" using bts x by blast
          have tyx1: "has_type g ?Bs x U" using has_type_agreeV[OF tyx bx] e1 by blast
          have bx1: "below (maxidx e) x" using below_mono[OF bx] e1 by blast
          have px: "proper x" "typs_ok ar x" using pts x by auto
          have IHx: "fails_ok (Some r1) \<and> (ppat x \<and> env_ppat e \<longrightarrow> r1 \<noteq> Err Pattern) \<and>
              (\<forall>s' env'. r1 = Ok (s', env') \<longrightarrow> (\<exists>V'. ty_ext ar g e V' env' \<and> below (maxidx env') s' \<and>
                has_type V' ?Ts s' U) \<and> new_ok e env' x \<and> (ppat x \<longrightarrow> env_ppat e \<longrightarrow> env_ppat env'))"
            using "1.IH"[OF pr1 _ bok _ _ px tyx1 bx1 d0 dl xsb] e1 by blast
          show "fails_ok (Some r1) \<and> (?N \<longrightarrow> r1 \<noteq> Err Pattern) \<and>
            (\<forall>y e1. r1 = Ok (y, e1) \<longrightarrow> (\<exists>g1. P g1 e1 \<and> R g1 e1 g e \<and> Q x y g1 e1))"
          proof (intro conjI allI impI)
            show "fails_ok (Some r1)" using IHx by blast
            show "r1 \<noteq> Err Pattern" if "?N" using IHx ppts[OF that] x ep1 that by blast
            fix y e2 assume r1: "r1 = Ok (y, e2)"
            with IHx obtain V2 where ext2: "ty_ext ar g e V2 e2" and by2: "below (maxidx e2) y"
              and ty2: "has_type V2 ?Ts y U" and nw2: "new_ok e e2 x"
              and ep2: "ppat x \<longrightarrow> env_ppat e \<longrightarrow> env_ppat e2"
              by blast
            have "ty_ext ar V env V2 e2" by (rule ty_ext_trans[OF ext1 ext2])
            moreover have "new_ok env e2 s0"
              using new_ok_trans[OF nw1 nw2 fr] x s0_eq by (auto simp: vars_list_comb)
            moreover have "env_ppat e2" if "?N"
              using ep2 ep1 that ppts x by blast
            ultimately have "P V2 e2" by (simp add: P_def)
            moreover have "R V2 e2 g e" using ext2 by (simp add: R_def ty_ext_def)
            moreover have "Q x y V2 e2" using by2 ty2 has_type_unique[OF tyx] by (auto simp: Q_def)
            ultimately show "\<exists>g1. P g1 e2 \<and> R g1 e2 g e \<and> Q x y g1 e2" by blast
          qed
        next
          fix x y g1 e1 g2 e2 assume "Q x y g1 e1" "R g2 e2 g1 e1"
          then show "Q x y g2 e2"
            by (auto simp: Q_def R_def intro: below_mono has_type_agreeV)
        next
          fix g1 e1 g2 e2 g3 e3 assume "R g2 e2 g1 e1" "R g3 e3 g2 e2"
          then show "R g3 e3 g1 e1" by (auto simp: R_def intro: agreeV_trans)
        next
          fix g e show "R g e g e" by (simp add: R_def)
        qed
        from rr show ?thesis
        proof (rule bindM_SomeE)
          fix e assume "hm = Some (Err e)" "r = Err e"
          with hd(1) show ?thesis by (auto simp: exn_ok_def)
        next
          fix h' assume h': "hm = Some (Ok h')" and rr2: "mapAccM (\<lambda>s env. prr xs s env d binders) ts env \<bind>
            (\<lambda>(ts', env'). return (list_comb h' ts', env')) = Some r"
          note hd' = hd(2)[OF h']
          from rr2 show ?thesis
          proof (rule bindM_SomeE)
            fix e assume "mapAccM (\<lambda>s env. prr xs s env d binders) ts env = Some (Err e)" "r = Err e"
            with mc show ?thesis by fastforce
          next
            fix tse assume m: "mapAccM (\<lambda>s env. prr xs s env d binders) ts env = Some (Ok tse)"
              and r: "(\<lambda>(ts', env'). return (list_comb h' ts', env')) tse = Some r"
            obtain ts' env' where tse: "tse = (ts', env')" by force
            from r tse have r': "r = Ok (list_comb h' ts', env')" by (simp add: return_def)
            from mc[OF m[unfolded tse]] obtain g' where Pg: "P g' env'"
              and Qs: "list_all2 (\<lambda>x y. Q x y g' env') ts ts'"
              by blast
            have "below (maxidx env') (list_comb h' ts')"
              using hd' Qs by (auto simp: below_list_comb Q_def list_all2_conv_all_nth in_set_conv_nth)
            moreover have "has_type g' ?Ts (list_comb h' ts') T"
            proof -
              have "list_all2 (has_type g' ?Ts) ts' Us"
                using Qs tyts by (auto simp: Q_def list_all2_conv_all_nth)
              then show ?thesis using hd' by (auto simp: has_type_list_comb)
            qed
            moreover have "new_ok env env' s" using Pg occ0 by (auto simp: P_def intro: new_ok_occt)
            ultimately show ?thesis using Pg r' by (auto simp: P_def)
          qed
        qed
      qed
    qed
  qed
qed


subsection \<open>Occurrences in patterns are rigid\<close>

lemma vars_subst_bound_aux_ge: "vars t \<subseteq> vars (subst_bound_aux arg lev t)"
  by (induction arg lev t rule: subst_bound_aux.induct) auto

lemma vars_subst_bound_Bound: "vars (subst_bound (Bound i) t) = vars t"
  using vars_subst_bound_aux[of "Bound i" 0 t] vars_subst_bound_aux_ge[of t "Bound i" 0]
  by (simp add: subst_bound_def)

lemma occt_Var_bound:
  "vt_lookup (tenv env) y = Some (U, u) \<Longrightarrow> occt env x (Var y T) \<longleftrightarrow> occt env x u"
proof
  assume lk: "vt_lookup (tenv env) y = Some (U, u)"
  {
    assume "occt env x (Var y T)"
    then have "occv env x y" by (simp add: occt_def)
    then show "occt env x u"
    proof cases
      case occv_refl
      with lk show ?thesis by simp
    next
      case (occv_step U' u' z)
      with lk show ?thesis by (auto simp: occt_def)
    qed
  next
    assume "occt env x u"
    with lk show "occt env x (Var y T)" by (auto simp: occt_def intro: occv_step)
  }
qed

lemma occurs_True_occt:
  assumes "occurs F t env = Some r"
  shows "r = Ok True \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> occt env F t"
  using assms
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 occ F t env r)
  from "1.hyps" "1.prems"(1) have h: "(case t of
      pterm.Var G T \<Rightarrow> lookup env G T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G))
    | t1 $ t2 \<Rightarrow> occ F t1 env \<bind> (\<lambda>b. if b then return True else occ F t2 env)
    | pterm.Abs _ _ u \<Rightarrow> occ F u env
    | _ \<Rightarrow> return False) = Some (Ok True)"
    by simp
  note IH = "1.IH"[OF _ refl "1.prems"(2)]
  show ?case
  proof (cases t)
    case (Var G U)
    from h Var obtain r' where lk: "ok (lookup env G U) r'"
      and rest: "(case r' of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G)) = Some (Ok True)"
      by (auto elim!: bindM_SomeE)
    from ok_lookup[OF "1.prems"(2) lk]
    consider "r' = None" "vt_lookup (tenv env) G = None" | u where "r' = Some u" "vt_lookup (tenv env) G = Some (U, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest have "F = G" by (simp add: return_def)
      with 1 Var show ?thesis by (auto simp: occt_def intro: occv_refl)
    next
      case 2
      with rest have "occt env F u" by (intro IH) simp
      with 2 Var show ?thesis by (simp add: occt_Var_bound)
    qed
  next
    case (App t1 t2)
    from h App obtain b where o1: "occ F t1 env = Some (Ok b)"
      and o2: "(if b then return True else occ F t2 env) = Some (Ok True)"
      by (auto elim!: bindM_SomeE)
    with App IH show ?thesis by (cases b) (auto simp: return_def)
  next
    case (Abs a U u)
    with h IH show ?thesis by auto
  qed (use h in \<open>simp_all add: return_def\<close>)
qed

text \<open>Head normalisation of a pattern keeps all variables reachable through bindings.\<close>

lemma head_norm_ppat_occt_aux:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow>
    ppat t' \<and> loose_BVars (tr t') \<subseteq> loose_BVars (tr t) \<and> (rigid_head t \<longrightarrow> t' = t) \<and>
    (occt env z t \<longrightarrow> occt env z t')"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have wf: "wf_env ar env" and epp: "env_ppat env" and pt: "ppat t" and t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  note IH = "1.IH"[OF _ refl wf epp]
  show ?case
  proof (cases t)
    case (Var xi U)
    have nr: "\<not> rigid_head t" using Var rigid_head_cases[of t] by (auto simp: is_rigid_def)
    from Var t' obtain r' where lk: "ok (lookup env xi U) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    from ok_lookup[OF wf_envD(1)[OF wf] lk]
    consider "r' = None" | u where "r' = Some u" "vt_lookup (tenv env) xi = Some (U, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest pt show ?thesis by auto
    next
      case 2
      with rest have hu: "hn env u = Some (Ok t')" by simp
      have "loose_BVars (tr u) = {}"
        using wf_envD(2)[OF wf 2(2)] by (simp add: no_loose_bound_loose_BVars)
      with IH[OF hu env_ppatD[OF epp 2(2)]] nr 2(2) Var show ?thesis by (simp add: occt_Var_bound)
    qed
  next
    case (Abs a U body)
    have nr: "\<not> rigid_head t" using Abs rigid_head_cases[of t] by (auto simp: is_rigid_def)
    with t' obtain b' where hb: "hn env body = Some (Ok b')" and tb: "t' = pterm.Abs a U b'"
      using Abs by auto
    from IH[OF hb ppat_AbsD[OF pt[unfolded Abs]]] have "ppat b'" "loose_BVars (tr b') \<subseteq> loose_BVars (tr body)"
      "occt env z body \<longrightarrow> occt env z b'"
      by simp_all
    with tb Abs nr show ?thesis by (auto intro: ppat.ppat_Abs)
  next
    case (App f u)
    from pt[unfolded App] show ?thesis
    proof (cases rule: ppat_AppE)
      case (rigid h ts)
      have nA: "\<not> is_Abs f" using rigid(1,2) by (cases ts rule: rev_cases) (auto simp: is_rigid_def list_comb_snoc)
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      have "rigid_head f" using rigid(1,2) by (auto simp: rigid_head_def)
      with IH[OF nf] rigid have "nf = f" by (auto intro: ppat.ppat_rigid)
      with rest nA have "t' = t" using App by (cases f) auto
      with pt show ?thesis by simp
    next
      case (flex x T iss i)
      have nA: "\<not> is_Abs f" using flex(1) by (cases iss rule: rev_cases) (auto simp: app_def)
      have nr: "\<not> rigid_head t" using flex(1,2) App not_rigid_head_app[of x T "iss @ [i]"] by (simp add: app_def)
      have pf: "ppat f" using flex(1,3,4) by (auto intro: ppat.ppat_flex)
      with t' App nA obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from IH[OF nf pf] have pnf: "ppat nf" and lnf: "loose_BVars (tr nf) \<subseteq> set (nats iss)"
        and onf: "occt env z f \<longrightarrow> occt env z nf"
        using flex(1) by (simp_all add: loose_BVars_tr_app)
      have i0: "0 \<le> i" using flex(4) by simp
      have ni: "nat_of_integer i \<notin> set (nats iss)"
      proof
        assume "nat_of_integer i \<in> set (nats iss)"
        then obtain j where "j \<in> set iss" "nat_of_integer j = nat_of_integer i" by auto
        with flex(4) i0 have "i \<in> set iss" by (auto simp: nat_of_integer_eq_iff)
        with flex(3) show False by simp
      qed
      have lt: "loose_BVars (tr t) = insert (nat_of_integer i) (set (nats iss))"
        using App flex(1,2) by (auto simp: tr_app')
      have ot: "occt env z t \<longrightarrow> occt env z nf" using onf App flex(2) by simp
      note fl = flex
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a U body where Abs: "nf = pterm.Abs a U body" by (cases nf) auto
        with rest have hb: "hn env (subst_bound u body) = Some (Ok t')" by simp
        have pb: "ppat body" using pnf Abs by (auto dest: ppat_AbsD)
        have "Suc (nat_of_integer i) \<notin> loose_BVars (tr body)"
          using lnf ni Abs by auto
        from ppat_subst_bound[OF pb i0 this] have ps: "ppat (subst_bound u body)" using fl(2) by simp
        have "loose_BVars (tr (subst_bound u body)) \<subseteq> insert (nat_of_integer i) (loose_BVars (dB.Abs (tr body)))"
          using fl(2) ppat_proper[OF pb] i0 loose_BVars_subst_BVar0[of "tr body" "nat_of_integer i"]
          by (simp add: tr_subst_bound)
        with lnf Abs lt have "loose_BVars (tr (subst_bound u body)) \<subseteq> loose_BVars (tr t)" by auto
        moreover have "occt env z t \<longrightarrow> occt env z (subst_bound u body)"
          using ot Abs fl(2) by (simp add: occt_def vars_subst_bound_Bound)
        ultimately show ?thesis using IH[OF hb ps] nr by auto
      next
        case False
        with rest have tt: "t' = nf $ u" by (cases nf) auto
        have lt': "loose_BVars (tr t') \<subseteq> loose_BVars (tr t)" using tt fl(2) lnf lt by auto
        have ot': "occt env z t \<longrightarrow> occt env z t'" using ot tt by simp
        from pnf False show ?thesis
        proof (cases rule: ppat_nonAbsE)
          case (rigid h ts)
          have "ppat (Bound i)" using ppat.ppat_rigid[of "Bound i" "[]"] i0 by (simp add: is_rigid_def)
          then have "ppat t'" using tt rigid fl(2) ppat.ppat_rigid[of h "ts @ [Bound i]"]
            by (auto simp: list_comb_snoc)
          with lt' nr ot' show ?thesis by simp
        next
          case (flex y V jss)
          have "i \<notin> set jss"
          proof
            assume "i \<in> set jss"
            then have "nat_of_integer i \<in> loose_BVars (tr nf)" using flex(1) by (auto simp: tr_app')
            with lnf ni show False by auto
          qed
          then have "ppat (app (Var y V) (jss @ [i]))" using flex(2,3) i0 by (auto intro!: ppat.ppat_flex)
          then have "ppat t'" using tt flex(1) fl(2) by (simp add: app_def)
          with lt' nr ot' show ?thesis by simp
        qed
      qed
    qed
  qed (use t' pt in auto)
qed

lemma head_norm_ppat_occt:
  "head_norm env t = Some (Ok t') \<Longrightarrow> wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow> occt env z t \<Longrightarrow> occt env z t'"
  using head_norm_ppat_occt_aux by blast

lemma strip_comb_list_comb_eq: "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> strip_comb (list_comb h ts) = (h, ts)"
proof -
  assume h: "\<not> (\<exists>f u. h = f $ u)"
  obtain h' ts' where s: "strip_comb (list_comb h ts) = (h', ts')" by force
  from strip_comb_list_comb[OF s] have "list_comb h ts = list_comb h' ts'" .
  with list_comb_eq_iff[OF h strip_comb_head[OF s]] s show ?thesis by simp
qed

lemma existsM_Ok:
  assumes "existsM P xs = Some r" "\<And>x r. x \<in> set xs \<Longrightarrow> P x = Some r \<Longrightarrow> \<exists>b. r = Ok b \<and> (Q x \<longrightarrow> b)"
  shows "\<exists>b. r = Ok b \<and> ((\<exists>x\<in>set xs. Q x) \<longrightarrow> b)"
  using assms
proof (induction xs arbitrary: r)
  case (Cons x xs)
  from Cons.prems(1) have "P x \<bind> (\<lambda>b. if b then return True else existsM P xs) = Some r" by simp
  then show ?case
  proof (rule bindM_SomeE)
    fix e assume "P x = Some (Err e)"
    with Cons.prems(2)[of x] show ?thesis by auto
  next
    fix b assume px: "P x = Some (Ok b)" and rest: "(if b then return True else existsM P xs) = Some r"
    from Cons.prems(2)[OF _ px] have qb: "Q x \<longrightarrow> b" by auto
    show ?thesis
    proof (cases b)
      case True
      with rest show ?thesis by (auto simp: return_def)
    next
      case False
      with rest have "existsM P xs = Some r" by simp
      from Cons.IH[OF this] Cons.prems(2) False qb show ?thesis by auto
    qed
  qed
qed (auto simp: return_def)

text \<open>In patterns, every occurrence of \<open>F\<close> reachable through bindings is rigid.\<close>

lemma rigid_occurs_ppat:
  assumes "rigid_occurs F t env = Some r"
  shows "wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> has_type V Ts t T \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow>
    \<exists>b. r = Ok b \<and> (occt env F t \<longrightarrow> b)"
  using assms
proof (induction F t env r arbitrary: Ts T rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t env r)
  have wf: "wf_env ar env" and ety: "env_typed V env" and tyt: "has_type V Ts t T"
    and epp: "env_ppat env" and pt: "ppat t"
    using 1 by simp_all
  note IH = "1.IH"
  define B where "B = (\<lambda>t'. case t' of
        pterm.Abs _ _ u \<Rightarrow> ro F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              pterm.Var G _ \<Rightarrow>
                if G = F then
                  handle (ints_of' env ts \<bind> (\<lambda>_. return True))
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | pterm.Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts)))"
  from "1.hyps" have "head_norm env t \<bind> B = Some r" by (simp add: B_def)
  then show ?case
  proof (rule bindM_SomeE)
    fix e assume "head_norm env t = Some (Err e)"
    with head_norm_no_exn_aux[OF _ wf ety tyt] show ?thesis by auto
  next
    fix t' assume hn: "head_norm env t = Some (Ok t')" and Bt: "B t' = Some r"
    from head_norm_no_exn_aux[OF hn wf ety tyt] have tyt': "has_type V Ts t' T" by simp
    have pt': "ppat t'" by (rule head_norm_ppat[OF hn wf epp pt])
    have occ: "occt env F t \<Longrightarrow> occt env F t'" by (rule head_norm_ppat_occt[OF hn wf epp pt])
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain a U u where t'a: "t' = pterm.Abs a U u" by (cases t') auto
      from tyt' t'a obtain W where tu: "has_type V (U # Ts) u W" by (auto elim: has_type_elims)
      from Bt t'a have "ro F u env = Some r" by (simp add: B_def)
      from IH[OF this wf ety tu epp ppat_AbsD[OF pt'[unfolded t'a]]] occ t'a show ?thesis by auto
    next
      case nA: False
      from pt' nA show ?thesis
      proof (cases rule: ppat_nonAbsE)
        case (rigid h ts)
        have sc: "strip_comb t' = (h, ts)"
          using strip_comb_list_comb_eq[OF is_rigid_not_App[OF rigid(1)]] rigid(2) by simp
        have ex: "existsM (\<lambda>u. ro F u env) ts = Some r"
          using Bt sc nA rigid(1) unfolding B_def by (cases t'; cases h) (simp_all add: is_rigid_def)
        from tyt' rigid(2) obtain Us where tyts: "list_all2 (has_type V Ts) ts Us"
          by (auto simp: has_type_list_comb)
        have elem: "\<exists>b. r' = Ok b \<and> (occt env F u \<longrightarrow> b)" if "u \<in> set ts" "ro F u env = Some r'" for u r'
        proof -
          from tyts that(1) obtain U where "has_type V Ts u U"
            by (metis in_set_conv_nth list_all2_conv_all_nth)
          from IH[OF that(2) wf ety this epp] rigid(3) that(1) show ?thesis by blast
        qed
        have "occt env F t' \<Longrightarrow> \<exists>u\<in>set ts. occt env F u"
          using rigid(1,2) by (auto simp: occt_def vars_list_comb is_rigid_def)
        with existsM_Ok[where Q = "\<lambda>u. occt env F u", OF ex elem] occ show ?thesis by blast
      next
        case (flex x U iss)
        have sc: "strip_comb t' = (Var x U, map Bound iss)"
          using strip_comb_list_comb_eq[of "Var x U" "map Bound iss"] flex(1) by (simp add: app_list_comb)
        have xu: "vt_lookup (tenv env) x = None"
          using head_norm_head_unbound[OF hn refl wf_envD(1)[OF wf]] sc by simp
        have "B t' = (if x = F then handle (ints_of' env (map Bound iss) \<bind> (\<lambda>_. return True))
            (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False)"
          using sc nA unfolding B_def by (cases t') simp_all
        also have "\<dots> = return (x = F)"
          using ints_of'_Bounds[OF flex(2,3), of env] by (simp add: return_def bindM_def handle_def)
        finally have "r = Ok (x = F)" using Bt by (simp add: return_def)
        moreover have "occt env F t' \<Longrightarrow> x = F"
          using flex(1) xu by (auto simp: occt_def vars_app dest: occv_unbound)
        ultimately show ?thesis using occ by auto
      qed
    qed
  qed
qed


subsection \<open>Flex-rigid problems\<close>

lemma proj_exn:
  assumes "proj t env binders is = Some r" "wf_env ar env" "binders_ok ar binders" "env_typed V env"
    "fresh_env env" "proper t" "typs_ok ar t" "has_type V (map snd binders) t T" "below (maxidx env) t"
    "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders"
  shows "fails_ok (Some r) \<and> (ppat t \<and> env_ppat env \<longrightarrow> r \<noteq> Err Pattern) \<and>
    (\<forall>u env'. r = Ok (u, env') \<longrightarrow> (\<exists>V'. ty_ext ar V env V' env' \<and> below (maxidx env') u \<and>
      has_type V' (rev (map (\<lambda>i. map snd binders ! nat_of_integer i) is)) u T) \<and> new_ok env env' t \<and>
      (ppat t \<longrightarrow> env_ppat env \<longrightarrow> env_ppat env'))"
proof (cases "downto0 is (ilength binders - 1)")
  case True
  then have r: "r = Ok (t, env)" using assms(1) by (simp add: proj_def return_def)
  from downto0_nats[OF True] have "nats is = downs (length binders)" by simp
  then have "map (\<lambda>i. map snd binders ! nat_of_integer i) is = map ((!) (map snd binders)) (downs (length binders))"
    by (metis (no_types, lifting) list.map_comp comp_apply map_eq_conv)
  then have "rev (map (\<lambda>i. map snd binders ! nat_of_integer i) is) = map snd binders"
    using map_nth_downs[of "map snd binders"] by simp
  with r assms(2,4,5,8,9) show ?thesis by (auto intro: ty_ext_refl new_ok_refl)
next
  case False
  with assms(1) have "pr is t env 0 binders = Some r" by (simp add: proj_def)
  from pr_exn[OF this assms(2-9) _ _ _] assms(10) show ?thesis by (simp add: pctx_def)
qed

lemma flexrigid_exn:
  assumes frg: "flexrigid env binders F Fty is t = Some r"
    and wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env" and Fm: "snd F \<le> maxidx env" and gF: "ground ar Fty"
    and tys: "has_type V (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type V (map snd binders) t T" and pt: "proper t" "typs_ok ar t"
    and bt: "below (maxidx env) t" and Fu: "vt_lookup (tenv env) F = None"
  shows "fails_ok (Some r) \<and> (ppat t \<and> env_ppat env \<longrightarrow> r \<noteq> Err Pattern) \<and>
    (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>V'. ty_ext ar V env V' env') \<and> (ppat t \<longrightarrow> env_ppat env \<longrightarrow> env_ppat env'))"
proof -
  let ?Bs = "map snd binders"
  note ti = has_type_app_Var[OF tys]
  have isb: "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders" using ti(1) by simp
  have isb0: "\<forall>i\<in>set is. 0 \<le> i" using isb by simp
  have nlb: "no_loose_bound (tr t) (length binders)" using has_type_closed[OF tyt] by simp
  let ?P = "proj t env binders is \<bind> (\<lambda>(u, env'). mkabs binders is u \<bind> (\<lambda>u'. update (F, Fty) u' env'))"
  let ?H = "\<lambda>e. case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env binders F is t)) | _ \<Rightarrow> raise e"
  let ?O = "rigid_occurs F t env \<bind> (\<lambda>b'. if b' then raise (Unif (Ocheck_Fail F t binders env))
    else raise Pattern)"
  have "occurs F t env \<bind> (\<lambda>b. if b then ?O else handle ?P ?H) = Some r"
    using frg by (simp add: flexrigid_def)
  then show ?thesis
  proof (rule bindM_SomeE)
    fix e assume a: "occurs F t env = Some (Err e)"
    from occurs_no_exn[OF a wf ety tyt] show ?thesis by simp
  next
    fix b assume oc: "occurs F t env = Some (Ok b)" and rest: "(if b then ?O else handle ?P ?H) = Some r"
    show ?thesis
    proof (cases b)
      case True
      with rest have "?O = Some r" by simp
      then show ?thesis
      proof (rule bindM_SomeE)
        fix e assume a: "rigid_occurs F t env = Some (Err e)"
        from rigid_occurs_no_exn[OF a wf ety tyt] show ?thesis by simp
      next
        fix b' assume ro: "rigid_occurs F t env = Some (Ok b')"
          and r: "(if b' then raise (Unif (Ocheck_Fail F t binders env)) else raise Pattern) = Some r"
        have "b'" if "ppat t \<and> env_ppat env"
        proof -
          have "occurs F t env = Some (Ok True)" using oc True by simp
          from occurs_True_occt[OF this refl wf_envD(1)[OF wf]] have "occt env F t" .
          with rigid_occurs_ppat[OF ro wf ety tyt] that show ?thesis by auto
        qed
        with r show ?thesis by (cases b') (auto simp: raise_def)
      qed
    next
      case False
      with rest have rP: "handle ?P ?H = Some r" by simp
      have "occurs F t env = Some (Ok False)" using oc False by simp
      from occurs_False_occt[OF this refl wf_envD(1)[OF wf]] have noF: "\<not> occt env F t" .
      obtain rp where rp: "proj t env binders is = Some rp"
        using rP by (cases "proj t env binders is") (simp_all add: handle_def bindM_def)
      note pe = proj_exn[OF rp wf bok ety fr pt tyt bt isb]
      show ?thesis
      proof (cases rp)
        case (Err e)
        with rP rp have "r = (case e of Unif _ \<Rightarrow> Err (Unif (Proj_Fail env binders F is t)) | _ \<Rightarrow> Err e)"
          by (cases e) (simp_all add: handle_def bindM_def raise_def)
        with pe Err show ?thesis by (cases e) (simp_all add: exn_ok_def)
      next
        case (Ok ue)
        obtain u env1 where ue: "ue = (u, env1)" by force
        from pe Ok ue obtain V1 where e1: "ty_ext ar V env V1 env1" and bu: "below (maxidx env1) u"
          and tyu: "has_type V1 (rev (map (\<lambda>i. ?Bs ! nat_of_integer i) is)) u T"
          and nw: "new_ok env env1 t" and ep: "ppat t \<longrightarrow> env_ppat env \<longrightarrow> env_ppat env1"
          by auto
        note e1' = e1[unfolded ty_ext_def]
        from mkabs_ok[OF isb, of u] obtain u' where u'E: "mkabs binders is u = return u'" by blast
        have u': "ok (mkabs binders is u) u'" using u'E by (simp add: return_def)
        have F1: "vt_lookup (tenv env1) F = None"
        proof (rule ccontr)
          assume "vt_lookup (tenv env1) F \<noteq> None"
          then obtain U w where "vt_lookup (tenv env1) F = Some (U, w)" by force
          from new_okD(3)[OF nw this Fu] noF Fm show False by simp
        qed
        from update_unbound[OF F1, of Fty u'] obtain env' where uE: "update (F, Fty) u' env1 = return env'"
          by blast
        have upd: "ok (update (F, Fty) u' env1) env'" using uE by (simp add: return_def)
        have rr: "r = Ok env'"
          using rP rp Ok ue u'E uE by (simp add: handle_def bindM_def return_def)
        define Us where "Us = map (\<lambda>i. ?Bs ! nat_of_integer i) is"
        have Fty: "Fty = foldr fun_type Us T" using ti(3) by (simp add: Us_def)
        have VF: "V1 F = Fty" using agreeV_D[OF conjunct1[OF e1'] Fm] ti(2) by simp
        have Us_alt: "Us = map (\<lambda>i. snd (binders ! nat_of_integer i)) is"
          unfolding Us_def by (rule map_cong[OF refl]) (use isb in auto)
        have tyu': "has_type V1 [] u' Fty"
          using has_type_mkabs0[OF u' isb tyu[folded Us_def, unfolded Us_alt]] by (simp add: Fty Us_alt)
        have bu': "below (maxidx env1) u'" using vars_mkabs[OF u'] bu by (simp add: below_def)
        have Fm1: "snd F \<le> maxidx env1" using Fm e1' by simp
        note up = typed_update[OF _ _ upd VF tyu' Fm1 bu'] e1'
        have frg': "flexrigid env binders F Fty is t = Some (Ok env')" using frg rr by simp
        have wf': "wf_env ar env'" by (rule flexrigid_sound(2)[OF frg' wf bok gF pt isb0 nlb])
        have "ty_ext ar V env V1 env'"
          using up wf' ok_update_extends[OF upd] e1' by (auto simp: ty_ext_def intro: extends_trans)
        moreover have "env_ppat env'" if "ppat t" "env_ppat env"
          by (rule flexrigid_ppat[OF frg' wf bok that(2) that(1) pt(2) isb0])
        ultimately show ?thesis using rr by auto
      qed
    qed
  qed
qed


subsection \<open>Flex-flex problems\<close>

text \<open>On well-typed inputs whose heads are unbound, flex-flex problems always succeed.\<close>

lemma mk_ff_list_aux_ok: "length is = length js \<Longrightarrow> \<exists>ks. mk_ff_list_aux is js k = return ks"
  by (induction "is" js k rule: mk_ff_list_aux.induct) (auto simp: return_def bindM_def)

lemma flexflex1_exn:
  assumes ff: "flexflex1 env binders F Fty is js = Some r"
    and wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env" and Fm: "snd F \<le> maxidx env" and gF: "ground ar Fty"
    and Fu: "vt_lookup (tenv env) F = None"
    and tys: "has_type V (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type V (map snd binders) (app (pterm.Var F Fty) js) T"
  shows "\<exists>env' V'. r = Ok env' \<and> ty_ext ar V env V' env' \<and> (env_ppat env \<longrightarrow> env_ppat env')"
proof (cases "is = js")
  case True
  with ff have "r = Ok env" by (simp add: flexflex1_def return_def)
  with wf ety fr show ?thesis by (blast intro: ty_ext_refl)
next
  case False
  let ?Bs = "map snd binders"
  note ti = has_type_app_Var[OF tys] and tj = has_type_app_Var[OF tyt]
  define Us where "Us = map (\<lambda>i. snd (binders ! nat_of_integer i)) is"
  have Us_eq: "map (\<lambda>i. ?Bs ! nat_of_integer i) is = Us" using ti(1) by (auto simp: Us_def)
  have Fty: "Fty = foldr fun_type Us T" using ti(3) by (simp add: Us_eq)
  have "map (\<lambda>i. ?Bs ! nat_of_integer i) js = Us"
    using foldr_fun_type_inj ti(3) tj(3) Us_eq by metis
  then have len: "length is = length js" by (metis length_map Us_def)
  have lenUs: "length Us = length is" by (simp add: Us_def)
  from mk_ff_list_aux_ok[OF len, of "ilength is - 1"] obtain ks where
    ksE: "mk_ff_list is js = return ks" by (auto simp: mk_ff_list_def)
  have ks: "ok (mk_ff_list is js) ks" using ksE by (simp add: return_def)
  have ksr: "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length Us" using mk_ff_list_ren(2)[OF ks] lenUs by auto
  define Gty where "Gty = foldr fun_type (map (\<lambda>k. rev Us ! nat_of_integer k) ks) T"
  have GtyE: "type_of_G env Fty (ilength is) ks = return Gty"
    using type_of_G_ok[OF wf_envD(1)[OF wf] ksr, of T] by (simp add: Fty Gty_def ilength_eq lenUs)
  obtain env1 G where G: "genvar (fst F) env Gty = (env1, G)" by force
  note nv = typed_new_var[OF fr ety G]
  let ?G = "(fst F, maxidx env + 1)"
  define V' where "V' = V(?G := Gty)"
  have isb: "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders" using ti(1) by simp
  from mkabs_ok[OF isb, of "app G ks"] obtain t where tE: "mkabs binders is (app G ks) = return t"
    by blast
  have t: "ok (mkabs binders is (app G ks)) t" using tE by (simp add: return_def)
  have F1: "vt_lookup (tenv env1) F = None" using Fu nv(7) by simp
  from update_unbound[OF F1, of Fty t] obtain env' where uE: "update (F, Fty) t env1 = return env'"
    by blast
  have upd: "ok (update (F, Fty) t env1) env'" using uE by (simp add: return_def)
  have r: "r = Ok env'"
    using ff False ksE GtyE G tE uE
    by (simp add: flexflex1_def mk_new_hnf_def mk_hnf_def return_def bindM_def)
  have F_ne: "F \<noteq> ?G" using Fm by (cases F) auto
  have tyt': "has_type V' [] t Fty"
  proof -
    have "has_type V' (rev Us) (app G ks) T"
      unfolding has_type_app using ksr nv(5,6)[folded V'_def] lenUs
      by (auto intro: has_type.Var simp: Gty_def)
    from has_type_mkabs0[OF t isb this[unfolded Us_def]] show ?thesis by (simp add: Fty Us_def)
  qed
  have VF: "V' F = Fty" using ti(2) F_ne by (simp add: V'_def)
  have Fm1: "snd F \<le> maxidx env1" using Fm nv(4) by simp
  have bt: "below (maxidx env1) t" using vars_mkabs[OF t] by (simp add: below_def vars_app nv(4,5))
  note up = typed_update[OF nv(3) nv(2)[folded V'_def] upd VF tyt' Fm1 bt]
  have ffo: "flexflex1 env binders F Fty is js = Some (Ok env')" using ff r by simp
  have "ty_ext ar V env V' env'"
    unfolding ty_ext_def using nv(1,4)[folded V'_def] up flexflex1_sound(1,2)[OF ffo wf gF bok] by simp
  with r flexflex1_ppat[OF ffo] show ?thesis by blast
qed

lemma mapM_idx_ok: "set ks \<subseteq> set xs \<Longrightarrow> \<exists>ks'. mapM (idx xs) ks = return ks'"
proof -
  assume sub: "set ks \<subseteq> set xs"
  have "\<exists>y. idx xs k = return y" if "k \<in> set ks" for k
  proof -
    from that sub obtain n where "Unification.idx xs k = Some n" using idx_None_iff[of xs k] by auto
    then show ?thesis by (auto dest: idx_eq_return)
  qed
  from mapM_return[of ks "idx xs", OF this] show ?thesis by blast
qed

lemma ff_exn:
  assumes ff: "ff env binders F Fty is G Gty js = Some r"
    and wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env" and Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env" and FG: "F \<noteq> G"
    and gF: "ground ar Fty" and gG: "ground ar Gty"
    and Fu: "vt_lookup (tenv env) F = None" and Gu: "vt_lookup (tenv env) G = None"
    and tys: "has_type V (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type V (map snd binders) (app (pterm.Var G Gty) js) T"
    and dist: "distinct is" "distinct js"
  shows "\<exists>env' V'. r = Ok env' \<and> ty_ext ar V env V' env' \<and> (env_ppat env \<longrightarrow> env_ppat env')"
proof -
  let ?Bs = "map snd binders"
  note ti = has_type_app_Var[OF tys] and tj = has_type_app_Var[OF tyt]
  define UsF where "UsF = map (\<lambda>i. snd (binders ! nat_of_integer i)) is"
  define UsG where "UsG = map (\<lambda>i. snd (binders ! nat_of_integer i)) js"
  have Fty: "Fty = foldr fun_type UsF T"
    using ti(1,3) by (auto simp: UsF_def intro!: arg_cong2[of _ _ _ _ "foldr fun_type"])
  have Gty: "Gty = foldr fun_type UsG T"
    using tj(1,3) by (auto simp: UsG_def intro!: arg_cong2[of _ _ _ _ "foldr fun_type"])
  have nonneg: "\<forall>i\<in>set is. 0 \<le> i" "\<forall>j\<in>set js. 0 \<le> j" using ti(1) tj(1) by auto
  have isb: "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders" using ti(1) by simp
  have jsb: "\<forall>j\<in>set js. 0 \<le> j \<and> nat_of_integer j < length binders" using tj(1) by simp
  have lenUsF: "length UsF = length is" by (simp add: UsF_def)
  have "\<exists>env'. r = Ok env' \<and> (\<exists>V'. ty_ext ar V env V' env')"
  proof (cases "subset js is")
    case True
    then have sub: "set js \<subseteq> set is" by (auto simp: subset_def list_all_iff)
    from mapM_idx_ok[OF sub] obtain ks where ksE: "mapM (idx is) js = return ks" by blast
    have ks: "ok (mapM (idx is) js) ks" using ksE by (simp add: return_def)
    note kb = ok_mapM_idx[OF ks nonneg]
    from mkabs_ok[OF isb, of "app (pterm.Var G Gty) ks"] obtain t where
      tE: "mkabs binders is (app (pterm.Var G Gty) ks) = return t" by blast
    have t: "ok (mkabs binders is (app (pterm.Var G Gty) ks)) t" using tE by (simp add: return_def)
    from update_unbound[OF Fu, of Fty t] obtain env' where uE: "update (F, Fty) t env = return env'"
      by blast
    have upd: "ok (update (F, Fty) t env) env'" using uE by (simp add: return_def)
    have r: "r = Ok env'" using ff True ksE tE uE by (simp add: ff_def return_def bindM_def)
    have tyt': "has_type V [] t Fty"
    proof -
      have "has_type V (rev UsF) (app (pterm.Var G Gty) ks) T"
        unfolding has_type_app using kb(1) tj(2) typ_idx[where binders=binders, OF ks sub]
        by (auto simp: UsF_def Gty UsG_def intro: has_type.Var)
      from has_type_mkabs0[OF t isb this[unfolded UsF_def]] show ?thesis by (simp add: Fty UsF_def)
    qed
    have bt: "below (maxidx env) t" using vars_mkabs[OF t] Gm by (simp add: below_def vars_app)
    note up = typed_update[OF fr ety upd ti(2) tyt' Fm bt]
    have ffo: "ff env binders F Fty is G Gty js = Some (Ok env')" using ff r by simp
    have "ty_ext ar V env V env'"
      unfolding ty_ext_def using up ff_sound(1,2)[OF ffo wf gF gG bok nonneg] by (simp add: agreeV_def)
    with r show ?thesis by blast
  next
    case False
    let ?ks = "inter js is"
    have ks_sub: "set ?ks \<subseteq> set is" "set ?ks \<subseteq> set js" by (auto simp: inter_def)
    have ks_nonneg: "\<forall>k\<in>set ?ks. 0 \<le> k" using nonneg(1) ks_sub(1) by auto
    from mapM_idx_ok[OF ks_sub(1)] obtain ksF where ksFE: "mapM (idx is) ?ks = return ksF" by blast
    from mapM_idx_ok[OF ks_sub(2)] obtain ksG where ksGE: "mapM (idx js) ?ks = return ksG" by blast
    have ksF: "ok (mapM (idx is) ?ks) ksF" and ksG: "ok (mapM (idx js) ?ks) ksG"
      using ksFE ksGE by (simp_all add: return_def)
    note kbF = ok_mapM_idx[OF ksF nonneg(1) ks_nonneg] and kbG = ok_mapM_idx[OF ksG nonneg(2) ks_nonneg]
    define Hty where "Hty = foldr fun_type (map (\<lambda>k. rev UsF ! nat_of_integer k) ksF) T"
    have HtyE: "type_of_G env Fty (ilength is) ksF = return Hty"
      using type_of_G_ok[OF wf_envD(1)[OF wf], of ksF UsF T] kbF(1) lenUsF
      by (simp add: Fty Hty_def ilength_eq)
    obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
    note nv = typed_new_var[OF fr ety H]
    let ?H = "(fst G, maxidx env + 1)"
    define V' where "V' = V(?H := Hty)"
    from mkabs_ok[OF jsb, of "app H ksG"] obtain tG where tGE: "mkabs binders js (app H ksG) = return tG"
      by blast
    from mkabs_ok[OF isb, of "app H ksF"] obtain tF where tFE: "mkabs binders is (app H ksF) = return tF"
      by blast
    have tG: "ok (mkabs binders js (app H ksG)) tG" and tF: "ok (mkabs binders is (app H ksF)) tF"
      using tGE tFE by (simp_all add: return_def)
    have F1: "vt_lookup (tenv env1) F = None" using Fu nv(7) by simp
    from update_unbound[OF F1, of Fty tF] obtain env2 where u2E: "update (F, Fty) tF env1 = return env2"
      by blast
    have env2: "ok (update (F, Fty) tF env1) env2" using u2E by (simp add: return_def)
    have G2: "vt_lookup (tenv env2) G = None" using ok_update(2)[OF env2] Gu nv(7) FG by simp
    from update_unbound[OF G2, of Gty tG] obtain env' where uE: "update (G, Gty) tG env2 = return env'"
      by blast
    have env': "ok (update (G, Gty) tG env2) env'" using uE by (simp add: return_def)
    have r: "r = Ok env'"
      using ff False ksFE HtyE H ksGE tGE tFE u2E uE by (simp add: ff_def Let_def return_def bindM_def)
    have F_ne: "F \<noteq> ?H" using Fm by (cases F) auto
    have G_ne: "G \<noteq> ?H" using Gm by (cases G) auto
    have tyF': "has_type V' [] tF Fty"
    proof -
      have "has_type V' (rev UsF) (app H ksF) T"
        unfolding has_type_app using kbF(1) nv(5,6)[folded V'_def] lenUsF
        by (auto intro: has_type.Var simp: Hty_def)
      from has_type_mkabs0[OF tF isb this[unfolded UsF_def]] show ?thesis by (simp add: Fty UsF_def)
    qed
    have tyG': "has_type V' [] tG Gty"
    proof -
      have "map (\<lambda>k. rev UsG ! nat_of_integer k) ksG = map (\<lambda>k. rev UsF ! nat_of_integer k) ksF"
        using typ_idx[where binders=binders, OF ksG ks_sub(2)] typ_idx[where binders=binders, OF ksF ks_sub(1)]
        by (simp add: UsF_def UsG_def)
      then have "has_type V' (rev UsG) (app H ksG) T"
        unfolding has_type_app using kbG(1) nv(5,6)[folded V'_def]
        by (auto intro: has_type.Var simp: UsG_def Hty_def)
      from has_type_mkabs0[OF tG jsb this[unfolded UsG_def]] show ?thesis by (simp add: Gty UsG_def)
    qed
    have VF: "V' F = Fty" using ti(2) F_ne by (simp add: V'_def)
    have VG: "V' G = Gty" using tj(2) G_ne by (simp add: V'_def)
    have Fm1: "snd F \<le> maxidx env1" using Fm nv(4) by simp
    have btF: "below (maxidx env1) tF" using vars_mkabs[OF tF] by (simp add: below_def vars_app nv(4,5))
    note up1 = typed_update[OF nv(3) nv(2)[folded V'_def] env2 VF tyF' Fm1 btF]
    have Gm2: "snd G \<le> maxidx env2" using Gm nv(4) up1(3) by simp
    have btG: "below (maxidx env2) tG"
      using vars_mkabs[OF tG] up1(3) by (simp add: below_def vars_app nv(4,5))
    note up2 = typed_update[OF up1(2) up1(1) env' VG tyG' Gm2 btG]
    have ffo: "ff env binders F Fty is G Gty js = Some (Ok env')" using ff r by simp
    have "ty_ext ar V env V' env'"
      unfolding ty_ext_def using nv(1,4)[folded V'_def] up1(3) up2 ff_sound(1,2)[OF ffo wf gF gG bok nonneg]
      by simp
    with r show ?thesis by blast
  qed
  with ff_ppat[OF _ _ dist nonneg] ff show ?thesis by blast
qed

lemma flexflex2_exn:
  assumes "flexflex2 env binders F Fty is G Gty js = Some r"
    and "wf_env ar env" "binders_ok ar binders" "env_typed V env" "fresh_env env"
    "snd F \<le> maxidx env" "snd G \<le> maxidx env" "F \<noteq> G" "ground ar Fty" "ground ar Gty"
    "vt_lookup (tenv env) F = None" "vt_lookup (tenv env) G = None"
    "has_type V (map snd binders) (app (pterm.Var F Fty) is) T"
    "has_type V (map snd binders) (app (pterm.Var G Gty) js) T"
    "distinct is" "distinct js"
  shows "\<exists>env' V'. r = Ok env' \<and> ty_ext ar V env V' env' \<and> (env_ppat env \<longrightarrow> env_ppat env')"
  using assms ff_exn[of env binders F Fty "is" G Gty js r ar V T]
    ff_exn[of env binders G Gty js F Fty "is" r ar V T]
  by (auto simp: flexflex2_def split: if_splits)


subsection \<open>Unification\<close>

lemma foldM_exn:
  assumes "foldM f xs e = Some r" "P g e"
    and "\<And>x g e r. x \<in> set xs \<Longrightarrow> P g e \<Longrightarrow> f x e = Some r \<Longrightarrow>
      fails_ok (Some r) \<and> (N \<longrightarrow> r \<noteq> Err Pattern) \<and> (\<forall>e1. r = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
  shows "fails_ok (Some r) \<and> (N \<longrightarrow> r \<noteq> Err Pattern) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
  using assms
proof (induction xs arbitrary: g e r)
  case Nil
  then show ?case by (auto simp: return_def)
next
  case (Cons x xs)
  have step: "fails_ok (Some r) \<and> (N \<longrightarrow> r \<noteq> Err Pattern) \<and> (\<forall>e1. r = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
    if "x' \<in> set xs" "P g e" "f x' e = Some r" for x' g e r
    using Cons.prems(3)[OF _ that(2,3)] that(1) by simp
  from Cons.prems(1) have "f x e \<bind> (\<lambda>b'. foldM f xs b') = Some r" by simp
  then show ?case
  proof (rule bindM_SomeE)
    fix ex assume "f x e = Some (Err ex)" "r = Err ex"
    with Cons.prems(3)[of x g e "Err ex"] Cons.prems(2) show ?thesis by simp
  next
    fix e1 assume fx: "f x e = Some (Ok e1)" and rest: "foldM f xs e1 = Some r"
    from Cons.prems(3)[of x g e, OF _ Cons.prems(2) fx] obtain g1 where "P g1 e1" by auto
    show ?thesis by (rule Cons.IH[OF rest \<open>P g1 e1\<close>], rule step, assumption+)
  qed
qed

lemma has_type_list_comb_args: "has_type V Ts (list_comb h ts) T \<Longrightarrow> \<forall>t\<in>set ts. \<exists>U. has_type V Ts t U"
  by (auto simp: has_type_list_comb list_all2_conv_all_nth in_set_conv_nth) blast

text \<open>
  On well-typed terms, \<^const>\<open>unif\<close> raises only \<open>Unif\<close> or \<open>Pattern\<close>, never \<open>Pattern\<close> on patterns,
  and preserves typing, freshness and well-formedness of the environment.
\<close>

theorem unif_exn:
  assumes "unif alg binders s t env = Some r"
  shows "wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow> env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow>
    wf_term ar (length binders) s \<Longrightarrow> wf_term ar (length binders) t \<Longrightarrow>
    has_type V (map snd binders) s T \<Longrightarrow> has_type V (map snd binders) t T \<Longrightarrow>
    below (maxidx env) s \<Longrightarrow> below (maxidx env) t \<Longrightarrow>
    fails_ok (Some r) \<and> (ppat s \<and> ppat t \<and> env_ppat env \<longrightarrow> r \<noteq> Err Pattern) \<and>
    (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>V'. ty_ext ar V env V' env') \<and>
      (ppat s \<and> ppat t \<and> env_ppat env \<longrightarrow> env_ppat env'))"
  using assms
proof (induction alg binders s t env r arbitrary: V T rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg binders s t env r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env"
    and ws: "wf_term ar (length binders) s" and wt: "wf_term ar (length binders) t"
    and tys: "has_type V (map snd binders) s T" and tyt: "has_type V (map snd binders) t T"
    and bs: "below (maxidx env) s" and bt: "below (maxidx env) t"
    using "1.prems" by simp_all
  let ?Bs = "map snd binders" and ?n = "length binders" and ?N = "ppat s \<and> ppat t \<and> env_ppat env"
  have vt: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wf])
  define R where "R = (\<lambda>s0 t0. if is_Abs s0 \<and> is_Abs t0 then
        (case (s0, t0) of
          (pterm.Abs ns Ts ts, pterm.Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            uni alg ((name, Ts) # binders) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s0 then
        (case s0 of
          pterm.Abs ns Ts ts \<Rightarrow> uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t0 then
        (case t0 of
          pterm.Abs nt Tt tt \<Rightarrow> uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s0; (ht, ts) = strip_comb t0 in
          if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (pterm.Var F Fty, pterm.Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env binders F Fty is js
                else flexflex2 env binders F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env binders F Fty is t0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env binders F Fty is s0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB binders i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env}
            | _ \<Rightarrow> rigid_clash binders hs ht)))"
  from "1.hyps" have "head_norm env s \<bind> (\<lambda>s0. head_norm env t \<bind> (\<lambda>t0. R s0 t0)) = Some r"
    unfolding R_def by (simp only:)
  then show ?case
  proof (rule bindM_SomeE)
    fix e assume "head_norm env s = Some (Err e)"
    with head_norm_no_exn[OF wf ety tys] show ?thesis by (simp add: no_exn_def)
  next
    fix s0 assume hs: "head_norm env s = Some (Ok s0)"
      and rest1: "head_norm env t \<bind> (\<lambda>t0. R s0 t0) = Some r"
    from rest1 show ?thesis
    proof (rule bindM_SomeE)
      fix e assume "head_norm env t = Some (Err e)"
      with head_norm_no_exn[OF wf ety tyt] show ?thesis by (simp add: no_exn_def)
    next
      fix t0 assume ht: "head_norm env t = Some (Ok t0)" and rest0: "R s0 t0 = Some r"
      note rest = rest0[unfolded R_def]
      from head_norm_sound[OF hs refl wf] ws have ws0: "wf_term ar ?n s0" by (auto simp: wf_term_def)
      from head_norm_sound[OF ht refl wf] wt have wt0: "wf_term ar ?n t0" by (auto simp: wf_term_def)
      have tys0: "has_type V ?Bs s0 T" by (rule head_norm_typed[OF hs refl wf ety tys])
      have tyt0: "has_type V ?Bs t0 T" by (rule head_norm_typed[OF ht refl wf ety tyt])
      have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF hs refl wf fr bs])
      have bt0: "below (maxidx env) t0" by (rule below_head_norm[OF ht refl wf fr bt])
      have ps0: "ppat s0" if ?N using head_norm_ppat[OF hs wf] that by blast
      have pt0: "ppat t0" if ?N using head_norm_ppat[OF ht wf] that by blast
      note IH = "1.IH"
      show ?thesis
      proof (cases "is_Abs s0")
        case sA: True
        then obtain ns Ts ts where s0a: "s0 = pterm.Abs ns Ts ts" by (cases s0) auto
        have gTs: "ground ar Ts" using ws0 s0a by (simp add: wf_term_def)
        from tys0 s0a obtain W where T: "T = Ts \<rightarrow>\<^sub>T W" and tyts: "has_type V (Ts # ?Bs) ts W"
          by (auto elim: has_type_elims)
        have bts: "below (maxidx env) ts" using bs0 s0a by simp
        have wts: "wf_term ar (Suc ?n) ts" using ws0 s0a by (simp add: wf_term_def)
        have pts: "ppat ts" if ?N using ps0[OF that] s0a by (auto dest: ppat_AbsD)
        show ?thesis
        proof (cases "is_Abs t0")
          case True
          then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
          from tyt0 t0a T have Tt: "Tt = Ts" and tytt: "has_type V (Ts # ?Bs) tt W"
            by (auto elim: has_type_elims)
          define nm where "nm = (if ns = STR '''' then nt else ns)"
          from rest sA True s0a t0a have u: "uni alg ((nm, Ts) # binders) ts tt env = Some r"
            by (simp add: Let_def nm_def unify_types_ground[OF gTs gTs] Tt)
          have bok': "binders_ok ar ((nm, Ts) # binders)" using bok gTs by (simp add: binders_ok_def)
          have btt: "below (maxidx env) tt" using bt0 t0a by simp
          have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
          have ptt: "ppat tt" if ?N using pt0[OF that] t0a by (auto dest: ppat_AbsD)
          note IHu = IH[OF u wf bok' ety fr _ _ _ _ bts btt]
          show ?thesis using IHu wts wtt tyts tytt pts ptt by simp
        next
          case False
          from rest sA False s0a have u: "uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env = Some r"
            by simp
          have bok': "binders_ok ar ((ns, Ts) # binders)" using bok gTs by (simp add: binders_ok_def)
          have wi: "wf_term ar (Suc ?n) (incr t0 $ Bound 0)"
            using wt0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
              intro: no_loose_bound_lift)
          have tyi: "has_type V (Ts # ?Bs) (incr t0 $ Bound 0) W"
            using has_type_incr[OF tyt0, of Ts] T by (intro has_type.App[of _ _ _ Ts]) (auto simp: has_type_Bound_iff)
          have bi: "below (maxidx env) (incr t0 $ Bound 0)" using bt0 by (simp add: below_def vars_incr)
          have pi: "ppat (incr t0 $ Bound 0)" if ?N by (rule ppat_incr_Bound0[OF pt0[OF that] False])
          note IHu = IH[OF u wf bok' ety fr _ _ _ _ bts bi]
          show ?thesis using IHu wts wi tyts tyi pts pi by simp
        qed
      next
        case nsA: False
        show ?thesis
        proof (cases "is_Abs t0")
          case True
          then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
          have gTt: "ground ar Tt" using wt0 t0a by (simp add: wf_term_def)
          from tyt0 t0a obtain W where T: "T = Tt \<rightarrow>\<^sub>T W" and tytt: "has_type V (Tt # ?Bs) tt W"
            by (auto elim: has_type_elims)
          from rest nsA True t0a have u: "uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env = Some r"
            by simp
          have bok': "binders_ok ar ((nt, Tt) # binders)" using bok gTt by (simp add: binders_ok_def)
          have btt: "below (maxidx env) tt" using bt0 t0a by simp
          have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
          have wi: "wf_term ar (Suc ?n) (incr s0 $ Bound 0)"
            using ws0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
              intro: no_loose_bound_lift)
          have tyi: "has_type V (Tt # ?Bs) (incr s0 $ Bound 0) W"
            using has_type_incr[OF tys0, of Tt] T by (intro has_type.App[of _ _ _ Tt]) (auto simp: has_type_Bound_iff)
          have bi: "below (maxidx env) (incr s0 $ Bound 0)" using bs0 by (simp add: below_def vars_incr)
          have ptt: "ppat tt" if ?N using pt0[OF that] t0a by (auto dest: ppat_AbsD)
          have pi: "ppat (incr s0 $ Bound 0)" if ?N by (rule ppat_incr_Bound0[OF ps0[OF that] nsA])
          note IHu = IH[OF u wf bok' ety fr _ _ _ _ bi btt]
          show ?thesis using IHu wi wtt tyi tytt pi ptt by simp
        next
          case nAt: False
          obtain hs ss where shs: "strip_comb s0 = (hs, ss)" by force
          obtain ht ts where sht: "strip_comb t0 = (ht, ts)" by force
          note s0e = strip_comb_list_comb[OF shs] and t0e = strip_comb_list_comb[OF sht]
          have wss: "wf_term ar ?n hs" "\<forall>t\<in>set ss. wf_term ar ?n t"
            using ws0 s0e by (simp_all add: wf_term_list_comb)
          have wts: "wf_term ar ?n ht" "\<forall>t\<in>set ts. wf_term ar ?n t"
            using wt0 t0e by (simp_all add: wf_term_list_comb)
          have pss: "\<forall>t\<in>set ss. proper t \<and> typs_ok ar t" and pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
            using wss(2) wts(2) by (auto simp: wf_term_def)
          have wt0': "proper t0" "typs_ok ar t0" and ws0': "proper s0" "typs_ok ar s0"
            using wt0 ws0 by (simp_all add: wf_term_def)
          have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
            using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
          have nAh: "\<not> is_Abs hs" "\<not> is_Abs ht"
            using head_norm_head[OF hs refl nsA] head_norm_head[OF ht refl nAt] shs sht by simp_all
          have rigI: "is_rigid h" if "\<not> is_Var h" "\<not> is_Abs h" "\<not> (\<exists>f u. h = f $ u)" "wf_term ar ?n h" for h
            using that by (cases h) (auto simp: is_rigid_def wf_term_def)
          have tss: "\<forall>u\<in>set ss. \<exists>U. has_type V ?Bs u U"
            using tys0[unfolded s0e] by (rule has_type_list_comb_args)
          have tts: "\<forall>u\<in>set ts. \<exists>U. has_type V ?Bs u U"
            using tyt0[unfolded t0e] by (rule has_type_list_comb_args)
          have unbF: "vt_lookup (tenv env) F = None" if "hs = pterm.Var F U" for F U
            using head_norm_head_unbound[OF hs refl vt] shs that by simp
          have unbG: "vt_lookup (tenv env) F = None" if "ht = pterm.Var F U" for F U
            using head_norm_head_unbound[OF ht refl vt] sht that by simp
          have ints_s: "e = Pattern \<and> \<not> ?N" if "ints_of' env ss = Some (Err e)" "hs = pterm.Var F U" for e F U
          proof
            from ints_of'_res[OF that(1) wf ety tss] show "e = Pattern" by simp
            show "\<not> ?N"
            proof
              assume N: ?N
              from ppat_strip_flex[OF shs[unfolded that(2)] ps0[OF N]] obtain iss
                where "ss = map Bound iss" "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i" .
              with that(1) ints_of'_Bounds show False by (simp add: return_def)
            qed
          qed
          have ints_t: "e = Pattern \<and> \<not> ?N" if "ints_of' env ts = Some (Err e)" "ht = pterm.Var F U" for e F U
          proof
            from ints_of'_res[OF that(1) wf ety tts] show "e = Pattern" by simp
            show "\<not> ?N"
            proof
              assume N: ?N
              from ppat_strip_flex[OF sht[unfolded that(2)] pt0[OF N]] obtain iss
                where "ts = map Bound iss" "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i" .
              with that(1) ints_of'_Bounds show False by (simp add: return_def)
            qed
          qed
          consider (VV) F Fty G Gty where "hs = pterm.Var F Fty" "ht = pterm.Var G Gty"
            | (VR) F Fty where "hs = pterm.Var F Fty" "\<not> is_Var ht"
            | (RV) G Gty where "\<not> is_Var hs" "ht = pterm.Var G Gty"
            | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
            by (cases hs; cases ht) auto
          then show ?thesis
          proof cases
            case VV
            from rest nsA nAt shs sht VV have ff0: "ints_of' env ss \<bind> (\<lambda>is. ints_of' env ts \<bind> (\<lambda>js.
                if F = G then flexflex1 env binders F Fty is js else flexflex2 env binders F Fty is G Gty js)) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ss = Some (Err e)" "r = Err e"
              with ints_s[OF _ VV(1)] show ?thesis by simp
            next
              fix "is" assume iss: "ok (ints_of' env ss) is" and ff1: "ints_of' env ts \<bind> (\<lambda>js.
                if F = G then flexflex1 env binders F Fty is js else flexflex2 env binders F Fty is G Gty js) =
                Some r"
              from ff1 show ?thesis
              proof (rule bindM_SomeE)
                fix e assume "ints_of' env ts = Some (Err e)" "r = Err e"
                with ints_t[OF _ VV(2)] show ?thesis by simp
              next
                fix js assume js: "ok (ints_of' env ts) js" and ff: "(if F = G then flexflex1 env binders F Fty is js
                  else flexflex2 env binders F Fty is G Gty js) = Some r"
                note iS = ints_of'_sound[OF iss wf pss] and jS = ints_of'_sound[OF js wf pts]
                have tyF: "has_type V ?Bs (app (pterm.Var F Fty) is) T"
                  using has_type_ints_of'[OF iss wf ety] tys0 s0e VV by simp
                have tyG: "has_type V ?Bs (app (pterm.Var G Gty) js) T"
                  using has_type_ints_of'[OF js wf ety] tyt0 t0e VV by simp
                have gF: "ground ar Fty" and gG: "ground ar Gty"
                  using wss(1) wts(1) VV by (simp_all add: wf_term_def)
                have Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env"
                  using bs0 bt0 s0e t0e VV by (simp_all add: below_list_comb)
                note Fu = unbF[OF VV(1)] and Gu = unbG[OF VV(2)]
                show ?thesis
                proof (cases "F = G")
                  case True
                  with ff have ff': "flexflex1 env binders F Fty is js = Some r" by simp
                  have GF: "Gty = Fty" using has_type_app_Var(2)[OF tyF] has_type_app_Var(2)[OF tyG] True by simp
                  then have tyG': "has_type V ?Bs (app (pterm.Var F Fty) js) T" using tyG True by simp
                  from flexflex1_exn[OF ff' wf bok ety fr Fm gF Fu tyF tyG'] show ?thesis by auto
                next
                  case False
                  with ff have ff': "flexflex2 env binders F Fty is G Gty js = Some r" by simp
                  from flexflex2_exn[OF ff' wf bok ety fr Fm Gm False gF gG Fu Gu tyF tyG iS(1) jS(1)]
                  show ?thesis by auto
                qed
              qed
            qed
          next
            case VR
            from rest nsA nAt shs sht VR have fr0: "ints_of' env ss \<bind> (\<lambda>is. flexrigid env binders F Fty is t0) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ss = Some (Err e)" "r = Err e"
              with ints_s[OF _ VR(1)] show ?thesis by simp
            next
              fix "is" assume iss: "ok (ints_of' env ss) is" and frg: "flexrigid env binders F Fty is t0 = Some r"
              have tyF: "has_type V ?Bs (app (pterm.Var F Fty) is) T"
                using has_type_ints_of'[OF iss wf ety] tys0 s0e VR by simp
              have gF: "ground ar Fty" using wss(1) VR by (simp add: wf_term_def)
              have Fm: "snd F \<le> maxidx env" using bs0 s0e VR by (simp add: below_list_comb)
              note c = flexrigid_exn[OF frg wf bok ety fr Fm gF tyF tyt0 wt0' bt0 unbF[OF VR(1)]]
              show ?thesis using c pt0 by auto
            qed
          next
            case RV
            from rest nsA nAt shs sht RV have fr0: "ints_of' env ts \<bind> (\<lambda>js. flexrigid env binders G Gty js s0) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ts = Some (Err e)" "r = Err e"
              with ints_t[OF _ RV(2)] show ?thesis by simp
            next
              fix js assume js: "ok (ints_of' env ts) js" and frg: "flexrigid env binders G Gty js s0 = Some r"
              have tyG: "has_type V ?Bs (app (pterm.Var G Gty) js) T"
                using has_type_ints_of'[OF js wf ety] tyt0 t0e RV by simp
              have gG: "ground ar Gty" using wts(1) RV by (simp add: wf_term_def)
              have Gm: "snd G \<le> maxidx env" using bt0 t0e RV by (simp add: below_list_comb)
              note c = flexrigid_exn[OF frg wf bok ety fr Gm gG tyG tys0 ws0' bs0 unbG[OF RV(2)]]
              show ?thesis using c ps0 by auto
            qed
          next
            case RR
            have rs: "is_rigid hs" by (rule rigI[OF RR(1) nAh(1) nApp(1) wss(1)])
            have rt: "is_rigid ht" by (rule rigI[OF RR(2) nAh(2) nApp(2) wts(1)])
            have gh: "typs_ok ar hs" "typs_ok ar ht" using wss(1) wts(1) by (simp_all add: wf_term_def)
            show ?thesis
            proof (cases "hs = ht")
              case False
              have "\<exists>u. r = Err (Unif u)"
                using rest nsA nAt shs sht RR rs rt nAh False gh
                by (cases hs; cases ht)
                  (auto simp: is_rigid_def unify_types_ground rigid_clash_def raise_def bindM_def split: if_splits)
              then show ?thesis by auto
            next
              case hsht: True
              from tys0 s0e obtain Us where tyhs: "has_type V ?Bs hs (foldr fun_type Us T)"
                and tyss: "list_all2 (has_type V ?Bs) ss Us"
                by (auto simp: has_type_list_comb)
              from tyt0 t0e obtain Us' where tyht: "has_type V ?Bs ht (foldr fun_type Us' T)"
                and tyts: "list_all2 (has_type V ?Bs) ts Us'"
                by (auto simp: has_type_list_comb)
              have "Us' = Us"
                using has_type_unique[OF tyhs tyht[folded hsht]] by (auto dest: foldr_fun_type_inj)
              note tyts = tyts[unfolded this]
              have len: "length ss = length ts" using list_all2_lengthD[OF tyss] list_all2_lengthD[OF tyts] by simp
              have fo: "foldM (\<lambda>(s, t) env. uni alg binders s t env) (zip ss ts) env = Some r"
              proof -
                from rs consider (C) c U where "hs = Const c U" | (Fr) c U where "hs = Free c U"
                  | (B) i where "hs = Bound i" by (auto simp: is_rigid_def)
                then show ?thesis
                proof cases
                  case C
                  with gh have "ground ar U" by simp
                  with rest nsA nAt shs sht C hsht len show ?thesis
                    by (simp add: unify_types_ground zip_eq_return)
                next
                  case Fr
                  with gh have "ground ar U" by simp
                  with rest nsA nAt shs sht Fr hsht len show ?thesis
                    by (simp add: unify_types_ground zip_eq_return)
                next
                  case B
                  with hsht have hb: "hs = Bound i" "ht = Bound i" by simp_all
                  from rest nsA nAt shs sht len show ?thesis by (simp add: hb zip_eq_return)
                qed
              qed
              have pargs: "(\<forall>u\<in>set ss. ppat u) \<and> (\<forall>u\<in>set ts. ppat u)" if ?N
                using ppat_spine[OF ps0[OF that, unfolded s0e] nApp(1) nsA[unfolded s0e]]
                  ppat_spine[OF pt0[OF that, unfolded t0e] nApp(2) nAt[unfolded t0e]] RR
                by auto
              have bss: "\<forall>t\<in>set ss. below (maxidx env) t" using bs0 s0e by (simp add: below_list_comb)
              have bts: "\<forall>t\<in>set ts. below (maxidx env) t" using bt0 t0e by (simp add: below_list_comb)
              define P where "P = (\<lambda>V1 e. ty_ext ar V env V1 e \<and> (?N \<longrightarrow> env_ppat e))"
              have "fails_ok (Some r) \<and> (?N \<longrightarrow> r \<noteq> Err Pattern) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
              proof (rule foldM_exn[OF fo, of P V])
                show "P V env" using wf ety fr by (simp add: P_def ty_ext_refl)
              next
                fix x V1 e r1
                assume x: "x \<in> set (zip ss ts)" and Pg: "P V1 e"
                  and f: "(\<lambda>(s, t) env. uni alg binders s t env) x e = Some r1"
                from x obtain i where i: "i < length ss" "x = (ss ! i, ts ! i)"
                  using len by (auto simp: in_set_zip)
                have e1: "ty_ext ar V env V1 e" and ep: "?N \<longrightarrow> env_ppat e" using Pg by (simp_all add: P_def)
                have agV: "agreeV (maxidx env) V V1" and ety1: "env_typed V1 e" and fr1: "fresh_env e"
                  and wf1: "wf_env ar e" and mx: "maxidx env \<le> maxidx e"
                  using e1 by (simp_all add: ty_ext_def)
                have ii: "i < length ts" using i(1) len by simp
                have u: "uni alg binders (ss ! i) (ts ! i) e = Some r1" using f i(2) by simp
                have ba: "below (maxidx env) (ss ! i)" and bb: "below (maxidx env) (ts ! i)"
                  using bss bts i(1) ii by simp_all
                have wa: "wf_term ar ?n (ss ! i)" and wb: "wf_term ar ?n (ts ! i)"
                  using wss(2) wts(2) i(1) ii by simp_all
                have tya: "has_type V1 ?Bs (ss ! i) (Us ! i)"
                  using has_type_agreeV[OF _ ba agV] tyss i(1) by (simp add: list_all2_conv_all_nth)
                have tyb: "has_type V1 ?Bs (ts ! i) (Us ! i)"
                  using has_type_agreeV[OF _ bb agV] tyts ii by (simp add: list_all2_conv_all_nth)
                have pa: "ppat (ss ! i) \<and> ppat (ts ! i)" if ?N using pargs[OF that] i(1) ii by simp
                note IHi = IH[OF u wf1 bok ety1 fr1 wa wb tya tyb below_mono[OF ba mx] below_mono[OF bb mx]]
                show "fails_ok (Some r1) \<and> (?N \<longrightarrow> r1 \<noteq> Err Pattern) \<and> (\<forall>e1. r1 = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
                proof (intro conjI allI impI)
                  show "fails_ok (Some r1)" using IHi by simp
                next
                  assume N: ?N
                  show "r1 \<noteq> Err Pattern" using IHi pa[OF N] ep N by simp
                next
                  fix e1 assume r1: "r1 = Ok e1"
                  from IHi r1 obtain V2 where t2: "ty_ext ar V1 e V2 e1"
                    and pp: "ppat (ss ! i) \<and> ppat (ts ! i) \<and> env_ppat e \<longrightarrow> env_ppat e1" by blast
                  show "\<exists>g1. P g1 e1" using ty_ext_trans[OF e1 t2] pp pa ep unfolding P_def by blast
                qed
              qed
              then show ?thesis by (auto simp: P_def)
            qed
          qed
        qed
      qed
    qed
  qed
qed

end
