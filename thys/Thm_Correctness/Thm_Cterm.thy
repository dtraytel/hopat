section \<open>Operations on certified terms\<close>

theory Thm_Cterm
  imports Strip_Shyps_Correct "Pure_Thm.Pure_Cterm"
begin

text \<open>
  The destructors and constructors of certified terms of theory \<^theory_text>\<open>Pure_Cterm\<close> keep
  certified terms well-formed (\<^const>\<open>pure_sig.cterm_wf\<close>): the type computed by
  \<open>Term.argument_type_of\<close> is that of the argument, \<open>Term.lambda_name\<close> abstracts over a closed
  term of the right type, and the results are lifted to the abstract type of certified terms.
\<close>

lemma liftMT_return [simp]: "liftMT (return x) = returnW x"
  by (simp add: liftMT_def)

lemma liftMT_raise [simp]: "liftMT (raise e) = raiseW (UExn (PExn e))"
  by (simp add: liftMT_def liftM_def raise_def raiseW_def liftWT_def)


subsection \<open>Types of terms\<close>

context pure_sig
begin

lemma fastype_typing:
  "e \<turnstile> t : T \<Longrightarrow> (\<forall>j. 0 \<le> j \<longrightarrow> j < k \<longrightarrow> fastype_of_bound Ts j = return (e j)) \<Longrightarrow> \<not> loose_bvar t k \<Longrightarrow>
    fastype_of_term Ts t = return T \<and> (\<forall>A B. T = A \<rightarrow>\<^sub>T B \<longrightarrow> range_type_of Ts t = return B)"
proof (induction arbitrary: Ts k rule: typing.induct)
  case (Bound i e T)
  then have "fastype_of_bound Ts i = return T" by auto
  then show ?case by (simp add: return_def)
next
  case (Abs T e t U a)
  have H: "\<forall>j. 0 \<le> j \<longrightarrow> j < k + 1 \<longrightarrow> fastype_of_bound (T # Ts) j = return ((e\<langle>0:T\<rangle>) j)"
  proof (intro allI impI)
    fix j :: integer assume j: "0 \<le> j" "j < k + 1"
    show "fastype_of_bound (T # Ts) j = return ((e\<langle>0:T\<rangle>) j)"
    proof (cases "j = 0")
      case False
      with j have "0 \<le> j - 1" "j - 1 < k" by (simp_all add: integer_arith)
      with Abs.prems(1) have "fastype_of_bound Ts (j - 1) = return (e (j - 1))" by blast
      with False j show ?thesis by (simp add: shift_def)
    qed (simp add: return_def)
  qed
  from Abs.IH[OF H] Abs.prems(2) show ?case by simp
next
  case (App e s T U t)
  from App.IH(1)[OF App.prems(1)] App.prems(2) have "range_type_of Ts s = return U" by simp
  then show ?case by (simp add: return_def)
qed (simp_all add: return_def)

lemma fastype_closed: "e \<turnstile> t : T \<Longrightarrow> closed t \<Longrightarrow> fastype_of_term [] t = return T"
  using fastype_typing[of e t T 0 "[]"] by (simp add: closed_def)

lemma arg_type_typing:
  "e \<turnstile> t : T \<Longrightarrow> (\<forall>j. 0 \<le> j \<longrightarrow> j < k \<longrightarrow> fastype_of_bound Ts j = return (e j)) \<Longrightarrow> \<not> loose_bvar t k \<Longrightarrow>
    0 \<le> i \<Longrightarrow> arg_type i Ts t = argT i T"
proof (induction t arbitrary: e T Ts k i)
  case (Abs a A b)
  from Abs.prems(1) obtain U where T: "T = A \<rightarrow>\<^sub>T U" and b: "e\<langle>0:A\<rangle> \<turnstile> b : U" by blast
  have H: "\<forall>j. 0 \<le> j \<longrightarrow> j < k + 1 \<longrightarrow> fastype_of_bound (A # Ts) j = return ((e\<langle>0:A\<rangle>) j)"
  proof (intro allI impI)
    fix j :: integer assume j: "0 \<le> j" "j < k + 1"
    show "fastype_of_bound (A # Ts) j = return ((e\<langle>0:A\<rangle>) j)"
    proof (cases "j = 0")
      case False
      with j have "0 \<le> j - 1" "j - 1 < k" by (simp_all add: integer_arith)
      with Abs.prems(2) have "fastype_of_bound Ts (j - 1) = return (e (j - 1))" by blast
      with False j show ?thesis by (simp add: shift_def)
    qed (simp add: return_def)
  qed
  show ?case
  proof (cases "i = 0")
    case False
    have "arg_type (i - 1) (A # Ts) b = argT (i - 1) U"
      by (rule Abs.IH[OF b H]) (use Abs.prems(3,4) False in \<open>simp_all add: integer_arith\<close>)
    with False T show ?thesis by simp
  qed (simp add: T)
next
  case (App s u)
  from App.prems(1) obtain V where s: "e \<turnstile> s : V \<rightarrow>\<^sub>T T" by blast
  have "arg_type (i + 1) Ts s = argT (i + 1) (V \<rightarrow>\<^sub>T T)"
    by (rule App.IH(1)[OF s App.prems(2)]) (use App.prems(3,4) in simp_all)
  with App.prems(4) show ?case by simp
qed (use fastype_typing in fastforce)+

lemma argument_type_of_closed:
  "e \<turnstile> t : T \<Longrightarrow> closed t \<Longrightarrow> 0 \<le> i \<Longrightarrow> argument_type_of t i = argT i T"
  unfolding argument_type_of_def by (rule arg_type_typing[of e t T 0 "[]"]) (simp_all add: closed_def)


subsection \<open>Well-formedness of the results\<close>

lemma cterm_wf_appD:
  assumes "cterm_wf (CTerm (c $ a) T m)"
  obtains A where "cterm_wf (CTerm c (A \<rightarrow>\<^sub>T T) m)" "cterm_wf (CTerm a A m)"
    "argument_type_of c 0 = return A"
proof -
  from assms have cl: "closed c" "closed a" and ty: "\<And>e. e \<turnstile> c $ a : T"
    and ib: "ibelow m c" "ibelow m a" and m: "-1 \<le> m"
    and nn: "\<forall>v\<in>vars c. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars c. 0 \<le> snd (fst v)"
      "\<forall>v\<in>vars a. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars a. 0 \<le> snd (fst v)"
    by (auto simp: cterm_wf_def closed_def ibelow_def)
  obtain A where A: "\<And>e. e \<turnstile> c : A \<rightarrow>\<^sub>T T" "\<And>e. e \<turnstile> a : A"
  proof -
    from ty[of "\<lambda>_. propT"] obtain A where c0: "(\<lambda>_. propT) \<turnstile> c : A \<rightarrow>\<^sub>T T" by blast
    have "argument_type_of c 0 = argT 0 (A \<rightarrow>\<^sub>T T)" by (rule argument_type_of_closed[OF c0 cl(1)]) simp
    have "e \<turnstile> c : A \<rightarrow>\<^sub>T T \<and> e \<turnstile> a : A" for e
    proof -
      from ty[of e] obtain A' where c': "e \<turnstile> c : A' \<rightarrow>\<^sub>T T" "e \<turnstile> a : A'" by blast
      have "argument_type_of c 0 = argT 0 (A' \<rightarrow>\<^sub>T T)" by (rule argument_type_of_closed[OF c'(1) cl(1)]) simp
      with \<open>argument_type_of c 0 = argT 0 (A \<rightarrow>\<^sub>T T)\<close> have "A' = A" by (simp add: return_def)
      with c' show ?thesis by simp
    qed
    then show thesis by (intro that) blast+
  qed
  have "argument_type_of c 0 = return A"
    using argument_type_of_closed[OF A(1)[of "\<lambda>_. propT"] cl(1)] by simp
  moreover have "cterm_wf (CTerm c (A \<rightarrow>\<^sub>T T) m)" "cterm_wf (CTerm a A m)"
    using cl A ib m nn by (simp_all add: cterm_wf_def closed_def)
  ultimately show thesis by (rule that[rotated -1])
qed

lemma dest_comb_wf: "cterm_wf ct \<Longrightarrow> okT (dest_comb ct) (c, a) \<Longrightarrow> cterm_wf c \<and> cterm_wf a"
proof -
  assume wf: "cterm_wf ct" and ok: "okT (dest_comb ct) (c, a)"
  then obtain f x where t: "ct_t ct = f $ x" by (auto simp: dest_comb_def split: pterm.splits)
  from wf t obtain A where w: "cterm_wf (CTerm f (A \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct))" "cterm_wf (CTerm x A (ct_maxidx ct))"
    and A: "argument_type_of f 0 = return A"
    by (cases ct) (auto elim: cterm_wf_appD)
  from ok t A have "c = CTerm f (A \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct)" "a = CTerm x A (ct_maxidx ct)"
    by (simp_all add: dest_comb_def)
  with w show ?thesis by simp
qed

lemma dest_fun_wf: "cterm_wf ct \<Longrightarrow> okT (dest_fun ct) c \<Longrightarrow> cterm_wf c"
proof -
  assume wf: "cterm_wf ct" and ok: "okT (dest_fun ct) c"
  then obtain f x where t: "ct_t ct = f $ x" by (auto simp: dest_fun_def split: pterm.splits)
  from wf t obtain A where w: "cterm_wf (CTerm f (A \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct))"
    and A: "argument_type_of f 0 = return A"
    by (cases ct) (auto elim: cterm_wf_appD)
  from ok t A have "c = CTerm f (A \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct)" by (simp add: dest_fun_def)
  with w show ?thesis by simp
qed

lemma dest_arg_wf: "cterm_wf ct \<Longrightarrow> okT (dest_arg ct) c \<Longrightarrow> cterm_wf c"
proof -
  assume wf: "cterm_wf ct" and ok: "okT (dest_arg ct) c"
  then obtain f x where t: "ct_t ct = f $ x" by (auto simp: dest_arg_def split: pterm.splits)
  from wf t obtain A where w: "cterm_wf (CTerm x A (ct_maxidx ct))"
    and A: "argument_type_of f 0 = return A"
    by (cases ct) (auto elim: cterm_wf_appD)
  from ok t A have "c = CTerm x A (ct_maxidx ct)" by (simp add: dest_arg_def)
  with w show ?thesis by simp
qed

lemma dest_fun2_wf: "cterm_wf ct \<Longrightarrow> okT (dest_fun2 ct) c \<Longrightarrow> cterm_wf c"
proof -
  assume wf: "cterm_wf ct" and ok: "okT (dest_fun2 ct) c"
  then obtain f x y where t: "ct_t ct = f $ x $ y"
    by (auto simp: dest_fun2_def split: pterm.splits)
  from wf t obtain B where w1: "cterm_wf (CTerm (f $ x) (B \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct))"
    by (cases ct) (auto elim: cterm_wf_appD)
  then obtain A where w: "cterm_wf (CTerm f (A \<rightarrow>\<^sub>T B \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct))"
    and A: "argument_type_of f 0 = return A"
    by (auto elim: cterm_wf_appD)
  have "argument_type_of f 1 = return B"
  proof -
    from w have "(\<lambda>_. propT) \<turnstile> f : A \<rightarrow>\<^sub>T B \<rightarrow>\<^sub>T ct_T ct" "closed f" by (simp_all add: cterm_wf_def)
    from argument_type_of_closed[OF this] show ?thesis by simp
  qed
  with ok t A have "c = CTerm f (A \<rightarrow>\<^sub>T B \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct)" by (simp add: dest_fun2_def)
  with w show ?thesis by simp
qed

lemma dest_arg1_wf: "cterm_wf ct \<Longrightarrow> okT (dest_arg1 ct) c \<Longrightarrow> cterm_wf c"
proof -
  assume wf: "cterm_wf ct" and ok: "okT (dest_arg1 ct) c"
  then obtain f x y where t: "ct_t ct = f $ x $ y"
    by (auto simp: dest_arg1_def split: pterm.splits)
  from wf t obtain B where w1: "cterm_wf (CTerm (f $ x) (B \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct))"
    by (cases ct) (auto elim: cterm_wf_appD)
  then obtain A where w: "cterm_wf (CTerm x A (ct_maxidx ct))" and A: "argument_type_of f 0 = return A"
    by (auto elim: cterm_wf_appD)
  from ok t A have "c = CTerm x A (ct_maxidx ct)" by (simp add: dest_arg1_def)
  with w show ?thesis by simp
qed

lemma dest_abs_with_wf:
  assumes wf: "cterm_wf ct" and ok: "okT (dest_abs_with nm ct) (v, b)"
  shows "cterm_wf v \<and> cterm_wf b"
proof -
  from ok obtain a T body n U0 U x' where t: "ct_t ct = Abs a T body" and ty: "ct_T ct = Type n [U0, U]"
    and n: "n = STR ''fun''" and x': "okT (nm (Abs a T body)) x'"
    and v: "v = CTerm (Free x' T) T (ct_maxidx ct)"
    and b: "b = CTerm (subst_bound (Free x' T) body) U (ct_maxidx ct)"
    by (auto simp: dest_abs_with_def bindW_def returnW_def raiseW_def
      split: pterm.splits ptyp.splits list.splits if_splits option.splits xres.splits prod.splits)
  from wf t ty n have cl: "closed (Abs a T body)" and tyA: "\<And>e. e \<turnstile> Abs a T body : Type n [U0, U]"
    and ib: "ibelow (ct_maxidx ct) (Abs a T body)" and m: "-1 \<le> ct_maxidx ct"
    and nn: "\<forall>v\<in>vars (Abs a T body). 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars (Abs a T body). 0 \<le> snd (fst v)"
    by (auto simp: cterm_wf_def)
  have TU: "U0 = T" and bd: "\<And>e. e\<langle>0:T\<rangle> \<turnstile> body : U" and cT: "cert_typ alg ar T"
    using tyA[of "\<lambda>_. propT"] tyA n by auto
  have tyb: "e \<turnstile> subst_bound (Free x' T) body : U" for e
    unfolding subst_bound_subst by (rule subst_lemma[OF bd]) (use cT in auto)
  have "cterm_wf v"
    using cT ib m nn by (auto simp: v cterm_wf_def closed_def ibelow_def)
  moreover have "cterm_wf b"
  proof -
    have red: "Abs a T body $ Free x' T \<rightarrow>\<^sub>\<beta> subst_bound (Free x' T) body" by (simp add: subst_bound_subst)
    have "closed (Abs a T body $ Free x' T)" using cl by (simp add: closed_def)
    then have clb: "closed (subst_bound (Free x' T) body)"
      using free_beta[OF red] by (auto simp: closed_iff_loose_bvar1)
    have bv: "vars (subst_bound (Free x' T) body) \<subseteq> vars (Abs a T body)"
      "typs (subst_bound (Free x' T) body) \<subseteq> typs (Abs a T body)"
      using betapply_vars_typs[of "Abs a T body" "Free x' T"] by auto
    have "ttvars (subst_bound (Free x' T) body) \<subseteq> ttvars (Abs a T body)" using bv(2) by (auto simp: ttvars_def)
    with bv(1) clb tyb ib m nn show ?thesis by (auto simp: b cterm_wf_def ibelow_def)
  qed
  ultimately show ?thesis ..
qed

lemma dest_abs_fresh_wf: "cterm_wf ct \<Longrightarrow> okT (dest_abs_fresh x ct) (v, b) \<Longrightarrow> cterm_wf v \<and> cterm_wf b"
  unfolding dest_abs_fresh_def by (rule dest_abs_with_wf)

lemma dest_abs_global_wf: "cterm_wf ct \<Longrightarrow> okT (dest_abs_global vl ct) (v, b) \<Longrightarrow> cterm_wf v \<and> cterm_wf b"
  unfolding dest_abs_global_def by (rule dest_abs_with_wf)

lemma apply_cterm_wf:
  assumes wf: "cterm_wf cf" "cterm_wf cx" and ok: "okT (apply_cterm cf cx) r"
  shows "cterm_wf r"
proof -
  from ok obtain dty rty where T: "ct_T cf = dty \<rightarrow>\<^sub>T rty" and x: "ct_T cx = dty"
    and r: "r = CTerm (ct_t cf $ ct_t cx) rty (max (ct_maxidx cf) (ct_maxidx cx))"
    by (auto simp: apply_cterm_def returnW_def raiseW_def split: ptyp.splits list.splits if_splits)
  from wf T x show ?thesis
    by (auto simp: r cterm_wf_def closed_def ibelow_def intro: typing.App)
qed

lemma typing_abstract_atom:
  assumes v: "e \<turnstile> v : V" and t: "e \<turnstile> t : U" and lev: "0 \<le> lev" "e' lev = V"
    and other: "\<not> aconv_term v t \<Longrightarrow> e' \<turnstile> t : U"
  shows "e' \<turnstile> (if aconv_term v t then Bound lev else t) : U"
proof (cases "aconv_term v t")
  case True
  have "e \<turnstile> t : V" by (rule typing_aconv[OF True v])
  with t have "U = V" using typing_unique by blast
  with True lev show ?thesis by auto
qed (use other in simp)

lemma typing_abstract_over_closed:
  assumes v: "\<And>e. e \<turnstile> v : V"
  shows "e \<turnstile> t : U \<Longrightarrow> 0 \<le> lev \<Longrightarrow> \<not> loose_bvar t lev \<Longrightarrow> (\<And>i. 0 \<le> i \<Longrightarrow> i < lev \<Longrightarrow> e' i = e i) \<Longrightarrow>
    e' lev = V \<Longrightarrow> e' \<turnstile> abstract_over_aux v lev t : U"
proof (induction t arbitrary: e e' lev U)
  case (Abs b W s)
  show ?case
  proof (cases "aconv_term v (Abs b W s)")
    case True
    have "e \<turnstile> Abs b W s : V" by (rule typing_aconv[OF True v])
    with Abs.prems(1) have "U = V" using typing_unique by blast
    with True Abs.prems(2,5) show ?thesis by auto
  next
    case False
    from Abs.prems(1) obtain U' where U: "U = W \<rightarrow>\<^sub>T U'" and s: "e\<langle>0:W\<rangle> \<turnstile> s : U'" and W: "cert_typ alg ar W"
      by blast
    have "e'\<langle>0:W\<rangle> \<turnstile> abstract_over_aux v (lev + 1) s : U'"
    proof (rule Abs.IH[OF s])
      show "(e'\<langle>0:W\<rangle>) i = (e\<langle>0:W\<rangle>) i" if i: "0 \<le> i" "i < lev + 1" for i
      proof (cases "i = 0")
        case False
        with i have "0 \<le> i - 1" "i - 1 < lev" by (simp_all add: integer_arith)
        with Abs.prems(4) False i show ?thesis by (simp add: shift_def)
      qed (simp add: shift_def)
    qed (use Abs.prems(2,3,5) in \<open>simp_all add: shift_def\<close>)
    with False U W show ?thesis by auto
  qed
next
  case (App s u)
  show ?case
  proof (cases "aconv_term v (s $ u)")
    case True
    have "e \<turnstile> s $ u : V" by (rule typing_aconv[OF True v])
    with App.prems(1) have "U = V" using typing_unique by blast
    with True App.prems(2,5) show ?thesis by auto
  next
    case False
    from App.prems(1) obtain W where s: "e \<turnstile> s : W \<rightarrow>\<^sub>T U" and u: "e \<turnstile> u : W" by blast
    have "e' \<turnstile> abstract_over_aux v lev s : W \<rightarrow>\<^sub>T U" by (rule App.IH(1)[OF s]) (use App.prems in auto)
    moreover have "e' \<turnstile> abstract_over_aux v lev u : W" by (rule App.IH(2)[OF u]) (use App.prems in auto)
    ultimately show ?thesis using False by auto
  qed
next
  case (Const c T)
  have "e' \<turnstile> (if aconv_term v (Const c T) then Bound lev else Const c T) : U"
    by (rule typing_abstract_atom[of e v V "Const c T" U lev e', OF v[of e] Const.prems(1) Const.prems(2,5)])
      (use Const.prems(1) in auto)
  then show ?case by simp
next
  case (Free x T)
  have "e' \<turnstile> (if aconv_term v (Free x T) then Bound lev else Free x T) : U"
    by (rule typing_abstract_atom[of e v V "Free x T" U lev e', OF v[of e] Free.prems(1) Free.prems(2,5)])
      (use Free.prems(1) in auto)
  then show ?case by simp
next
  case (Var x T)
  have "e' \<turnstile> (if aconv_term v (Var x T) then Bound lev else Var x T) : U"
    by (rule typing_abstract_atom[of e v V "Var x T" U lev e', OF v[of e] Var.prems(1) Var.prems(2,5)])
      (use Var.prems(1) in auto)
  then show ?case by simp
next
  case (Bound i)
  have o: "e' \<turnstile> Bound i : U" if "\<not> aconv_term v (Bound i)"
  proof -
    from Bound.prems(1) have "U = e i" "0 \<le> i" by auto
    moreover have "i < lev" using Bound.prems(3) by simp
    ultimately show ?thesis using Bound.prems(4) by auto
  qed
  have "e' \<turnstile> (if aconv_term v (Bound i) then Bound lev else Bound i) : U"
    by (rule typing_abstract_atom[of e v V "Bound i" U lev e', OF v[of e] Bound.prems(1) Bound.prems(2,5) o])
  then show ?case by simp
qed

lemma loose_bvar_abstract_over_aux: "\<not> loose_bvar t lev \<Longrightarrow> \<not> loose_bvar (abstract_over_aux v lev t) (lev + 1)"
  by (induction v lev t rule: abstract_over_aux.induct) auto

lemma vars_typs_abstract_over_aux:
  "vars (abstract_over_aux v lev t) \<subseteq> vars t \<and> typs (abstract_over_aux v lev t) \<subseteq> typs t"
  by (induction v lev t rule: abstract_over_aux.induct) auto

lemma lambda_name_wf:
  assumes wf: "cterm_wf ct1" "cterm_wf ct2" and ok: "okT (lambda_name x ct1 ct2) r"
  shows "cterm_wf r"
proof -
  obtain v V m1 where c1: "ct1 = CTerm v V m1" by (cases ct1)
  obtain t T m2 where c2: "ct2 = CTerm t T m2" by (cases ct2)
  from wf have v: "closed v" "\<And>e. e \<turnstile> v : V" and t: "closed t" "\<And>e. e \<turnstile> t : T"
    by (simp_all add: c1 c2 cterm_wf_def)
  have fv: "fastype_of v = return V" using fastype_closed[OF v(2) v(1)] by (simp add: fastype_of_def)
  let ?n = "if x = STR '''' then term_name v else x"
  from ok fv have r: "r = CTerm (Abs ?n V (abstract_over v t)) (V \<rightarrow>\<^sub>T T) (max m1 m2)"
    by (simp add: lambda_name_def lambda_name_term_def c1 c2)
  have cV: "cert_typ alg ar V" using typing_cert_closed[OF v(2) v(1)] .
  have ty: "e \<turnstile> Abs ?n V (abstract_over v t) : V \<rightarrow>\<^sub>T T" for e
  proof -
    have "e\<langle>0:V\<rangle> \<turnstile> abstract_over_aux v 0 t : T"
      by (rule typing_abstract_over_closed[OF v(2) t(2)]) (use t(1) in \<open>simp_all add: closed_def\<close>)
    with cV show ?thesis by (auto simp: abstract_over_def)
  qed
  have cl: "closed (Abs ?n V (abstract_over v t))"
    using loose_bvar_abstract_over_aux[of t 0 v] t(1) by (simp add: closed_def abstract_over_def)
  have vt: "vars (abstract_over v t) \<subseteq> vars t" "typs (abstract_over v t) \<subseteq> typs t"
    using vars_typs_abstract_over_aux[of v 0 t] by (simp_all add: abstract_over_def)
  have tV: "tvars V \<subseteq> ttvars v"
    using fastype_of_term_tvars[of "[]" v V] fv by (simp add: fastype_of_def)
  have tt: "ttvars (Abs ?n V (abstract_over v t)) \<subseteq> ttvars v \<union> ttvars t"
    using vt(2) tV by (auto simp: ttvars_def)
  from wf have ib: "ibelow m1 v" "ibelow m2 t" "-1 \<le> m1" "-1 \<le> m2"
    and nn: "\<forall>w\<in>vars t. 0 \<le> snd (fst w)" "\<forall>w\<in>ttvars v. 0 \<le> snd (fst w)" "\<forall>w\<in>ttvars t. 0 \<le> snd (fst w)"
    by (simp_all add: c1 c2 cterm_wf_def)
  have "ibelow (max m1 m2) (Abs ?n V (abstract_over v t))"
    unfolding ibelow_def
  proof (intro conjI ballI)
    fix w assume "w \<in> vars (Abs ?n V (abstract_over v t))"
    then have "w \<in> vars t" using vt(1) by auto
    then show "snd (fst w) \<le> max m1 m2" using ib(2) unfolding ibelow_def by (auto simp: le_max_iff_disj)
  next
    fix p assume "p \<in> ttvars (Abs ?n V (abstract_over v t))"
    then have "p \<in> ttvars v \<or> p \<in> ttvars t" using tt by blast
    then show "snd (fst p) \<le> max m1 m2" using ib(1,2) unfolding ibelow_def by (auto simp: le_max_iff_disj)
  qed
  moreover have "\<forall>w\<in>vars (Abs ?n V (abstract_over v t)). 0 \<le> snd (fst w)" using vt(1) nn(1) by auto
  moreover have "\<forall>w\<in>ttvars (Abs ?n V (abstract_over v t)). 0 \<le> snd (fst w)" using tt nn(2,3) by blast
  ultimately show ?thesis using ty cl ib(3,4) by (simp add: r cterm_wf_def)
qed

lemma incr_indexes_cterm_wf:
  assumes wf: "cterm_wf ct" and ok: "okT (incr_indexes_cterm i ct) r"
  shows "cterm_wf r"
proof (cases "i = 0")
  case True
  with ok wf show ?thesis by (simp add: incr_indexes_cterm_def returnW_def raiseW_def split: if_splits)
next
  case False
  obtain t T m where c: "ct = CTerm t T m" by (cases ct)
  from ok False have i: "0 < i" and r: "r = CTerm (incr_indexes [] i t) (incr_tvar i T) (m + i)"
    by (auto simp: incr_indexes_cterm_def c returnW_def raiseW_def split: if_splits)
  from wf have t: "closed t" "\<And>e. e \<turnstile> t : T" and ib: "ibelow m t" and m: "-1 \<le> m"
    and nn: "\<forall>v\<in>vars t. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars t. 0 \<le> snd (fst v)"
    by (simp_all add: c cterm_wf_def)
  have "ibelow (m + i) (incr_indexes [] i t)"
    using ib incr_indexes_vars[of _ i t] incr_indexes_ttvars[of _ i t] unfolding ibelow_def by fastforce
  moreover have "\<forall>v\<in>vars (incr_indexes [] i t). 0 \<le> snd (fst v)"
    using nn(1) incr_indexes_vars[of _ i t] i by fastforce
  moreover have "\<forall>v\<in>ttvars (incr_indexes [] i t). 0 \<le> snd (fst v)"
    using nn(2) incr_indexes_ttvars[of _ i t] i by fastforce
  ultimately show ?thesis
    using incr_indexes_typed[OF t(2) t(1)] m i by (simp add: r cterm_wf_def)
qed

end


subsection \<open>Certified terms\<close>

text \<open>
  The operations on the abstract type of certified terms: the results have the certificate (the
  signature) and the sorts of the arguments; \<open>apply\<close> and \<open>lambda_name\<close> require the same signature
  (\<open>Context.join_certificate\<close> of two equal certificates).
\<close>

definition cmap :: "(cterm_rep \<Rightarrow> cterm_rep T) \<Rightarrow> pure_cterm \<Rightarrow> pure_cterm option" where
  "cmap f ct = map_option (\<lambda>r. Abs_cterm (rep_cterm ct\<lparr>cd_rep := r\<rparr>)) (resT (f (crep_of ct)))"

definition cmap2 :: "(cterm_rep \<Rightarrow> (cterm_rep \<times> cterm_rep) T) \<Rightarrow> pure_cterm \<Rightarrow> (pure_cterm \<times> pure_cterm) option" where
  "cmap2 f ct = map_option (\<lambda>(r1, r2). (Abs_cterm (rep_cterm ct\<lparr>cd_rep := r1\<rparr>), Abs_cterm (rep_cterm ct\<lparr>cd_rep := r2\<rparr>)))
    (resT (f (crep_of ct)))"

definition cbin :: "(cterm_rep \<Rightarrow> cterm_rep \<Rightarrow> cterm_rep T) \<Rightarrow> pure_cterm \<Rightarrow> pure_cterm \<Rightarrow> pure_cterm option" where
  "cbin f ct1 ct2 =
    (if csign_of ct1 = csign_of ct2 then
       map_option (\<lambda>r. Abs_cterm \<lparr>cd_rep = r, cd_sorts = csorts_of ct1 \<union> csorts_of ct2, cd_sign = csign_of ct1\<rparr>)
         (resT (f (crep_of ct1) (crep_of ct2)))
     else None)"

lemma cterm_ok_rep:
  "(pure_sig (sg_alg (cd_sign d)) (sg_ar (cd_sign d)) \<Longrightarrow>
    pure_sig.cterm_wf (sg_alg (cd_sign d)) (sg_ar (cd_sign d)) (sg_consts (cd_sign d)) (cd_rep d)) \<Longrightarrow> cterm_ok d"
  by (simp add: cterm_ok_def)

lemma cmap:
  assumes pres: "\<And>r. pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) \<Longrightarrow>
      pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct) \<Longrightarrow>
      okT (f (crep_of ct)) r \<Longrightarrow>
      pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r"
    and c: "cmap f ct = Some ct'"
  shows "okT (f (crep_of ct)) (crep_of ct')" "csign_of ct' = csign_of ct" "csorts_of ct' = csorts_of ct"
proof -
  from c obtain r where ok: "okT (f (crep_of ct)) r" and ct': "ct' = Abs_cterm (rep_cterm ct\<lparr>cd_rep := r\<rparr>)"
    by (auto simp: cmap_def resT_Some)
  have "cterm_ok (rep_cterm ct\<lparr>cd_rep := r\<rparr>)"
    by (rule cterm_ok_rep) (use pres[OF _ _ ok] pure_cterm_wf[of ct] in simp)
  then have "rep_cterm ct' = rep_cterm ct\<lparr>cd_rep := r\<rparr>" unfolding ct' by (simp add: Abs_cterm_inverse)
  with ok show "okT (f (crep_of ct)) (crep_of ct')" "csign_of ct' = csign_of ct" "csorts_of ct' = csorts_of ct"
    by simp_all
qed

lemma cmap2:
  assumes pres: "\<And>r1 r2. pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) \<Longrightarrow>
      pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct) \<Longrightarrow>
      okT (f (crep_of ct)) (r1, r2) \<Longrightarrow>
      pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r1 \<and>
      pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r2"
    and c: "cmap2 f ct = Some (ct1, ct2)"
  shows "okT (f (crep_of ct)) (crep_of ct1, crep_of ct2)" "csign_of ct1 = csign_of ct" "csorts_of ct1 = csorts_of ct"
    "csign_of ct2 = csign_of ct" "csorts_of ct2 = csorts_of ct"
proof -
  from c obtain r1 r2 where ok: "okT (f (crep_of ct)) (r1, r2)"
    and ct': "ct1 = Abs_cterm (rep_cterm ct\<lparr>cd_rep := r1\<rparr>)" "ct2 = Abs_cterm (rep_cterm ct\<lparr>cd_rep := r2\<rparr>)"
    by (auto simp: cmap2_def resT_Some)
  have "cterm_ok (rep_cterm ct\<lparr>cd_rep := r1\<rparr>)" "cterm_ok (rep_cterm ct\<lparr>cd_rep := r2\<rparr>)"
    by (rule cterm_ok_rep, use pres[OF _ _ ok] pure_cterm_wf[of ct] in simp)+
  then have "rep_cterm ct1 = rep_cterm ct\<lparr>cd_rep := r1\<rparr>" "rep_cterm ct2 = rep_cterm ct\<lparr>cd_rep := r2\<rparr>"
    unfolding ct' by (simp_all add: Abs_cterm_inverse)
  with ok show "okT (f (crep_of ct)) (crep_of ct1, crep_of ct2)" "csign_of ct1 = csign_of ct"
    "csorts_of ct1 = csorts_of ct" "csign_of ct2 = csign_of ct" "csorts_of ct2 = csorts_of ct"
    by simp_all
qed

lemma cbin:
  assumes pres: "\<And>r. pure_sig (sg_alg (csign_of ct1)) (sg_ar (csign_of ct1)) \<Longrightarrow>
      pure_sig.cterm_wf (sg_alg (csign_of ct1)) (sg_ar (csign_of ct1)) (sg_consts (csign_of ct1)) (crep_of ct1) \<Longrightarrow>
      pure_sig.cterm_wf (sg_alg (csign_of ct1)) (sg_ar (csign_of ct1)) (sg_consts (csign_of ct1)) (crep_of ct2) \<Longrightarrow>
      okT (f (crep_of ct1) (crep_of ct2)) r \<Longrightarrow>
      pure_sig.cterm_wf (sg_alg (csign_of ct1)) (sg_ar (csign_of ct1)) (sg_consts (csign_of ct1)) r"
    and c: "cbin f ct1 ct2 = Some ct"
  shows "okT (f (crep_of ct1) (crep_of ct2)) (crep_of ct)" "csign_of ct2 = csign_of ct1"
    "csign_of ct = csign_of ct1" "csorts_of ct = csorts_of ct1 \<union> csorts_of ct2"
proof -
  from c obtain r where s: "csign_of ct1 = csign_of ct2" and ok: "okT (f (crep_of ct1) (crep_of ct2)) r"
    and ct: "ct = Abs_cterm \<lparr>cd_rep = r, cd_sorts = csorts_of ct1 \<union> csorts_of ct2, cd_sign = csign_of ct1\<rparr>"
    by (auto simp: cbin_def resT_Some split: if_splits)
  have "cterm_ok \<lparr>cd_rep = r, cd_sorts = csorts_of ct1 \<union> csorts_of ct2, cd_sign = csign_of ct1\<rparr>"
    by (rule cterm_ok_rep) (use pres[OF _ _ _ ok] pure_cterm_wf[of ct1] pure_cterm_wf[of ct2] s in simp)
  then have "rep_cterm ct = \<lparr>cd_rep = r, cd_sorts = csorts_of ct1 \<union> csorts_of ct2, cd_sign = csign_of ct1\<rparr>"
    unfolding ct by (simp add: Abs_cterm_inverse)
  with ok s show "okT (f (crep_of ct1) (crep_of ct2)) (crep_of ct)" "csign_of ct2 = csign_of ct1"
    "csign_of ct = csign_of ct1" "csorts_of ct = csorts_of ct1 \<union> csorts_of ct2"
    by simp_all
qed

definition "dest_comb_cterm = cmap2 dest_comb"
definition "dest_fun_cterm = cmap dest_fun"
definition "dest_arg_cterm = cmap dest_arg"
definition "dest_fun2_cterm = cmap dest_fun2"
definition "dest_arg1_cterm = cmap dest_arg1"
definition "dest_abs_fresh_cterm x = cmap2 (dest_abs_fresh x)"
definition "dest_abs_global_cterm vl = cmap2 (dest_abs_global vl)"
definition "apply_pure_cterm = cbin apply_cterm"
definition "lambda_name_cterm x = cbin (lambda_name x)"
definition "incr_indexes_pure_cterm i = cmap (incr_indexes_cterm i)"

theorem dest_comb_cterm:
  assumes c: "dest_comb_cterm ct = Some (c, a)"
  shows "okT (dest_comb (crep_of ct)) (crep_of c, crep_of a) \<and>
    csign_of c = csign_of ct \<and> csorts_of c = csorts_of ct \<and> csign_of a = csign_of ct \<and> csorts_of a = csorts_of ct"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r1 \<and>
      pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r2"
    if "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
      "okT (dest_comb (crep_of ct)) (r1, r2)" for r1 r2
    by (rule pure_sig.dest_comb_wf[OF that])
  show ?thesis using cmap2[OF pres c[unfolded dest_comb_cterm_def]] by blast
qed

theorem dest_fun_cterm:
  assumes c: "dest_fun_cterm ct = Some c"
  shows "okT (dest_fun (crep_of ct)) (crep_of c) \<and>
    csign_of c = csign_of ct \<and> csorts_of c = csorts_of ct"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r"
    if "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
      "okT (dest_fun (crep_of ct)) r" for r
    by (rule pure_sig.dest_fun_wf[OF that])
  show ?thesis using cmap[OF pres c[unfolded dest_fun_cterm_def]] by blast
qed

theorem dest_arg_cterm:
  assumes c: "dest_arg_cterm ct = Some c"
  shows "okT (dest_arg (crep_of ct)) (crep_of c) \<and>
    csign_of c = csign_of ct \<and> csorts_of c = csorts_of ct"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r"
    if "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
      "okT (dest_arg (crep_of ct)) r" for r
    by (rule pure_sig.dest_arg_wf[OF that])
  show ?thesis using cmap[OF pres c[unfolded dest_arg_cterm_def]] by blast
qed

theorem dest_fun2_cterm:
  assumes c: "dest_fun2_cterm ct = Some c"
  shows "okT (dest_fun2 (crep_of ct)) (crep_of c) \<and>
    csign_of c = csign_of ct \<and> csorts_of c = csorts_of ct"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r"
    if "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
      "okT (dest_fun2 (crep_of ct)) r" for r
    by (rule pure_sig.dest_fun2_wf[OF that])
  show ?thesis using cmap[OF pres c[unfolded dest_fun2_cterm_def]] by blast
qed

theorem dest_arg1_cterm:
  assumes c: "dest_arg1_cterm ct = Some c"
  shows "okT (dest_arg1 (crep_of ct)) (crep_of c) \<and>
    csign_of c = csign_of ct \<and> csorts_of c = csorts_of ct"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r"
    if "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
      "okT (dest_arg1 (crep_of ct)) r" for r
    by (rule pure_sig.dest_arg1_wf[OF that])
  show ?thesis using cmap[OF pres c[unfolded dest_arg1_cterm_def]] by blast
qed

theorem dest_abs_fresh_cterm:
  assumes c: "dest_abs_fresh_cterm x ct = Some (v, b)"
  shows "okT (dest_abs_fresh x (crep_of ct)) (crep_of v, crep_of b) \<and>
    csign_of v = csign_of ct \<and> csorts_of v = csorts_of ct \<and> csign_of b = csign_of ct \<and> csorts_of b = csorts_of ct"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r1 \<and>
      pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r2"
    if "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
      "okT (dest_abs_fresh x (crep_of ct)) (r1, r2)" for r1 r2
    by (rule pure_sig.dest_abs_fresh_wf[OF that])
  show ?thesis using cmap2[OF pres c[unfolded dest_abs_fresh_cterm_def]] by blast
qed

theorem dest_abs_global_cterm:
  assumes c: "dest_abs_global_cterm vl ct = Some (v, b)"
  shows "okT (dest_abs_global vl (crep_of ct)) (crep_of v, crep_of b) \<and>
    csign_of v = csign_of ct \<and> csorts_of v = csorts_of ct \<and> csign_of b = csign_of ct \<and> csorts_of b = csorts_of ct"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r1 \<and>
      pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r2"
    if "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
      "okT (dest_abs_global vl (crep_of ct)) (r1, r2)" for r1 r2
    by (rule pure_sig.dest_abs_global_wf[OF that])
  show ?thesis using cmap2[OF pres c[unfolded dest_abs_global_cterm_def]] by blast
qed

theorem incr_indexes_pure_cterm:
  assumes c: "incr_indexes_pure_cterm i ct = Some ct'"
  shows "okT (incr_indexes_cterm i (crep_of ct)) (crep_of ct') \<and>
    csign_of ct' = csign_of ct \<and> csorts_of ct' = csorts_of ct"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) r"
    if "pure_sig (sg_alg (csign_of ct)) (sg_ar (csign_of ct))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct)) (sg_ar (csign_of ct)) (sg_consts (csign_of ct)) (crep_of ct)"
      "okT (incr_indexes_cterm i (crep_of ct)) r" for r
    by (rule pure_sig.incr_indexes_cterm_wf[OF that])
  show ?thesis using cmap[OF pres c[unfolded incr_indexes_pure_cterm_def]] by blast
qed

theorem apply_pure_cterm:
  assumes c: "apply_pure_cterm cf cx = Some ct"
  shows "okT (apply_cterm (crep_of cf) (crep_of cx)) (crep_of ct) \<and>
    csign_of cx = csign_of cf \<and> csign_of ct = csign_of cf \<and>
    csorts_of ct = csorts_of cf \<union> csorts_of cx"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of cf)) (sg_ar (csign_of cf)) (sg_consts (csign_of cf)) r"
    if "pure_sig (sg_alg (csign_of cf)) (sg_ar (csign_of cf))"
      "pure_sig.cterm_wf (sg_alg (csign_of cf)) (sg_ar (csign_of cf)) (sg_consts (csign_of cf)) (crep_of cf)"
      "pure_sig.cterm_wf (sg_alg (csign_of cf)) (sg_ar (csign_of cf)) (sg_consts (csign_of cf)) (crep_of cx)"
      "okT (apply_cterm (crep_of cf) (crep_of cx)) r" for r
    by (rule pure_sig.apply_cterm_wf[OF that])
  show ?thesis using cbin[OF pres c[unfolded apply_pure_cterm_def]] by blast
qed

theorem lambda_name_cterm:
  assumes c: "lambda_name_cterm x ct1 ct2 = Some ct"
  shows "okT (lambda_name x (crep_of ct1) (crep_of ct2)) (crep_of ct) \<and>
    csign_of ct2 = csign_of ct1 \<and> csign_of ct = csign_of ct1 \<and>
    csorts_of ct = csorts_of ct1 \<union> csorts_of ct2"
proof -
  have pres: "pure_sig.cterm_wf (sg_alg (csign_of ct1)) (sg_ar (csign_of ct1)) (sg_consts (csign_of ct1)) r"
    if "pure_sig (sg_alg (csign_of ct1)) (sg_ar (csign_of ct1))"
      "pure_sig.cterm_wf (sg_alg (csign_of ct1)) (sg_ar (csign_of ct1)) (sg_consts (csign_of ct1)) (crep_of ct1)"
      "pure_sig.cterm_wf (sg_alg (csign_of ct1)) (sg_ar (csign_of ct1)) (sg_consts (csign_of ct1)) (crep_of ct2)"
      "okT (lambda_name x (crep_of ct1) (crep_of ct2)) r" for r
    by (rule pure_sig.lambda_name_wf[OF that])
  show ?thesis using cbin[OF pres c[unfolded lambda_name_cterm_def]] by blast
qed

end
