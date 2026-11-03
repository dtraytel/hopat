section \<open>Abstractions Applied to Bound Variables\<close>

theory Pattern_Terms
  imports Pattern_Head_Norm "Pure_Lambda.Pure_Inversion"
begin

text \<open>
  Pattern unification binds a variable to \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. t\<close> (\<^const>\<open>mkabs\<close>) and applies it to
  distinct bound variables \<open>y\<^sub>1 \<dots> y\<^sub>n\<close> (\<^const>\<open>app\<close>). This \<open>\<beta>\<close>-reduces to a renaming of
  the bound variables of \<open>t\<close>.
\<close>

subsection \<open>Renaming bound variables\<close>

text \<open>\<open>rename f d t\<close> renames the loose bound variables \<open>d + i\<close> of \<open>t\<close> to \<open>d + f i\<close>.\<close>

fun rename :: "(integer \<Rightarrow> integer) \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "rename f d (Bound i) = (if i < d then Bound i else Bound (f (i - d) + d))"
| "rename f d (Abs a T t) = Abs a T (rename f (d + 1) t)"
| "rename f d (s $ t) = rename f d s $ rename f d t"
| "rename f d t = t"

definition nonneg :: "(integer \<Rightarrow> integer) \<Rightarrow> bool" where
  "nonneg f \<longleftrightarrow> (\<forall>k\<ge>0. 0 \<le> f k)"

lemma rename_id: "rename (\<lambda>k. k) d t = t"
  by (induction "\<lambda>k::integer. k" d t rule: rename.induct) auto

lemma rename_no_loose: "\<not> loose_bvar t d \<Longrightarrow> rename f d t = t"
  by (induction f d t rule: rename.induct) auto

lemma rename_closed: "closed t \<Longrightarrow> 0 \<le> d \<Longrightarrow> rename f d t = t"
  by (simp add: rename_no_loose closed_loose_bvar)

lemma rename_apps: "rename f d (s \<degree>\<degree> ts) = rename f d s \<degree>\<degree> map (rename f d) ts"
  by (induction ts arbitrary: s) auto

lemma inst_rename: "inst \<rho> (rename f d t) = rename f d (inst \<rho> t)"
  by (induction f d t rule: rename.induct) auto

lemma vsubst_rename: "closed_subst \<sigma> \<Longrightarrow> 0 \<le> d \<Longrightarrow> vsubst \<sigma> (rename f d t) = rename f d (vsubst \<sigma> t)"
  by (induction f d t rule: rename.induct) (auto simp: rename_closed closed_substD)

text \<open>Substituting a bound variable for the innermost bound variable is a renaming:\<close>

lemma subst_rename:
  "0 \<le> d \<Longrightarrow> 0 \<le> j \<Longrightarrow> nonneg f \<Longrightarrow>
    (rename f (d + 1) t)[Bound (j + d)/d] = rename (\<lambda>k. if k = 0 then j else f (k - 1)) d t"
proof (induction t arbitrary: d)
  case (Bound i)
  consider "i < d" | "i = d" | "d < i" by fastforce
  then show ?case
  proof cases
    case 3
    with Bound.prems have "0 \<le> f (i - d - 1)" by (simp add: nonneg_def integer_arith)
    with 3 Bound.prems show ?thesis by (auto simp: subst_Bound integer_arith algebra_simps)
  qed (use Bound.prems in \<open>auto simp: subst_Bound integer_arith\<close>)
next
  case (Abs a T t)
  have "(rename f (d + 1 + 1) t)[Bound (j + (d + 1))/d + 1] =
      rename (\<lambda>k. if k = 0 then j else f (k - 1)) (d + 1) t"
    using Abs.prems by (intro Abs.IH) (simp_all add: integer_arith)
  with Abs.prems show ?case by (simp add: algebra_simps)
qed auto

text \<open>\<open>bren js\<close> maps the bound variables of the body of an \<open>n\<close>-fold abstraction to the bound
  variables in \<open>rev js\<close>, it is applied to (the last argument instantiates the innermost binder).\<close>

fun bren :: "integer list \<Rightarrow> integer \<Rightarrow> integer" where
  "bren [] k = k"
| "bren (j # js) k = (if k = 0 then j else bren js (k - 1))"

lemma nonneg_bren: "\<forall>j\<in>set js. 0 \<le> j \<Longrightarrow> nonneg (bren js)"
  unfolding nonneg_def by (induction js) (auto simp: integer_arith)

lemma bren_Cons: "bren (j # js) = (\<lambda>k. if k = 0 then j else bren js (k - 1))"
  by auto

lemma bren_nth: "0 \<le> k \<Longrightarrow> k < ilength js \<Longrightarrow> bren js k = js ! nat_of_integer k"
proof (induction js arbitrary: k)
  case (Cons j js)
  show ?case
  proof (cases "k = 0")
    case False
    with Cons.prems have "nat_of_integer k = Suc (nat_of_integer (k - 1))"
      by (simp add: integer_arith nat_of_integer.rep_eq)
    with False Cons.prems Cons.IH[of "k - 1"] show ?thesis by (simp add: integer_arith)
  qed simp
qed simp


subsection \<open>Iterated abstraction\<close>

definition abs_list :: "binders \<Rightarrow> pterm \<Rightarrow> pterm" where
  "abs_list bs t = foldr (\<lambda>(x, T) t. Abs x T t) bs t"

lemma abs_list_simps [simp]:
  "abs_list [] t = t"
  "abs_list ((x, T) # bs) t = Abs x T (abs_list bs t)"
  "abs_list (bs @ [(x, T)]) t = abs_list bs (Abs x T t)"
  by (simp_all add: abs_list_def)

lemma beta_abs_list_apps:
  "length bs = length js \<Longrightarrow> \<forall>j\<in>set js. 0 \<le> j \<Longrightarrow>
    abs_list bs t \<degree>\<degree> map Bound js \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bren (rev js)) 0 t"
proof (induction js arbitrary: bs t rule: rev_induct)
  case Nil
  then show ?case by (simp add: rename_id)
next
  case (snoc j js)
  then obtain bs' x T where bs: "bs = bs' @ [(x, T)]" and len: "length bs' = length js"
    by (cases bs rule: rev_cases) auto
  have "abs_list bs t \<degree>\<degree> map Bound (js @ [j]) = (abs_list bs' (Abs x T t) \<degree>\<degree> map Bound js) $ Bound j"
    by (simp add: bs)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bren (rev js)) 0 (Abs x T t) $ Bound j"
  proof -
    have "abs_list bs' (Abs x T t) \<degree>\<degree> map Bound js \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bren (rev js)) 0 (Abs x T t)"
      using snoc.IH[OF len, of "Abs x T t"] snoc.prems(2) by simp
    from apps_preserves_beta2[OF this, where ss="[Bound j]"] show ?thesis by simp
  qed
  also have "\<dots> \<rightarrow>\<^sub>\<beta> (rename (bren (rev js)) 1 t)[Bound j/0]"
    by simp
  also have "(rename (bren (rev js)) 1 t)[Bound j/0] = rename (bren (rev (js @ [j]))) 0 t"
    using subst_rename[of 0 j "bren (rev js)" t] snoc.prems(2) nonneg_bren[of "rev js"]
    by (simp add: bren_Cons)
  finally show ?case .
qed

lemma inst_abs_list: "inst \<rho> (abs_list bs t) = abs_list (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs) (inst \<rho> t)"
  by (induction bs) auto

lemma vsubst_abs_list: "vsubst \<sigma> (abs_list bs t) = abs_list bs (vsubst \<sigma> t)"
  by (induction bs) auto


subsection \<open>The ML functions\<close>

lemma app_apps: "app s is = s \<degree>\<degree> map Bound is"
  by (induction "is" arbitrary: s) (simp_all add: app_def)

lemma ok_mkabs:
  "ok (mkabs bs is t) u \<longleftrightarrow>
    (\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs) \<and> u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) t"
proof (induction "is" arbitrary: u)
  case (Cons i "is")
  show ?case
    by (cases "bs ! nat_of_integer i") (auto simp: ok_nth Cons.IH)
qed (simp add: eq_commute)

lemma ok_ints_of: "ok (ints_of ts) is \<longleftrightarrow> ts = map Bound is \<and> distinct is"
proof (induction ts arbitrary: "is")
  case (Cons t ts)
  show ?case by (cases t) (auto simp: Cons.IH)
qed (auto simp: eq_commute[of "[]"])


subsection \<open>Loose bound variables\<close>

lemma loose_bvar_apps: "loose_bvar (s \<degree>\<degree> ts) k \<longleftrightarrow> loose_bvar s k \<or> (\<exists>t\<in>set ts. loose_bvar t k)"
  by (induction ts arbitrary: s) auto

lemma loose_bvar_abs_list: "loose_bvar (abs_list bs t) k \<longleftrightarrow> loose_bvar t (k + ilength bs)"
proof (induction bs arbitrary: k)
  case (Cons b bs)
  then show ?case by (cases b) (simp add: algebra_simps)
qed simp

lemma closed_abs_list: "\<not> loose_bvar t (ilength bs) \<Longrightarrow> closed (abs_list bs t)"
  by (simp add: closed_def loose_bvar_abs_list)

lemma loose_bvar_lift: "0 \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> loose_bvar (lift s j) (k + 1) \<longleftrightarrow> loose_bvar s k"
proof (induction s arbitrary: j k)
  case (Abs a T s)
  then show ?case using Abs.IH[of "j + 1" "k + 1"] by (simp add: integer_arith)
qed (auto simp: integer_arith)

lemma loose_bvar_subst:
  "0 \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> \<not> loose_bvar t (k + 1) \<Longrightarrow> \<not> loose_bvar s k \<Longrightarrow> \<not> loose_bvar (t[s/j]) k"
proof (induction t arbitrary: j k s)
  case (Bound i)
  then show ?case by (auto simp: subst_Bound integer_arith)
next
  case (Abs a T t)
  have "\<not> loose_bvar (lift s 0) (k + 1)" using Abs.prems loose_bvar_lift[of 0 k s] by simp
  with Abs.prems show ?case using Abs.IH[of "j + 1" "k + 1" "lift s 0"] by (simp add: integer_arith)
qed auto


text \<open>Rigid heads: constants, free and bound variables.\<close>

definition rigid :: "pterm \<Rightarrow> bool" where
  "rigid h \<longleftrightarrow> (case h of Const _ _ \<Rightarrow> True | Free _ _ \<Rightarrow> True | Bound _ \<Rightarrow> True | _ \<Rightarrow> False)"

lemma rigid_simps [simp]:
  "rigid (Const c T)" "rigid (Free f T)" "rigid (Bound i)"
  "\<not> rigid (Var x T)" "\<not> rigid (Abs a T t)" "\<not> rigid (s $ t)"
  by (simp_all add: rigid_def)

lemma rigid_iff: "rigid h \<longleftrightarrow> atom h \<and> \<not> is_Var h"
  by (cases h) simp_all

context signature
begin

subsection \<open>Equivalence of applications\<close>

lemma wt_apps_head: "wt (s \<degree>\<degree> ts) \<Longrightarrow> wt s"
  by (induction ts arbitrary: s) (auto dest: wt_AppD)

lemma conv_apps:
  "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) ts ts' \<Longrightarrow> wt (s \<degree>\<degree> ts) \<Longrightarrow> wt (s' \<degree>\<degree> ts') \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' \<Longrightarrow>
    s \<degree>\<degree> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' \<degree>\<degree> ts'"
proof (induction ts ts' arbitrary: s s' rule: list_all2_induct)
  case (Cons t ts t' ts')
  have "s $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' $ t'"
    using conv_App wt_apps_head Cons.prems Cons.hyps(1) by (metis foldl_Cons)
  with Cons.IH Cons.prems show ?case by simp
qed simp


subsection \<open>Typing\<close>

definition renv :: "(integer \<Rightarrow> ptyp) \<Rightarrow> (integer \<Rightarrow> integer) \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> ptyp" where
  "renv e f d i = (if i < d then e i else e (f (i - d) + d))"

lemma renv_shift: "nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> (renv e f d)\<langle>0:T\<rangle> = renv (e\<langle>0:T\<rangle>) f (d + 1)"
proof (rule ext)
  fix i
  assume f: "nonneg f" and d: "0 \<le> d"
  show "((renv e f d)\<langle>0:T\<rangle>) i = renv (e\<langle>0:T\<rangle>) f (d + 1) i"
  proof (cases "d + 1 \<le> i")
    case True
    with f d have "0 \<le> f (i - (d + 1))" by (simp add: nonneg_def integer_arith)
    with True d show ?thesis by (simp add: renv_def shift_def integer_arith algebra_simps)
  qed (use d in \<open>simp add: renv_def shift_def integer_arith algebra_simps\<close>)
qed

lemma typing_rename:
  "e' \<turnstile> t : T \<Longrightarrow> e' = renv e f d \<Longrightarrow> nonneg f \<Longrightarrow> 0 \<le> d \<Longrightarrow> e \<turnstile> rename f d t : T"
proof (induction arbitrary: e d rule: typing.induct)
  case (Bound i e' T)
  show ?case
  proof (cases "i < d")
    case False
    with Bound have f: "0 \<le> f (i - d)" by (simp add: nonneg_def integer_arith)
    have "e \<turnstile> Bound (f (i - d) + d) : T"
      using Bound f False by (intro typing.Bound) (simp_all add: renv_def integer_arith)
    with False show ?thesis by simp
  qed (use Bound in \<open>auto simp: renv_def\<close>)
next
  case (Abs T e' t U a)
  have "e\<langle>0:T\<rangle> \<turnstile> rename f (d + 1) t : U"
    using Abs.prems by (intro Abs.IH) (simp_all add: renv_shift integer_arith)
  with Abs.hyps(1) show ?case by auto
qed auto

text \<open>Iterated abstraction pushes the types of the binders:\<close>

fun pushes :: "(integer \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> integer \<Rightarrow> ptyp" where
  "pushes e [] = e"
| "pushes e (T # Ts) = pushes (e\<langle>0:T\<rangle>) Ts"

lemma typing_abs_list:
  "pushes e (map snd bs) \<turnstile> t : U \<Longrightarrow> \<forall>T\<in>snd ` set bs. ty_ok T \<Longrightarrow> e \<turnstile> abs_list bs t : map snd bs \<Rrightarrow> U"
  by (induction bs arbitrary: e) auto

end

end
