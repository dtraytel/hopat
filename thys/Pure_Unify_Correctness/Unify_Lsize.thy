section \<open>The Size of \<open>\<eta>\<close>-Long Forms\<close>

theory Unify_Lsize
  imports Nipkow_Grobauer_Pattern.Unif_Occurs
begin

text \<open>
  Huet's search terminates on a given solution: every \<open>MATCH\<close> step replaces the value of a
  variable by smaller values of new variables. The size has to be measured on \<open>\<eta>\<close>-long forms
  (\<open>?F := \<lambda>x. c (?G x)\<close> solves \<open>?F a =?= c a\<close> with \<open>?F \<mapsto> c\<close> and \<open>?G \<mapsto> \<lambda>x. x\<close>, and \<open>\<lambda>x. x\<close> is
  larger than \<open>c\<close>). As for the depth \<^const>\<open>ld\<close> of \<^theory>\<open>Nipkow_Grobauer_Pattern.Unif_Occurs\<close>, we
  compute the size of the \<open>\<eta>\<close>-long form of a \<open>\<beta>\<close>-normal term from its type, without building
  it, and show that it is invariant under \<open>\<eta>\<close>-reduction of well-typed \<open>\<beta>\<close>-normal terms and hence
  under \<open>\<beta>\<eta>\<close>-equivalence. Only the heads are counted.
\<close>

subsection \<open>The measure\<close>

text \<open>The size of the \<open>\<eta>\<close>-long form of a variable of a given type.\<close>

fun tsize :: "type \<Rightarrow> nat" where
  "tsize (Atom _) = 1"
| "tsize (T \<Rightarrow> U) = tsize T + tsize U"

lemma tsize_pos: "0 < tsize T"
  by (induction T rule: tsize.induct) auto

lemma tsize_dom_rng: "tsize (dom_type T \<Rightarrow> rng_type T) \<le> tsize T + tsize (dom_type T)"
  by (cases T) auto

text \<open>
  \<open>hsize\<close>: the size of a term whose head is not an abstraction, without the \<open>\<eta>\<close>-expansion of the
  term itself; \<open>lsize\<close>: the size of the \<open>\<eta>\<close>-long form of a term of a given type.
\<close>

fun hsize :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> nat"
  and lsize :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> nat" where
  "hsize e \<tau> (BVar x) = 1"
| "hsize e \<tau> (Var F) = 1"
| "hsize e \<tau> (Abs t) = 1"
| "hsize e \<tau> (s \<degree> t) = hsize e \<tau> s + lsize e \<tau> t (dom_type (spine_type e \<tau> s))"
| "lsize e \<tau> (Abs t) T = lsize (e\<langle>0:dom_type T\<rangle>) \<tau> t (rng_type T)"
| "lsize e \<tau> (BVar x) T = hsize e \<tau> (BVar x) + (tsize T - 1)"
| "lsize e \<tau> (Var F) T = hsize e \<tau> (Var F) + (tsize T - 1)"
| "lsize e \<tau> (s \<degree> t) T = hsize e \<tau> (s \<degree> t) + (tsize T - 1)"

lemma lsize_nonAbs: "\<not> is_Abs s \<Longrightarrow> lsize e \<tau> s T = hsize e \<tau> s + (tsize T - 1)"
  by (cases s) auto

lemma hsize_pos: "0 < hsize e \<tau> s"
  by (induction s) auto

lemma lsize_pos: "0 < lsize e \<tau> s T"
  by (induction s arbitrary: e T) (auto simp: hsize_pos)


lemma hsize_lsize_map_BVars:
  "(\<And>v. v \<in> loose_BVars t \<Longrightarrow> e' (f v) = e v) \<Longrightarrow> hsize e' \<tau> (map_BVars f t) = hsize e \<tau> t"
  "(\<And>v. v \<in> loose_BVars t \<Longrightarrow> e' (f v) = e v) \<Longrightarrow> lsize e' \<tau> (map_BVars f t) T = lsize e \<tau> t T"
proof (induction t arbitrary: e e' f T)
  case (Abs t)
  {
    case 2
    have "lsize (e'\<langle>0:dom_type T\<rangle>) \<tau> (map_BVars (case_nat 0 (\<lambda>a. Suc (f a))) t) (rng_type T) =
      lsize (e\<langle>0:dom_type T\<rangle>) \<tau> t (rng_type T)"
    proof (rule Abs.IH(2))
      fix v assume "v \<in> loose_BVars t"
      with 2 show "(e'\<langle>0:dom_type T\<rangle>) (case v of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (f a)) = (e\<langle>0:dom_type T\<rangle>) v"
        by (cases v) (auto simp: shift_def)
    qed
    then show ?case by simp
  }
next
  case (App s t)
  {
    case 1
    then show ?case using App.IH by (simp add: spine_type_map_BVars)
  next
    case 2
    then show ?case using App.IH by (simp add: spine_type_map_BVars)
  }
qed auto

lemmas hsize_map_BVars = hsize_lsize_map_BVars(1)
lemmas lsize_map_BVars = hsize_lsize_map_BVars(2)


subsection \<open>Invariance under \<open>\<beta>\<eta>\<close>-equivalence\<close>

lemma lsize_eta:
  assumes "s \<rightarrow>\<^sub>\<eta> t" "(e, \<tau>) \<turnstile> s : T" "no_redex s"
  shows "lsize e \<tau> t T = lsize e \<tau> s T \<and> no_redex t"
  using assms
proof (induction arbitrary: e T rule: eta.induct)
  case (eta s dummy)
  from eta.prems(1) obtain A U where T: "T = A \<Rightarrow> U" and ty: "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> s : A \<Rightarrow> U"
    by auto
  have nr: "no_redex s" "\<not> is_Abs s" using eta.prems(2) by auto
  have sp: "spine_type (e\<langle>0:A\<rangle>) \<tau> s = A \<Rightarrow> U" using spine_type_typing[OF ty nr] .
  have "lsize e \<tau> (Abs (s \<degree> BVar 0)) T = hsize (e\<langle>0:A\<rangle>) \<tau> s + tsize A + (tsize U - 1)"
    using tsize_pos[of A] by (simp add: T sp)
  moreover have "hsize e \<tau> (map_BVars (\<lambda>j. j - 1) s) = hsize (e\<langle>0:A\<rangle>) \<tau> s"
  proof (rule hsize_map_BVars)
    fix v assume "v \<in> loose_BVars s"
    with eta.hyps have "v \<noteq> 0" by (auto simp: loose_BVars_free) (metis gr0I)
    then show "e (v - 1) = (e\<langle>0:A\<rangle>) v" by (cases v) (auto simp: shift_def)
  qed
  moreover have "\<not> is_Abs (map_BVars (\<lambda>j. j - 1) s)" using nr(2) by simp
  ultimately show ?case
    using nr eta.hyps tsize_pos[of U] by (simp add: subst_dummy_map_BVars T lsize_nonAbs)
next
  case (appL s t u)
  from appL.prems obtain A where tys: "(e, \<tau>) \<turnstile> s : A \<Rightarrow> T" and tyu: "(e, \<tau>) \<turnstile> u : A" by auto
  have nr: "no_redex s" "\<not> is_Abs s" "no_redex u" using appL.prems(2) by auto
  from appL.IH[OF tys nr(1)] have IH: "lsize e \<tau> t (A \<Rightarrow> T) = lsize e \<tau> s (A \<Rightarrow> T)" "no_redex t" by auto
  have nt: "\<not> is_Abs t" using eta_not_Abs[OF appL.hyps nr(2)] .
  moreover have "(e, \<tau>) \<turnstile> t : A \<Rightarrow> T" using subject_reduction_eta[OF appL.hyps tys] .
  ultimately have "spine_type e \<tau> t = A \<Rightarrow> T" using spine_type_typing IH(2) by blast
  moreover have "spine_type e \<tau> s = A \<Rightarrow> T" using spine_type_typing[OF tys nr(1,2)] .
  moreover have "hsize e \<tau> t = hsize e \<tau> s" using IH(1) nt nr(2) by (simp add: lsize_nonAbs)
  ultimately show ?case using IH nr nt by simp
next
  case (appR s t u)
  from appR.prems obtain A where tyu: "(e, \<tau>) \<turnstile> u : A \<Rightarrow> T" and tys: "(e, \<tau>) \<turnstile> s : A" by auto
  have nr: "no_redex u" "\<not> is_Abs u" "no_redex s" using appR.prems(2) by auto
  from appR.IH[OF tys nr(3)] have IH: "lsize e \<tau> t A = lsize e \<tau> s A" "no_redex t" by auto
  have "spine_type e \<tau> u = A \<Rightarrow> T" using spine_type_typing[OF tyu nr(1,2)] .
  then show ?case using IH nr by simp
next
  case (abs s t)
  from abs.prems obtain A U where T: "T = A \<Rightarrow> U" and ty: "(e\<langle>0:A\<rangle>, \<tau>) \<turnstile> s : U" by auto
  from abs.IH[OF ty] abs.prems(2) show ?case by (simp add: T)
qed

lemma lsize_\<beta>\<eta>cl:
  assumes "\<beta>\<eta>cl s t" "(e, \<tau>) \<turnstile> s : T" "no_redex s"
  shows "lsize e \<tau> t T = lsize e \<tau> s T \<and> no_redex t"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case (step t u)
  have "(e, \<tau>) \<turnstile> t : T" using subject_reduction_\<beta>\<eta>[OF step.hyps(1) assms(2)] .
  moreover from step.IH have "no_redex t" by simp
  moreover from this step.hyps(2) have "t \<rightarrow>\<^sub>\<eta> u" by (auto dest: no_redex_no_beta)
  ultimately show ?case using lsize_eta step.IH by metis
qed (simp add: assms(3))

lemma lsize_equiv:
  assumes "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t" "(e, \<tau>) \<turnstile> s : T" "(e, \<tau>) \<turnstile> t : T" "no_redex s" "no_redex t"
  shows "lsize e \<tau> s T = lsize e \<tau> t T"
proof -
  from normal_form_ex[OF assms(2)] obtain n where n: "\<beta>\<eta>cl s n" "normal n" by blast
  have "t \<equiv>\<^sub>\<beta>\<^sub>\<eta> n" using assms(1) n(1) by (meson \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
  then have "\<beta>\<eta>cl t n" using n(2) by (rule equiv_\<beta>\<eta>cl_normal)
  with n(1) show ?thesis using lsize_\<beta>\<eta>cl assms(2-5) by metis
qed

lemma lsize_Abs_m: "length Ts = m \<Longrightarrow> lsize e \<tau> (Abs_m m t) (Ts \<Rrightarrow> T) = lsize (env_ext e Ts) \<tau> t T"
proof (induction Ts arbitrary: e m)
  case (Cons U Ts)
  then show ?case by (cases m) auto
qed simp


subsection \<open>Atoms applied to arguments\<close>

lemma hsize_atom_apps:
  assumes "is_atom h" "(e, \<tau>) \<turnstile> h : Ts \<Rrightarrow> T" "(e, \<tau>) \<tturnstile> ws : Ts" "\<forall>w\<in>set ws. no_redex w"
  shows "hsize e \<tau> (h \<degree>\<degree> ws) = Suc (\<Sum>i<length ws. lsize e \<tau> (ws ! i) (Ts ! i))"
  using assms(2-4)
proof (induction ws arbitrary: Ts T rule: rev_induct)
  case Nil
  then show ?case using assms(1) by (auto simp: is_atom_def)
next
  case (snoc w ws)
  from snoc.prems(2) obtain Us U where Ts: "Ts = Us @ [U]" "(e, \<tau>) \<tturnstile> ws : Us" "(e, \<tau>) \<turnstile> w : U"
    by (elim types_snocE)
  have lenUs: "length Us = length ws" using typings_length[OF Ts(2)] .
  have h: "(e, \<tau>) \<turnstile> h : Us \<Rrightarrow> U \<Rightarrow> T" using snoc.prems(1) Ts(1) by simp
  have "(e, \<tau>) \<turnstile> h \<degree>\<degree> ws : U \<Rightarrow> T" using list_app_typeI[OF h Ts(2)] .
  moreover have "no_redex (h \<degree>\<degree> ws)" "\<not> is_Abs (h \<degree>\<degree> ws)"
    using snoc.prems(3) assms(1) by (simp_all add: no_redex_atom_apps is_Abs_atom_apps)
  ultimately have sp: "spine_type e \<tau> (h \<degree>\<degree> ws) = U \<Rightarrow> T" by (rule spine_type_typing)
  have IH: "hsize e \<tau> (h \<degree>\<degree> ws) = Suc (\<Sum>i<length ws. lsize e \<tau> (ws ! i) (Us ! i))"
    using snoc.IH[OF h Ts(2)] snoc.prems(3) by simp
  have "(\<Sum>i<length (ws @ [w]). lsize e \<tau> ((ws @ [w]) ! i) (Ts ! i)) =
      (\<Sum>i<length ws. lsize e \<tau> (ws ! i) (Us ! i)) + lsize e \<tau> w U"
    using lenUs by (simp add: Ts(1) nth_append)
  with IH sp show ?case by simp
qed

lemma lsize_atom_apps:
  assumes "is_atom h" "(e, \<tau>) \<turnstile> h : Ts \<Rrightarrow> T" "(e, \<tau>) \<tturnstile> ws : Ts" "\<forall>w\<in>set ws. no_redex w"
  shows "lsize e \<tau> (h \<degree>\<degree> ws) T = Suc (\<Sum>i<length ws. lsize e \<tau> (ws ! i) (Ts ! i)) + (tsize T - 1)"
  using hsize_atom_apps[OF assms] is_Abs_atom_apps[OF assms(1)] by (simp add: lsize_nonAbs)

end
