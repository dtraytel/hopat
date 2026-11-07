section \<open>Inversion of \<open>\<alpha>\<beta>\<eta>\<close>-Equivalence\<close>

theory Pure_Inversion
  imports Pure_Normal
begin

text \<open>
  Equivalent abstractions have equivalent bodies, and equivalent applications with atomic heads
  have the same head and equivalent arguments. Both follow from the Church--Rosser property.
\<close>

subsection \<open>Lifting\<close>

lemma alpha_lift: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> lift s k \<rightarrow>\<^sub>\<alpha> lift t k"
  by (induction arbitrary: k set: alpha) auto

lemma subst_lift_Bound: "0 \<le> k \<Longrightarrow> (lift s (k + 1))[Bound k/k] = s"
proof (induction s arbitrary: k)
  case (Abs a T s)
  then show ?case using Abs.IH[of "k + 1"] by (simp add: integer_arith)
qed (auto simp: subst_Bound integer_arith)

context signature
begin

lemma wt_lift: "wt s \<Longrightarrow> 0 \<le> k \<Longrightarrow> wt (lift s k)"
  unfolding wt_def by (blast intro: lift_type)

lemma conv_lift: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> 0 \<le> k \<Longrightarrow> lift s k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift t k"
proof -
  assume k: "0 \<le> k"
  have step: "conv_step s t \<Longrightarrow> conv_step (lift s k) (lift t k)" for s t
    unfolding conv_step_def using alpha_lift lift_preserves_beta[OF _ k] eta_lift[OF _ k] wt_lift[OF _ k] by blast
  show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> lift s k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift t k"
    unfolding conv_def by (induction rule: equivclp_induct) (auto intro: equivclp_into_equivclp step)
qed

lemma typing_unique: "e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t : T' \<Longrightarrow> T = T'"
proof (induction arbitrary: T' rule: typing.induct)
  case (App e s T U t)
  from App.prems obtain T0 where "e \<turnstile> s : T0 \<rightarrow>\<^sub>T T'" "e \<turnstile> t : T0" by auto
  with App.IH show ?case by blast
next
  case (Abs T e t U a)
  from Abs.prems obtain U' where "T' = T \<rightarrow>\<^sub>T U'" "e\<langle>0:T\<rangle> \<turnstile> t : U'" by auto
  with Abs.IH show ?case by simp
qed auto


subsection \<open>Abstractions\<close>

text \<open>A term of a function type is equivalent to its body applied to a new bound variable:\<close>

lemma conv_Abs_body:
  assumes "e \<turnstile> Abs a T s : T \<rightarrow>\<^sub>T U"
  shows "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (Abs a T s) 0 $ Bound 0"
proof -
  from assms have "e\<langle>0:T\<rangle> \<turnstile> lift (Abs a T s) 0 $ Bound 0 : U" by (auto intro!: lift_type)
  then have "wt (lift (Abs a T s) 0 $ Bound 0)" by (auto simp: wt_def)
  moreover have "lift (Abs a T s) 0 $ Bound 0 \<rightarrow>\<^sub>\<beta> s"
    using beta.beta[of a T "lift s 1" "Bound 0"] subst_lift_Bound[of 0 s] by simp
  ultimately have "lift (Abs a T s) 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
    by (intro beta_eta_conv r_into_rtranclp) simp_all
  then show ?thesis by (rule conv_sym)
qed

theorem conv_Abs_inv:
  assumes "e \<turnstile> Abs a T s : V" "e \<turnstile> Abs b T' t : V" "Abs a T s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs b T' t"
  shows "T' = T" and "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
proof -
  from assms(1) obtain U where V: "V = T \<rightarrow>\<^sub>T U" and ts: "e\<langle>0:T\<rangle> \<turnstile> s : U" by auto
  from assms(2) obtain U' where V': "V = T' \<rightarrow>\<^sub>T U'" and tt: "e\<langle>0:T'\<rangle> \<turnstile> t : U'" by auto
  from V V' show TT: "T' = T" by simp
  have ty: "e\<langle>0:T\<rangle> \<turnstile> lift (Abs a T s) 0 $ Bound 0 : U" "e\<langle>0:T\<rangle> \<turnstile> lift (Abs b T' t) 0 $ Bound 0 : U"
    using assms(1,2) V V' TT by (auto intro!: lift_type)
  have "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (Abs a T s) 0 $ Bound 0"
    using conv_Abs_body assms(1) V by blast
  also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (Abs b T' t) 0 $ Bound 0"
  proof (rule conv_App[OF _ _ conv_lift[OF assms(3) order_refl] conv_refl])
    show "wt (lift (Abs a T s) 0 $ Bound 0)" "wt (lift (Abs b T' t) 0 $ Bound 0)"
      using ty unfolding wt_def by blast+
  qed
  also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
    using conv_Abs_body[of e b T' t U'] assms(2) V' by (blast intro: conv_sym)
  finally show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" .
qed

end


subsection \<open>Applications with atomic heads\<close>

lemma sup_beta_eta_App_cases:
  assumes "sup beta eta (r $ s) u" "\<not> is_Abs r"
  shows "(\<exists>r'. sup beta eta r r' \<and> u = r' $ s) \<or> (\<exists>s'. sup beta eta s s' \<and> u = r $ s')"
proof -
  from assms(1) have "beta (r $ s) u \<or> eta (r $ s) u" by simp
  then show ?thesis
  proof
    assume "beta (r $ s) u"
    then show ?thesis using assms(2) by (cases rule: beta.cases) auto
  next
    assume "eta (r $ s) u"
    then show ?thesis by (cases rule: eta.cases) auto
  qed
qed

lemma not_is_Abs_atom_apps: "atom h \<Longrightarrow> \<not> is_Abs (h \<degree>\<degree> ss)"
  by (cases ss rule: rev_cases) (auto elim: atom.elims)

lemma beta_eta_atom_apps_step:
  "sup beta eta (h \<degree>\<degree> ss) u \<Longrightarrow> atom h \<Longrightarrow>
    \<exists>ss'. u = h \<degree>\<degree> ss' \<and> list_all2 (sup beta eta)\<^sup>*\<^sup>* ss ss'"
proof (induction ss arbitrary: u rule: rev_induct)
  case Nil
  then show ?case by (cases h) (auto elim: beta.cases eta.cases)
next
  case (snoc s ss)
  have hs: "h \<degree>\<degree> (ss @ [s]) = (h \<degree>\<degree> ss) $ s" by simp
  from sup_beta_eta_App_cases[OF snoc.prems(1)[unfolded hs] not_is_Abs_atom_apps[OF snoc.prems(2)]]
  show ?case
  proof (elim disjE exE conjE)
    fix u1 assume u1: "sup beta eta (h \<degree>\<degree> ss) u1" "u = u1 $ s"
    from snoc.IH[OF u1(1) snoc.prems(2)] obtain ss' where A: "u1 = h \<degree>\<degree> ss'"
      and B: "list_all2 (sup beta eta)\<^sup>*\<^sup>* ss ss'"
      by blast
    have C: "list_all2 (sup beta eta)\<^sup>*\<^sup>* [s] [s]" by simp
    show ?thesis
    proof (rule exI[of _ "ss' @ [s]"], rule conjI)
      show "u = h \<degree>\<degree> (ss' @ [s])" using A u1(2) by simp
    qed (rule list_all2_appendI[OF B C])
  next
    fix s' assume s': "sup beta eta s s'" "u = (h \<degree>\<degree> ss) $ s'"
    have B: "list_all2 (sup beta eta)\<^sup>*\<^sup>* ss ss" by (simp add: list_all2_refl)
    have C: "list_all2 (sup beta eta)\<^sup>*\<^sup>* [s] [s']" using s'(1) by (simp add: r_into_rtranclp)
    show ?thesis
    proof (rule exI[of _ "ss @ [s']"], rule conjI)
      show "u = h \<degree>\<degree> (ss @ [s'])" using s'(2) by simp
    qed (rule list_all2_appendI[OF B C])
  qed
qed

lemma beta_eta_atom_apps:
  "(sup beta eta)\<^sup>*\<^sup>* (h \<degree>\<degree> ss) u \<Longrightarrow> atom h \<Longrightarrow>
    \<exists>ss'. u = h \<degree>\<degree> ss' \<and> list_all2 (sup beta eta)\<^sup>*\<^sup>* ss ss'"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by (auto simp: list_all2_refl)
next
  case (step u v)
  then obtain ss' where u: "u = h \<degree>\<degree> ss'" "list_all2 (sup beta eta)\<^sup>*\<^sup>* ss ss'" by blast
  from beta_eta_atom_apps_step[OF step(2)[unfolded u(1)] step(4)] obtain ss'' where
    "v = h \<degree>\<degree> ss''" "list_all2 (sup beta eta)\<^sup>*\<^sup>* ss' ss''"
    by blast
  with u(2) show ?case by (blast intro: list_all2_trans rtranclp_trans)
qed

lemma aconv_atom_apps:
  "atom h \<Longrightarrow> atom h' \<Longrightarrow> aconv_term (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) \<Longrightarrow>
    h = h' \<and> list_all2 aconv_term ss ts"
proof (induction ss arbitrary: ts rule: rev_induct)
  case Nil
  then show ?case by (cases ts rule: rev_cases) (cases h; cases h'; auto)+
next
  case (snoc s ss)
  show ?case
  proof (cases ts rule: rev_cases)
    case Nil
    with snoc.prems show ?thesis by (cases h'; cases h) auto
  next
    case (snoc ts' t)
    with snoc.prems snoc.IH[of ts'] show ?thesis by (auto simp: list_all2_appendI)
  qed
qed

context signature
begin

lemma wt_apps_headD: "wt (h \<degree>\<degree> ss) \<Longrightarrow> wt h"
  by (induction ss arbitrary: h) (auto dest: wt_AppD)

lemma wt_apps_args: "wt (h \<degree>\<degree> ss) \<Longrightarrow> s \<in> set ss \<Longrightarrow> wt s"
proof (induction ss arbitrary: h)
  case (Cons s0 ss)
  then show ?case using wt_apps_headD[of "h $ s0" ss] by (auto dest: wt_AppD)
qed simp

theorem conv_atom_apps_inv:
  assumes "atom h" "atom h'" "wt (h \<degree>\<degree> ss)" "h \<degree>\<degree> ss \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> h' \<degree>\<degree> ts"
  shows "h = h'" and "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) ss ts"
proof -
  obtain u v where uv: "(sup beta eta)\<^sup>*\<^sup>* (h \<degree>\<degree> ss) u" "(sup beta eta)\<^sup>*\<^sup>* (h' \<degree>\<degree> ts) v" "aconv_term u v"
    using church_rosser[OF assms(3,4)] by blast
  from beta_eta_atom_apps[OF uv(1) assms(1)] obtain ss' where
    ss': "u = h \<degree>\<degree> ss'" "list_all2 (sup beta eta)\<^sup>*\<^sup>* ss ss'" by blast
  from beta_eta_atom_apps[OF uv(2) assms(2)] obtain ts' where
    ts': "v = h' \<degree>\<degree> ts'" "list_all2 (sup beta eta)\<^sup>*\<^sup>* ts ts'" by blast
  from aconv_atom_apps[OF assms(1,2) uv(3)[unfolded ss'(1) ts'(1)]]
  have hh: "h = h'" and a: "list_all2 aconv_term ss' ts'" by simp_all
  then show "h = h'" by simp
  have wtt: "wt (h' \<degree>\<degree> ts)" using wt_conv[OF assms(4)] assms(3) by simp
  from ss'(2) a ts'(2) have "list_all2 (\<lambda>s t. (sup beta eta)\<^sup>*\<^sup>* s t) ss ss' \<and>
      list_all2 aconv_term ss' ts' \<and> list_all2 (\<lambda>s t. (sup beta eta)\<^sup>*\<^sup>* s t) ts ts'"
    by simp
  then have "length ss = length ts \<and> (\<forall>i<length ss. (sup beta eta)\<^sup>*\<^sup>* (ss ! i) (ss' ! i) \<and>
      aconv_term (ss' ! i) (ts' ! i) \<and> (sup beta eta)\<^sup>*\<^sup>* (ts ! i) (ts' ! i))"
    by (auto simp: list_all2_conv_all_nth)
  moreover have "wt (ss ! i)" "wt (ts ! i)" if "i < length ss" "length ss = length ts" for i
    using wt_apps_args[OF assms(3)] wt_apps_args[OF wtt] that by auto
  ultimately have len: "length ss = length ts"
    and r: "\<And>i. i < length ss \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (ss ! i) (ss' ! i) \<and>
      aconv_term (ss' ! i) (ts' ! i) \<and> (sup beta eta)\<^sup>*\<^sup>* (ts ! i) (ts' ! i) \<and> wt (ss ! i) \<and> wt (ts ! i)"
    by blast+
  have "ss ! i \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ts ! i" if "i < length ss" for i
  proof -
    note ri = r[OF that]
    have "ss ! i \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ss' ! i" using ri by (blast intro: beta_eta_conv)
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ts' ! i" using ri by (blast intro: aconv_term_conv)
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ts ! i" using ri by (blast intro: beta_eta_conv conv_sym)
    finally show ?thesis .
  qed
  with len show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) ss ts" by (simp add: list_all2_conv_all_nth)
qed

end

end
