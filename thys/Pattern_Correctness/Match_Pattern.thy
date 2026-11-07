section \<open>The Pattern Test\<close>

theory Match_Pattern
  imports Match_Complete
begin

text \<open>
  \<^const>\<open>pattern\<close> (\<open>Pattern.pattern\<close>) decides whether a term is a higher-order pattern: it agrees
  with the inductive characterization \<^const>\<open>ppat\<close> on terms without \<open>\<beta>\<close>-redexes; on terms with
  \<open>\<beta>\<close>-redexes it does not inspect the heads of redexes.
\<close>

context pure_sig
begin

lemma has_duplicates_Bounds: "has_duplicates_by aconv_term (map Bound is) \<longleftrightarrow> \<not> distinct is"
  by (induction "is") (auto simp: list_ex_iff)

lemma pattern_Abs: "pattern (Abs a T t) \<longleftrightarrow> pattern t"
  by (subst pattern.simps) simp

lemma pattern_apps:
  assumes "\<not> (\<exists>f u. h = f $ u)" "\<not> is_Abs (h \<degree>\<degree> ts)"
  shows "pattern (h \<degree>\<degree> ts) \<longleftrightarrow>
    (if is_Var h then list_all is_Bound ts \<and> \<not> has_duplicates_by aconv_term ts else list_all pattern ts)"
proof -
  have nonAbs: "pattern t = (let (head, args) = strip_comb t in
      if is_Var head then list_all is_Bound args \<and> \<not> has_duplicates_by aconv_term args
      else list_all (\<lambda>u. pattern u) args)" if "\<not> is_Abs t" for t
    using that by (subst pattern.simps) (cases t; simp)
  have s: "strip_comb (h \<degree>\<degree> ts) = (h, ts)" by (rule strip_comb_atom_apps[OF assms(1)])
  show ?thesis using nonAbs[OF assms(2)] by (simp add: s)
qed

lemma all_Bound_map: "list_all is_Bound ts \<Longrightarrow> \<exists>is. ts = map Bound is"
proof (induction ts)
  case (Cons t ts)
  then obtain i "is" where "t = Bound i" "ts = map Bound is" by (cases t) auto
  then show ?case by (intro exI[of _ "i # is"]) simp
qed simp

theorem ppat_pattern: "ppat t \<Longrightarrow> pattern t"
proof (induction rule: ppat.induct)
  case (ppat_Abs t a T)
  then show ?case by (simp add: pattern_Abs)
next
  case (ppat_rigid h ts)
  have h: "\<not> (\<exists>f u. h = f $ u)" "\<not> is_Var h" "\<not> is_Abs h" using ppat_rigid(1) by (cases h; simp)+
  have "\<not> is_Abs (h \<degree>\<degree> ts)" using h(3) by (simp add: is_Abs_apps)
  with pattern_apps[OF h(1)] h(2) ppat_rigid(2) show ?case by (simp add: list_all_iff)
next
  case (ppat_flex "is" x T)
  have "\<not> is_Abs (Var x T \<degree>\<degree> map Bound is)" by (simp add: is_Abs_apps)
  with pattern_apps[of "Var x T" "map Bound is"] ppat_flex show ?case
    by (simp add: app_apps has_duplicates_Bounds list_all_iff)
qed

theorem pattern_ppat: "pattern t \<Longrightarrow> no_redex t \<Longrightarrow> ppat t"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "is_Abs t")
    case True
    then obtain a T u where t: "t = Abs a T u" by (cases t) auto
    with less show ?thesis by (auto simp: pattern_Abs intro: ppat_Abs)
  next
    case False
    obtain h ts where s: "strip_comb t = (h, ts)" by force
    have t: "t = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF s])
    have h: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF s])
    have sz: "size u < size t" if "u \<in> set ts" for u using strip_comb_arg(2)[OF s that] .
    note nr = no_redex_strip[OF less.prems(2) False s]
    have pat: "if is_Var h then list_all is_Bound ts \<and> \<not> has_duplicates_by aconv_term ts else list_all pattern ts"
      using less.prems(1) pattern_apps[OF h] False by (simp add: t)
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain x T where hx: "h = Var x T" by (cases h) auto
      from True pat obtain "is" where ts: "ts = map Bound is" using all_Bound_map by auto
      have "distinct is" using True pat by (simp add: ts has_duplicates_Bounds)
      then show ?thesis using ppat_flex[of "is" x T] by (simp add: t hx ts app_apps)
    next
      case False
      have "rigid h" using nr(1) False by (cases h) simp_all
      moreover have "\<forall>u\<in>set ts. ppat u"
        using less.IH sz nr(2) pat False by (auto simp: list_all_iff)
      ultimately show ?thesis by (simp add: t ppat_rigid)
    qed
  qed
qed

corollary pattern_iff_ppat: "no_redex t \<Longrightarrow> pattern t \<longleftrightarrow> ppat t"
  using pattern_ppat ppat_pattern by blast

end

end
