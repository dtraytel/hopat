section \<open>The Pattern Test\<close>

theory Match_Pattern
  imports Pattern_Exceptions
begin

context csig
begin

text \<open>
  \<^const>\<open>pattern\<close> (\<open>Pattern.pattern\<close>) decides whether a term is a higher-order pattern. It agrees
  with the inductive characterization \<^const>\<open>ppat\<close> on proper terms without \<open>\<beta>\<close>-redexes; on
  terms with \<open>\<beta>\<close>-redexes it does not inspect the heads of redexes.
\<close>

fun rfree :: "pterm \<Rightarrow> bool" where
  "rfree (Abs _ _ t) \<longleftrightarrow> rfree t"
| "rfree (s $ t) \<longleftrightarrow> \<not> is_Abs s \<and> rfree s \<and> rfree t"
| "rfree _ \<longleftrightarrow> True"

lemma rfree_list_comb:
  "rfree (list_comb h ts) \<longleftrightarrow> rfree h \<and> (\<forall>t\<in>set ts. rfree t) \<and> (ts \<noteq> [] \<longrightarrow> \<not> is_Abs h)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma has_duplicates_Bounds: "has_duplicates_by aconv_term (map Bound is) \<longleftrightarrow> \<not> distinct is"
  by (induction "is") (auto simp: list_ex_iff)

lemma pattern_Abs: "pattern (Abs a T t) \<longleftrightarrow> pattern t"
  by (subst pattern.simps) simp

lemma pattern_list_comb:
  assumes "\<not> (\<exists>f u. h = f $ u)" "\<not> is_Abs (list_comb h ts)"
  shows "pattern (list_comb h ts) \<longleftrightarrow>
    (if is_Var h then list_all is_Bound ts \<and> \<not> has_duplicates_by aconv_term ts else list_all pattern ts)"
proof -
  have nonAbs: "pattern t = (let (head, args) = strip_comb t in
      if is_Var head then list_all is_Bound args \<and> \<not> has_duplicates_by aconv_term args
      else list_all pattern args)" if "\<not> is_Abs t" for t
    using that by (subst pattern.simps) (cases t; simp)
  have s: "strip_comb (list_comb h ts) = (h, ts)" by (rule strip_comb_list_comb_eq[OF assms(1)])
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
  have h: "\<not> (\<exists>f u. h = f $ u)" "\<not> is_Var h" "\<not> is_Abs h" using ppat_rigid(1) by (auto simp: is_rigid_def)
  have "\<not> is_Abs (list_comb h ts)" using h(3) by (cases ts rule: rev_cases) (simp_all add: list_comb_def)
  with pattern_list_comb[OF h(1)] h(2) ppat_rigid(2) show ?case by (simp add: list_all_iff)
next
  case (ppat_flex "is" x T)
  have "\<not> is_Abs (list_comb (Var x T) (map Bound is))"
    by (cases "is" rule: rev_cases) (simp_all add: list_comb_def)
  with pattern_list_comb[of "Var x T" "map Bound is"] ppat_flex show ?case
    by (simp add: app_list_comb has_duplicates_Bounds list_all_iff)
qed

theorem pattern_ppat: "pattern t \<Longrightarrow> proper t \<Longrightarrow> rfree t \<Longrightarrow> ppat t"
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
    have t: "t = list_comb h ts" by (rule strip_comb_list_comb[OF s])
    have h: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF s])
    have sz: "size u < size t" if "u \<in> set ts" for u
      using strip_comb_acc_size[of t "[]" h ts u] s that False by (cases t) (auto simp: strip_comb_def)
    have pr: "proper h" "\<forall>u\<in>set ts. proper u" using less.prems(2) by (simp_all add: t proper_list_comb)
    have rf: "rfree h" "\<forall>u\<in>set ts. rfree u" "ts \<noteq> [] \<longrightarrow> \<not> is_Abs h"
      using less.prems(3) by (simp_all add: t rfree_list_comb)
    have pat: "if is_Var h then list_all is_Bound ts \<and> \<not> has_duplicates_by aconv_term ts else list_all pattern ts"
      using less.prems(1) pattern_list_comb[OF h] False by (simp add: t)
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain x T where hx: "h = Var x T" by (cases h) auto
      from True pat obtain "is" where ts: "ts = map Bound is"
        using all_Bound_map by auto
      have "distinct is" using True pat by (simp add: ts has_duplicates_Bounds)
      moreover have "\<forall>i\<in>set is. 0 \<le> i" using pr(2) by (simp add: ts)
      ultimately show ?thesis using ppat_flex[of "is" x T] by (simp add: t hx ts app_list_comb)
    next
      case False
      have "is_rigid h"
      proof (cases h)
        case (Abs a T u)
        with t \<open>\<not> is_Abs t\<close> rf(3) show ?thesis by (cases ts) auto
      next
        case (Bound i)
        with pr(1) show ?thesis by (simp add: is_rigid_def)
      qed (use False h in \<open>auto simp: is_rigid_def\<close>)
      moreover have "\<forall>u\<in>set ts. ppat u"
        using less.IH sz pr(2) rf(2) pat False by (auto simp: list_all_iff)
      ultimately show ?thesis by (simp add: t ppat_rigid)
    qed
  qed
qed

corollary pattern_iff_ppat: "proper t \<Longrightarrow> rfree t \<Longrightarrow> pattern t \<longleftrightarrow> ppat t"
  using pattern_ppat ppat_pattern by blast

end

end
