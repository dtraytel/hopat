section \<open>Auxiliary Functions of Matching\<close>

theory Match_Base
  imports Match_Types Pattern_Normal
begin

text \<open>
  The semantics of the auxiliary functions of \<open>Pattern.match\<close>: \<^const>\<open>mapbnd\<close> renames loose
  bound variables, \<^const>\<open>red\<close> \<open>\<beta>\<close>-reduces an abstraction applied to bound variables,
  \<^const>\<open>loose_bnos\<close> lists the loose bound variables, \<^const>\<open>eta_contract\<close> \<open>\<eta>\<close>-reduces,
  \<^const>\<open>fastype_of\<close> computes the type of a well-typed term, and \<^const>\<open>subst_type\<close>
  instantiates a type by \<^const>\<open>mtinst\<close>.
\<close>

context pure_sig_gen
begin

subsection \<open>Renaming of loose bound variables\<close>

lemma mapbnd_rename:
  "(\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t (k + d) \<Longrightarrow> ok (f k) (g k)) \<Longrightarrow> ok (mapbnd f d t) (rename g d t)"
proof (induction t arbitrary: d)
  case (Bound i)
  show ?case
  proof (cases "i < d")
    case False
    then have "ok (f (i - d)) (g (i - d))" using Bound[of "i - d"] by (simp add: integer_arith)
    with False show ?thesis by (simp add: return_def)
  qed (simp add: return_def)
next
  case (Abs a T t)
  have "ok (mapbnd f (d + 1) t) (rename g (d + 1) t)"
    using Abs.prems by (intro Abs.IH) (simp add: algebra_simps)
  then show ?case by (simp add: return_def)
next
  case (App s t)
  then show ?case by (simp add: return_def)
qed (simp_all add: return_def)

lemma ok_mapbnd_loose:
  "ok (mapbnd f d t) t' \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar1 t (k + d) \<Longrightarrow> \<exists>j. ok (f k) j"
proof (induction t arbitrary: d t')
  case (Bound i)
  then show ?case by (auto split: if_splits)
next
  case (Abs a T t)
  then show ?case by (auto simp: algebra_simps)
next
  case (App s t)
  then show ?case by auto
qed simp_all

lemma ok_mapbnd_eq:
  "ok (mapbnd f d t) t' \<Longrightarrow> ok (mapbnd f d t) (rename (\<lambda>k. SOME j. ok (f k) j) d t)"
  by (rule mapbnd_rename) (meson ok_mapbnd_loose someI_ex)

lemma ok_mapbnd_nth:
  assumes "ok (mapbnd (nth js) d t) t'"
  shows "t' = rename (bren js) d t"
proof -
  have "t' = rename (\<lambda>k. SOME j. ok (nth js k) j) d t"
    using ok_mapbnd_eq[OF assms] assms by simp
  also have "\<dots> = rename (bren js) d t"
  proof (rule rename_cong)
    fix k assume k: "0 \<le> k" "loose_bvar1 t (k + d)"
    then obtain j where "ok (nth js k) j" using ok_mapbnd_loose[OF assms] by blast
    then show "(SOME j. ok (nth js k) j) = bren js k"
      by (simp add: ok_nth bren_nth)
  qed
  finally show ?thesis .
qed

lemma ok_mapbnd_idx:
  assumes "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t (k + d) \<Longrightarrow> k \<in> set is"
  shows "ok (mapbnd (idx is) d t) (rename (bidx is) d t)"
  by (rule mapbnd_rename) (simp add: ok_idx_bidx assms)


subsection \<open>Reduction of abstractions applied to bound variables\<close>

lemma red_beta:
  "ok (red t is js) u \<Longrightarrow> \<forall>i\<in>set is \<union> set js. 0 \<le> i \<Longrightarrow>
    rename (bren js) 0 t \<degree>\<degree> map Bound is \<rightarrow>\<^sub>\<beta>\<^sup>* u"
proof (induction t "is" js arbitrary: u rule: red.induct)
  case (1 a T s i "is" js)
  have nn: "nonneg (bren js)" using "1.prems"(2) by (intro nonneg_bren) simp
  have i: "0 \<le> i" using "1.prems"(2) by simp
  have "rename (bren js) 0 (Abs a T s) \<degree>\<degree> map Bound (i # is) =
      (Abs a T (rename (bren js) (0 + 1) s) $ Bound (i + 0)) \<degree>\<degree> map Bound is"
    by simp
  also have "\<dots> \<rightarrow>\<^sub>\<beta> (rename (bren js) (0 + 1) s)[Bound (i + 0)/0] \<degree>\<degree> map Bound is"
    by (intro apps_preserves_beta) (rule beta.beta)
  also have "(rename (bren js) (0 + 1) s)[Bound (i + 0)/0] = rename (bren (i # js)) 0 s"
    using subst_rename[of 0 i "bren js" s] nn i by (simp add: bren_Cons)
  finally have st: "rename (bren js) 0 (Abs a T s) \<degree>\<degree> map Bound (i # is) \<rightarrow>\<^sub>\<beta>
      rename (bren (i # js)) 0 s \<degree>\<degree> map Bound is" .
  have "rename (bren (i # js)) 0 s \<degree>\<degree> map Bound is \<rightarrow>\<^sub>\<beta>\<^sup>* u"
    using "1.prems" by (intro "1.IH") auto
  with st show ?case by (rule converse_rtranclp_into_rtranclp)
next
  case (2 t)
  have "bren [] = (\<lambda>k. k)" by (rule ext) simp
  with 2 show ?case by (simp add: rename_id)
qed (auto simp: app_apps ok_nth bren_nth dest!: ok_mapbnd_nth)


subsection \<open>Loose bound variables\<close>

lemma set_add_loose_bnos:
  "0 \<le> lev \<Longrightarrow> set (add_loose_bnos t lev js) = set js \<union> {k. 0 \<le> k \<and> loose_bvar1 t (k + lev)}"
proof (induction t arbitrary: lev js)
  case (Bound i)
  then show ?case by (auto simp: integer_arith)
next
  case (Abs a T t)
  then show ?case by (auto simp: algebra_simps)
next
  case (App s t)
  then show ?case by auto
qed simp_all

lemma set_loose_bnos: "set (loose_bnos t) = {k. 0 \<le> k \<and> loose_bvar1 t k}"
  using set_add_loose_bnos[of 0 t "[]"] by (simp add: loose_bnos_def)

lemma subset_iff_set: "subset xs ys \<longleftrightarrow> set xs \<subseteq> set ys"
  by (auto simp: subset_def list_all_iff)

lemma is_open_closed: "is_open t \<longleftrightarrow> \<not> closed t"
  by (simp add: is_open_def closed_def)


subsection \<open>\<open>\<eta>\<close>-contraction\<close>

text \<open>Equivalent terms have the same type:\<close>

lemma conv_typing_eq: "e \<turnstile> s : S \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> S = T"
proof -
  assume s: "e \<turnstile> s : S" and t: "e \<turnstile> t : T" and c: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  obtain u v where uv: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* v" "aconv_term u v"
    using church_rosser[OF _ c] s by (auto simp: wt_def)
  have "e \<turnstile> v : S" using typing_aconv[OF uv(3) subject_reduction_reds[OF uv(1) s]] .
  moreover have "e \<turnstile> v : T" using subject_reduction_reds[OF uv(2) t] .
  ultimately show ?thesis by (rule typing_unique)
qed

lemma typing_lift0D: "e\<langle>0:U\<rangle> \<turnstile> lift s 0 : T \<Longrightarrow> e \<turnstile> s : T"
  using strengthening[of "e\<langle>0:U\<rangle>" "lift s 0" T e 0 U s] by simp


subsection \<open>Instantiation of types\<close>

lemma mtinst_empty: "vt_is_empty tye \<Longrightarrow> mtinst tye = TVar"
  by (intro ext) (simp add: mtinst_def vt_is_empty_lookup)

lemma ok_subst_type: "ok (subst_type tye T) T' \<Longrightarrow> T' = tsubst (mtinst tye) T"
proof -
  have "ok (subst_type_aux tye T) T' \<Longrightarrow> T' = tsubst (mtinst tye) T" for T'
  proof (induction tye T arbitrary: T' rule: subst_type_aux.induct)
    case (1 tye a Ts)
    then obtain Ts' where "list_all2 (\<lambda>x y. ok (subst_type_aux tye x) y) Ts Ts'" "T' = Type a Ts'"
      by (auto simp: ok_mapM)
    with "1.IH" show ?case by (auto simp: list_all2_conv_all_nth intro: nth_equalityI)
  next
    case (2 tye v S)
    then show ?case by (auto simp: ok_type_lookup mtinst_def split: option.splits)
  qed simp_all
  then show "ok (subst_type tye T) T' \<Longrightarrow> T' = tsubst (mtinst tye) T"
    by (auto simp: subst_type_def mtinst_empty split: if_splits)
qed


subsection \<open>Certified types\<close>

lemma cert_typ_tsubst_tvars:
  "cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow> (v, S) \<in> tvars T \<Longrightarrow> cert_typ alg ar (\<rho> v S)"
  by (induction T) (auto simp: cert_typ_def)

definition tye_cert :: "tyenv \<Rightarrow> bool" where
  "tye_cert tye \<longleftrightarrow> (\<forall>v S U. vt_lookup tye v = Some (S, U) \<longrightarrow> cert_typ alg ar U)"

lemma cert_inst_mtinst: "tye_cert tye \<Longrightarrow> cert_inst (mtinst tye)"
  by (auto simp: cert_inst_def tye_cert_def mtinst_def cert_typ_TVar split: option.splits)

lemma typ_match_cert:
  assumes "ok (typ_match alg T U tye) tye'" "wft ar T" "wft ar U" "cert_typ alg ar U" "tye_cert tye"
  shows "tye_cert tye'"
  unfolding tye_cert_def
proof (intro allI impI)
  fix v S U' assume b: "vt_lookup tye' v = Some (S, U')"
  note s = typ_match_sound[OF assms(2,3) assms(1)[folded return_def]]
  show "cert_typ alg ar U'"
  proof (cases "vt_lookup tye v")
    case None
    with s(4)[OF b] have "(v, S) \<in> tvars T" by blast
    with cert_typ_tsubst_tvars[where \<rho> = "mtinst tye'" and T = T and v = v and S = S] assms(4) s(2) b
    show ?thesis
      by (simp add: mtinst_def)
  next
    case (Some x)
    with s(1) b have "vt_lookup tye v = Some (S, U')" by (cases x, cases v) (auto simp: textends_def)
    with assms(5) show ?thesis unfolding tye_cert_def by (cases v) auto
  qed
qed

end

end
