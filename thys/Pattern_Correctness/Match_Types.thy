section \<open>Correctness of Type Matching\<close>

theory Match_Types
  imports Type_Mgu
begin

text \<open>
  We verify the model of \<open>Type.typ_match\<close> (\<^const>\<open>typ_match\<close>). A type environment for
  matching is applied once, without chasing bindings (\<open>Envir.subst_type\<close>): it denotes the type
  instantiation \<^term>\<open>mtinst tye\<close>. On well-formed types with consistent sorts,
  \<^const>\<open>typ_match\<close> returns the unique extension of the environment by a well-sorted matcher, or
  fails with \<open>Type_Match\<close> if none exists.
\<close>

definition mtinst :: "tyenv \<Rightarrow> tinst" where
  "mtinst tye v S = (case vt_lookup tye v of Some (_, U) \<Rightarrow> U | None \<Rightarrow> TVar v S)"

text \<open>
  A matcher of \<open>T\<close> to \<open>U\<close> relative to \<open>tye\<close>: a well-sorted type instantiation that maps \<open>T\<close> to
  \<open>U\<close> and agrees with the bindings of \<open>tye\<close> on the type variables of \<open>T\<close>.
\<close>

definition tmatcher :: "algebra \<Rightarrow> tyenv \<Rightarrow> tinst \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tmatcher alg tye \<rho> T U \<longleftrightarrow> tsubst \<rho> T = U \<and> (\<forall>(v, S)\<in>tvars T.
    (case vt_lookup tye v of Some (S', U') \<Rightarrow> S' = S \<and> \<rho> v S = U' | None \<Rightarrow> has_sort alg (\<rho> v S) S))"

text \<open>The type variables of \<open>T\<close> have consistent sorts, also with the bindings of \<open>tye\<close>:\<close>

definition mcons :: "tyenv \<Rightarrow> ptyp \<Rightarrow> bool" where
  "mcons tye T \<longleftrightarrow> scons (tvars T) \<and> tcons tye T"

text \<open>Type matching only adds bindings:\<close>

lemma typ_match_textends: "typ_match alg T U tye = return tye' \<Longrightarrow> textends tye tye'"
proof (induction T arbitrary: U tye tye')
  case (TVar v S)
  then show ?case
    by (cases "vt_lookup tye v")
      (auto simp: type_lookup_def update_new_def vt_defined_lookup textends_def tvar_clash_def bindM_def
        return_def raise_def split: if_splits option.splits res.splits prod.splits)
next
  case (Type a Ts)
  have "textends tye tye'"
    if "set ps \<subseteq> set (zip Ts Us)" "foldM (\<lambda>(T, U) subs. typ_match alg T U subs) ps tye = return tye'"
    for ps Us tye tye'
    using that
  proof (induction ps arbitrary: tye)
    case (Cons p ps)
    obtain T1 U1 where p: "p = (T1, U1)" by force
    from Cons.prems(2) obtain tye1 where m1: "typ_match alg T1 U1 tye = return tye1"
      and m2: "foldM (\<lambda>(T, U) subs. typ_match alg T U subs) ps tye1 = return tye'"
      by (cases "typ_match alg T1 U1 tye") (auto simp: p bindM_def return_def split: option.splits res.splits)
    have "T1 \<in> set Ts" using Cons.prems(1) p by (auto dest: set_zip_leftD)
    with Type.IH m1 have "textends tye tye1" by blast
    with Cons.IH[of tye1] Cons.prems(1) m2 show ?case by (auto intro: textends_trans)
  qed (simp add: return_def)
  with Type.prems show ?case
    by (cases U) (auto simp: raise_def return_def split: if_splits)
next
  case (TFree a S)
  then show ?case by (cases U) (auto simp: raise_def return_def split: if_splits)
qed

context wf_algebra
begin

lemma map_zip_eqI: "length Ts = length Us \<Longrightarrow> (\<forall>(T, U)\<in>set (zip Ts Us). f T = U) \<Longrightarrow> map f Ts = Us"
  by (induction Ts Us rule: list_induct2) auto

definition tmsound :: "ptyp \<Rightarrow> ptyp \<Rightarrow> tyenv \<Rightarrow> tyenv \<Rightarrow> bool" where
  "tmsound T U tye tye' \<longleftrightarrow> textends tye tye' \<and> tsubst (mtinst tye') T = U \<and>
    (\<forall>(v, S)\<in>tvars T. vt_lookup tye' v \<noteq> None) \<and>
    (\<forall>v S U'. vt_lookup tye' v = Some (S, U') \<longrightarrow> vt_lookup tye v = None \<longrightarrow> (v, S) \<in> tvars T \<and> has_sort alg U' S)"

lemma mtinst_textends:
  "textends tye tye' \<Longrightarrow> \<forall>(v, S)\<in>tvars T. vt_lookup tye v \<noteq> None \<Longrightarrow> tsubst (mtinst tye') T = tsubst (mtinst tye) T"
  by (rule tsubst_cong) (auto simp: mtinst_def textends_def)

lemma tmsound_Cons:
  assumes s1: "tmsound T1 U1 tye tye1" and s2: "tmsound (Type a Ts) (Type a Us) tye1 tye'"
  shows "tmsound (Type a (T1 # Ts)) (Type a (U1 # Us)) tye tye'"
proof -
  have ex: "textends tye tye1" "textends tye1 tye'" using s1 s2 by (simp_all add: tmsound_def)
  have b1: "\<forall>(v, S)\<in>tvars T1. vt_lookup tye1 v \<noteq> None" using s1 by (simp add: tmsound_def)
  have "tsubst (mtinst tye') T1 = U1" using s1 mtinst_textends[OF ex(2) b1] by (simp add: tmsound_def)
  moreover have "\<forall>(v, S)\<in>tvars T1. vt_lookup tye' v \<noteq> None"
    using b1 ex(2) by (fastforce simp: textends_def)
  moreover have "(v, S) \<in> tvars (Type a (T1 # Ts)) \<and> has_sort alg U' S"
    if "vt_lookup tye' v = Some (S, U')" "vt_lookup tye v = None" for v S U'
  proof (cases "vt_lookup tye1 v")
    case None
    with s2 that show ?thesis by (auto simp: tmsound_def)
  next
    case (Some y)
    with ex(2) that(1) have "vt_lookup tye1 v = Some (S, U')" by (auto simp: textends_def)
    with s1 that(2) show ?thesis by (auto simp: tmsound_def)
  qed
  ultimately show ?thesis using s1 s2 textends_trans[OF ex] by (auto simp: tmsound_def)
qed

lemma typ_match_sound_aux:
  "wft ar T \<Longrightarrow> wft ar U \<Longrightarrow> typ_match alg T U tye = return tye' \<Longrightarrow> tmsound T U tye tye'"
proof (induction T arbitrary: U tye tye')
  case (TVar v S)
  show ?case
  proof (cases "vt_lookup tye v")
    case None
    with TVar.prems of_sort_sem[OF TVar.prems(2), of S] show ?thesis
      by (auto simp: type_lookup_def update_new_def vt_defined_lookup tmsound_def textends_def mtinst_def
          split: if_splits)
  next
    case (Some x)
    obtain S' U' where x: "x = (S', U')" by force
    with TVar.prems Some show ?thesis
      by (auto simp: type_lookup_def tvar_clash_def tmsound_def mtinst_def split: if_splits)
  qed
next
  case (Type a Ts)
  obtain Us where U: "U = Type a Us" and len: "length Ts = length Us"
    using Type.prems by (cases U) (auto split: if_splits simp: tarity_def raise_def return_def)
  have "tmsound (Type a (map fst ps)) (Type a (map snd ps)) tye tye'"
    if "set ps \<subseteq> set (zip Ts Us)" "foldM (\<lambda>(T, U) subs. typ_match alg T U subs) ps tye = return tye'"
    for ps tye tye'
    using that
  proof (induction ps arbitrary: tye)
    case Nil
    then show ?case by (simp add: tmsound_def return_def)
  next
    case (Cons p ps)
    obtain T1 U1 where p: "p = (T1, U1)" by force
    from Cons.prems(2) obtain tye1 where m1: "typ_match alg T1 U1 tye = return tye1"
      and m2: "foldM (\<lambda>(T, U) subs. typ_match alg T U subs) ps tye1 = return tye'"
      by (cases "typ_match alg T1 U1 tye") (auto simp: p bindM_def return_def split: option.splits res.splits)
    have mem: "(T1, U1) \<in> set (zip Ts Us)" using Cons.prems(1) p by auto
    have T1: "T1 \<in> set Ts" using mem by (rule set_zip_leftD)
    have wf: "wft ar T1" "wft ar U1"
      using Type.prems(1,2) mem by (auto simp: U dest: set_zip_leftD set_zip_rightD)
    have "tmsound T1 U1 tye tye1" by (rule Type.IH[OF T1 wf m1])
    moreover have "tmsound (Type a (map fst ps)) (Type a (map snd ps)) tye1 tye'"
      using Cons.IH[of tye1] Cons.prems(1) m2 by simp
    ultimately show ?case unfolding p by (simp add: tmsound_Cons)
  qed
  from this[of "zip Ts Us" tye tye'] Type.prems(3) len show ?case by (simp add: U)
next
  case (TFree a S)
  then show ?case
    by (cases U) (auto simp: tmsound_def raise_def return_def split: if_splits)
qed

theorem typ_match_sound:
  assumes "wft ar T" "wft ar U" "typ_match alg T U tye = return tye'"
  shows "textends tye tye'" "tsubst (mtinst tye') T = U" "\<forall>(v, S)\<in>tvars T. vt_lookup tye' v \<noteq> None"
    "\<And>v S U'. vt_lookup tye' v = Some (S, U') \<Longrightarrow> vt_lookup tye v = None \<Longrightarrow> (v, S) \<in> tvars T \<and> has_sort alg U' S"
  using typ_match_sound_aux[OF assms] by (auto simp: tmsound_def)

definition tmcomplete :: "tinst \<Rightarrow> ptyp \<Rightarrow> tyenv \<Rightarrow> tyenv \<Rightarrow> bool" where
  "tmcomplete \<rho> T tye tye' \<longleftrightarrow> textends tye tye' \<and> (\<forall>(v, S)\<in>tvars T. vt_lookup tye' v = Some (S, \<rho> v S)) \<and>
    (\<forall>v. vt_lookup tye' v \<noteq> None \<longrightarrow> vt_lookup tye v \<noteq> None \<or> (\<exists>S. (v, S) \<in> tvars T))"

text \<open>The bindings of \<open>tye\<close> agree with \<open>\<rho>\<close> on a set \<open>A\<close> of type variables, and \<open>\<rho>\<close> is well-sorted on the others:\<close>

definition tagrees :: "tyenv \<Rightarrow> tinst \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "tagrees tye \<rho> A \<longleftrightarrow> (\<forall>(v, S)\<in>A.
    (case vt_lookup tye v of Some (S', U') \<Rightarrow> S' = S \<and> \<rho> v S = U' | None \<Rightarrow> has_sort alg (\<rho> v S) S))"

lemma tmatcher_tagrees: "tmatcher alg tye \<rho> T U \<longleftrightarrow> tsubst \<rho> T = U \<and> tagrees tye \<rho> (tvars T)"
  by (simp add: tmatcher_def tagrees_def)

lemma tagrees_mono: "tagrees tye \<rho> A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> tagrees tye \<rho> B"
  unfolding tagrees_def by blast

lemma tagrees_step:
  assumes "tagrees tye \<rho> A" "scons A" "tvars T \<subseteq> A" "tmcomplete \<rho> T tye tye'"
  shows "tagrees tye' \<rho> A"
  unfolding tagrees_def
proof (intro ballI, clarify)
  fix v S assume vS: "(v, S) \<in> A"
  note c = assms(4)[unfolded tmcomplete_def]
  show "case vt_lookup tye' v of Some (S', U') \<Rightarrow> S' = S \<and> \<rho> v S = U' | None \<Rightarrow> has_sort alg (\<rho> v S) S"
  proof (cases "vt_lookup tye v")
    case (Some x)
    with c assms(1) vS show ?thesis by (auto simp: textends_def tagrees_def)
  next
    case None
    show ?thesis
    proof (cases "vt_lookup tye' v")
      case None
      with \<open>vt_lookup tye v = None\<close> assms(1) vS show ?thesis by (auto simp: tagrees_def)
    next
      case (Some y)
      with c \<open>vt_lookup tye v = None\<close> obtain S0 where "(v, S0) \<in> tvars T" by blast
      moreover from this c have "vt_lookup tye' v = Some (S0, \<rho> v S0)" by blast
      moreover have "S0 = S" using assms(2,3) vS calculation(1) unfolding scons_def by blast
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma tmcomplete_Cons:
  assumes c1: "tmcomplete \<rho> T1 tye tye1" and c2: "tmcomplete \<rho> (Type a Ts) tye1 tye'"
  shows "tmcomplete \<rho> (Type a (T1 # Ts)) tye tye'"
proof -
  have ex: "textends tye tye1" "textends tye1 tye'" using c1 c2 by (simp_all add: tmcomplete_def)
  have "\<forall>(v, S)\<in>tvars T1. vt_lookup tye' v = Some (S, \<rho> v S)"
    using c1 ex(2) unfolding tmcomplete_def textends_def by blast
  moreover have "vt_lookup tye v \<noteq> None \<or> (\<exists>S. (v, S) \<in> tvars (Type a (T1 # Ts)))"
    if "vt_lookup tye' v \<noteq> None" for v
  proof -
    from c2 that have "vt_lookup tye1 v \<noteq> None \<or> (\<exists>S. (v, S) \<in> tvars (Type a Ts))"
      by (simp add: tmcomplete_def)
    with c1 show ?thesis unfolding tmcomplete_def by auto
  qed
  ultimately show ?thesis using c2 textends_trans[OF ex] by (auto simp: tmcomplete_def)
qed

lemma typ_match_complete_aux:
  "wft ar T \<Longrightarrow> wft ar U \<Longrightarrow> scons (tvars T) \<Longrightarrow> tmatcher alg tye \<rho> T U \<Longrightarrow>
    \<exists>tye'. typ_match alg T U tye = return tye' \<and> tmcomplete \<rho> T tye tye'"
proof (induction T arbitrary: U tye)
  case (TVar v S)
  then have U: "U = \<rho> v S" by (simp add: tmatcher_def)
  show ?case
  proof (cases "vt_lookup tye v")
    case None
    with TVar.prems of_sort_sem[OF TVar.prems(2), of S] show ?thesis
      by (auto simp: U type_lookup_def update_new_def vt_defined_lookup tmcomplete_def textends_def
          tmatcher_def)
  next
    case (Some x)
    with TVar.prems show ?thesis
      by (auto simp: U type_lookup_def tmcomplete_def tmatcher_def)
  qed
next
  case (Type a Ts)
  have U: "U = Type a (map (tsubst \<rho>) Ts)" and ag: "tagrees tye \<rho> (tvars (Type a Ts))"
    using Type.prems(4) by (simp_all add: tmatcher_tagrees)
  have "\<exists>tye'. foldM (\<lambda>(T, U) subs. typ_match alg T U subs) (zip Us (map (tsubst \<rho>) Us)) tye = return tye' \<and>
      tmcomplete \<rho> (Type a Us) tye tye'"
    if "set Us \<subseteq> set Ts" "tagrees tye \<rho> (tvars (Type a Ts))" for Us tye
    using that
  proof (induction Us arbitrary: tye)
    case Nil
    then show ?case by (simp add: tmcomplete_def return_def)
  next
    case (Cons T1 Us)
    have T1: "T1 \<in> set Ts" using Cons.prems(1) by simp
    have wf: "wft ar T1" "wft ar (tsubst \<rho> T1)" using Type.prems(1,2) T1 by (auto simp: U)
    have sc: "scons (tvars T1)" using Type.prems(3) T1 by (auto simp: scons_def)
    have "tmatcher alg tye \<rho> T1 (tsubst \<rho> T1)"
      using Cons.prems(2) T1 by (auto simp: tmatcher_tagrees intro: tagrees_mono)
    from Type.IH[OF T1 wf sc this] obtain tye1 where m1: "typ_match alg T1 (tsubst \<rho> T1) tye = return tye1"
      and c1: "tmcomplete \<rho> T1 tye tye1" by blast
    have "tagrees tye1 \<rho> (tvars (Type a Ts))"
      by (rule tagrees_step[OF Cons.prems(2) Type.prems(3) _ c1]) (use T1 in auto)
    from Cons.IH[OF _ this] Cons.prems(1) obtain tye' where
      m2: "foldM (\<lambda>(T, U) subs. typ_match alg T U subs) (zip Us (map (tsubst \<rho>) Us)) tye1 = return tye'"
      and c2: "tmcomplete \<rho> (Type a Us) tye1 tye'" by auto
    have "tmcomplete \<rho> (Type a (T1 # Us)) tye tye'" by (rule tmcomplete_Cons[OF c1 c2])
    with m1 m2 show ?case by (auto simp: bindM_def return_def)
  qed
  from this[OF _ ag] show ?case by (simp add: U zip_map2 map_zip_eqI)
next
  case (TFree a S)
  then have "U = TFree a S" by (simp add: tmatcher_def)
  then show ?case by (simp add: tmcomplete_def return_def)
qed

theorem typ_match_complete:
  assumes "wft ar T" "wft ar U" "scons (tvars T)" "tmatcher alg tye \<rho> T U"
  shows "\<exists>tye'. typ_match alg T U tye = return tye' \<and> textends tye tye' \<and>
    (\<forall>(v, S)\<in>tvars T. vt_lookup tye' v = Some (S, \<rho> v S)) \<and>
    (\<forall>v. vt_lookup tye' v \<noteq> None \<longrightarrow> vt_lookup tye v \<noteq> None \<or> (\<exists>S. (v, S) \<in> tvars T))"
  using typ_match_complete_aux[OF assms] by (simp add: tmcomplete_def)

lemma tcons_step:
  assumes "tcons tye T'" "scons A" "tvars T \<subseteq> A" "tvars T' \<subseteq> A"
    and "textends tye tye1" "\<And>v S U'. vt_lookup tye1 v = Some (S, U') \<Longrightarrow> vt_lookup tye v = None \<Longrightarrow> (v, S) \<in> tvars T"
  shows "tcons tye1 T'"
  unfolding tcons_def
proof (intro allI impI)
  fix v S S' U assume vS: "(v, S) \<in> tvars T'" and b: "vt_lookup tye1 v = Some (S', U)"
  show "S' = S"
  proof (cases "vt_lookup tye v")
    case None
    with assms(6) b have "(v, S') \<in> tvars T" by blast
    with assms(2-4) vS show ?thesis unfolding scons_def by blast
  next
    case (Some x)
    with assms(5) b have "vt_lookup tye v = Some (S', U)" by (auto simp: textends_def)
    with assms(1) vS show ?thesis unfolding tcons_def by blast
  qed
qed

lemma typ_match_exn_aux:
  "wft ar T \<Longrightarrow> wft ar U \<Longrightarrow> scons (tvars T) \<Longrightarrow> tcons tye T \<Longrightarrow>
    (\<exists>tye'. typ_match alg T U tye = return tye') \<or> typ_match alg T U tye = raise Type_Match"
proof (induction T arbitrary: U tye)
  case (TVar v S)
  show ?case
  proof (cases "vt_lookup tye v")
    case None
    with TVar.prems of_sort_sem[OF TVar.prems(2), of S] show ?thesis
      by (auto simp: type_lookup_def update_new_def vt_defined_lookup)
  next
    case (Some x)
    obtain S' U' where x: "x = (S', U')" by force
    with Some TVar.prems(4) have "S' = S" by (auto simp: tcons_def)
    with Some x show ?thesis by (simp add: type_lookup_def)
  qed
next
  case (Type a Ts)
  show ?case
  proof (cases U)
    case (Type b Us)
    have "(\<exists>tye'. foldM (\<lambda>(T, U) subs. typ_match alg T U subs) ps tye = return tye') \<or>
        foldM (\<lambda>(T, U) subs. typ_match alg T U subs) ps tye = raise Type_Match"
      if "set ps \<subseteq> set (zip Ts Us)" "tcons tye (Type a Ts)" for ps tye
      using that
    proof (induction ps arbitrary: tye)
      case Nil
      then show ?case by simp
    next
      case (Cons p ps)
      obtain T1 U1 where p: "p = (T1, U1)" by force
      have mem: "(T1, U1) \<in> set (zip Ts Us)" using Cons.prems(1) p by auto
      have T1: "T1 \<in> set Ts" using mem by (rule set_zip_leftD)
      have wf: "wft ar T1" "wft ar U1"
        using Type.prems(1,2) mem \<open>U = Type b Us\<close> by (auto dest: set_zip_leftD set_zip_rightD)
      have sc: "scons (tvars T1)" using Type.prems(3) T1 by (auto simp: scons_def)
      have tc: "tcons tye T1" using Cons.prems(2) T1 by (auto simp: tcons_def)
      from Type.IH[OF T1 wf sc tc] show ?case
      proof
        assume "\<exists>tye1. typ_match alg T1 U1 tye = return tye1"
        then obtain tye1 where m1: "typ_match alg T1 U1 tye = return tye1" by blast
        note s = typ_match_sound[OF wf m1]
        have "tcons tye1 (Type a Ts)"
          by (rule tcons_step[of tye "Type a Ts" "tvars (Type a Ts)" T1 tye1])
            (use Cons.prems(2) Type.prems(3) T1 s(1) s(4) in auto)
        from Cons.IH[OF _ this] Cons.prems(1) m1 show ?case by (auto simp: p)
      next
        assume "typ_match alg T1 U1 tye = raise Type_Match"
        then show ?case by (simp add: p)
      qed
    qed
    from this[of "zip Ts Us" tye] Type.prems(4) show ?thesis by (auto simp: \<open>U = Type b Us\<close>)
  qed simp_all
next
  case (TFree a S)
  then show ?case by (cases U) auto
qed

theorem typ_match_exn:
  assumes "wft ar T" "wft ar U" "mcons tye T"
  shows "(\<exists>tye'. typ_match alg T U tye = return tye') \<or> typ_match alg T U tye = raise Type_Match"
  using typ_match_exn_aux assms by (simp add: mcons_def)

text \<open>Hence \<open>Type_Match\<close> means that there is no matcher.\<close>

corollary typ_match_fail:
  assumes "wft ar T" "wft ar U" "scons (tvars T)" "typ_match alg T U tye = raise Type_Match"
  shows "\<not> tmatcher alg tye \<rho> T U"
proof
  assume "tmatcher alg tye \<rho> T U"
  from typ_match_complete[OF assms(1-3) this] assms(4) show False by (auto simp: return_def raise_def)
qed

end

end
