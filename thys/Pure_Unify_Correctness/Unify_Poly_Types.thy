section \<open>Soundness of Type Unification\<close>

theory Unify_Poly_Types
  imports Unify_Poly_Semantics
begin

text \<open>
  For soundness we do not need the invariant of type unification (theory
  \<^theory>\<open>Pure_Pattern_Correctness.Type_Mgu\<close>): if \<open>Type.unify\<close> returns, its type environment
  extends the old one, and every solution of it unifies the types. We only need that the
  types are well-formed, so that type constructors have the same number of arguments.
\<close>

definition twf :: "(name \<Rightarrow> nat) \<Rightarrow> tyenv \<Rightarrow> bool" where
  "twf ar \<theta> \<longleftrightarrow> (\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> wft ar U)"

lemma twfD: "twf ar \<theta> \<Longrightarrow> vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> wft ar U"
  unfolding twf_def by blast

lemma tsolD: "tsol \<theta> \<rho> \<Longrightarrow> vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> \<rho> v S = tsubst \<rho> U"
  unfolding tsol_def by blast

lemma ok_type_lookup:
  "ok (type_lookup \<theta> v S) r \<Longrightarrow> r = None \<or> (\<exists>U. r = Some U \<and> vt_lookup \<theta> v = Some (S, U))"
  by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)

lemma devar_sound:
  assumes "devar \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> (tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T' = tsubst \<rho> T) \<and> (twf ar \<theta> \<longrightarrow> wft ar T \<longrightarrow> wft ar T')"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  show ?case
  proof (cases T)
    case (TVar ixn S)
    from "1.hyps" "1.prems" TVar obtain r' where lk: "ok (type_lookup \<theta> ixn S) r'"
      and rest: "ok (case r' of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T) T'"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest show ?thesis by (simp add: return_def)
    next
      fix U assume r': "r' = Some U" and l: "vt_lookup \<theta> ixn = Some (S, U)"
      with rest have "dv \<theta> U = Some (Ok T')" by simp
      from "1.IH"[OF this refl] l TVar show ?thesis by (auto dest: tsolD twfD)
    qed
  qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
qed

lemma ok_devar_sound:
  "ok (devar \<theta> T) T' \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T' = tsubst \<rho> T"
  "ok (devar \<theta> T) T' \<Longrightarrow> twf ar \<theta> \<Longrightarrow> wft ar T \<Longrightarrow> wft ar T'"
  using devar_sound[of \<theta> T "Ok T'" T' \<rho> ar] by simp_all

lemma ok_update_new: "ok (update_new (v, x) \<theta>) \<theta>' \<Longrightarrow> \<theta>' = vt_update (v, x) \<theta> \<and> vt_lookup \<theta> v = None"
  by (auto simp: update_new_def vt_defined_lookup raise_def split: if_splits)

lemma textends_update_new: "ok (update_new (v, x) \<theta>) \<theta>' \<Longrightarrow> textends \<theta> \<theta>'"
  by (auto simp: textends_def dest!: ok_update_new)

text \<open>Folding a step that extends the environment:\<close>

lemma foldM_textends:
  assumes "\<forall>x\<in>set xs. \<forall>st st'. ok (f x st) st' \<longrightarrow> twf ar (fst st) \<longrightarrow>
      textends (fst st) (fst st') \<and> twf ar (fst st') \<and> P x (fst st')"
    and "ok (foldM f xs st) st'" "twf ar (fst st)"
    and "\<And>x \<theta> \<theta>'. P x \<theta> \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> P x \<theta>'"
  shows "textends (fst st) (fst st') \<and> twf ar (fst st') \<and> (\<forall>x\<in>set xs. P x (fst st'))"
  using assms(1-3)
proof (induction xs arbitrary: st)
  case (Cons x xs)
  from Cons.prems(2) obtain st1 where s1: "ok (f x st) st1" and r: "ok (foldM f xs st1) st'"
    by (auto simp: bind_def split: option.splits res.splits)
  have "ok (f x st) st1 \<longrightarrow> twf ar (fst st) \<longrightarrow> textends (fst st) (fst st1) \<and> twf ar (fst st1) \<and> P x (fst st1)"
    using bspec[OF Cons.prems(1) list.set_intros(1)] by blast
  with s1 Cons.prems(3) have i1: "textends (fst st) (fst st1)" "twf ar (fst st1)"
    "P x (fst st1)" by simp_all
  from Cons.IH[OF _ r i1(2)] Cons.prems(1) have i2: "textends (fst st1) (fst st')" "twf ar (fst st')"
    "\<forall>y\<in>set xs. P y (fst st')" by simp_all
  from i1 i2 assms(4) show ?case by (auto intro: textends_trans)
qed (simp add: return_def)

lemma meet_sound:
  assumes "meet alg T S st = Some r"
  shows "r = Ok st' \<Longrightarrow> twf ar (fst st) \<Longrightarrow> textends (fst st) (fst st') \<and> twf ar (fst st')"
  using assms
proof (induction alg T S st r arbitrary: st' rule: meet.raw_induct[rotated, consumes 1])
  case (1 mt alg T S st r)
  obtain tye cnt where st: "st = (tye, cnt)" by (cases st)
  show ?case
  proof (cases "S = []")
    case True
    with "1.hyps" "1.prems" show ?thesis by (simp add: return_def)
  next
    case False
    show ?thesis
    proof (cases T)
      case (TVar xi S')
      show ?thesis
      proof (cases "sort_le alg S' S")
        case True
        with "1.hyps" "1.prems" False TVar st show ?thesis by (simp add: return_def)
      next
        case nle: False
        obtain V cnt' where g: "gen_tyvar (inter_sort alg S' S) cnt = (V, cnt')"
          by (cases "gen_tyvar (inter_sort alg S' S) cnt")
        from "1.hyps" "1.prems"(1) False TVar st nle g obtain tye' where
          u: "ok (update_new (xi, (S', V)) tye) tye'" and st': "st' = (tye', cnt')"
          by (auto simp: bind_def return_def split: option.splits res.splits)
        have "twf ar tye'" using ok_update_new[OF u] "1.prems"(2) st g
          by (auto simp: twf_def gen_tyvar_def)
        with textends_update_new[OF u] st st' show ?thesis by simp
      qed
    next
      case (TFree a S')
      with "1.hyps" "1.prems" False st show ?thesis
        by (auto simp: return_def raise_def split: if_splits)
    next
      case (Type a Ts)
      from "1.hyps" "1.prems"(1) False Type st obtain Ss where
        f: "ok (foldM (\<lambda>(T, S) st. do {T' \<leftarrow> devar (fst st) T; mt alg T' S st}) (zip Ts Ss) st) st'"
        by (auto simp: bind_def split: option.splits res.splits)
      have "textends (fst st) (fst st') \<and> twf ar (fst st') \<and> (\<forall>x\<in>set (zip Ts Ss). True)"
      proof (rule foldM_textends[OF _ f "1.prems"(2)], intro ballI allI impI)
        fix x st1 st2
        assume "ok ((\<lambda>(T, S) st. do {T' \<leftarrow> devar (fst st) T; mt alg T' S st}) x st1) st2" "twf ar (fst st1)"
        then obtain T1 S1 T' where "ok (mt alg T' S1 st1) st2"
          by (cases x) (auto simp: bind_def split: option.splits res.splits)
        with "1.IH"[of alg T' S1 st1 "Ok st2" st2] \<open>twf ar (fst st1)\<close>
        show "textends (fst st1) (fst st2) \<and> twf ar (fst st2) \<and> True" by simp
      qed simp
      then show ?thesis by simp
    qed
  qed
qed

lemma ok_type_occurs_False: "ok (type_occurs v \<theta> T) False \<Longrightarrow> True"
  by simp

lemma unify_aux_sound:
  assumes "unify_aux alg T U st = Some r"
  shows "r = Ok st' \<Longrightarrow> twf ar (fst st) \<Longrightarrow> wft ar T \<Longrightarrow> wft ar U \<Longrightarrow>
    textends (fst st) (fst st') \<and> twf ar (fst st') \<and> (\<forall>\<rho>. tsol (fst st') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"
  using assms
proof (induction alg T U st r arbitrary: st' rule: unify_aux.raw_induct[rotated, consumes 1])
  case (1 ua alg ty1 ty2 st r)
  obtain tye cnt where st: "st = (tye, cnt)" by (cases st)
  from "1.hyps" "1.prems"(1) st obtain T U where dT: "ok (devar tye ty1) T" and dU: "ok (devar tye ty2) U"
    and rest: "ok (case (T, U) of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return st else tvar_clash v S1 S2)
          else if sort_le alg S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T)) tye; return (tye', cnt)}
          else if sort_le alg S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U)) tye; return (tye', cnt)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg S1 S2) cnt;
            tye' \<leftarrow> update_new (w, (S2, S)) tye;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v tye U;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U)) tye; meet alg U S (tye', cnt)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v tye T;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T)) tye; meet alg T S (tye', cnt)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. ua alg T U st) (zip Ts Us) st
      | _ \<Rightarrow> if T = U then return st else raise TUnify) st'"
    by (auto simp: bind_def Let_def split: option.splits res.splits)
  have tw: "twf ar tye" using "1.prems"(2) st by simp
  have eT: "tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> ty1" "tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> U = tsubst \<rho> ty2"
    if "textends tye \<theta>" for \<theta> \<rho>
    using ok_devar_sound(1)[OF dT] ok_devar_sound(1)[OF dU] that by (auto intro: tsol_textends)
  have wT: "wft ar T" "wft ar U"
    using ok_devar_sound(2)[OF dT tw] ok_devar_sound(2)[OF dU tw] "1.prems"(3,4) by simp_all
  text \<open>It suffices to show the claim for \<open>T\<close> and \<open>U\<close>.\<close>
  have suff: "?case" if "textends tye (fst st')" "twf ar (fst st')"
    "\<And>\<rho>. tsol (fst st') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    using that eT[OF that(1)] st by auto
  have bind_var: "textends tye \<theta>' \<and> twf ar \<theta>' \<and> (\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> \<rho> v S = tsubst \<rho> X)"
    if "ok (update_new (v, (S, X)) tye) \<theta>'" "wft ar X" for v S X \<theta>'
  proof -
    from ok_update_new[OF that(1)] have \<theta>': "\<theta>' = vt_update (v, (S, X)) tye" and n: "vt_lookup tye v = None"
      by simp_all
    have "vt_lookup \<theta>' v = Some (S, X)" using \<theta>' by simp
    moreover have "textends tye \<theta>'" using \<theta>' n by (auto simp: textends_def)
    moreover have "twf ar \<theta>'" using \<theta>' that(2) tw unfolding twf_def by auto
    ultimately show ?thesis by (blast dest: tsolD)
  qed
  have bind_meet: "textends tye (fst st') \<and> twf ar (fst st') \<and> (\<forall>\<rho>. tsol (fst st') \<rho> \<longrightarrow> \<rho> v S = tsubst \<rho> X)"
    if "ok (update_new (v, (S, X)) tye) \<theta>'" "ok (meet alg X S (\<theta>', cnt)) st'" "wft ar X" for v S X \<theta>'
  proof -
    from bind_var[OF that(1,3)] have b1: "textends tye \<theta>'" "twf ar \<theta>'"
      "\<And>\<rho>. tsol \<theta>' \<rho> \<Longrightarrow> \<rho> v S = tsubst \<rho> X" by auto
    from meet_sound[OF that(2) refl] b1(2) have m: "textends \<theta>' (fst st')" "twf ar (fst st')" by simp_all
    have "\<rho> v S = tsubst \<rho> X" if "tsol (fst st') \<rho>" for \<rho>
      using b1(3)[OF tsol_textends[OF m(1) that]] .
    with b1(1) m show ?thesis by (auto intro: textends_trans)
  qed
  consider (VV) v S1 w S2 where "T = TVar v S1" "U = TVar w S2"
    | (VX) v S where "T = TVar v S" "\<not> is_TVar U"
    | (XV) v S where "\<not> is_TVar T" "U = TVar v S"
    | (TT) a Ts b Us where "T = Type a Ts" "U = Type b Us"
    | (XX) "\<not> is_TVar T" "\<not> is_TVar U" "\<forall>a Ts b Us. T \<noteq> Type a Ts \<or> U \<noteq> Type b Us"
    by (cases T; cases U) auto
  then show ?case
  proof cases
    case VV
    consider "v = w" | "v \<noteq> w" "sort_le alg S1 S2" | "v \<noteq> w" "\<not> sort_le alg S1 S2" "sort_le alg S2 S1"
      | "v \<noteq> w" "\<not> sort_le alg S1 S2" "\<not> sort_le alg S2 S1" by blast
    then show ?thesis
    proof cases
      case 1
      with rest VV have "S1 = S2" "st' = st"
        by (auto simp: return_def tvar_clash_def raise_def split: if_splits)
      with 1 VV st tw show ?thesis by (intro suff) simp_all
    next
      case 2
      with rest VV obtain tye' where u: "ok (update_new (w, (S2, T)) tye) tye'"
        and s': "st' = (tye', cnt)"
        by (auto simp: bind_def return_def split: option.splits res.splits)
      from bind_var[OF u wT(1)] s' VV show ?thesis by (intro suff) auto
    next
      case 3
      with rest VV obtain tye' where u: "ok (update_new (v, (S1, U)) tye) tye'"
        and s': "st' = (tye', cnt)"
        by (auto simp: bind_def return_def split: option.splits res.splits)
      from bind_var[OF u wT(2)] s' VV show ?thesis by (intro suff) auto
    next
      case 4
      obtain V cnt' where g: "gen_tyvar (inter_sort alg S1 S2) cnt = (V, cnt')"
        by (cases "gen_tyvar (inter_sort alg S1 S2) cnt")
      with 4 rest VV obtain tye' tye'' where u1: "ok (update_new (w, (S2, V)) tye) tye'"
        and u2: "ok (update_new (v, (S1, V)) tye') tye''" and s': "st' = (tye'', cnt')"
        by (auto simp: bind_def return_def Let_def split: option.splits res.splits)
      have wV: "wft ar V" using g by (auto simp: gen_tyvar_def)
      from bind_var[OF u1 wV] have b1: "textends tye tye'" "twf ar tye'"
        "\<And>\<rho>. tsol tye' \<rho> \<Longrightarrow> \<rho> w S2 = tsubst \<rho> V" by auto
      from ok_update_new[OF u2] have t2: "tye'' = vt_update (v, (S1, V)) tye'" "vt_lookup tye' v = None"
        by simp_all
      have b2: "textends tye' tye''" "twf ar tye''"
        "\<And>\<rho>. tsol tye'' \<rho> \<Longrightarrow> \<rho> v S1 = tsubst \<rho> V"
        using t2 b1(2) wV by (auto simp: textends_def twf_def dest: tsolD)
      have "\<rho> w S2 = tsubst \<rho> V" if "tsol tye'' \<rho>" for \<rho>
        using b1(3) tsol_textends[OF b2(1) that] by blast
      with b1 b2 s' VV show ?thesis
        by (intro suff) (auto intro: textends_trans)
    qed
  next
    case VX
    with rest obtain b \<theta>' where "\<not> b" and u: "ok (update_new (v, (S, U)) tye) \<theta>'"
      and m: "ok (meet alg U S (\<theta>', cnt)) st'"
      by (cases U) (auto simp: bind_def raise_def split: option.splits res.splits if_splits)
    from bind_meet[OF u m wT(2)] VX show ?thesis by (intro suff) auto
  next
    case XV
    with rest obtain b \<theta>' where "\<not> b" and u: "ok (update_new (v, (S, T)) tye) \<theta>'"
      and m: "ok (meet alg T S (\<theta>', cnt)) st'"
      by (cases T) (auto simp: bind_def raise_def split: option.splits res.splits if_splits)
    from bind_meet[OF u m wT(1)] XV show ?thesis by (intro suff) auto
  next
    case TT
    with rest have ab: "a = b" and f: "ok (foldM (\<lambda>(T, U) st. ua alg T U st) (zip Ts Us) st) st'"
      by (auto simp: raise_def split: if_splits)
    have len: "length Ts = length Us" using wT TT ab by simp
    have "textends (fst st) (fst st') \<and> twf ar (fst st') \<and>
        (\<forall>x\<in>set (zip Ts Us). (\<lambda>(T, U) \<theta>. \<forall>\<rho>. tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) x (fst st'))"
    proof (rule foldM_textends[OF _ f], intro ballI allI impI)
      fix x st1 st2
      assume x: "x \<in> set (zip Ts Us)" and s: "ok ((\<lambda>(T, U) st. ua alg T U st) x st1) st2"
        and tw1: "twf ar (fst st1)"
      obtain T1 U1 where x': "x = (T1, U1)" by (cases x)
      have "wft ar T1" "wft ar U1" using x x' wT TT by (auto dest: set_zip_leftD set_zip_rightD)
      with "1.IH"[of alg T1 U1 st1 "Ok st2" st2] s x' tw1
      show "textends (fst st1) (fst st2) \<and> twf ar (fst st2) \<and>
          (\<lambda>(T, U) \<theta>. \<forall>\<rho>. tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) x (fst st2)"
        by simp
    next
      show "twf ar (fst st)" using tw st by simp
    next
      fix x \<theta> \<theta>'
      assume "(\<lambda>(T, U) \<theta>. \<forall>\<rho>. tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) x \<theta>" "textends \<theta> \<theta>'"
      then show "(\<lambda>(T, U) \<theta>. \<forall>\<rho>. tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) x \<theta>'"
        by (auto intro: tsol_textends)
    qed
    then have r: "textends tye (fst st')" "twf ar (fst st')"
      "\<And>\<rho> T1 U1. tsol (fst st') \<rho> \<Longrightarrow> (T1, U1) \<in> set (zip Ts Us) \<Longrightarrow> tsubst \<rho> T1 = tsubst \<rho> U1"
      using st by auto
    have "map (tsubst \<rho>) Ts = map (tsubst \<rho>) Us" if "tsol (fst st') \<rho>" for \<rho>
      using len r(3)[OF that] by (auto simp: list_eq_iff_nth_eq in_set_zip)
    with r(1,2) TT ab show ?thesis by (intro suff) auto
  next
    case XX
    with rest have "T = U" "st' = st"
      by (cases T; cases U; auto simp: return_def raise_def split: if_splits)+
    with st tw show ?thesis by (intro suff) simp_all
  qed
qed

lemma unify_types_psound:
  assumes "ok (unify_types alg T U env) env'" "twf ar (tyenv env)" "wft ar T" "wft ar U"
  shows "tenv env' = tenv env" "textends (tyenv env) (tyenv env')" "twf ar (tyenv env')"
    "tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
proof -
  have "tenv env' = tenv env \<and> textends (tyenv env) (tyenv env') \<and> twf ar (tyenv env') \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"
  proof (cases "T = U")
    case True
    with assms show ?thesis by (simp add: unify_types_def return_def)
  next
    case False
    have hr: "\<not> ok ((\<lambda>e. case e of TUnify \<Rightarrow> raise (Unif (Typ_Clash (tyenv env) T U))
        | _ \<Rightarrow> raise e) e) y" for e y
      by (cases e) simp_all
    from assms(1) False have "ok (do {(tye', maxidx') \<leftarrow> type_unify alg U T (tyenv env, maxidx env);
        return (Envir maxidx' (tenv env) tye')}) env'"
      by (auto simp: unify_types_def ok_handle hr)
    then obtain tye' n' where u: "ok (unify_aux alg U T (tyenv env, maxidx env)) (tye', n')"
      and e': "env' = Envir n' (tenv env) tye'"
      by (auto simp: type_unify_def bind_def return_def split: option.splits res.splits prod.splits)
    from unify_aux_sound[OF u refl _ assms(4,3)] assms(2) e' show ?thesis
      by auto
  qed
  then show "tenv env' = tenv env" "textends (tyenv env) (tyenv env')" "twf ar (tyenv env')"
    "tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U" by auto
qed

lemma cunify_types_psound:
  assumes "okW (cunify_types alg T U env) env'" "twf ar (tyenv env)" "wft ar T" "wft ar U"
  shows "tenv env' = tenv env" "pextends env' env" "twf ar (tyenv env')"
    "tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
proof -
  have u: "ok (unify_types alg T U env) env'"
    using assms(1) by (auto simp: cunify_types_def split: option.splits res.splits exn.splits)
  note s = unify_types_psound[OF u assms(2-4)]
  show "tenv env' = tenv env" "twf ar (tyenv env')" "tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    using s by simp_all
  show "pextends env' env" using s by (simp add: pextends_def extends_def)
qed

lemma test_unify_types_psound:
  assumes "okW (test_unify_types alg T U env) env'" "twf ar (tyenv env)" "wft ar T" "wft ar U"
  shows "tenv env' = tenv env" "pextends env' env" "twf ar (tyenv env')"
    "tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
proof -
  from assms(1) have "okW (cunify_types alg T U env) env'"
    by (auto simp: test_unify_types_def okW_whenW)
  from cunify_types_psound[OF this assms(2-4)]
  show "tenv env' = tenv env" "pextends env' env" "twf ar (tyenv env')"
    "tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U" by simp_all
qed

text \<open>Substitutions that respect a type environment identify the constants that it unifies:\<close>

lemma tresp_Const:
  "tresp \<theta> \<sigma> \<Longrightarrow> (\<And>\<rho>. tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<Longrightarrow>
    mk_subst \<sigma> (tr (Const a T)) = mk_subst \<sigma> (tr (Const a U))"
  "tresp \<theta> \<sigma> \<Longrightarrow> (\<And>\<rho>. tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<Longrightarrow>
    mk_subst \<sigma> (tr (Free a T)) = mk_subst \<sigma> (tr (Free a U))"
  by (auto dest: trespD)

end
