section \<open>Soundness of the Type Operations\<close>

theory Pattern_Types
  imports Pattern_Monad "Pure_Pattern_Correctness.Type_Mgu"
begin

text \<open>
  The type operations are sound without invariants on the type environment \<open>\<theta>\<close>: a successful
  computation respects every solution \<open>\<rho>\<close> of \<open>\<theta>\<close>. Lookups compare sorts (\<open>Type.lookup\<close>), so a
  type variable is only replaced by its binding at the sort of the binding.
\<close>

lemma tsolD: "tsol \<theta> \<rho> \<Longrightarrow> vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> \<rho> v S = tsubst \<rho> U"
  unfolding tsol_def by blast

lemma ok_type_lookup_sound:
  "ok (type_lookup \<theta> v S) (Some U) \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> \<rho> v S = tsubst \<rho> U"
  by (cases "vt_lookup \<theta> v") (auto simp: ok_type_lookup dest: tsolD)

lemma devar_sound:
  assumes "devar \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T' = tsubst \<rho> T"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  note d = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (TVar v S)
    with d obtain lr where lr: "ok (type_lookup \<theta> v S) lr"
      and rest: "ok (case lr of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T) T'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some U)
      with rest have "ok (dv \<theta> U) T'" by simp
      with "1.IH" "1.prems"(2) have "tsubst \<rho> T' = tsubst \<rho> U" by blast
      with ok_type_lookup_sound[OF lr[unfolded Some] "1.prems"(2)] TVar show ?thesis by simp
    qed (use rest in simp)
  qed (use d in simp_all)
qed

lemma ok_allM: "ok (allM P xs) True \<Longrightarrow> x \<in> set xs \<Longrightarrow> ok (P x) True"
  by (induction xs) (auto split: if_splits)

lemma unified_aux_sound:
  assumes "unified_aux \<theta> T U = Some r"
  shows "r = Ok True \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
  using assms
proof (induction \<theta> T U r rule: unified_aux.raw_induct[rotated, consumes 1])
  case (1 ua \<theta> T U r)
  from "1.hyps"[unfolded "1.prems"(1)] obtain T' U' where
    T': "ok (devar \<theta> T) T'" and U': "ok (devar \<theta> U) U'" and
    rest: "ok (case (T', U') of
        (Type s Ts, Type s' Ts') \<Rightarrow>
          if s = s' then do {
            b \<leftarrow> allM (\<lambda>(T, T'). ua \<theta> T T') (zip Ts Ts');
            return (b \<and> length Ts = length Ts')}
          else return False
      | _ \<Rightarrow> return (T' = U')) True"
    by auto
  have "tsubst \<rho> T' = tsubst \<rho> U'"
  proof (cases "\<exists>a Ts b Us. T' = Type a Ts \<and> U' = Type b Us")
    case True
    then obtain a Ts b Us where TU: "T' = Type a Ts" "U' = Type b Us" by blast
    with rest have "a = b" and len: "length Ts = length Us"
      and all: "ok (allM (\<lambda>(T, T'). ua \<theta> T T') (zip Ts Us)) True"
      by (auto split: if_splits)
    have "tsubst \<rho> (Ts ! i) = tsubst \<rho> (Us ! i)" if "i < length Ts" for i
    proof -
      have "(Ts ! i, Us ! i) \<in> set (zip Ts Us)" using that len by (auto simp: in_set_zip)
      from ok_allM[OF all this] have "ok (ua \<theta> (Ts ! i) (Us ! i)) True" by simp
      with "1.IH" "1.prems"(2) show ?thesis by blast
    qed
    with TU \<open>a = b\<close> len show ?thesis by (simp add: list_eq_iff_nth_eq)
  next
    case False
    with rest have "T' = U'" by (auto split: ptyp.splits)
    then show ?thesis by simp
  qed
  with devar_sound[OF T' refl "1.prems"(2)] devar_sound[OF U' refl "1.prems"(2)] show ?case by simp
qed

lemma unified_sound: "ok (unified \<theta> T U) True \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
  unfolding unified_def using unified_aux_sound by (auto split: if_splits)

lemma norm_type_aux_sound:
  assumes "norm_type_aux \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T' = tsubst \<rho> T"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nt \<theta> T r)
  note n = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Ts)
    with n obtain Ts' where l: "list_all2 (\<lambda>x y. ok (nt \<theta> x) y) Ts Ts'" and T': "T' = Type a Ts'"
      by (auto simp: ok_mapM)
    from l have "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
      by (induction rule: list_all2_induct) (use "1.IH" "1.prems"(2) in auto)
    with Type T' show ?thesis by simp
  next
    case (TVar v S)
    with n obtain lr where lr: "ok (type_lookup \<theta> v S) lr"
      and rest: "ok (case lr of Some U \<Rightarrow> nt \<theta> U | None \<Rightarrow> return T) T'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some U)
      with rest have "ok (nt \<theta> U) T'" by simp
      with "1.IH" "1.prems"(2) have "tsubst \<rho> T' = tsubst \<rho> U" by blast
      with ok_type_lookup_sound[OF lr[unfolded Some] "1.prems"(2)] TVar show ?thesis by simp
    qed (use rest in simp)
  qed (use n in simp)
qed

lemma norm_type_sound: "ok (norm_type \<theta> T) T' \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T' = tsubst \<rho> T"
  unfolding norm_type_def using norm_type_aux_sound by (auto split: if_splits)


subsection \<open>Type unification\<close>

text \<open>Type unification only adds bindings.\<close>

lemma textends_update_new: "ok (update_new (v, x) \<theta>) \<theta>' \<Longrightarrow> textends \<theta> \<theta>'"
  by (auto simp: ok_update_new intro: textends_update)

lemma meet_textends:
  assumes "meet alg T S st = Some r"
  shows "r = Ok st' \<Longrightarrow> textends (fst st) (fst st')"
  using assms
proof (induction alg T S st r arbitrary: st' rule: meet.raw_induct[rotated, consumes 1])
  case (1 mt alg T S st r)
  obtain \<theta> n where st: "st = (\<theta>, n)" by (cases st)
  note m = "1.hyps"[unfolded "1.prems"(1) st]
  show ?case
  proof (cases "S = []")
    case False
    show ?thesis
    proof (cases T)
      case (TVar v S')
      with m False show ?thesis
        by (auto simp: st gen_tyvar_def split: if_splits dest: textends_update_new)
    next
      case (TFree a S')
      with m False show ?thesis by (auto simp: st split: if_splits)
    next
      case (Type a Ts)
      with m False obtain Ss where
        f: "ok (foldM (\<lambda>(T, S) st. do {T' \<leftarrow> devar (fst st) T; mt alg T' S st}) (zip Ts Ss) (\<theta>, n)) st'"
        by auto
      have "textends (fst b) (fst b')"
        if "ok (foldM (\<lambda>(T, S) st. do {T' \<leftarrow> devar (fst st) T; mt alg T' S st}) ps b) b'" for ps b b'
        using that
      proof (induction rule: ok_foldM_induct)
        case (Cons p ps b b1 b')
        obtain T0 S0 where p: "p = (T0, S0)" by (cases p)
        with Cons.hyps(1) obtain T0' where "ok (mt alg T0' S0 b) b1" by auto
        with "1.IH" have "textends (fst b) (fst b1)" by blast
        then show ?case using Cons.IH by (rule textends_trans)
      qed simp
      from this[OF f] show ?thesis by (simp add: st)
    qed
  qed (use m in \<open>simp add: st\<close>)
qed

lemma update_new_sound:
  assumes "ok (update_new (v, (S, U)) \<theta>) \<theta>1" "textends \<theta>1 \<theta>'"
  shows "textends \<theta> \<theta>'" and "tsol \<theta>' \<rho> \<Longrightarrow> \<rho> v S = tsubst \<rho> U"
proof -
  from assms(1) have "vt_lookup \<theta>1 v = Some (S, U)" by (simp add: ok_update_new)
  with assms(2) have "vt_lookup \<theta>' v = Some (S, U)" unfolding textends_def by blast
  then show "tsol \<theta>' \<rho> \<Longrightarrow> \<rho> v S = tsubst \<rho> U" by (rule tsolD[rotated])
  show "textends \<theta> \<theta>'" using textends_update_new[OF assms(1)] assms(2) by (rule textends_trans)
qed

lemma tsubst_Type_eq:
  "length Ts = length Us \<Longrightarrow> (\<And>i. i < length Ts \<Longrightarrow> tsubst \<rho> (Ts ! i) = tsubst \<rho> (Us ! i)) \<Longrightarrow>
    tsubst \<rho> (Type a Ts) = tsubst \<rho> (Type a Us)"
  by (simp add: list_eq_iff_nth_eq)

lemma unify_aux_sound:
  assumes "unify_aux alg T U st = Some r"
  shows "r = Ok st' \<Longrightarrow> textends (fst st) (fst st') \<and>
    (\<forall>\<rho>. tsol (fst st') \<rho> \<longrightarrow> wft ar (tsubst \<rho> T) \<longrightarrow> wft ar (tsubst \<rho> U) \<longrightarrow>
      tsubst \<rho> T = tsubst \<rho> U)"
  using assms
proof (induction alg T U st r arbitrary: st' rule: unify_aux.raw_induct[rotated, consumes 1])
  case (1 ua alg ty1 ty2 st r)
  obtain \<theta> n where st: "st = (\<theta>, n)" by (cases st)
  from "1.hyps"[unfolded "1.prems"(1) st] obtain T U where
    T: "ok (devar \<theta> ty1) T" and U: "ok (devar \<theta> ty2) U" and
    rest: "ok (case (T, U) of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return (\<theta>, n) else tvar_clash v S1 S2)
          else if sort_le alg S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T)) \<theta>; return (tye', n)}
          else if sort_le alg S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U)) \<theta>; return (tye', n)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg S1 S2) n;
            tye' \<leftarrow> update_new (w, (S2, S)) \<theta>;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> U;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U)) \<theta>; meet alg U S (tye', n)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> T;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T)) \<theta>; meet alg T S (tye', n)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. ua alg T U st) (zip Ts Us) (\<theta>, n)
      | _ \<Rightarrow> if T = U then return (\<theta>, n) else raise TUnify) st'"
    by (auto simp: Let_def)
  text \<open>It suffices to show the claim for the results of \<open>devar\<close>.\<close>
  have "textends \<theta> (fst st') \<and>
    (\<forall>\<rho>. tsol (fst st') \<rho> \<longrightarrow> wft ar (tsubst \<rho> T) \<longrightarrow> wft ar (tsubst \<rho> U) \<longrightarrow>
      tsubst \<rho> T = tsubst \<rho> U)"
  proof (cases T)
    case T_TVar: (TVar v S1)
    show ?thesis
    proof (cases U)
      case (TVar w S2)
      show ?thesis
      proof (cases "v = w")
        case True
        with T_TVar TVar rest show ?thesis by (auto simp: tvar_clash_def split: if_splits)
      next
        case False
        consider (le) "sort_le alg S1 S2" | (ge) "\<not> sort_le alg S1 S2" "sort_le alg S2 S1"
          | (new) "\<not> sort_le alg S1 S2" "\<not> sort_le alg S2 S1"
          by blast
        then show ?thesis
        proof cases
          case le
          with False T_TVar TVar rest obtain \<theta>1 where
            u: "ok (update_new (w, (S2, T)) \<theta>) \<theta>1" and st': "st' = (\<theta>1, n)"
            by auto
          have "tsubst \<rho> T = tsubst \<rho> U" if "tsol \<theta>1 \<rho>" for \<rho>
            using update_new_sound(2)[OF u textends_refl that] T_TVar TVar by simp
          with update_new_sound(1)[OF u textends_refl] st' show ?thesis by simp
        next
          case ge
          with False T_TVar TVar rest obtain \<theta>1 where
            u: "ok (update_new (v, (S1, U)) \<theta>) \<theta>1" and st': "st' = (\<theta>1, n)"
            by auto
          have "tsubst \<rho> T = tsubst \<rho> U" if "tsol \<theta>1 \<rho>" for \<rho>
            using update_new_sound(2)[OF u textends_refl that] T_TVar TVar by simp
          with update_new_sound(1)[OF u textends_refl] st' show ?thesis by simp
        next
          case new
          let ?V = "TVar (aT, n + 1) (inter_sort alg S1 S2)"
          from new False T_TVar TVar rest obtain \<theta>1 \<theta>2 where
            u1: "ok (update_new (w, (S2, ?V)) \<theta>) \<theta>1" and u2: "ok (update_new (v, (S1, ?V)) \<theta>1) \<theta>2"
            and st': "st' = (\<theta>2, n + 1)"
            by (auto simp: gen_tyvar_def)
          note b2 = update_new_sound[OF u2 textends_refl]
          note b1 = update_new_sound[OF u1 textends_update_new[OF u2]]
          have "tsubst \<rho> T = tsubst \<rho> U" if "tsol \<theta>2 \<rho>" for \<rho>
            using b1(2)[OF that] b2(2)[OF that] T_TVar TVar by simp
          with b1(1) st' show ?thesis by simp
        qed
      qed
    next
      case (Type b Us)
      with T_TVar rest obtain \<theta>1 where
        u: "ok (update_new (v, (S1, U)) \<theta>) \<theta>1" and m: "ok (meet alg U S1 (\<theta>1, n)) st'"
        by (auto split: if_splits)
      from meet_textends[OF m] have "textends \<theta>1 (fst st')" by simp
      with update_new_sound[OF u] T_TVar show ?thesis by auto
    next
      case (TFree b S2)
      with T_TVar rest obtain \<theta>1 where
        u: "ok (update_new (v, (S1, U)) \<theta>) \<theta>1" and m: "ok (meet alg U S1 (\<theta>1, n)) st'"
        by (auto split: if_splits)
      from meet_textends[OF m] have "textends \<theta>1 (fst st')" by simp
      with update_new_sound[OF u] T_TVar show ?thesis by auto
    qed
  next
    case T_Type: (Type a Ts)
    show ?thesis
    proof (cases U)
      case (TVar v S)
      with T_Type rest obtain \<theta>1 where
        u: "ok (update_new (v, (S, T)) \<theta>) \<theta>1" and m: "ok (meet alg T S (\<theta>1, n)) st'"
        by (auto split: if_splits)
      from meet_textends[OF m] have "textends \<theta>1 (fst st')" by simp
      with update_new_sound[OF u] TVar show ?thesis by auto
    next
      case (Type b Us)
      with T_Type rest have "a = b"
        and f: "ok (foldM (\<lambda>(T, U) st. ua alg T U st) (zip Ts Us) (\<theta>, n)) st'"
        by (auto split: if_splits)
      text \<open>The type arguments are unified one after the other.\<close>
      have "textends (fst st0) (fst st') \<and>
        (\<forall>\<rho>. tsol (fst st') \<rho> \<longrightarrow> (\<forall>(T, U)\<in>set ps. wft ar (tsubst \<rho> T) \<longrightarrow> wft ar (tsubst \<rho> U) \<longrightarrow>
          tsubst \<rho> T = tsubst \<rho> U))"
        if "ok (foldM (\<lambda>(T, U) st. ua alg T U st) ps st0) st'" for ps st0
        using that
      proof (induction rule: ok_foldM_induct)
        case (Cons p ps b b1 b')
        obtain T0 U0 where p: "p = (T0, U0)" by (cases p)
        with Cons.hyps(1) "1.IH" have IH: "textends (fst b) (fst b1) \<and>
          (\<forall>\<rho>. tsol (fst b1) \<rho> \<longrightarrow> wft ar (tsubst \<rho> T0) \<longrightarrow> wft ar (tsubst \<rho> U0) \<longrightarrow>
            tsubst \<rho> T0 = tsubst \<rho> U0)"
          by simp
        with Cons.IH p show ?case using textends_trans tsol_textends by fastforce
      qed simp
      from this[OF f] have ext: "textends \<theta> (fst st')"
        and eq: "\<And>\<rho> T U. tsol (fst st') \<rho> \<Longrightarrow> (T, U) \<in> set (zip Ts Us) \<Longrightarrow>
          wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar (tsubst \<rho> U) \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
        by auto
      have "tsubst \<rho> T = tsubst \<rho> U"
        if \<rho>: "tsol (fst st') \<rho>" and wf: "wft ar (tsubst \<rho> T)" "wft ar (tsubst \<rho> U)" for \<rho>
      proof -
        from wf T_Type Type \<open>a = b\<close> have len: "length Ts = length Us" by simp
        have "tsubst \<rho> (Ts ! i) = tsubst \<rho> (Us ! i)" if "i < length Ts" for i
        proof (rule eq[OF \<rho>])
          show "(Ts ! i, Us ! i) \<in> set (zip Ts Us)" using that len by (auto simp: in_set_zip)
          show "wft ar (tsubst \<rho> (Ts ! i))" "wft ar (tsubst \<rho> (Us ! i))"
            using wf that len T_Type Type by auto
        qed
        with len T_Type Type \<open>a = b\<close> show ?thesis by (simp add: list_eq_iff_nth_eq)
      qed
      with ext show ?thesis by blast
    next
      case (TFree b S)
      with T_Type rest show ?thesis by (auto split: if_splits)
    qed
  next
    case T_TFree: (TFree a S)
    show ?thesis
    proof (cases U)
      case (TVar v S')
      with T_TFree rest obtain \<theta>1 where
        u: "ok (update_new (v, (S', T)) \<theta>) \<theta>1" and m: "ok (meet alg T S' (\<theta>1, n)) st'"
        by (auto split: if_splits)
      from meet_textends[OF m] have "textends \<theta>1 (fst st')" by simp
      with update_new_sound[OF u] TVar show ?thesis by auto
    qed (use T_TFree rest in \<open>auto split: if_splits\<close>)
  qed
  moreover have "tsubst \<rho> T = tsubst \<rho> ty1" "tsubst \<rho> U = tsubst \<rho> ty2" if "tsol (fst st') \<rho>" for \<rho>
    using devar_sound[OF T refl] devar_sound[OF U refl] tsol_textends[OF _ that] calculation by blast+
  ultimately show ?case unfolding st fst_conv by metis
qed

lemma type_unify_sound:
  assumes "ok (type_unify alg T U (\<theta>, n)) (\<theta>', n')"
  shows "textends \<theta> \<theta>'"
    and "tsol \<theta>' \<rho> \<Longrightarrow> wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar (tsubst \<rho> U) \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
  using unify_aux_sound[OF assms[unfolded type_unify_def] refl] by auto

end
