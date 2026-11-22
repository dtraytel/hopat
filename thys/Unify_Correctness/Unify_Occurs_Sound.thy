section \<open>Soundness of the Occurs Checks for Names with Several Types\<close>

theory Unify_Occurs_Sound
  imports Unify_Simpl_Inv
begin

text \<open>
  The occurs checks of the higher-order unifier are sound for every result they return (partial
  correctness, without termination), for any names of the variables. Used by the acyclicity
  proofs and by the termination proofs with names at two types.
\<close>

context pure_sig_gen
begin

subsection \<open>Soundness of the occurs checks\<close>

lemma occur_sound:
  assumes "occur t env v seen = Some r"
  shows "r = Ok (b, s) \<Longrightarrow> acyc env \<Longrightarrow> set seen \<subseteq> set s \<and> (\<not> b \<longrightarrow> osafe env v seen t s)"
  using assms
proof (induction t env v seen r arbitrary: b s rule: occur.raw_induct[rotated, consumes 1])
  case (1 oc t env v seen r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2)
  have IH: "set seen' \<subseteq> set s' \<and> (\<not> b' \<longrightarrow> osafe env v seen' u s')"
    if "ok (oc u env v seen') (b', s')" for u seen' b' s'
    using "1.IH"[OF that refl ac] .
  show ?case
  proof (cases t)
    case (Var w T)
    show ?thesis
    proof (cases "w \<in> set seen")
      case True
      then show ?thesis using h Var by (auto simp: osafe_def intro: good_refl)
    next
      case nseen: False
      show ?thesis
      proof (cases "v = w")
        case True
        with nseen h Var show ?thesis by auto
      next
        case vw: False
        from h Var nseen vw obtain lr where lk: "ok (lookup env w T) lr"
          and rest: "ok (case lr of None \<Rightarrow> return (False, w # seen) | Some u \<Rightarrow> oc u env v (w # seen)) (b, s)"
          by auto
        show ?thesis
        proof (cases lr)
          case None
          have "vt_lookup (tenv env) w = None" using ok_lookup_None lk None by simp
          then have "good env v seen w"
            unfolding good_def using vw dep_bound by (metis rtranclD)
          then show ?thesis using rest None Var by (auto simp: osafe_def intro: good_refl)
        next
          case (Some u)
          from ok_lookup_Some[OF lk[unfolded Some]] obtain U where b: "vt_lookup (tenv env) w = Some (U, u)" .
          from rest Some have r: "ok (oc u env v (w # seen)) (b, s)" by simp
          note I = IH[OF r]
          have "osafe env v seen (Var w T) s" if nb: "\<not> b"
          proof -
            from I nb have o: "\<forall>y\<in>fst ` vars u. good env v (w # seen) y" "\<forall>x\<in>set s. good env v (w # seen) x"
              by (simp_all add: osafe_def)
            have gw: "good env v seen w" by (rule good_bound[OF ac b vw o(1)])
            have gs: "\<forall>x\<in>set (w # seen). good env v seen x" using gw by (auto intro: good_refl)
            show ?thesis using gw o(2) good_trans[OF gs] by (simp add: osafe_def)
          qed
          then show ?thesis using I Var by auto
        qed
      qed
    qed
  next
    case (Abs a T body)
    from h Abs have "ok (oc body env v seen) (b, s)" by simp
    from IH[OF this] Abs show ?thesis by (simp add: osafe_def)
  next
    case (App f u)
    from h App obtain p1 where r1': "ok (oc u env v seen) p1"
      and rest': "ok (if fst p1 then return (True, snd p1) else oc f env v (snd p1)) (b, s)"
      by auto
    obtain b1 s1 where p1: "p1 = (b1, s1)" by (cases p1)
    from r1' have r1: "ok (oc u env v seen) (b1, s1)" by (simp only: p1)
    from rest' have rest: "ok (if b1 then return (True, s1) else oc f env v s1) (b, s)"
      by (simp only: p1 fst_conv snd_conv)
    note I1 = IH[OF r1]
    show ?thesis
    proof (cases b1)
      case True
      with rest I1 show ?thesis by auto
    next
      case False
      with rest have r2: "ok (oc f env v s1) (b, s)" by simp
      note I2 = IH[OF r2]
      have "\<not> b \<longrightarrow> osafe env v seen (f $ u) s"
        using I1 I2 False osafe_trans[of env v seen u s1 f s "f $ u"] by auto
      with I1 I2 App show ?thesis by auto
    qed
  qed (use h in \<open>auto simp: osafe_def intro: good_refl\<close>)
qed

lemma occurs_list_sound:
  "ok (occurs_list env v seen ts) (b, s) \<Longrightarrow> acyc env \<Longrightarrow>
    set seen \<subseteq> set s \<and> (\<not> b \<longrightarrow> (\<forall>t\<in>set ts. osafe env v seen t s) \<and> (\<forall>w\<in>set s. good env v seen w))"
proof (induction ts arbitrary: seen)
  case Nil
  then show ?case by (auto intro: good_refl)
next
  case (Cons t ts)
  from Cons.prems(1) obtain p1 where r1': "ok (occur t env v seen) p1"
    and rest': "ok (if fst p1 then return (True, snd p1) else occurs_list env v (snd p1) ts) (b, s)"
    by auto
  obtain b1 s1 where p1: "p1 = (b1, s1)" by (cases p1)
  from r1' have r1: "ok (occur t env v seen) (b1, s1)" by (simp only: p1)
  from rest' have rest: "ok (if b1 then return (True, s1) else occurs_list env v s1 ts) (b, s)"
    by (simp only: p1 fst_conv snd_conv)
  note I1 = occur_sound[OF r1 refl Cons.prems(2)]
  show ?case
  proof (cases b1)
    case True
    with rest I1 show ?thesis by auto
  next
    case False
    with rest have r2: "ok (occurs_list env v s1 ts) (b, s)" by simp
    note I2 = Cons.IH[OF r2 Cons.prems(2)]
    from I1 False have o1: "osafe env v seen t s1" by simp
    have g1: "\<forall>w\<in>set s1. good env v seen w" using o1 by (simp add: osafe_def)
    have "(\<forall>t'\<in>set (t # ts). osafe env v seen t' s) \<and> (\<forall>w\<in>set s. good env v seen w)" if nb: "\<not> b"
    proof -
      from I2 nb have o2: "\<forall>t'\<in>set ts. osafe env v s1 t' s" and g2: "\<forall>w\<in>set s. good env v s1 w" by blast+
      have gs: "\<forall>w\<in>set s. good env v seen w" using g2 good_trans[OF g1] by blast
      have "osafe env v seen t' s" if "t' \<in> set ts" for t'
        using o2 that gs good_trans[OF g1] by (simp add: osafe_def)
      moreover have "osafe env v seen t s" using o1 gs by (simp add: osafe_def)
      ultimately show ?thesis using gs by auto
    qed
    with I1 I2 show ?thesis by auto
  qed
qed

lemma osafe_unreach: "osafe env v [] t s \<Longrightarrow> y \<in> fst ` vars t \<Longrightarrow> (v, y) \<notin> (dep env)\<^sup>*"
  by (auto simp: osafe_def good_def)

theorem occurs_terms_sound:
  "ok (occurs_terms env v ts) False \<Longrightarrow> acyc env \<Longrightarrow> t \<in> set ts \<Longrightarrow> y \<in> fst ` vars t \<Longrightarrow>
    (v, y) \<notin> (dep env)\<^sup>*"
proof -
  assume o: "ok (occurs_terms env v ts) False" and ac: "acyc env" and t: "t \<in> set ts" and y: "y \<in> fst ` vars t"
  from o obtain s where "ok (occurs_list env v [] ts) (False, s)" by (auto simp: occurs_terms_def)
  from occurs_list_sound[OF this ac] t have "osafe env v [] t s" by blast
  from osafe_unreach[OF this y] show ?thesis .
qed

lemma nonrigid_sound:
  "ok (nonrigid env v seen t) r \<Longrightarrow> acyc env \<Longrightarrow>
    set seen \<subseteq> set (snd r) \<and> (fst r = NoOcc \<longrightarrow> osafe env v seen t (snd r))"
proof -
  assume r: "ok (nonrigid env v seen t) r" and ac: "acyc env"
  from r obtain b s where o: "ok (occurs_list env v seen [t]) (b, s)"
    and r': "r = (if b then Nonrigid else NoOcc, s)"
    by (auto simp: nonrigid_def)
  from occurs_list_sound[OF o ac] r' show ?thesis by auto
qed

lemma occomb_sound:
  assumes H: "\<And>s seen' r'. ok (oc seen' s) r' \<Longrightarrow>
      set seen' \<subseteq> set (snd r') \<and> (fst r' = NoOcc \<longrightarrow> osafe env v seen' s (snd r'))"
  shows "ok (occomb oc seen t) r \<Longrightarrow> set seen \<subseteq> set (snd r) \<and> (fst r = NoOcc \<longrightarrow> osafe env v seen t (snd r))"
proof (induction t arbitrary: seen r)
  case (App f x)
  from App.prems obtain r1 where r1: "ok (oc seen x) r1"
    and rest: "ok (if fst r1 = Rigid then return (Rigid, snd r1)
      else do {r2 \<leftarrow> occomb oc (snd r1) f; return (if fst r2 = NoOcc then fst r1 else fst r2, snd r2)}) r"
    by auto
  note I1 = H[OF r1]
  show ?case
  proof (cases "fst r1 = Rigid")
    case True
    with rest I1 show ?thesis by auto
  next
    case False
    with rest obtain r2 where r2: "ok (occomb oc (snd r1) f) r2"
      and r: "r = (if fst r2 = NoOcc then fst r1 else fst r2, snd r2)"
      by auto
    note I2 = App.IH(1)[OF r2]
    have "(if fst r2 = NoOcc then fst r1 else fst r2) = NoOcc \<longrightarrow> osafe env v seen (f $ x) (snd r2)"
      using I1 I2 osafe_trans[of env v seen x "snd r1" f "snd r2" "f $ x"] by (auto split: if_splits)
    with I1 I2 r show ?thesis by auto
  qed
qed (use H in auto)

lemma rocc_sound:
  assumes "rocc t env v seen = Some r"
  shows "r = Ok r' \<Longrightarrow> acyc env \<Longrightarrow> set seen \<subseteq> set (snd r') \<and> (fst r' = NoOcc \<longrightarrow> osafe env v seen t (snd r'))"
  using assms
proof (induction t env v seen r arbitrary: r' rule: rocc.raw_induct[rotated, consumes 1])
  case (1 oc t env v seen r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2)
  have IH: "set seen' \<subseteq> set (snd r'') \<and> (fst r'' = NoOcc \<longrightarrow> osafe env v seen' u (snd r''))"
    if "ok (oc u env v seen') r''" for u seen' r''
    using "1.IH"[OF that refl ac] .
  show ?case
  proof (cases t)
    case (Var w T)
    show ?thesis
    proof (cases "w \<in> set seen")
      case True
      then show ?thesis using h Var by (auto simp: osafe_def intro: good_refl)
    next
      case nseen: False
      show ?thesis
      proof (cases "v = w")
        case True
        with nseen h Var show ?thesis by auto
      next
        case vw: False
        from h Var nseen vw obtain lr where lk: "ok (lookup env w T) lr"
          and rest: "ok (case lr of None \<Rightarrow> return (NoOcc, w # seen) | Some u \<Rightarrow> oc u env v (w # seen)) r'"
          by auto
        show ?thesis
        proof (cases lr)
          case None
          have "vt_lookup (tenv env) w = None" using ok_lookup_None lk None by simp
          then have "good env v seen w"
            unfolding good_def using vw dep_bound by (metis rtranclD)
          then show ?thesis using rest None Var by (auto simp: osafe_def intro: good_refl)
        next
          case (Some u)
          from ok_lookup_Some[OF lk[unfolded Some]] obtain U where b: "vt_lookup (tenv env) w = Some (U, u)" .
          from rest Some have r: "ok (oc u env v (w # seen)) r'" by simp
          note I = IH[OF r]
          have "osafe env v seen (Var w T) (snd r')" if nb: "fst r' = NoOcc"
          proof -
            from I nb have o: "\<forall>y\<in>fst ` vars u. good env v (w # seen) y"
              "\<forall>x\<in>set (snd r'). good env v (w # seen) x"
              by (simp_all add: osafe_def)
            have gw: "good env v seen w" by (rule good_bound[OF ac b vw o(1)])
            have gs: "\<forall>x\<in>set (w # seen). good env v seen x" using gw by (auto intro: good_refl)
            show ?thesis using gw o(2) good_trans[OF gs] by (simp add: osafe_def)
          qed
          then show ?thesis using I Var by auto
        qed
      qed
    qed
  next
    case (Abs a T body)
    from h Abs have "ok (oc body env v seen) r'" by simp
    from IH[OF this] Abs show ?thesis by (simp add: osafe_def)
  next
    case (App f u)
    note nr = nonrigid_sound[of env v seen t _, OF _ ac]
    have occ: "set seen \<subseteq> set (snd r') \<and> (fst r' = NoOcc \<longrightarrow> osafe env v seen t (snd r'))"
      if "ok (occomb (\<lambda>seen t. oc t env v seen) seen t) r'"
      by (rule occomb_sound[OF IH that])
    from h App obtain hd where hd: "ok (head_of_in env f) hd"
      and rest: "ok (case hd of
          Var w _ \<Rightarrow> do {
            b \<leftarrow> if v = w then rigid_occ env v t else return False;
            if b then return (Rigid, seen) else nonrigid env v seen t}
        | Abs _ _ _ \<Rightarrow> nonrigid env v seen t
        | _ \<Rightarrow> occomb (\<lambda>seen t. oc t env v seen) seen t) r'"
      by (auto simp del: occomb.simps)
    show ?thesis
    proof (cases hd)
      case (Var w W)
      with rest obtain b where rb: "ok (if v = w then rigid_occ env v t else return False) b"
        and r: "ok (if b then return (Rigid, seen) else nonrigid env v seen t) r'"
        by auto
      show ?thesis
      proof (cases b)
        case True
        with r show ?thesis by auto
      next
        case False
        with r have "ok (nonrigid env v seen t) r'" by simp
        from nr[OF this] show ?thesis .
      qed
    next
      case (Abs a T b)
      with rest have "ok (nonrigid env v seen t) r'" by simp
      from nr[OF this] show ?thesis .
    qed (use rest occ in \<open>simp_all del: occomb.simps\<close>)
  qed (use h in \<open>auto simp: osafe_def intro: good_refl\<close>)
qed

theorem rigid_occurs_term_sound:
  "ok (rigid_occurs_term env v t) NoOcc \<Longrightarrow> acyc env \<Longrightarrow> y \<in> fst ` vars t \<Longrightarrow> (v, y) \<notin> (dep env)\<^sup>*"
proof -
  assume o: "ok (rigid_occurs_term env v t) NoOcc" and ac: "acyc env" and y: "y \<in> fst ` vars t"
  from o obtain r where r: "ok (rocc t env v []) r" "fst r = NoOcc" by (auto simp: rigid_occurs_term_def)
  from rocc_sound[OF r(1) refl ac] r(2) have "osafe env v [] t (snd r)" by blast
  from osafe_unreach[OF this y] show ?thesis .
qed

end

end
