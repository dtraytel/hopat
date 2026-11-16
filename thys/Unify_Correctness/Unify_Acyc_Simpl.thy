section \<open>Acyclicity for Names with Several Types: the Occurs Check and \<open>SIMPL\<close>\<close>

theory Unify_Acyc_Simpl
  imports Unify_Search_Inv
begin

text \<open>
  The term environment stays acyclic (\<open>acyc\<close>, on names, ignoring types) through the steps of
  the higher-order unifier, for any names of the variables. Here: the occurs checks are sound
  for every result they return (partial correctness, without termination), and \<open>SIMPL\<close> keeps the
  environment acyclic.
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


subsection \<open>\<open>SIMPL\<close> keeps the environment acyclic\<close>

lemma acyc_tenv: "tenv env' = tenv env \<Longrightarrow> acyc env' = acyc env"
  by (simp add: acyc_def dep_def)

lemma dep_tenv: "tenv env' = tenv env \<Longrightarrow> dep env' = dep env"
  by (simp add: dep_def)

theorem assignment_acyc:
  assumes a: "okW (assignment al rb t u env) env'" and ac: "acyc env"
  shows "acyc env'"
proof -
  from a obtain v T oc where gev: "okW (get_eta_var rb 0 t) (v, T)" and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types al T1 T2 env; liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def)
  from rest have no: "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where cu: "okW (cunify_types al T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by auto
  have te: "tenv env1 = tenv env" by (rule cunify_types_sound(1)[OF cu])
  show ?thesis
  proof (rule acyc_update[OF upd])
    show "acyc env1" using ac acyc_tenv[OF te] by simp
    show "(v, y) \<notin> (dep env1)\<^sup>*" if "(y, U) \<in> vars (rlist_abs rb u)" for y U
    proof -
      have "y \<in> fst ` vars u" using that by force
      from rigid_occurs_term_sound[OF oc[unfolded no] ac this] show ?thesis by (simp add: dep_tenv[OF te])
    qed
  qed
qed

lemma okW_assign_handle_acyc:
  assumes "okW (handleW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)})
    (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e)) st'"
  shows "(\<exists>env'. okW (assignment al rb t u env) env' \<and> st' = (env', ffs, frs)) \<or> st' = x"
proof -
  from assms[unfolded okW_handleW] consider
    (a) "okW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)}) st'"
  | (b) e where "okW (case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) st'"
    by blast
  then show ?thesis
  proof cases
    case a
    then show ?thesis by auto
  next
    case b
    from okW_ASSIGN_return[OF b] show ?thesis by simp
  qed
qed

lemma simrands_acyc:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> acyc (fst st) \<Longrightarrow> acyc (fst st')) \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> acyc (fst st) \<Longrightarrow> acyc (fst st')"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  from "1.IH"[OF "1.prems"(1) r "1.prems"(3)] have "acyc (fst st1)" .
  from "1.prems"(1)[OF s this] show ?case .
qed auto

lemma SIMPL0_rest_acyc:
  assumes F: "\<And>dp st st'. okW (S al dp st) st' \<Longrightarrow> acyc (fst st) \<Longrightarrow> acyc (fst st')"
    and ok: "okW (SIMPL0_rest S al rb t u env ffs frs) st'" and ac: "acyc env"
  shows "acyc (fst st')"
proof -
  have asg: "acyc (fst st')" if "okW (handleW (do {env' \<leftarrow> assignment al rb s s' env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, s, s') # frs) | _ \<Rightarrow> raiseW e)) st'" for s s'
  proof -
    from okW_assign_handle_acyc[OF that] show ?thesis
    proof
      assume "\<exists>env'. okW (assignment al rb s s' env) env' \<and> st' = (env', ffs, frs)"
      then obtain env' where "okW (assignment al rb s s' env) env'" "st' = (env', ffs, frs)" by blast
      with assignment_acyc[OF _ ac] show ?thesis by simp
    qed (use ac in simp)
  qed
  consider (VV) x T y U where "head_of t = Var x T" "head_of u = Var y U"
    | (VR) x T where "head_of t = Var x T" "\<not> is_Var (head_of u)"
    | (RV) y U where "\<not> is_Var (head_of t)" "head_of u = Var y U"
    | (RR) "\<not> is_Var (head_of t)" "\<not> is_Var (head_of u)"
    by (cases "head_of t"; cases "head_of u") auto
  then show ?thesis
  proof cases
    case VV
    with ok obtain T' U' env' where cu: "okW (cunify_types al T' U' env) env'"
      and st': "st' = (env', (rb, t, u) # ffs, frs)"
      by (auto simp: SIMPL0_rest_def)
    show ?thesis using ac acyc_tenv[OF cunify_types_sound(1)[OF cu]] by (simp add: st')
  next
    case VR
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    from asg[OF h] show ?thesis .
  next
    case RV
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment al rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    from asg[OF h] show ?thesis .
  next
    case RR
    have ct: "tenv env' = tenv env" if "cunify_types al T U env = Some (evs, Ok env')" for T U evs env'
      using that by (intro cunify_types_sound(1)) blast
    from ok RR obtain env1 where e1: "tenv env1 = tenv env"
      and sr: "okW (simrands (S al) rb u t u (env1, ffs, frs)) st'"
      by (cases "head_of t"; cases "head_of u") (auto simp: SIMPL0_rest_def split: if_splits dest: ct)
    from simrands_acyc[OF F sr] ac acyc_tenv[OF e1] show ?thesis by simp
  qed
qed

lemma SIMPL0_acyc_aux:
  assumes "SIMPL0 al dp0 st = Some r"
  shows "snd r = Ok st' \<Longrightarrow> acyc (fst st) \<Longrightarrow> acyc (fst st')"
  using assms
proof (induction al dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S al dp0 st r)
  have IH: "acyc (fst st2)" if "okW (S al dp st1) st2" "acyc (fst st1)" for dp st1 st2
  proof -
    from that(1) obtain evs where "S al dp st1 = Some (evs, Ok st2)" by blast
    from "1.IH"[OF this] that(2) show ?thesis by simp
  qed
  obtain env ffs frs where st: "st = (env, ffs, frs)" by (cases st)
  have "\<exists>rb t u env1. okW (head_norm_dpair al env dp0) ((rb, t, u), env1) \<and>
      okW (SIMPL0_rest S al rb t u env1 ffs frs) st'"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] st by (auto simp: SIMPL0_rest_def split: prod.splits)
  then obtain rb t u env1 where hnd: "okW (head_norm_dpair al env dp0) ((rb, t, u), env1)"
    and step: "okW (SIMPL0_rest S al rb t u env1 ffs frs) st'"
    by blast
  have "acyc env1" using "1.prems"(2) st acyc_tenv[OF head_norm_dpair_sound(1)[OF hnd]] by simp
  from SIMPL0_rest_acyc[OF IH step this] show ?case .
qed

theorem SIMPL0_acyc: "okW (SIMPL0 al dp st) st' \<Longrightarrow> acyc (fst st) \<Longrightarrow> acyc (fst st')"
  using SIMPL0_acyc_aux by fastforce

lemma foldrW_SIMPL0_acyc: "okW (foldrW (SIMPL0 al) dps st) st' \<Longrightarrow> acyc (fst st) \<Longrightarrow> acyc (fst st')"
proof (induction dps arbitrary: st')
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 al) dps st) st1"
    and s: "okW (SIMPL0 al dp st1) st'" by auto
  from SIMPL0_acyc[OF s Cons.IH[OF f Cons.prems(2)]] show ?case .
qed simp

lemma SIMPL_acyc_aux:
  assumes "SIMPL al env dps = Some r"
  shows "snd r = Ok st' \<Longrightarrow> acyc env \<Longrightarrow> acyc (fst st')"
  using assms
proof (induction al env dps r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S al env dps r)
  have IH: "acyc (fst st2)" if "okW (S al env1 dps1) st2" "acyc env1" for env1 dps1 st2
  proof -
    from that(1) obtain evs where "S al env1 dps1 = Some (evs, Ok st2)" by blast
    from "1.IH"[OF this] that(2) show ?thesis by simp
  qed
  have "\<exists>env1 ffs frs. okW (foldrW (SIMPL0 al) dps (env, [], [])) (env1, ffs, frs) \<and>
      (okW (S al env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs))"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] by (auto simp: Let_def split: prod.splits if_splits)
  then obtain env1 ffs frs where f: "okW (foldrW (SIMPL0 al) dps (env, [], [])) (env1, ffs, frs)"
    and rest: "okW (S al env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by blast
  have a1: "acyc env1" using foldrW_SIMPL0_acyc[OF f] "1.prems"(2) by simp
  from rest show ?case
  proof
    assume "okW (S al env1 (frs @ ffs)) st'"
    from IH[OF this a1] show ?thesis .
  qed (use a1 in simp)
qed

theorem SIMPL_acyc: "okW (SIMPL al env dps) (env', ffs, frs) \<Longrightarrow> acyc env \<Longrightarrow> acyc env'"
  using SIMPL_acyc_aux by fastforce

end

end
