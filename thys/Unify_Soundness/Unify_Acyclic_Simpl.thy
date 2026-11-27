section \<open>Acyclicity for Names with Several Types: the Occurs Check and \<open>SIMPL\<close>\<close>

theory Unify_Acyclic_Simpl
  imports Unify_Typed_Inv Unify_Occurs_Sound
begin

text \<open>
  The term environment stays acyclic (\<open>acyc\<close>, on names, ignoring types) through the steps of
  the higher-order unifier, for any names of the variables. Here: \<open>SIMPL\<close> keeps the environment acyclic;
  the occurs checks are sound by theory \<open>Unify_Occurs_Sound\<close>.
\<close>

context pure_sig_gen
begin

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
