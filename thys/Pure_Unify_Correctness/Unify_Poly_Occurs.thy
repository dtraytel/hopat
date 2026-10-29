section \<open>Problems with Type Variables: Occurs Checks on Instances\<close>

theory Unify_Poly_Occurs
  imports Unify_Poly_Typing
begin

text \<open>
  The occurs checks of \<open>unify.ML\<close> on a ground instance compute what they compute on the original
  problem, if the lookups of the variables are decided as in the original problem
  (\<^const>\<open>lkdec\<close>). The results contain no terms, so they are equal. Only the direction from the
  instance to the original problem is shown: it transfers the termination of the checks on
  ground problems.
\<close>

lemma head_of_in_pinst:
  assumes "head_of_in env' t' = Some r'"
  shows "env' = instE \<rho> env \<Longrightarrow> t' = inst \<rho> t \<Longrightarrow> tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    \<exists>r. head_of_in env t = Some r \<and> r' = instr \<rho> (inst \<rho>) r"
  using assms
proof (induction env' t' r' arbitrary: t rule: head_of_in.raw_induct[rotated, consumes 1])
  case (1 hoi env' t' r' t)
  note e = "1.prems"(1) and tt = "1.prems"(2) and ok = "1.prems"(3) and d = "1.prems"(4)
  show ?case
  proof (cases t)
    case (App f u)
    from "1.hyps" tt App have h: "hoi env' (inst \<rho> f) = Some r'" by simp
    have "vps f \<union> bvps env \<subseteq> vps t \<union> bvps env" using App by auto
    from "1.IH"[OF h e refl ok lkdec_mono[OF d this]] show ?thesis
      by (subst head_of_in.simps) (simp add: App)
  next
    case (Var xi T)
    have lk: "lookup env' xi (tsubst \<rho> T) = instM \<rho> (map_option (inst \<rho>)) (lookup env xi T)"
      unfolding e by (rule lookup_inst[OF ok lkdec_mono[OF d]]) (simp add: Var)
    from "1.hyps" tt Var lk obtain lr where lr: "lookup env xi T = Some lr"
      by (cases "lookup env xi T") (auto simp: instM_def)
    have hp: "head_of_in env t = bindM (lookup env xi T)
        (\<lambda>r. case r of Some u \<Rightarrow> head_of_in env u | None \<Rightarrow> return t)"
      by (subst head_of_in.simps) (simp add: Var)
    show ?thesis
    proof (cases "lr = Ok None \<or> (\<exists>e. lr = Err e)")
      case True
      then show ?thesis using "1.hyps" tt Var lk hp lr by (auto simp: return_def)
    next
      case False
      then obtain u where lu: "lr = Ok (Some u)" by (cases lr) auto
      from lr lu obtain U where b: "vt_lookup (tenv env) xi = Some (U, u)" using lookup_SomeD by blast
      from "1.hyps" tt Var lk lr lu have hu: "hoi env' (inst \<rho> u) = Some r'" by simp
      have "vps u \<union> bvps env \<subseteq> vps t \<union> bvps env" using bvpsI[OF b] by auto
      from "1.IH"[OF hu e refl ok lkdec_mono[OF d this]] show ?thesis using hp lr lu by simp
    qed
  qed (use "1.hyps" tt in \<open>subst head_of_in.simps; auto simp: return_def\<close>)+
qed


lemma occur_pinst:
  assumes "occur t' env' v seen = Some r'"
  shows "env' = instE \<rho> env \<Longrightarrow> t' = inst \<rho> t \<Longrightarrow> tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    \<exists>r. occur t env v seen = Some r \<and> r' = instr \<rho> id r"
  using assms
proof (induction t' env' v seen r' arbitrary: t rule: occur.raw_induct[rotated, consumes 1])
  case (1 oc t' env' v seen r' t)
  note e = "1.prems"(1) and tt = "1.prems"(2) and ok = "1.prems"(3) and d = "1.prems"(4)
  show ?case
  proof (cases t)
    case (Var xi T)
    show ?thesis
    proof (cases "xi \<in> set seen \<or> v = xi")
      case True
      then show ?thesis using "1.hyps" tt Var by (subst occur.simps) (auto simp: return_def)
    next
      case nseen: False
      have lk: "lookup env' xi (tsubst \<rho> T) = instM \<rho> (map_option (inst \<rho>)) (lookup env xi T)"
        unfolding e by (rule lookup_inst[OF ok lkdec_mono[OF d]]) (simp add: Var)
      from "1.hyps" tt Var nseen lk obtain lr where lr: "lookup env xi T = Some lr"
        by (cases "lookup env xi T") (auto simp: instM_def)
      have hp: "occur t env v seen = bindM (lookup env xi T)
          (\<lambda>r. case r of None \<Rightarrow> return (False, xi # seen) | Some u \<Rightarrow> occur u env v (xi # seen))"
        using nseen by (subst occur.simps) (simp add: Var)
      show ?thesis
      proof (cases "lr = Ok None \<or> (\<exists>e. lr = Err e)")
        case True
        then show ?thesis using "1.hyps" tt Var nseen lk hp lr by (auto simp: return_def)
      next
        case False
        then obtain u where lu: "lr = Ok (Some u)" by (cases lr) auto
        from lr lu obtain U where b: "vt_lookup (tenv env) xi = Some (U, u)" using lookup_SomeD by blast
        from "1.hyps" tt Var nseen lk lr lu have hu: "oc (inst \<rho> u) env' v (xi # seen) = Some r'" by simp
        have "vps u \<union> bvps env \<subseteq> vps t \<union> bvps env" using bvpsI[OF b] by auto
        from "1.IH"[OF hu e refl ok lkdec_mono[OF d this]] show ?thesis using hp lr lu by simp
      qed
    qed
  next
    case (Abs a T body)
    from "1.hyps" tt Abs have h: "oc (inst \<rho> body) env' v seen = Some r'" by simp
    have "vps body \<union> bvps env \<subseteq> vps t \<union> bvps env" using Abs by auto
    from "1.IH"[OF h e refl ok lkdec_mono[OF d this]] show ?thesis by (subst occur.simps) (simp add: Abs)
  next
    case (App f u)
    from "1.hyps" tt App have h: "bindM (oc (inst \<rho> u) env' v seen)
        (\<lambda>r. if fst r then return (True, snd r) else oc (inst \<rho> f) env' v (snd r)) = Some r'"
      by simp
    then obtain ru where hu: "oc (inst \<rho> u) env' v seen = Some ru" by (cases "oc (inst \<rho> u) env' v seen") auto
    have su: "vps u \<union> bvps env \<subseteq> vps t \<union> bvps env" and sf: "vps f \<union> bvps env \<subseteq> vps t \<union> bvps env"
      using App by auto
    from "1.IH"[OF hu e refl ok lkdec_mono[OF d su]] obtain r0 where
      r0: "occur u env v seen = Some r0" "ru = instr \<rho> id r0" by blast
    have hp: "occur t env v seen = bindM (occur u env v seen)
        (\<lambda>r. if fst r then return (True, snd r) else occur f env v (snd r))"
      by (subst occur.simps) (simp add: App)
    show ?thesis
    proof (cases r0)
      case (Ok p)
      show ?thesis
      proof (cases "fst p")
        case True
        then show ?thesis using h hu r0 Ok hp by (auto simp: return_def)
      next
        case False
        with h hu r0 Ok have hf: "oc (inst \<rho> f) env' v (snd p) = Some r'" by simp
        from "1.IH"[OF hf e refl ok lkdec_mono[OF d sf]] show ?thesis using hp r0 Ok False by simp
      qed
    qed (use h hu r0 hp in simp)
  qed (use "1.hyps" tt in \<open>subst occur.simps; auto simp: return_def\<close>)+
qed

lemma occurs_list_pinst:
  "occurs_list (instE \<rho> env) v seen (map (inst \<rho>) ts) = Some r' \<Longrightarrow> tyok env \<Longrightarrow>
    \<forall>t\<in>set ts. lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    \<exists>r. occurs_list env v seen ts = Some r \<and> r' = instr \<rho> id r"
proof (induction ts arbitrary: seen r')
  case Nil
  then show ?case by (auto simp: return_def)
next
  case (Cons t ts)
  from Cons.prems(1) obtain rt where ht: "occur (inst \<rho> t) (instE \<rho> env) v seen = Some rt"
    by (cases "occur (inst \<rho> t) (instE \<rho> env) v seen") auto
  from occur_pinst[OF ht refl refl Cons.prems(2)] Cons.prems(3) obtain r0 where
    r0: "occur t env v seen = Some r0" "rt = instr \<rho> id r0" by auto
  show ?case
  proof (cases r0)
    case (Ok p)
    show ?thesis
    proof (cases "fst p")
      case True
      then show ?thesis using Cons.prems(1) ht r0 Ok by (auto simp: return_def)
    next
      case False
      with Cons.prems(1) ht r0 Ok have "occurs_list (instE \<rho> env) v (snd p) (map (inst \<rho>) ts) = Some r'" by simp
      from Cons.IH[OF this Cons.prems(2)] Cons.prems(3) show ?thesis using r0 Ok False by simp
    qed
  qed (use Cons.prems(1) ht r0 in simp)
qed

lemma occomb_pinst:
  assumes "occomb oc' seen (inst \<rho> t) = Some r'"
    and "\<And>seen s r'. vps s \<subseteq> vps t \<Longrightarrow> oc' seen (inst \<rho> s) = Some r' \<Longrightarrow>
      \<exists>r. oc seen s = Some r \<and> r' = instr \<rho> id r"
  shows "\<exists>r. occomb oc seen t = Some r \<and> r' = instr \<rho> id r"
  using assms
proof (induction t arbitrary: seen r')
  case (App f u)
  from App.prems(1) have h: "bindM (oc' seen (inst \<rho> u)) (\<lambda>r. if fst r = Rigid then return (Rigid, snd r)
      else bindM (occomb oc' (snd r) (inst \<rho> f))
        (\<lambda>r2. return (if fst r2 = NoOcc then fst r else fst r2, snd r2))) = Some r'"
    by simp
  then obtain ru where hu: "oc' seen (inst \<rho> u) = Some ru" by (cases "oc' seen (inst \<rho> u)") auto
  from App.prems(2)[OF _ hu] obtain r0 where r0: "oc seen u = Some r0" "ru = instr \<rho> id r0" by auto
  show ?case
  proof (cases r0)
    case (Ok p)
    show ?thesis
    proof (cases "fst p = Rigid")
      case True
      then show ?thesis using h hu r0 Ok by (auto simp: return_def)
    next
      case False
      with h hu r0 Ok have hf: "bindM (occomb oc' (snd p) (inst \<rho> f))
          (\<lambda>r2. return (if fst r2 = NoOcc then fst p else fst r2, snd r2)) = Some r'" by simp
      then obtain rf where rf: "occomb oc' (snd p) (inst \<rho> f) = Some rf"
        by (cases "occomb oc' (snd p) (inst \<rho> f)") auto
      have hf': "\<exists>r. oc seen s = Some r \<and> r' = instr \<rho> id r"
        if "vps s \<subseteq> vps f" "oc' seen (inst \<rho> s) = Some r'" for seen s r'
        using App.prems(2)[of s seen r'] that by auto
      from App.IH(1)[OF rf hf'] obtain r1 where
        r1: "occomb oc (snd p) f = Some r1" "rf = instr \<rho> id r1" by blast
      show ?thesis using hf rf r1 r0 Ok False by (cases r1) (auto simp: return_def)
    qed
  qed (use h hu r0 in simp)
qed (use assms in auto)

lemma pattern_occ_inst[simp]: "pattern_occ v (inst \<rho> t) \<longleftrightarrow> pattern_occ v t"
proof -
  obtain h ts where s: "strip_comb t = (h, ts)" by force
  have "strip_comb (inst \<rho> t) = (inst \<rho> h, map (inst \<rho>) ts)"
    using s by (simp add: strip_comb_inst)
  moreover have "is_Bound (inst \<rho> s) \<longleftrightarrow> is_Bound s" for s by simp
  ultimately show ?thesis using s by (cases h) (auto simp: pattern_occ_def list_all_iff)
qed


lemma nonrigid_pinst:
  "nonrigid (instE \<rho> env) v seen (inst \<rho> t) = Some r' \<Longrightarrow> tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    \<exists>r. nonrigid env v seen t = Some r \<and> r' = instr \<rho> id r"
proof -
  assume a: "nonrigid (instE \<rho> env) v seen (inst \<rho> t) = Some r'" "tyok env" "lkdec \<rho> env (vps t \<union> bvps env)"
  from a(1) obtain ro where o: "occurs_list (instE \<rho> env) v seen (map (inst \<rho>) [t]) = Some ro"
    by (cases "occurs_list (instE \<rho> env) v seen [inst \<rho> t]") (auto simp: nonrigid_def)
  from occurs_list_pinst[OF o a(2)] a(3) obtain r0 where
    r0: "occurs_list env v seen [t] = Some r0" "ro = instr \<rho> id r0" by auto
  show ?thesis using a(1) o r0 by (cases r0) (auto simp: nonrigid_def return_def)
qed

lemma rocc_pinst:
  assumes "rocc t' env' v seen = Some r'"
  shows "env' = instE \<rho> env \<Longrightarrow> t' = inst \<rho> t \<Longrightarrow> tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    \<exists>r. rocc t env v seen = Some r \<and> r' = instr \<rho> id r"
  using assms
proof (induction t' env' v seen r' arbitrary: t rule: rocc.raw_induct[rotated, consumes 1])
  case (1 rc t' env' v seen r' t)
  note e = "1.prems"(1) and tt = "1.prems"(2) and ok = "1.prems"(3) and d = "1.prems"(4)
  show ?case
  proof (cases t)
    case (Var xi T)
    show ?thesis
    proof (cases "xi \<in> set seen \<or> v = xi")
      case True
      then show ?thesis using "1.hyps" tt Var by (subst rocc.simps) (auto simp: return_def)
    next
      case nseen: False
      have lk: "lookup env' xi (tsubst \<rho> T) = instM \<rho> (map_option (inst \<rho>)) (lookup env xi T)"
        unfolding e by (rule lookup_inst[OF ok lkdec_mono[OF d]]) (simp add: Var)
      from "1.hyps" tt Var nseen lk obtain lr where lr: "lookup env xi T = Some lr"
        by (cases "lookup env xi T") (auto simp: instM_def)
      have hp: "rocc t env v seen = bindM (lookup env xi T)
          (\<lambda>r. case r of None \<Rightarrow> return (NoOcc, xi # seen) | Some u \<Rightarrow> rocc u env v (xi # seen))"
        using nseen by (subst rocc.simps) (simp add: Var)
      show ?thesis
      proof (cases "lr = Ok None \<or> (\<exists>e. lr = Err e)")
        case True
        then show ?thesis using "1.hyps" tt Var nseen lk hp lr by (auto simp: return_def)
      next
        case False
        then obtain u where lu: "lr = Ok (Some u)" by (cases lr) auto
        from lr lu obtain U where b: "vt_lookup (tenv env) xi = Some (U, u)" using lookup_SomeD by blast
        from "1.hyps" tt Var nseen lk lr lu have hu: "rc (inst \<rho> u) env' v (xi # seen) = Some r'" by simp
        have "vps u \<union> bvps env \<subseteq> vps t \<union> bvps env" using bvpsI[OF b] by auto
        from "1.IH"[OF hu e refl ok lkdec_mono[OF d this]] show ?thesis using hp lr lu by simp
      qed
    qed
  next
    case (Abs a T body)
    from "1.hyps" tt Abs have h: "rc (inst \<rho> body) env' v seen = Some r'" by simp
    have "vps body \<union> bvps env \<subseteq> vps t \<union> bvps env" using Abs by auto
    from "1.IH"[OF h e refl ok lkdec_mono[OF d this]] show ?thesis by (subst rocc.simps) (simp add: Abs)
  next
    case (App f u)
    let ?C' = "\<lambda>h. case h of Var w _ \<Rightarrow> if v = w \<and> pattern_occ v (inst \<rho> t) then return (Rigid, seen)
          else nonrigid env' v seen (inst \<rho> t)
        | Abs _ _ _ \<Rightarrow> nonrigid env' v seen (inst \<rho> t)
        | _ \<Rightarrow> occomb (\<lambda>seen t. rc t env' v seen) seen (inst \<rho> t)"
    from "1.hyps" tt App have h: "bindM (head_of_in env' (inst \<rho> f)) ?C' = Some r'"
      by (simp only: inst.simps pterm.case)
    then obtain rh where hh: "head_of_in env' (inst \<rho> f) = Some rh" by (cases "head_of_in env' (inst \<rho> f)") auto
    have sf: "vps f \<union> bvps env \<subseteq> vps t \<union> bvps env" using App by auto
    from head_of_in_pinst[OF hh e refl ok lkdec_mono[OF d sf]] obtain rh0 where
      rh0: "head_of_in env f = Some rh0" "rh = instr \<rho> (inst \<rho>) rh0" by blast
    have hp: "rocc t env v seen = bindM (head_of_in env f) (\<lambda>h. case h of
          Var w _ \<Rightarrow> if v = w \<and> pattern_occ v t then return (Rigid, seen) else nonrigid env v seen t
        | Abs _ _ _ \<Rightarrow> nonrigid env v seen t
        | _ \<Rightarrow> occomb (\<lambda>seen t. rocc t env v seen) seen t)"
      by (subst rocc.simps) (simp add: App)
    have nr: "\<exists>r. nonrigid env v seen t = Some r \<and> r' = instr \<rho> id r"
      if "nonrigid env' v seen (inst \<rho> t) = Some r'"
      using nonrigid_pinst[OF that[unfolded e] ok d] .
    have oc: "\<exists>r. occomb (\<lambda>seen t. rocc t env v seen) seen t = Some r \<and> r' = instr \<rho> id r"
      if "occomb (\<lambda>seen t. rc t env' v seen) seen (inst \<rho> t) = Some r'"
    proof (rule occomb_pinst[OF that])
      fix seen s r' assume s: "vps s \<subseteq> vps t" "rc (inst \<rho> s) env' v seen = Some r'"
      have "vps s \<union> bvps env \<subseteq> vps t \<union> bvps env" using s(1) by auto
      from "1.IH"[OF s(2) e refl ok lkdec_mono[OF d this]]
      show "\<exists>r. rocc s env v seen = Some r \<and> r' = instr \<rho> id r" .
    qed
    show ?thesis
    proof (cases rh0)
      case (Ok h0)
      with h hh rh0 have h': "?C' (inst \<rho> h0) = Some r'" by simp
      show ?thesis
      proof (cases h0)
        case (Var w W)
        show ?thesis
        proof (cases "v = w \<and> pattern_occ v t")
          case True
          then show ?thesis using h' hp rh0 Ok Var by (auto simp: return_def)
        next
          case False
          with h' Var have "nonrigid env' v seen (inst \<rho> t) = Some r'" by simp
          from nr[OF this] show ?thesis using hp rh0 Ok Var False by simp
        qed
      next
        case (Abs a T b)
        with h' have "nonrigid env' v seen (inst \<rho> t) = Some r'" by simp
        from nr[OF this] show ?thesis using hp rh0 Ok Abs by simp
      qed (use h' hp rh0 Ok oc in simp_all)
    qed (use h hh rh0 hp in simp)
  qed (use "1.hyps" tt in \<open>subst rocc.simps; auto simp: return_def\<close>)+
qed

lemma rigid_occurs_term_pinst:
  assumes "rigid_occurs_term (instE \<rho> env) v (inst \<rho> t) = Some r'" "tyok env" "lkdec \<rho> env (vps t \<union> bvps env)"
  shows "\<exists>r. rigid_occurs_term env v t = Some r \<and> r' = instr \<rho> id r"
proof -
  from assms(1) obtain ro where o: "rocc (inst \<rho> t) (instE \<rho> env) v [] = Some ro"
    by (cases "rocc (inst \<rho> t) (instE \<rho> env) v []") (auto simp: rigid_occurs_term_def)
  from rocc_pinst[OF o refl refl assms(2,3)] obtain r0 where
    r0: "rocc t env v [] = Some r0" "ro = instr \<rho> id r0" by blast
  show ?thesis using assms(1) o r0 by (cases r0) (auto simp: rigid_occurs_term_def return_def)
qed



subsection \<open>Body types modulo the type environment\<close>

lemma body_type_ptnorm:
  assumes ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and T: "tcons (tyenv env) T"
  shows "tnorm (tyenv env) T = foldr fun_type Us B \<Longrightarrow> \<not> is_funT B \<Longrightarrow>
    \<exists>B'. body_type env T = return B' \<and> tnorm (tyenv env) B' = B \<and> tcons (tyenv env) B'"
  using T
proof (induction arbitrary: Us rule: tnorm_induct[OF ac, consumes 1, case_names TFree Type Unbound Bound])
  case (TFree a S)
  then have "Us = []" by (cases Us) auto
  with TFree show ?case by (subst body_type.simps) (auto simp: return_def)
next
  case (Type a Ts)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>A U. Ts = [A, U])")
    case True
    then obtain A U where a: "a = STR ''fun''" and Ts: "Ts = [A, U]" by blast
    from Type.prems(1,2) a Ts obtain Us' where "tnorm (tyenv env) U = foldr fun_type Us' B"
      by (cases Us) auto
    from Type.IH[of U, OF _ this Type.prems(2)] Ts obtain B' where
      "body_type env U = return B'" "tnorm (tyenv env) B' = B" "tcons (tyenv env) B'" by auto
    then show ?thesis using body_type_fun[of env A U] by (simp add: a Ts)
  next
    case False
    have "Us = []"
    proof (rule ccontr)
      assume "Us \<noteq> []"
      then obtain A Us' where "Us = A # Us'" by (cases Us) auto
      with Type.prems(1) False show False by auto
    qed
    with Type.prems(1) Type.hyps False show ?thesis
      by (subst body_type.simps) (auto simp: return_def split: list.splits)
  qed
next
  case (Unbound v S)
  then have "Us = []" by (cases Us) (auto simp: tnorm_TVar[OF ac(1)])
  with Unbound show ?case
    by (subst body_type.simps) (auto simp: type_lookup_ok(1) bindM_def return_def tnorm_TVar[OF ac(1)] tcons_TVar)
next
  case (Bound v S U)
  have "tnorm (tyenv env) U = foldr fun_type Us B"
    using Bound.prems(1) Bound(1) by (simp add: tnorm_TVar[OF ac(1)])
  from Bound.IH[OF this Bound.prems(2)] obtain B' where
    "body_type env U = return B'" "tnorm (tyenv env) B' = B" "tcons (tyenv env) B'" by blast
  then show ?case using Bound(1)
    by (subst body_type.simps) (auto simp: type_lookup_ok(2) bindM_def return_def)
qed

end
