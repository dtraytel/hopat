section \<open>Sequences of Results that Bind No Loose Name\<close>

theory Unify_Seq_Loose
  imports Unify_Match_Fin Unify_Flexflex_Sound
begin

text \<open>
  The statements on the sequences of \<open>MATCH\<close> and of the search have two readings, as those on
  computations (\<open>lxokE\<close> in theory \<open>Unify_Simpl_Term\<close>): without loose names, a sequence is finite
  and its elements satisfy a predicate (\<^const>\<open>fin\<close>); with loose names, the elements whose
  environments bind no loose name satisfy it. For the second reading the environments of the
  elements have to extend the environments from which the sequence was made, also where the
  invariants of the termination proofs are not available. This is a property of the code alone;
  the first part of this theory proves it.
\<close>

subsection \<open>The environments of the elements extend those of the sequence\<close>

fun eenv :: "elem \<Rightarrow> env" where
  "eenv (El_R env tps) = env"
| "eenv (El_E env dps) = env"

context pure_sig_gen
begin

text \<open>\<open>sext e s\<close>: the environments in the sequence \<open>s\<close> extend \<open>e\<close>.\<close>

inductive sext :: "env \<Rightarrow> seq \<Rightarrow> bool" for e where
  Empty: "sext e S_Empty"
| Single: "extends e (eenv x) \<Longrightarrow> sext e (S_Single x)"
| AddUnify: "extends e env \<Longrightarrow> sext e R \<Longrightarrow> sext e (S_AddUnify td env dps R)"
| ItRight: "sext e xq \<Longrightarrow> sext e yq \<Longrightarrow> sext e (S_ItRight td xq yq)"
| Proj: "extends e env \<Longrightarrow> sext e tail \<Longrightarrow> sext e (S_Proj vname env Ts Us targs rb u dps head targ X tail)"
| Maps: "sext e xq \<Longrightarrow> sext e (S_Maps vname env0 rb targs G uarg xq)"
| Append: "sext e xq \<Longrightarrow> sext e yq \<Longrightarrow> sext e (S_Append xq yq)"

inductive_cases sext_SingleE: "sext e (S_Single x)"
inductive_cases sext_AddUnifyE: "sext e (S_AddUnify td env dps R)"
inductive_cases sext_ItRightE: "sext e (S_ItRight td xq yq)"
inductive_cases sext_ProjE: "sext e (S_Proj vname env Ts Us targs rb u dps head targ X tail)"
inductive_cases sext_MapsE: "sext e (S_Maps vname env0 rb targs G uarg xq)"
inductive_cases sext_AppendE: "sext e (S_Append xq yq)"


lemma sext_mono: "sext e s \<Longrightarrow> extends e' e \<Longrightarrow> sext e' s"
  by (induction rule: sext.induct) (auto intro: sext.intros extends_trans)

lemma copyargs_sext: "extends e env \<Longrightarrow> sext e (copyargs vname env0 rb targs gus env dps)"
  by (induction gus) (auto intro: sext.intros)

lemma make_args_extends: "make_args name Ts env Us = (env', args) \<Longrightarrow> extends env env'"
  by (erule make_args_props) (rule extends_tenv_eq)

lemma gentvars_extends: "gentvars p env = (env', Cs) \<Longrightarrow> extends env env'"
  using gentvars_props[of p env env' Cs] by (auto intro: extends_tenv_eq)

lemma extends_updateX: "ok (update X b e1) e2 \<Longrightarrow> extends e1 e2"
  by (cases X) (auto intro: extends_update)

lemma proj_unify_extends: "okW (proj_unify cfg base bary Cs env) env' \<Longrightarrow> extends env env'"
  using cunify_types_sound(2) by (auto simp: proj_unify_def test_unify_types_ok split: if_splits)

lemma projenv_sext:
  assumes "sext env tail" "okW (projenv cfg vname rb targs u env dps X base Ts head Usb targ p tail) s"
  shows "sext env s"
proof -
  obtain Us bary where Usb: "Usb = (Us, bary)" by (cases Usb)
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  let ?m = "bindW (proj_unify cfg base bary Cs env0)
      (\<lambda>env'. returnW (S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ X tail))"
  let ?h = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e"
  have "okW (handleW ?m ?h) s" using assms(2) by (simp add: projenv_def Usb g)
  then consider "okW ?m s" | e where "okW (?h e) s" unfolding okW_handleW by blast
  then show ?thesis
  proof cases
    case 1
    then obtain env' where pu: "okW (proj_unify cfg base bary Cs env0) env'"
      and s: "s = S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ X tail" by auto
    have "extends env env'" by (rule extends_trans[OF gentvars_extends[OF g] proj_unify_extends[OF pu]])
    then show ?thesis unfolding s using assms(1) by (rule sext.Proj)
  next
    case 2
    then have "s = tail" by (cases e) auto
    with assms(1) show ?thesis by simp
  qed
qed

lemma foldrW_projenv_sext:
  "sext env tail \<Longrightarrow> okW (foldrW (projenv cfg vname rb targs u env dps X base Ts head Usb targ) ps tail) s \<Longrightarrow>
    sext env s"
proof (induction ps arbitrary: s)
  case (Cons p ps)
  from Cons.prems(2) obtain s1 where
    "okW (foldrW (projenv cfg vname rb targs u env dps X base Ts head Usb targ) ps tail) s1"
    "okW (projenv cfg vname rb targs u env dps X base Ts head Usb targ p s1) s" by auto
  from projenv_sext[OF Cons.IH[OF Cons.prems(1) this(1)] this(2)] show ?case .
qed simp

lemma imitate_sext:
  assumes "okW (imitate vname env0 rb targs env dps X Ts uhead uargs) s"
  shows "sext env s"
proof -
  from assms obtain Us where im: "okW (case make_args vname Ts env Us of (env', args) \<Rightarrow>
      bindW (liftM (update X (types_abs Ts (list_comb uhead args)) env'))
        (\<lambda>env''. returnW (copyargs vname env0 rb targs (zip (map head_of args) uargs) env'' dps))) s"
    by (auto simp: imitate_def)
  obtain env' args where ma: "make_args vname Ts env Us = (env', args)" by (cases "make_args vname Ts env Us")
  from im ma obtain env'' where up: "ok (update X (types_abs Ts (list_comb uhead args)) env') env''"
    and s: "s = copyargs vname env0 rb targs (zip (map head_of args) uargs) env'' dps" by auto
  have "extends env env''"
    by (rule extends_trans[OF make_args_extends[OF ma] extends_updateX[OF up]])
  then show ?thesis unfolding s by (rule copyargs_sext)
qed

lemma matchfun_sext:
  "okW (matchfun cfg vname env0 rb targs u env dps X uhead uargs base Ts projs) s \<Longrightarrow> sext env s"
proof (induction projs arbitrary: s)
  case Nil
  then show ?case by (cases uhead) (auto intro: imitate_sext sext.Empty)
next
  case (Cons pr projs)
  obtain bvar T targ where pr: "pr = (bvar, T, targ)" by (cases pr)
  from Cons.prems obtain Us bary tail where
    t: "okW (matchfun cfg vname env0 rb targs u env dps X uhead uargs base Ts projs) tail"
    and f: "okW (foldrW (projenv cfg vname rb targs u env dps X base Ts bvar (Us, bary) targ)
      (arity_guesses cfg bary) tail) s"
    by (auto simp: pr)
  from foldrW_projenv_sext[OF Cons.IH[OF t] f] show ?case .
qed

lemma mc_sext: "okW (mc cfg vname env0 X rb targs u env dps) s \<Longrightarrow> sext env s"
proof (induction "size u" arbitrary: u X rb targs env s rule: less_induct)
  case less
  note mc = less.prems[unfolded mc.simps[of cfg vname env0 X rb targs u env dps]]
  from mc obtain r where r: "ok (lookup env (fst X) (snd X)) r" by auto
  show ?case
  proof (cases "r \<noteq> None")
    case True
    with mc r have "s = S_Single (El_E env ((rb, list_comb (Var (fst X) (snd X)) targs, u) # dps))" by auto
    then show ?thesis by (auto intro: sext.Single extends_refl)
  next
    case False
    let ?uh = "fst (strip_comb u)"
    from mc r False obtain T0 base Ts where rest: "okW (case ?uh of
        Abs a T body \<Rightarrow> bindW (liftM (fastype env ((a, T) # rb) body)) (\<lambda>B.
          (case genvar vname env (foldr fun_type (Ts @ [T]) B) of (env', Y) \<Rightarrow>
            bindW (dest_Var Y) (\<lambda>Y'.
              bindW (liftM (update X (types_abs Ts (Abs a T (combound Y 0 (Suc (length Ts))))) env')) (\<lambda>env''.
                mc cfg vname env0 Y' ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env'' dps))))
      | Var w _ \<Rightarrow>
          (case genvar (fst w) env (foldr fun_type Ts base) of (env', newhd) \<Rightarrow>
            bindW (liftM (update X (types_abs Ts (combound newhd 0 (length Ts))) env')) (\<lambda>env''.
              returnW (S_Single (El_E env'' ((rb, list_comb newhd targs, u) # dps)))))
      | _ \<Rightarrow> bindW (make_projs u targs Ts targs) (\<lambda>projs.
          matchfun cfg vname env0 rb targs u env dps X ?uh (snd (strip_comb u)) base Ts (rev projs))) s"
      by (auto simp: Let_def)
    note upx = extends_updateX
    show ?thesis
    proof (cases ?uh)
      case (Abs a T body)
      from rest[unfolded Abs] obtain B where B: "ok (fastype env ((a, T) # rb) body) B"
        and r1: "okW (case genvar vname env (foldr fun_type (Ts @ [T]) B) of (env', Y) \<Rightarrow>
            bindW (dest_Var Y) (\<lambda>Y'.
              bindW (liftM (update X (types_abs Ts (Abs a T (combound Y 0 (Suc (length Ts))))) env')) (\<lambda>env''.
                mc cfg vname env0 Y' ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env'' dps))) s"
        by auto
      obtain env' Y where g: "genvar vname env (foldr fun_type (Ts @ [T]) B) = (env', Y)"
        by (cases "genvar vname env (foldr fun_type (Ts @ [T]) B)")
      from r1[unfolded g prod.case okW_bindW] obtain Y' where r2: "\<exists>env''.
          okW (liftM (update X (types_abs Ts (Abs a T (combound Y 0 (Suc (length Ts))))) env')) env'' \<and>
          okW (mc cfg vname env0 Y' ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env'' dps) s"
        by blast
      then obtain env'' where
        up: "ok (update X (types_abs Ts (Abs a T (combound Y 0 (Suc (length Ts))))) env') env''"
        and m: "okW (mc cfg vname env0 Y' ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env'' dps) s"
        by auto
      have "size body < size u" by (rule strip_comb_Abs_size[OF Abs])
      from less.hyps[OF this m] have "sext env'' s" .
      moreover have "extends env env''" by (rule extends_trans[OF extends_genvar[OF g] upx[OF up]])
      ultimately show ?thesis by (rule sext_mono)
    next
      case (Var w W)
      obtain env' newhd where g: "genvar (fst w) env (foldr fun_type Ts base) = (env', newhd)"
        by (cases "genvar (fst w) env (foldr fun_type Ts base)")
      from rest[unfolded Var] g obtain env'' where
        up: "ok (update X (types_abs Ts (combound newhd 0 (length Ts))) env') env''"
        and s: "s = S_Single (El_E env'' ((rb, list_comb newhd targs, u) # dps))" by auto
      have "extends env env''" by (rule extends_trans[OF extends_genvar[OF g] upx[OF up]])
      then show ?thesis unfolding s by (auto intro: sext.Single)
    qed (use rest in \<open>auto intro: matchfun_sext\<close>)
  qed
qed

lemma copycons_sext: "okW (copycons cfg vname env0 rb targs G uarg env dps) cs \<Longrightarrow> sext env cs"
  by (auto simp: copycons_def split: if_splits intro: mc_sext sext.Single extends_refl)

lemma match_pair_sext: "okW (match_pair cfg env dp dps) s \<Longrightarrow> sext env s"
proof -
  assume m: "okW (match_pair cfg env dp dps) s"
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain h targs where st: "strip_comb t = (h, targs)" by (cases "strip_comb t")
  from m dp st obtain v T where "h = Var v T" by (cases h) (auto simp: match_pair_def)
  with m dp st have "okW (mc cfg (fst v) env (v, T) rb targs u env dps) s" by (simp add: match_pair_def)
  then show ?thesis by (rule mc_sext)
qed

lemma match_sat_sext: "okW (match_sat cfg env dp dps) s \<Longrightarrow> sext env s"
proof -
  assume m: "okW (match_sat cfg env dp dps) s"
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain h targs where st: "strip_comb t = (h, targs)" by (cases "strip_comb t")
  from m dp st obtain v T where h: "h = Var v T" by (cases h) (auto simp: match_sat_def)
  from m dp st h obtain Ts where
    "okW (match_pair cfg env (eta_expand_dpair (drop (length targs) Ts) dp) dps) s"
    by (auto simp: match_sat_def)
  then show ?thesis by (rule match_pair_sext)
qed

lemma match_eta_sext:
  assumes "sext env tail" "okW (match_eta cfg env dp dps B j tail) s"
  shows "sext env s"
proof (cases "j = 0")
  case True
  with assms show ?thesis by (auto simp: match_eta_def intro: sext.Append match_sat_sext)
next
  case False
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by (cases "gentvars (Suc j) env")
  let ?m = "bindW (cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1)
      (\<lambda>env2. bindW (match_sat cfg env2 dp dps) (\<lambda>s. returnW (S_Append s tail)))"
  let ?h = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e"
  have "okW (handleW ?m ?h) s" using assms(2) False by (simp add: match_eta_def g)
  then consider "okW ?m s" | e where "okW (?h e) s" unfolding okW_handleW by blast
  then show ?thesis
  proof cases
    case 1
    then obtain env2 s1 where cu: "okW (cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1) env2"
      and ms: "okW (match_sat cfg env2 dp dps) s1" and s: "s = S_Append s1 tail" by auto
    have "extends env env2" by (rule extends_trans[OF gentvars_extends[OF g] cunify_types_sound(2)[OF cu]])
    from sext_mono[OF match_sat_sext[OF ms] this] assms(1) show ?thesis unfolding s by (rule sext.Append)
  next
    case 2
    then have "s = tail" by (cases e) auto
    with assms(1) show ?thesis by simp
  qed
qed

lemma MATCH_sext: "okW (MATCH cfg env dp dps) ms \<Longrightarrow> sext env ms"
proof -
  assume m: "okW (MATCH cfg env dp dps) ms"
  have f: "sext env s" if "okW (foldrW (match_eta cfg env dp dps B) js S_Empty) s" for B js s
    using that
  proof (induction js arbitrary: s)
    case (Cons j js)
    from Cons.prems obtain s1 where "okW (foldrW (match_eta cfg env dp dps B) js S_Empty) s1"
      "okW (match_eta cfg env dp dps B j s1) s" by auto
    from match_eta_sext[OF Cons.IH[OF this(1)] this(2)] show ?case .
  qed (auto intro: sext.Empty)
  from m show ?thesis
    by (auto simp: MATCH_def split: prod.splits pterm.splits if_splits intro: f match_sat_sext)
qed

text \<open>Hence the environment of an element extends every environment that the sequence extends:\<close>

theorem ev_sext: "ev cfg s x \<Longrightarrow> sext e s \<Longrightarrow> extends e (eenv x)"
proof (induction arbitrary: e rule: ev.induct)
  case (single x)
  then show ?case by (auto elim: sext_SingleE)
next
  case (au_tail reseq x td env dps)
  from au_tail.prems show ?case by (auto elim!: sext_AddUnifyE intro: au_tail.IH)
next
  case (au_res env dps env' ffs r td reseq)
  from au_res.prems have "extends e env" by (auto elim: sext_AddUnifyE)
  moreover have "extends env env'" using dstepD(1)[OF SIMPL_sound[OF au_res.hyps(1)]] .
  moreover have "extends env' (fst r)"
    using dstepD(1)[OF foldrW_add_ffpair_sound[of "cfg_alg cfg" ffs env' "[]" "fst r" "snd r"]] au_res.hyps(2)
    by simp
  ultimately show ?case by (auto intro: extends_trans)
next
  case (au_match env dps env' ffs dp frs td ms reseq x)
  from au_match.prems have e: "extends e env" "sext e reseq" by (auto elim: sext_AddUnifyE)
  have "extends e env'" by (rule extends_trans[OF e(1) dstepD(1)[OF SIMPL_sound[OF au_match.hyps(1)]]])
  from sext_mono[OF MATCH_sext[OF au_match.hyps(3)] this] e(2)
  have "sext e (S_ItRight (td + 1) ms reseq)" by (rule sext.ItRight)
  then show ?case by (rule au_match.IH)
next
  case (ir_tail yq x td xq)
  from ir_tail.prems show ?case by (auto elim!: sext_ItRightE intro: ir_tail.IH)
next
  case (ir_head xq env dps td x yq)
  from ir_head.prems have "sext e xq" by (auto elim: sext_ItRightE)
  from ir_head.IH(1)[OF this] have "extends e env" by simp
  moreover have "extends env (eenv x)"
    by (rule ir_head.IH(2)[of env S_Empty]) (auto intro: sext.intros extends_refl)
  ultimately show ?case by (rule extends_trans)
next
  case (proj vname Ts env Us env' args X head env'' rb targ targs u dpairs env2 frigid fflex tail)
  from proj.prems have "extends e env" by (auto elim: sext_ProjE)
  moreover have "extends env env'" by (rule make_args_extends[OF proj.hyps(1)])
  moreover have "extends env' env''" by (rule extends_updateX[OF proj.hyps(2)])
  moreover have "extends env'' env2" using dstepD(1)[OF SIMPL_sound[OF proj.hyps(3)]] .
  ultimately show ?case by (auto intro: extends_trans)
next
  case (proj_tail tail x vname env Ts Us targs rb u dpairs head targ X)
  from proj_tail.prems show ?case by (auto elim!: sext_ProjE intro: proj_tail.IH)
next
  case (maps xq env dps vname env0 rb targs G uarg cs x)
  from maps.prems have "sext e xq" by (auto elim: sext_MapsE)
  from maps.IH(1)[OF this] have "extends e env" by simp
  moreover have "extends env (eenv x)" by (rule maps.IH(2)[OF copycons_sext[OF maps.hyps(2)]])
  ultimately show ?case by (rule extends_trans)
next
  case (append_l xq x yq)
  from append_l.prems show ?case by (auto elim!: sext_AppendE intro: append_l.IH)
next
  case (append_r yq x xq)
  from append_r.prems show ?case by (auto elim!: sext_AppendE intro: append_r.IH)
qed

corollary ev_nfree:
  assumes "ev cfg s x" "sext e s" "nfree (eenv x)"
  shows "nfree e"
  by (rule nfree_extends[OF ev_sext[OF assms(1,2)] assms(3)])


subsection \<open>Sequences\<close>

definition lfin :: "cfg \<Rightarrow> seq \<Rightarrow> (elem \<Rightarrow> bool) \<Rightarrow> bool" where
  "lfin cfg s Q \<longleftrightarrow> (if loose = {} then fin cfg s Q else (\<forall>x. ev cfg s x \<longrightarrow> nfree (eenv x) \<longrightarrow> Q x))"

lemma lfin_strict: "loose = {} \<Longrightarrow> lfin cfg s Q \<longleftrightarrow> fin cfg s Q"
  unfolding lfin_def by simp

lemma lfin_D: "lfin cfg s Q \<Longrightarrow> ev cfg s x \<Longrightarrow> nfree (eenv x) \<Longrightarrow> Q x"
  unfolding lfin_def fin_def using evals_ev by (auto split: if_splits)

lemma lfin_looseI: "loose \<noteq> {} \<Longrightarrow> (\<And>x. ev cfg s x \<Longrightarrow> nfree (eenv x) \<Longrightarrow> Q x) \<Longrightarrow> lfin cfg s Q"
  unfolding lfin_def by simp

lemma lfin_mono: "lfin cfg s P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> lfin cfg s Q"
  unfolding lfin_def using fin_mono[of cfg s P Q] by (auto split: if_splits)

lemma lfin_Empty [simp]: "lfin cfg S_Empty Q"
  unfolding lfin_def by (auto elim: ev_EmptyE)

lemma lfin_Single: "(nfree (eenv x) \<Longrightarrow> Q x) \<Longrightarrow> lfin cfg (S_Single x) Q"
  unfolding lfin_def using nfree_strict by (auto elim: ev_SingleE intro: fin_Single)

lemma lfin_Append: "lfin cfg xq Q \<Longrightarrow> lfin cfg yq Q \<Longrightarrow> lfin cfg (S_Append xq yq) Q"
  unfolding lfin_def by (auto elim: ev_AppendE intro: fin_Append split: if_splits)

text \<open>The environment at the start may be assumed to bind no loose name:\<close>

lemma lfin_nfree:
  assumes "nfree e0 \<Longrightarrow> lfin cfg s Q" "sext e0 s"
  shows "lfin cfg s Q"
proof (cases "loose = {}")
  case True
  then show ?thesis using assms(1) nfree_strict by blast
next
  case False
  then show ?thesis by (rule lfin_looseI) (use assms ev_nfree lfin_D in blast)
qed

text \<open>
  Computations that return a sequence: the first argument of \<open>lxokE\<close> is not used for them
  (the condition is on the elements), and is set to an environment without bindings.
\<close>

definition env_empty :: env where
  "env_empty = Envir 0 vt_empty vt_empty"

lemma nfree_env_empty [simp]: "nfree env_empty"
  by (simp add: nfree_def env_empty_def)

abbreviation lxokS :: "(uexn \<Rightarrow> bool) \<Rightarrow> 'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "lxokS Xe m P \<equiv> lxokE Xe (\<lambda>_. env_empty) m P"

lemma lxokS_strict: "loose = {} \<Longrightarrow>
    lxokS Xe m P \<longleftrightarrow> (\<exists>evs e. m = Some (evs, Err e) \<and> Xe e) \<or> (\<exists>x. okW m x \<and> P x)"
  by (rule lxokE_strict)

lemma lxokS_D: "lxokS Xe m P \<Longrightarrow> okW m x \<Longrightarrow> P x"
  by (erule lxokE_D) simp_all

lemma lxokS_looseI: "loose \<noteq> {} \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x) \<Longrightarrow> lxokS Xe m P"
  unfolding lxokE_def by simp

lemma lxokS_bindW:
  assumes "lxokS Xe m P" "\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> lxokS Xe (k x) Q"
  shows "lxokS Xe (bindW m k) Q"
  by (rule lxokE_bindW[OF assms(1)]) (use assms(2) in simp_all)

lemma lxokS_liftM_return: "m = return x \<Longrightarrow> lxokS Xe (f x) Q \<Longrightarrow> lxokS Xe (bindW (liftM m) f) Q"
  by (simp add: liftM_def return_def bindW_def option.map_id)

lemma lxokS_handle_CANTUNIFY_ret:
  assumes "lxokS (\<lambda>e. e = CANTUNIFY) m P" "\<And>x. P x \<Longrightarrow> Q x" "Q r"
  shows "lxokS (\<lambda>e. e = CANTUNIFY) (handleW m (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e)) Q"
proof -
  have h: "lxokS (\<lambda>e. e = CANTUNIFY) ((\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e) CANTUNIFY) Q"
    using assms(3) by simp
  have m': "lxokS (\<lambda>e. e = CANTUNIFY) m Q" by (rule lxokE_mono[OF assms(1)]) (rule assms(2))
  show ?thesis
  proof (rule lxokE_handleW[where h = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e", OF m' h])
    show "\<not> okW (case e of CANTUNIFY \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e) y" if "e \<noteq> CANTUNIFY" for e y
      using that by (cases e) auto
  qed
qed

lemma nfree_tenv: "tenv e' = tenv e \<Longrightarrow> nfree e' \<longleftrightarrow> nfree e"
  by (simp add: nfree_def)

lemma lxokE_Xmono: "lxokE Xe f m P \<Longrightarrow> (\<And>e. Xe e \<Longrightarrow> Xe' e) \<Longrightarrow> lxokE Xe' f m P"
  unfolding lxokE_def by (auto split: if_splits)

lemma lxokE_noCU: "lxok CANTUNIFY f m P \<Longrightarrow> noCU m \<Longrightarrow> lxokE (\<lambda>_. False) f m P"
  unfolding lxokE_def noCU_def by (auto split: if_splits)

lemma lxokS_bind_okW:
  assumes "okW m x" "lxokS Xe (k x) Q"
  shows "lxokS Xe (bindW m k) Q"
proof (rule lxokS_bindW[where P = "\<lambda>y. y = x"])
  show "lxokS Xe m (\<lambda>y. y = x)" by (rule lxokE_okI[OF assms(1)]) (rule refl)
  show "lxokS Xe (k y) Q" if "y = x" for y using that assms(2) by simp
qed

lemma lfin_mres_mono:
  "lfin cfg s (mres A1 env1) \<Longrightarrow> A0 \<subseteq> A1 \<Longrightarrow> tnew A0 env0 A1 env1 \<Longrightarrow> maxidx env0 \<le> maxidx env1 \<Longrightarrow>
    lfin cfg s (mres A0 env0)"
  by (erule lfin_mono) (rule mres_mono)

lemma lxokS_nfree:
  assumes "nfree e0 \<Longrightarrow> lxokS Xe m (\<lambda>s. lfin cfg s Q)" "\<And>s. okW m s \<Longrightarrow> sext e0 s"
  shows "lxokS Xe m (\<lambda>s. lfin cfg s Q)"
proof (cases "loose = {}")
  case True
  then show ?thesis using assms(1) nfree_strict by blast
next
  case False
  then show ?thesis
  proof (rule lxokS_looseI)
    fix s assume s: "okW m s"
    show "lfin cfg s Q" by (rule lfin_nfree[OF lxokS_D[OF assms(1) s] assms(2)[OF s]])
  qed
qed

lemma foldrW_lxokS_lfin:
  assumes "\<And>x b. x \<in> set xs \<Longrightarrow> lfin cfg b Q \<Longrightarrow> lxokS Xe (f x b) (\<lambda>s. lfin cfg s Q)" "lfin cfg b0 Q"
  shows "lxokS Xe (foldrW f xs b0) (\<lambda>s. lfin cfg s Q)"
  using assms(1) by (induction xs) (auto intro: assms(2) lxokS_bindW)

text \<open>The sequences of \<open>MATCH\<close>:\<close>

lemma lfin_Maps:
  assumes "lfin cfg xq (\<lambda>x. \<exists>env dps. x = El_E env dps \<and>
      lxokS (\<lambda>_. False) (copycons cfg vname env0 rb targs G uarg env dps) (\<lambda>cs. lfin cfg cs Q))"
  shows "lfin cfg (S_Maps vname env0 rb targs G uarg xq) Q"
proof (cases "loose = {}")
  case True
  have "fin cfg xq (\<lambda>x. \<exists>env dps cs. x = El_E env dps \<and>
      okW (copycons cfg vname env0 rb targs G uarg env dps) cs \<and> fin cfg cs Q)"
    by (rule fin_mono[OF assms[unfolded lfin_strict[OF True]]])
      (auto simp: lxokS_strict[OF True] lfin_strict[OF True])
  from fin_Maps[OF this] show ?thesis by (simp add: lfin_strict[OF True])
next
  case False
  show ?thesis
  proof (rule lfin_looseI[OF False])
    fix x assume "ev cfg (S_Maps vname env0 rb targs G uarg xq) x" and nf: "nfree (eenv x)"
    then obtain env dps cs where xq: "ev cfg xq (El_E env dps)"
      and cc: "okW (copycons cfg vname env0 rb targs G uarg env dps) cs" and cs: "ev cfg cs x"
      by (auto elim: ev_MapsE)
    have "nfree env" by (rule ev_nfree[OF cs copycons_sext[OF cc] nf])
    with lfin_D[OF assms xq] have "lxokS (\<lambda>_. False) (copycons cfg vname env0 rb targs G uarg env dps) (\<lambda>cs. lfin cfg cs Q)"
      by simp
    from lfin_D[OF lxokS_D[OF this cc] cs nf] show "Q x" .
  qed
qed

lemma lfin_Proj:
  assumes ma: "make_args vname Ts env Us = (env', args)"
    and up: "ok (update X (types_abs Ts (list_comb head args)) env') env''"
    and s: "lcuok fst (SIMPL (cfg_alg cfg) env''
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (\<lambda>(env2, fr, ff). Q (El_E env2 (fr @ ff)))"
    and t: "lfin cfg tail Q"
  shows "lfin cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail) Q"
proof (cases "loose = {}")
  case True
  have s': "cuok (SIMPL (cfg_alg cfg) env''
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (\<lambda>(env2, fr, ff). Q (El_E env2 (fr @ ff)))"
    using s unfolding lxokE_strict[OF True] xokW_def by auto
  from fin_Proj[OF ma up s' t[unfolded lfin_strict[OF True]]]
  show ?thesis by (simp add: lfin_strict[OF True])
next
  case False
  show ?thesis
  proof (rule lfin_looseI[OF False])
    fix x assume ev: "ev cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail) x" and nf: "nfree (eenv x)"
    from ev consider (p) env2 frigid fflex where "x = El_E env2 (frigid @ fflex)"
        "okW (SIMPL (cfg_alg cfg) env''
          ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, frigid, fflex)"
      | (t) "ev cfg tail x"
      using ma up by (auto elim!: ev_ProjE)
    then show "Q x"
    proof cases
      case p
      from lxokE_D[OF s p(2)] nf p(1) show ?thesis by simp
    next
      case t
      from lfin_D[OF \<open>lfin cfg tail Q\<close> this nf] show ?thesis .
    qed
  qed
qed

text \<open>The search below the elements of a sequence:\<close>

lemma lfin_ItRight:
  assumes "lfin cfg xq (\<lambda>x. \<exists>env dps. x = El_E env dps \<and>
      (\<forall>R. lfin cfg R Q \<longrightarrow> lfin cfg (S_AddUnify td env dps R) Q))"
    and "lfin cfg yq Q"
  shows "lfin cfg (S_ItRight td xq yq) Q"
proof (cases "loose = {}")
  case True
  from fin_ItRight[of cfg xq Q td yq] assms show ?thesis by (simp add: lfin_strict[OF True])
next
  case False
  show ?thesis
  proof (rule lfin_looseI[OF False])
    fix x assume ev: "ev cfg (S_ItRight td xq yq) x" and nf: "nfree (eenv x)"
    from ev consider (tl) "ev cfg yq x"
      | (hd) env dps where "ev cfg xq (El_E env dps)" "\<And>R. ev cfg (S_AddUnify td env dps R) x"
      by (auto elim!: ev_ItRightE)
    then show "Q x"
    proof cases
      case tl
      from lfin_D[OF assms(2) this nf] show ?thesis .
    next
      case hd
      have "sext env (S_AddUnify td env dps S_Empty)" by (auto intro: sext.intros extends_refl)
      from ev_nfree[OF hd(2)[of S_Empty] this nf] have "nfree env" .
      with lfin_D[OF assms(1) hd(1)] have "lfin cfg (S_AddUnify td env dps S_Empty) Q" by simp
      from lfin_D[OF this hd(2) nf] show ?thesis .
    qed
  qed
qed

end

end
