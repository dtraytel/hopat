section \<open>Composition of theorems with proofs\<close>

theory Proof_Bicompose
  imports Proof_Norm
begin

text \<open>
  \<^const>\<open>bicompose_proof\<close> builds the proof of a result of \<open>bicompose_aux\<close> from the proofs of
  the proof state and of the (renamed) rule. If it succeeds without a warning, the proof is
  valid for the result: the instance argument of the soundness of \<open>bicompose_aux\<close> carries
  over to the proofs, and the normalization of the proofs is correct at every instance.
\<close>

subsection \<open>Preliminaries\<close>

definition core_prf :: "bool \<Rightarrow> nat \<Rightarrow> pterm list \<Rightarrow> pterm option \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf" where
  "core_prf flatten lb oldAs A n m sprf p = PAppp
    (proof_combP sprf (map PBound (downto (integer_of_nat lb + integer_of_nat (length oldAs) - 1)
      (integer_of_nat (length oldAs)))))
    (proof_combP p ((if 0 < n then [mk_asm_prf (the A) n m] else []) @
      map (if flatten then flatten_params_proof 0 0 n else (\<lambda>x. PBound (snd x)))
        (zip oldAs (downto (integer_of_nat (length oldAs) - 1) 0))))"

lemma liftMP_eq_returnP: "liftMP m = returnW x \<longleftrightarrow> ok m x"
  by (auto simp: liftMP_def returnW_def)

lemma prf_aeq_proof_combP: "prf_aeq p p' \<Longrightarrow> prf_aeq (proof_combP p qs) (proof_combP p' qs)"
  unfolding proof_combP_def by (induction qs arbitrary: p p') (auto intro: prf_aeq.PAppp prf_aeq.refl)

lemma prf_aeq_mk_AbsP: "prf_aeq p p' \<Longrightarrow> prf_aeq (mk_AbsP xs p) (mk_AbsP xs p')"
  unfolding mk_AbsP_def by (induction xs) (auto intro: prf_aeq.AbsP simp: ann_eq_def)

lemma length_downto0: "length (downto (integer_of_nat k - 1) 0) = k"
  by (simp add: downto_map integer_reps integer_of_nat.rep_eq)

lemma nth_downto0: "j < k \<Longrightarrow> downto (integer_of_nat k - 1) 0 ! j = integer_of_nat (k - 1 - j)"
  by (simp add: downto_map integer_reps integer_of_nat.rep_eq integer_eq_iff of_nat_diff)

context prf_sig
begin

lemma prf_ap_simps [simp]:
  "prf_ap \<rho> \<sigma> (Abst a T p) = Abst a (map_option (tsubst \<rho>) T) (prf_ap \<rho> \<sigma> p)"
  "prf_ap \<rho> \<sigma> (AbsP a t p) = AbsP a (map_option (ap \<rho> \<sigma>) t) (prf_ap \<rho> \<sigma> p)"
  "prf_ap \<rho> \<sigma> (PAppt p t) = PAppt (prf_ap \<rho> \<sigma> p) (map_option (ap \<rho> \<sigma>) t)"
  "prf_ap \<rho> \<sigma> (PAppp p q) = PAppp (prf_ap \<rho> \<sigma> p) (prf_ap \<rho> \<sigma> q)"
  "prf_ap \<rho> \<sigma> (PBound i) = PBound i" "prf_ap \<rho> \<sigma> MinProof = MinProof" "prf_ap \<rho> \<sigma> (Hyp h) = Hyp h"
  by (simp_all add: prf_ap_def)

lemma prf_ap_proof_combt: "prf_ap \<rho> \<sigma> (proof_combt p ts) = proof_combt (prf_ap \<rho> \<sigma> p) (map (ap \<rho> \<sigma>) ts)"
  unfolding proof_combt_def by (induction ts arbitrary: p) simp_all

lemma prf_ap_flatten_params_proof: "prf_ap \<rho> \<sigma> (flatten_params_proof i j n x) = flatten_params_proof i j n x"
  by (induction i j n x rule: flatten_params_proof.induct)
    (simp_all add: prf_ap_proof_combP prf_ap_proof_combt comp_def)

lemma prf_ap_imp_prf: "prf_ap \<rho> \<sigma> (imp_prf A i m) = imp_prf A i m"
  by (induction A i m rule: imp_prf.induct) simp_all

lemma prf_ap_mk_asm_prf: "prf_ap \<rho> \<sigma> (mk_asm_prf A i m) = mk_asm_prf A i m"
proof -
  have "prf_ap \<rho> \<sigma> (all_prf i m A) = all_prf i m A"
    by (induction i m A rule: all_prf.induct) (simp_all add: prf_ap_imp_prf)
  then show ?thesis by (simp add: mk_asm_prf_def)
qed

lemma prf_ok_mono_H: "prf_ok ax H E e Hs p \<phi> \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> prf_ok ax H' E e Hs p \<phi>"
  by (induction rule: prf_ok.induct) (auto intro: prf_ok.intros)

text \<open>Renaming the schematic variables of a proof:\<close>

lemma prf_aeq_ren:
  "\<forall>t\<in>prf_terms p. \<forall>v\<in>vars t. m < snd (fst v) \<Longrightarrow>
    prf_aeq (prf_ap \<rho> (rsubst m (fst r) \<sigma>) p) (prf_ap \<rho> \<sigma> (map_proof_terms (ren_term r) id p))"
proof (induction p)
  have ae: "ann_eq (map_option (ap \<rho> (rsubst m (fst r) \<sigma>)) t) (map_option (ap \<rho> \<sigma>) (map_option (ren_term r) t))"
    if "\<forall>u\<in>set_option t. \<forall>v\<in>vars u. m < snd (fst v)" for t
  proof (cases t)
    case (Some u)
    have "aconv_term (vsubst \<sigma> (ren_term r (inst \<rho> u))) (vsubst (rsubst m (fst r) \<sigma>) (inst \<rho> u))"
      by (rule aconv_ren_term) (use that Some in \<open>auto simp: vars_inst\<close>)
    then have "ap \<rho> \<sigma> (ren_term r u) \<approx> ap \<rho> (rsubst m (fst r) \<sigma>) u"
      unfolding ap_def inst_ren_term by (rule conv_ueq[OF aconv_term_conv])
    then show ?thesis using Some by (simp add: ann_eq_def ueq_sym)
  qed (simp add: ann_eq_def)
  {
    case (AbsP a t p)
    with ae[of t] show ?case by (auto intro: prf_aeq.AbsP)
  next
    case (PAppt p t)
    with ae[of t] show ?case by (auto intro: prf_aeq.PAppt)
  next
    case (PAppp p q)
    then show ?case by (auto intro: prf_aeq.PAppp)
  next
    case (Abst a T p)
    then show ?case by (auto simp: option.map_ident intro: prf_aeq.Abst)
  }
qed (auto simp: prf_ap_def option.map_ident id_def intro: prf_aeq.refl)



subsection \<open>Conversion under a prefix\<close>

fun lap :: "tinst \<Rightarrow> vsubst \<Rightarrow> litem \<Rightarrow> litem" where
  "lap \<rho> \<sigma> (LImp c H) = LImp (ap \<rho> \<sigma> c) (ap \<rho> \<sigma> H)"
| "lap \<rho> \<sigma> (LAll c a T) = LAll (ap \<rho> \<sigma> c) a (tsubst \<rho> T)"

lemma ap_lift_pre: "ap \<rho> \<sigma> (lift_pre p X) = lift_pre (map (lap \<rho> \<sigma>) p) (ap \<rho> \<sigma> X)"
  by (induction p X rule: lift_pre.induct) simp_all

lemma ap_abs_pre: "ap \<rho> \<sigma> (abs_pre p X) = abs_pre (map (lap \<rho> \<sigma>) p) (ap \<rho> \<sigma> X)"
  by (induction p X rule: abs_pre.induct) simp_all

lemma litem_ok_lap: "litem_ok i \<Longrightarrow> litem_ok (lap \<rho> \<sigma> i)"
  by (cases i) auto

lemma typing_abs_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> e \<turnstile> lift_pre p X : propT \<Longrightarrow> e \<turnstile> abs_pre p X : ptys p \<Rrightarrow> propT"
proof (induction p arbitrary: e)
  case (Cons i p)
  have oki: "litem_ok i" and okp: "\<forall>i\<in>set p. litem_ok i" using Cons.prems(1) by simp_all
  show ?case
  proof (cases i)
    case (LImp c H)
    from typing_lift_pre_imp[OF oki Cons.prems(2) LImp] Cons.IH[OF okp] LImp show ?thesis by simp
  next
    case (LAll c a T)
    note t = typing_lift_pre_all[OF oki Cons.prems(2) LAll]
    have "cert_typ alg ar T" using typing_lift_pre[OF Cons.prems(1,2)] LAll by simp
    with Cons.IH[OF okp t(2)] LAll show ?thesis by auto
  qed
qed simp

lemma conv_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> e \<turnstile> lift_pre p X : propT \<Longrightarrow> e \<turnstile> lift_pre p Y : propT \<Longrightarrow>
    abs_pre p X \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_pre p Y \<Longrightarrow> lift_pre p X \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift_pre p Y"
proof (induction p arbitrary: e)
  case (Cons i p)
  have oki: "litem_ok i" and okp: "\<forall>i\<in>set p. litem_ok i" using Cons.prems(1) by simp_all
  have w: "wt (lift_pre (i # p) X)" "wt (lift_pre (i # p) Y)" using Cons.prems(2,3) by (auto simp: wt_def)
  show ?case
  proof (cases i)
    case (LImp c H)
    note tX = typing_lift_pre_imp[OF oki Cons.prems(2) LImp]
      and tY = typing_lift_pre_imp[OF oki Cons.prems(3) LImp]
    have "lift_pre p X \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift_pre p Y"
      by (rule Cons.IH[OF okp tX(3) tY(3)]) (use Cons.prems(4) LImp in simp)
    then show ?thesis using w unfolding tX(1) tY(1) by (rule conv_App[rotated 3]) simp_all
  next
    case (LAll c a T)
    note tX = typing_lift_pre_all[OF oki Cons.prems(2) LAll]
      and tY = typing_lift_pre_all[OF oki Cons.prems(3) LAll]
    have tA: "e \<turnstile> Abs a T (abs_pre p X) : T \<rightarrow>\<^sub>T (ptys p \<Rrightarrow> propT)"
      "e \<turnstile> Abs a T (abs_pre p Y) : T \<rightarrow>\<^sub>T (ptys p \<Rrightarrow> propT)"
      using typing_abs_pre[OF Cons.prems(1,2)] typing_abs_pre[OF Cons.prems(1,3)] LAll by simp_all
    have "abs_pre p X \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_pre p Y"
      by (rule conv_Abs_inv(2)[OF tA]) (use Cons.prems(4) LAll in simp)
    have wA: "wt (Abs a T (lift_pre p X))" "wt (Abs a T (lift_pre p Y))"
      using Cons.prems(2,3) unfolding tX(1) tY(1) wt_def by auto
    from Cons.IH[OF okp tX(2) tY(2) \<open>abs_pre p X \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_pre p Y\<close>]
    have "Abs a T (lift_pre p X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a T (lift_pre p Y)"
      by (rule conv_Abs[OF wA])
    then show ?thesis using w unfolding tX(1) tY(1) by (rule conv_App[rotated 3]) simp_all
  qed
qed simp

lemma conv_list_implies:
  "C \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> C' \<Longrightarrow> e \<turnstile> list_implies Ns C : propT \<Longrightarrow> e \<turnstile> list_implies Ns C' : propT \<Longrightarrow>
    list_implies Ns C \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> list_implies Ns C'"
proof (induction Ns)
  case (Cons N Ns)
  have w: "wt (list_implies (N # Ns) C)" "wt (list_implies (N # Ns) C')" using Cons.prems(2,3) by (auto simp: wt_def)
  have "list_implies Ns C \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> list_implies Ns C'"
    using Cons.IH[OF Cons.prems(1)] Cons.prems(2,3) by (simp add: typing_implies)
  then show ?case using w by simp (rule conv_App[rotated 3]; simp)
qed simp


subsection \<open>The skeleton\<close>

lemma bicompose_core_returnP:
  assumes "bicompose_core env flatten Bs As A oldAs n m sprf p = returnW x"
  shows "length oldAs = length As \<and> x = mk_AbsP (Bs @ As) (core_prf flatten (length Bs) oldAs A n m sprf p)"
proof -
  have asm: "(if 0 < n then case A of None \<Rightarrow> raiseW (Failure STR ''Option'') | Some C \<Rightarrow> returnW [mk_asm_prf C n m]
      else returnW []) = returnW a \<Longrightarrow> a = (if 0 < n then [mk_asm_prf (the A) n m] else [])" for a
    by (auto simp: raiseP_returnP split: option.splits if_splits)
  from assms have "length oldAs = length As \<and>
      (\<exists>Ns :: pterm list. length Ns = length (Bs @ As) \<and> x = mk_AbsP Ns (core_prf flatten (length Bs) oldAs A n m sprf p))"
    unfolding bicompose_core_def Let_def bindP_eq_returnP liftMP_eq_returnP
    by (auto simp: core_prf_def ok_mapM ok_zip_eq length_downto0 dest!: asm list_all2_lengthD)
  then show ?thesis using mk_AbsP_length by metis
qed

lemma prf_ap_core_prf:
  "prf_ap \<rho> \<sigma> (core_prf flatten lb oldAs A n m sprf p) = core_prf flatten lb oldAs A n m (prf_ap \<rho> \<sigma> sprf) (prf_ap \<rho> \<sigma> p)"
  by (cases flatten) (simp_all add: core_prf_def prf_ap_proof_combP prf_ap_mk_asm_prf prf_ap_flatten_params_proof comp_def)

lemma prf_aeq_core_prf:
  "prf_aeq sp sp' \<Longrightarrow> prf_aeq p p' \<Longrightarrow>
    prf_aeq (core_prf flatten lb oldAs A n m sp p) (core_prf flatten lb oldAs A n m sp' p')"
  unfolding core_prf_def by (intro prf_aeq.PAppp prf_aeq_proof_combP)

subsection \<open>Validity of the composed proof\<close>

text \<open>The variables of the annotations of the proof of the lifted rule have indices above \<open>m\<close>:\<close>

definition prf_above :: "integer \<Rightarrow> prf \<Rightarrow> bool" where
  "prf_above m p \<longleftrightarrow> (\<forall>t\<in>prf_terms p. \<forall>v\<in>vars t. m < snd (fst v))"

text \<open>The renaming of the proof of the rule by the wrapper of \<open>bicompose_aux\<close>:\<close>

definition ren_prf :: "ren option \<Rightarrow> prf \<Rightarrow> prf" where
  "ren_prf r p = (case r of None \<Rightarrow> p | Some r \<Rightarrow> map_proof_terms (ren_term r) id p)"

lemma newAs_n: "okT (newAs vl ctx As0 n dps tps1) na \<Longrightarrow> na_n na = n"
proof -
  have h: "\<not> okT (case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseW (THM (STR ''bicompose: 1st premise'') 0 Orule)
        | _ \<Rightarrow> raiseW e) y" for e and y :: newas
    by (auto simp: raiseW_def split: texn.splits uexn.splits exn.splits)
  assume "okT (newAs vl ctx As0 n dps tps1) na"
  then show ?thesis
    unfolding newAs_def by (auto simp: okW_handleW h ok_mapM list.rel_eq split: if_splits option.splits)
qed

subsection \<open>The flex-flex pairs of the result as equations\<close>

lemma eqv_vsubst_map:
  assumes st: "eqv E e s t" and \<sigma>: "wt_subst \<sigma>"
    and ax: "\<And>l r e T. (l, r) \<in> E \<Longrightarrow> e \<turnstile> l : T \<Longrightarrow> e \<turnstile> r : T \<Longrightarrow> eqv F e (vsubst \<sigma> l) (vsubst \<sigma> r)"
  shows "eqv F e (vsubst \<sigma> s) (vsubst \<sigma> t)"
  by (rule eqv_map[where Pk = "\<lambda>_ _. True" and Me = "\<lambda>_ e. e" and Fm = "\<lambda>_. vsubst \<sigma>" and Gm = "\<lambda>T. T"
        and nxt = "\<lambda>_ _. ()" and k = "()", OF st])
    (use \<sigma> ax in \<open>auto intro: conv_vsubst typing_vsubst\<close>)

text \<open>
  The equational statement of the unifier: the problem holds modulo the equations of the
  remaining pairs, at a solution of the environment.
\<close>

lemma ures_solves_eqv:
  assumes ur: "ures env tus (El_R env' tps)" and pw: "pwf env tus"
    and sol: "solution \<rho> \<sigma> env'" and ci: "cert_inst \<rho>"
    and ts: "\<And>t u e. (t, u) \<in> set tps \<Longrightarrow> eqv F e (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
    and tu: "(t, u) \<in> set tus"
  shows "eqv F e (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
proof -
  from ures_pwf[OF ur pw] obtain A where "uresult A env tus (El_R env' tps)" .
  then have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1))
  from pw obtain A0 K X where si: "sinv A0 K X env (tdps tus)" by (auto simp: pwf_def)
  have t': "tsol (tyenv env') \<rho>" by (rule solutionD(2)[OF sol])
  have tt: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t' dstepD(1)[OF ds]])
  from winvD[OF _ tt ci] si have w: "wt_env \<rho> env" "vinv \<rho> env X" by (auto simp: sinv_def)
  have v: "vinv \<rho> env ({} \<union> dvars (tdps tus))"
    using ur_vinv_sub[OF w(2)] sinv_dvars[OF si] by simp
  from ures_inv[OF ur pw] obtain A' K' X' where wi': "winv env' X'" by blast
  have wte': "wt_env \<rho> env'" using winvD[OF wi' t' ci] by blast
  let ?E = "binds \<rho> env' \<union> dp_eqs \<rho> (tdps tps)"
  have D: "deqv ?E \<rho> (tdps tus)"
    by (rule dstepD(3)[OF ds t' extends_refl w(1) sinv_dtyped[OF si tt ci] v])
  have ws: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  from si tu have ok: "upok A0 env [] X t u" by (auto simp: sinv_def)
  then have c: "closed (inst \<rho> t)" "closed (inst \<rho> u)" by (auto simp: upok_def closed_def)
  from ok tt ci obtain e0 T where "e0 \<turnstile> inst \<rho> t : T" "e0 \<turnstile> inst \<rho> u : T"
    by (auto simp: upok_def)
  then have ty: "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T" using typing_closed c by blast+
  with D tu have "eqv ?E e (inst \<rho> t) (inst \<rho> u)" by (fastforce simp: deqv_def bs_env_def)
  then show ?thesis unfolding ap_def
  proof (rule eqv_vsubst_map[OF _ ws])
    fix l r e' V assume lr: "(l, r) \<in> ?E" and tl: "e' \<turnstile> l : V" "e' \<turnstile> r : V"
    show "eqv F e' (vsubst \<sigma> l) (vsubst \<sigma> r)"
    proof (cases "(l, r) \<in> binds \<rho> env'")
      case True
      then obtain x U s where l: "l = Var x (tsubst \<rho> U)" and r: "r = inst \<rho> s"
        and lk: "vt_lookup (tenv env') x = Some (U, s)" unfolding binds_def by blast
      show ?thesis
        by (rule eqv.eqv_conv[OF _ typing_vsubst[OF tl(1) ws] typing_vsubst[OF tl(2) ws]])
          (use solutionD(4)[OF sol lk] in \<open>simp add: l r ap_def\<close>)
    next
      case False
      with lr obtain t0 u0 where "(t0, u0) \<in> set tps" "l = inst \<rho> t0" "r = inst \<rho> u0"
        by (auto simp: dp_eqs_def)
      with ts show ?thesis by (simp add: ap_def)
    qed
  qed
qed

lemma addth_tpairs_eqv:
  assumes ad: "okT (addth ctx A na (env', tps)) r" and ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" and \<sigma>: "gsubst \<sigma>"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>e T. e \<turnstile> inst \<rho>' t : T \<and> e \<turnstile> inst \<rho>' u : T)"
    and tu: "(t, u) \<in> set tps"
  shows "eqv (ceqs (pmap (ap \<rho> \<sigma>) (set (br_tpairs r)))) e (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
proof -
  note i = iextD[OF ie]
  let ?F = "ceqs (pmap (ap \<rho> \<sigma>) (set (br_tpairs r)))"
  from tw tu obtain e0 T where ty: "e0 \<turnstile> inst \<rho>' t : T" "e0 \<turnstile> inst \<rho>' u : T"
    and c: "closed t" "closed u" by blast
  have g: "gterm (ap \<rho>' \<sigma>' s) T" if "closed s" "e0 \<turnstile> inst \<rho>' s : T" for s
    by (rule gterm_apI[OF i(2) that])
  note gt = g[OF c(1) ty(1)] and gu = g[OF c(2) ty(2)]
  from ad show ?thesis
  proof (cases rule: addth_cases)
    case empty
    have eq: "ap \<rho>' \<sigma>' s = ap \<rho> \<sigma> s" for s by (rule iext_unb[OF ie unb_empty[OF empty(1)]])
    have m: "(ap \<rho> \<sigma> t, ap \<rho> \<sigma> u) \<in> ?F"
      using pmapI[OF tu, of "ap \<rho> \<sigma>"] empty(2) gt gu eq by (simp add: gterm_def)
    have "e \<turnstile> ap \<rho> \<sigma> t : T" "e \<turnstile> ap \<rho> \<sigma> u : T" using gt gu eq by (simp_all add: gterm_def)
    from eqv.eqv_ax[OF m this] show ?thesis by (simp add: eq)
  next
    case (norm ntps Hs C')
    from list_all2_ex1[OF norm(3) tu] obtain tu' where tu': "tu' \<in> set ntps"
      and n: "ok (norm_term env' t) (fst tu')" "ok (norm_term env' u) (snd tu')"
      by auto
    obtain t' u' where tu'': "tu' = (t', u')" by (cases tu')
    note tu' = tu'[unfolded tu''] and n = n[unfolded tu'' fst_conv snd_conv]
    have gc: "gterm (ap \<rho> \<sigma> s') T \<and> ap \<rho> \<sigma> s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' s"
      if "ok (norm_term env' s) s'" "e0 \<turnstile> inst \<rho>' s : T" "closed s" for s s'
    proof -
      note ns = nsoundD[OF norm_term_sound[OF that(1) i(5,4)]]
      have "closed s'" using ns(2)[of 0] that(3) by (simp add: closed_def)
      then show ?thesis
        using gterm_apI[OF \<sigma> _ iext_norm_term(2)[OF ie that(1,2)]] iext_norm_term(1)[OF ie that(1,2)] by blast
    qed
    note gt' = gc[OF n(1) ty(1) c(1)] and gu' = gc[OF n(2) ty(2) c(2)]
    have m: "(ap \<rho> \<sigma> t', ap \<rho> \<sigma> u') \<in> ?F"
      using pmapI[OF tu', of "ap \<rho> \<sigma>"] norm(2) gt' gu' by (simp add: gterm_def)
    have "e \<turnstile> ap \<rho> \<sigma> t' : T" "e \<turnstile> ap \<rho> \<sigma> u' : T" using gt' gu' by (simp_all add: gterm_def)
    from eqv.eqv_ax[OF m this] have a: "eqv ?F e (ap \<rho> \<sigma> t') (ap \<rho> \<sigma> u')" .
    have 1: "eqv ?F e (ap \<rho>' \<sigma>' t) (ap \<rho> \<sigma> t')"
      by (rule eqv.eqv_conv[OF conv_sym[OF conjunct2[OF gt']]]) (use gt gt' in \<open>auto simp: gterm_def\<close>)
    have 2: "eqv ?F e (ap \<rho> \<sigma> u') (ap \<rho>' \<sigma>' u)"
      by (rule eqv.eqv_conv[OF conjunct2[OF gu']]) (use gu gu' in \<open>auto simp: gterm_def\<close>)
    show ?thesis by (rule eqv.eqv_trans[OF eqv.eqv_trans[OF 1 a] 2])
  qed
qed

lemma bresult_inst_eqv:
  assumes its: "itsok sp A na tus" and pa: "pinv_all sp" and ur: "ures (sp_env sp) tus (El_R env' tps)"
    and ad: "okT (addth (sp_ctx sp) A na (env', tps)) r"
    and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  obtains \<rho>' \<sigma>' where "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
    "\<And>t u e. (t, u) \<in> set tus \<Longrightarrow> eqv (ceqs (pmap (ap \<rho> \<sigma>) (set (br_tpairs r)))) e (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
proof -
  from ures_inv[OF ur itsok_pwf[OF its pa]] obtain A' K' X' where ei': "einv A' K' env'" and wi': "winv env' X'"
    and tpok: "\<forall>(t, u)\<in>set tps. upok A' env' [] X' t u" by blast
  obtain \<rho>' \<sigma>' \<rho>0 where ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
    by (rule iext_exists_sb[OF ei' wi' \<rho> \<sigma>]) blast
  note i = iextD[OF ie]
  have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
  have tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>e T. e \<turnstile> inst \<rho>' t : T \<and> e \<turnstile> inst \<rho>' u : T)"
  proof (intro ballI, clarify)
    fix t u assume "(t, u) \<in> set tps"
    with tpok have ok: "upok A' env' [] X' t u" by blast
    then have "closed t" "closed u" by (simp_all add: upok_def closed_def)
    moreover from upokD(9)[OF ok i(5) ci'] have "\<exists>e T. e \<turnstile> inst \<rho>' t : T \<and> e \<turnstile> inst \<rho>' u : T" by blast
    ultimately show "closed t \<and> closed u \<and> (\<exists>e T. e \<turnstile> inst \<rho>' t : T \<and> e \<turnstile> inst \<rho>' u : T)" by blast
  qed
  have "eqv (ceqs (pmap (ap \<rho> \<sigma>) (set (br_tpairs r)))) e (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
    if "(t, u) \<in> set tus" for t u e
    by (rule ures_solves_eqv[OF ur itsok_pwf[OF its pa] i(3) ci' _ that])
      (rule addth_tpairs_eqv[OF ad ie \<sigma> tw])
  with ie show thesis by (rule that)
qed

text \<open>Equations between the closures over the parameters of a subgoal hold below them:\<close>

lemma eqv_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> e \<turnstile> lift_pre p X : propT \<Longrightarrow> e \<turnstile> lift_pre p Y : propT \<Longrightarrow>
    eqv (ceqs E) e (abs_pre p X) (abs_pre p Y) \<Longrightarrow> eqv (ceqs E) e (lift_pre p X) (lift_pre p Y)"
proof (induction p arbitrary: e)
  case (Cons i p)
  have oki: "litem_ok i" and okp: "\<forall>i\<in>set p. litem_ok i" using Cons.prems(1) by simp_all
  show ?case
  proof (cases i)
    case (LImp c H)
    note tX = typing_lift_pre_imp[OF oki Cons.prems(2) LImp]
      and tY = typing_lift_pre_imp[OF oki Cons.prems(3) LImp]
    have r: "eqv (ceqs E) e (lift_pre p X) (lift_pre p Y)"
      by (rule Cons.IH[OF okp tX(3) tY(3)]) (use Cons.prems(4) LImp in simp)
    have ta: "e \<turnstile> implies \<degree>\<degree> [H, lift_pre p X] : propT" using Cons.prems(2) tX(1) by simp
    then obtain Ts where "e \<turnstile> implies : Ts \<Rrightarrow> propT" by (rule list_app_typeE)
    then have "eqv (ceqs E) e implies implies" by (rule eqv_refl)
    from eqv_apps[of "ceqs E" e "[H, lift_pre p X]" "[H, lift_pre p Y]", OF _ this ta] eqv_refl[OF tX(2)] r
    show ?thesis unfolding tX(1) tY(1) by simp
  next
    case (LAll c a T)
    note tX = typing_lift_pre_all[OF oki Cons.prems(2) LAll]
      and tY = typing_lift_pre_all[OF oki Cons.prems(3) LAll]
    have "cert_typ alg ar T" using typing_lift_pre[OF Cons.prems(1,2)] LAll by simp
    have "eqv (ceqs E) (e\<langle>0:T\<rangle>) (abs_pre p X) (abs_pre p Y)"
      by (rule eqv_Abs_inv) (use Cons.prems(4) LAll in simp)
    from Cons.IH[OF okp tX(2) tY(2) this]
    have "eqv (ceqs E) e (Abs a T (lift_pre p X)) (Abs a T (lift_pre p Y))"
      by (rule eqv.eqv_abs) fact
    moreover have ta: "e \<turnstile> all_const T \<degree>\<degree> [Abs a T (lift_pre p X)] : propT" using Cons.prems(2) tX(1) by simp
    then obtain Ts where "e \<turnstile> all_const T : Ts \<Rrightarrow> propT" by (rule list_app_typeE)
    then have "eqv (ceqs E) e (all_const T) (all_const T)" by (rule eqv_refl)
    ultimately show ?thesis
      using eqv_apps[of "ceqs E" e "[Abs a T (lift_pre p X)]" "[Abs a T (lift_pre p Y)]", OF _ _ ta]
      unfolding tX(1) tY(1) by simp
  qed
qed simp

lemma eqv_lift_pre_ap:
  assumes "\<forall>i\<in>set p. litem_ok i" "e \<turnstile> ap \<rho> \<sigma> (lift_pre p X) : propT" "e \<turnstile> ap \<rho> \<sigma> (lift_pre p Y) : propT"
    "eqv (ceqs E) e (ap \<rho> \<sigma> (abs_pre p X)) (ap \<rho> \<sigma> (abs_pre p Y))"
  shows "eqv (ceqs E) e (ap \<rho> \<sigma> (lift_pre p X)) (ap \<rho> \<sigma> (lift_pre p Y))"
proof -
  have ok: "\<forall>i\<in>set (map (lap \<rho> \<sigma>) p). litem_ok i" using assms(1) litem_ok_lap by auto
  from eqv_lift_pre[OF ok assms(2,3)[unfolded ap_lift_pre] assms(4)[unfolded ap_abs_pre]]
  show ?thesis unfolding ap_lift_pre .
qed

text \<open>
  The proof built by \<^const>\<open>bicompose_proof\<close> for a result of a call of \<open>bicompose_aux\<close> (with
  the arguments given by the wrapper) is valid for the result, if the proofs of the proof state
  and of the rule are valid and their annotations are below and above the maximal index of the
  proof state, respectively. The computation must not print a warning.
\<close>

theorem bicompose_proof_valid:
  assumes sp: "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and r: "rchar sp r" and pa: "pinv_all sp"
    and state: "prf_valid ax (set hs) stpairs sprf (list_implies (Bs @ [Bi]) C)" "wtp (list_implies (Bs @ [Bi]) C)"
      "ibelow smax (list_implies (Bs @ [Bi]) C)" "\<forall>(t, u)\<in>set stpairs. ibelow smax t \<and> ibelow smax u"
    and rule: "prf_valid ax (set hr) rtpairs rprf (list_implies (rev rAs) B)" "wtp (list_implies (rev rAs) B)"
      "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B" "lifted \<Longrightarrow> prf_above smax rprf"
    and vl: "\<And>xs. length (vl xs) = length xs"
    and res: "bicompose_proof (br_env r) smax flatten Bs (na_As (br_newas r)) (br_A r) (na_oldAs (br_newas r))
      (na_n (br_newas r)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1)
      (ren_prf (na_ren (br_newas r)) rprf) sprf = returnW p"
  shows "prf_valid ax (set (hs @ hr)) (br_tpairs r) p (br_prop r)"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have sp_sel: "sp_eres sp = eres_flg" "sp_ctx sp = ctx" "sp_vl sp = vl" "sp_rAs sp = rAs" "sp_env sp = env"
    by (simp_all add: sp')
  obtain A1o na tus env' tps Pre As0 n dps tps1 where its: "itsok sp A1o na tus"
    and ur: "ures env tus (El_R env' tps)" and ad: "okT (addth ctx A1o na (env', tps)) r"
    and rAs: "rev rAs = Pre @ As0" and na: "okT (newAs vl ctx As0 n dps tps1) na"
    and dps: "BBi \<in> set dps" and tus: "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
    and n: "0 \<le> n" "n \<le> count_prems (strip_all_body Bi)"
      "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)" "0 \<le> nlift"
    and A1o: "Pre = [] \<and> A1o = None \<and> n = 0 \<or> (\<exists>A1. Pre = [A1] \<and> A1o = Some A1 \<and> 1 \<le> n)"
    and pre: "\<And>A1. A1 \<in> set Pre \<Longrightarrow> \<exists>params asms concl asm. eres_flg \<and> Pre = [A1] \<and>
      assum_problems (nlift + 1) A1 = (params, asms, concl) \<and> asm \<in> set asms \<and>
      nat_of_integer n \<le> length asms \<and> asm = asms ! (nat_of_integer n - 1) \<and>
      (rlist_abs params concl, rlist_abs params asm) \<in> set dps \<and>
      (rlist_abs params asm, rlist_abs params concl) \<in> set tus"
    by (rule rchar_data[OF sp' ctx_def nlift_def r]) blast
  have rr: "br_env r = env' \<and> br_A r = A1o \<and> br_newas r = na"
    using ad by (cases rule: addth_cases) auto
  have wS: "\<forall>X\<in>set Bs. wtp X" "wtp Bi" "wtp C"
    using wtp_list_implies[of "Bs @ [Bi]" "Bs @ [Bi]" C C] state(2) by simp_all
  have iS: "\<forall>X\<in>set Bs. ibelow smax X" "ibelow smax Bi" "ibelow smax C" using state(3) by simp_all
  have wR: "\<forall>X\<in>set (rev rAs). wtp X" "wtp B"
    using wtp_list_implies[of "rev rAs" "rev rAs" B B] rule(2) by simp_all
  have wP: "\<forall>X\<in>set Pre. wtp X" "\<forall>X\<in>set As0. wtp X" using wR(1) rAs by auto
  have lr0: "lifted \<Longrightarrow> lifted_rule smax Bi (Pre @ As0) B" using rule(3) rAs by simp
  have lr: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
    using lr0 by (induction Pre) (auto dest: lifted_rule_Cons)
  have pv: "\<forall>v\<in>pvars p. snd (fst v) \<le> smax" if "lsplit Bi = (p, Bi0)" for p Bi0
    using iS(2) lsplit_ok[OF that] by (auto simp: ibelow_def vars_lift_pre)
  from ures_inv[OF ur itsok_pwf[OF its pa, unfolded sp_sel(5)]] obtain A' K' X' where ei': "einv A' K' env'" by blast
  have tac: "tacyc (tyenv env')" "tcons_env (tyenv env')" using einvD(6,7)[OF ei'] .
  have lr': "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B" using lr by (simp add: ctx_sel)
  have ib: "ibelow (bc_smax ctx) (bc_Bi ctx)" using iS(2) by (simp add: ctx_sel)
  obtain tab where
    ren: "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> vnames t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> vnames t \<and> x \<notin> vnames u)"
    and nren: "na_ren na = None \<and> tab = [] \<or> (\<exists>r2. bc_lifted ctx \<and> na_ren na = Some (tab, r2))"
    and oldAs: "list_all2 (\<lambda>A1 A. wtp A1 \<and> wtp A \<and> (\<forall>\<rho> \<sigma>. aconv_term (ap \<rho> \<sigma> A1) (ap \<rho> (rsubst (bc_smax ctx) tab \<sigma>) A)))
      (na_oldAs na) As0"
    and flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    and wN: "\<forall>A\<in>set (na_As na). wtp A"
    by (rule newAs_old[OF na lr' ib wP(2) vl]) blast+
  let ?la = "length (na_As na)" and ?lb = "length Bs" and ?m = "nlift + 1"
  have lold: "length (na_oldAs na) = ?la" using list_all2_lengthD[OF flat] by simp
  have lAs0: "length As0 = ?la" using list_all2_lengthD[OF oldAs] lold by simp
  text \<open>The variables that are not renamed.\<close>
  have keep: "ap \<rho> (rsubst smax tab \<sigma>) t = ap \<rho> \<sigma> t"
    if "\<And>v. v \<in> vars t \<Longrightarrow> snd (fst v) \<le> smax \<or> ren_name tab (fst (fst v)) = fst (fst v)" for \<rho> \<sigma> t
    using that by (intro ap_rsubst_id) blast
  text \<open>The renamed proof of the rule.\<close>
  define rprf' where "rprf' = ren_prf (na_ren na) rprf"
  have rprf': "prf_aeq (prf_ap \<rho> (rsubst smax tab \<sigma>) rprf) (prf_ap \<rho> \<sigma> rprf')" for \<rho> \<sigma>
    using nren
  proof (elim disjE exE conjE)
    assume "na_ren na = None" "tab = []"
    then show ?thesis by (simp add: rprf'_def ren_prf_def prf_aeq.refl)
  next
    fix r2 assume "bc_lifted ctx" "na_ren na = Some (tab, r2)"
    then show ?thesis
      using prf_aeq_ren[of rprf smax \<rho> "(tab, r2)" \<sigma>] rule(4) by (simp add: rprf'_def ren_prf_def prf_above_def ctx_sel)
  qed
  text \<open>The relation of the new theorem to its unnormalized instance.\<close>
  have wSc: "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wtp X \<and> ibelow (bc_smax ctx) X"
    using wS iS by (simp add: ctx_sel)
  have sk: "0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
    if "bc_lifted ctx"
  proof -
    from that have lf: lifted by (simp add: ctx_sel)
    have "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)).
        \<exists>H0\<in>set (spine_hyps Bi). vars H = vars H0 \<and> typs H = typs H0"
      using newAs_skip[OF na _ _ vl n(4)] lf lr n(3) by (simp add: ctx_sel)
    then show ?thesis
      using ibelow_spine_hyps[OF iS(2)] n(4) by (fastforce simp: ctx_sel ibelow_def ttvars_def)
  qed
  have core: "prf_ok ax (set (hs @ hr)) (pmap (ap \<rho> \<sigma>) (set (br_tpairs r))) e []
      (mk_AbsP (Bs @ na_As na) (core_prf flatten ?lb (na_oldAs na) A1o n ?m Sp (prf_ap \<rho>' \<sigma>' rprf')))
      (ap \<rho> \<sigma> (br_prop r))"
    if \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
      and dsol: "\<And>t u e'. (t, u) \<in> set tus \<Longrightarrow>
        eqv (ceqs (pmap (ap \<rho> \<sigma>) (set (br_tpairs r)))) e' (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
      and hS0: "prf_ok ax (set hs) (pmap (ap \<rho> \<sigma>) (set (br_tpairs r))) e [] Sp (ap \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
    for e \<rho> \<sigma> \<rho>' \<sigma>' Sp
  proof -
    note i = iextD[OF ie]
    let ?F = "pmap (ap \<rho> \<sigma>) (set (br_tpairs r))"
    let ?\<sigma>r = "rsubst smax tab \<sigma>'" and ?H = "set (hs @ hr)"
    have gr: "gsubst ?\<sigma>r" using i(2) wt_subst_rsubst by (auto simp: gsubst_def rsubst_def)
    text \<open>The instances of the proof state and of the rule.\<close>
    have hS: "prf_ok ax ?H ?F e [] Sp (ap \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
      by (rule prf_ok_mono_H[OF hS0]) auto
    have hR0: "prf_ok ax (set hr) (pmap (ap \<rho>' ?\<sigma>r) (set rtpairs)) e [] (prf_ap \<rho>' ?\<sigma>r rprf)
        (ap \<rho>' ?\<sigma>r (list_implies (rev rAs) B))"
      by (rule prf_validD[OF rule(1) i(1) gr])
    have hR: "prf_ok ax (set hr) ?F e [] (prf_ap \<rho>' ?\<sigma>r rprf) (ap \<rho>' ?\<sigma>r (list_implies (rev rAs) B))"
    proof (rule prf_ok_eqs[OF _ hR0])
      fix l r' e' assume "(l, r') \<in> pmap (ap \<rho>' ?\<sigma>r) (set rtpairs)"
      then obtain t u where tu: "(t, u) \<in> set rtpairs" and lr: "l = ap \<rho>' ?\<sigma>r t" "r' = ap \<rho>' ?\<sigma>r u" by auto
      have nr: "ren_name tab (fst (fst v)) = fst (fst v)" if "v \<in> vars t \<union> vars u" for v
      proof (rule ccontr)
        assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
        from bspec[OF conjunct2[OF ren[OF this]], of "(t, u)"] tu
        have "fst (fst v) \<notin> vnames t \<and> fst (fst v) \<notin> vnames u" by (simp add: ctx_sel)
        moreover have "fst (fst v) \<in> vnames t \<union> vnames u" using that by blast
        ultimately show False by blast
      qed
      have "ap \<rho>' ?\<sigma>r t = ap \<rho>' \<sigma>' t" "ap \<rho>' ?\<sigma>r u = ap \<rho>' \<sigma>' u"
        by (rule keep; simp add: nr)+
      with dsol[of t u] tus tu lr show "eqv (ceqs ?F) e' l r'" by auto
    qed
    have hR': "prf_ok ax ?H ?F e [] (prf_ap \<rho>' \<sigma>' rprf') (ap \<rho>' ?\<sigma>r (list_implies (rev rAs) B))"
      by (rule prf_ok_mono_H[OF prf_ok_aeq[OF hR rprf']]) auto
    text \<open>The conclusion of the rule is convertible to the subgoal.\<close>
    have BBi_sol: "eqv (ceqs ?F) e (ap \<rho>' \<sigma>' (fst BBi)) (ap \<rho>' \<sigma>' (snd BBi))"
      using dsol[of "fst BBi" "snd BBi"] tus by simp
    have cB: "eqv (ceqs ?F) e (ap \<rho>' ?\<sigma>r B) (ap \<rho>' \<sigma>' Bi)"
    proof (cases lifted)
      case True
      from lr0[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0"
        by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
        and at: "atomic Bi0" by auto
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)"
        using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      have nr: "ren_name tab (fst (fst v)) = fst (fst v)" if "v \<in> vars B0" for v
      proof (rule ccontr)
        assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
        from ren[OF this] dps have "case BBi of (t, u) \<Rightarrow> fst (fst v) \<notin> vnames t" by blast
        with that BBi show False by auto
      qed
      have "ap \<rho>' ?\<sigma>r B = ap \<rho>' \<sigma>' B"
        by (rule keep) (use pv[OF ls] nr in \<open>auto simp: B vars_lift_pre\<close>)
      moreover have "eqv (ceqs ?F) e (ap \<rho>' \<sigma>' (lift_pre p B0)) (ap \<rho>' \<sigma>' (lift_pre p Bi0))"
        by (rule eqv_lift_pre_ap[OF ok typing_ap_wtp[OF _ i(1,2)] typing_ap_wtp[OF _ i(1,2)]])
          (use wR(2) wS(2) BBi_sol BBi B Bi in simp_all)
      ultimately show ?thesis by (simp add: B Bi)
    next
      case False
      then have "ap \<rho>' ?\<sigma>r B = ap \<rho>' \<sigma>' B" using nren by (auto simp: ctx_sel)
      moreover have "BBi = (B, Bi)" using False by (simp add: BBi_def)
      ultimately show ?thesis using BBi_sol by simp
    qed
    text \<open>The new theorem and its relation to the instance.\<close>
    obtain Hs C' where P: "br_prop r = list_implies Hs C'"
      and rs: "list_all2 (\<lambda>X Y. gterm (ap \<rho> \<sigma> Y) propT \<and> ap \<rho> \<sigma> Y \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' X) (Bs @ na_As na) Hs"
      and rc: "gterm (ap \<rho> \<sigma> C') propT \<and> ap \<rho> \<sigma> C' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' C"
      by (rule addth_rel[OF ad ie \<sigma> wSc wN sk]) (simp_all add: ctx_sel)
    define Ns where "Ns = map (ap \<rho> \<sigma>) Hs"
    have lHs: "length Hs = ?lb + ?la" using list_all2_lengthD[OF rs] by simp
    have relk: "gterm (Ns ! k) propT \<and> Ns ! k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' ((Bs @ na_As na) ! k)" if "k < ?lb + ?la" for k
      using list_all2_nthD[OF rs, of k] that lHs by (simp add: Ns_def)
    have lNs: "length Ns = length (map (ap \<rho>' \<sigma>') Bs) + length (map (ap \<rho>' \<sigma>') (na_As na))"
      using lHs by (simp add: Ns_def)
    have tNs: "\<forall>N\<in>set Ns. e \<turnstile> N : propT"
      using relk lNs by (auto simp: in_set_conv_nth gterm_def)
    have NB: "\<forall>j<length (map (ap \<rho>' \<sigma>') Bs). Ns ! j \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> map (ap \<rho>' \<sigma>') Bs ! j"
    proof (intro allI impI)
      fix j assume "j < length (map (ap \<rho>' \<sigma>') Bs)"
      with relk[of j] show "Ns ! j \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> map (ap \<rho>' \<sigma>') Bs ! j" by (simp add: nth_append)
    qed
    text \<open>The proofs of the premises of the rule.\<close>
    let ?f = "if flatten then flatten_params_proof 0 0 n else (\<lambda>x. PBound (snd x))"
    let ?ks = "downto (integer_of_nat ?la - 1) 0"
    have olds: "list_all2 (\<lambda>a P. prf_ok ax ?H ?F e (rev Ns) a P)
        (map ?f (zip (na_oldAs na) ?ks)) (map (ap \<rho>' ?\<sigma>r) As0)"
    proof (rule list_all2_all_nthI)
      show "length (map ?f (zip (na_oldAs na) ?ks)) = length (map (ap \<rho>' ?\<sigma>r) As0)"
        using lold lAs0 by (simp add: length_downto0)
      fix j assume "j < length (map ?f (zip (na_oldAs na) ?ks))"
      then have j: "j < ?la" using lold by (simp add: length_downto0)
      let ?Ao = "na_oldAs na ! j" and ?An = "na_As na ! j" and ?Ar = "As0 ! j" and ?k = "?la - 1 - j"
      have oj: "wtp ?Ao \<and> wtp ?Ar \<and> (\<forall>\<rho> \<sigma>. aconv_term (ap \<rho> \<sigma> ?Ao) (ap \<rho> (rsubst smax tab \<sigma>) ?Ar))"
        using list_all2_nthD[OF oldAs, of j] j lold by (simp add: ctx_sel)
      have fj: "if flatten then ok (flatten_params vl n ?Ao) ?An else ?Ao = ?An"
        using list_all2_nthD[OF flat, of j] j lold by (simp add: ctx_sel)
      have wA: "wtp ?An" using wN j by simp
      have kl: "?k < length (rev Ns)" using j lNs by simp
      have rk: "rev Ns ! ?k = Ns ! (?lb + j)" using j lNs by (simp add: rev_nth)
      have relj: "gterm (rev Ns ! ?k) propT \<and> rev Ns ! ?k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' ?An"
        using relk[of "?lb + j"] j rk by (simp add: nth_append)
      have wH: "\<forall>h\<in>set (rev Ns). e \<turnstile> h : propT" using tNs by simp
      have cv0: "ap \<rho>' \<sigma>' ?Ao \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' ?\<sigma>r ?Ar" using oj by (blast intro: aconv_term_conv)
      have t0: "e \<turnstile> ap \<rho>' ?\<sigma>r ?Ar : propT" using oj typing_ap_wtp[OF _ i(1) gr] by blast
      have "prf_ok ax ?H ?F e (rev Ns) (?f (?Ao, integer_of_nat ?k)) (ap \<rho>' \<sigma>' ?Ao)"
      proof (cases flatten)
        case True
        with fj have fl: "ok (flatten_params vl n ?Ao) ?An" by simp
        from flatten_params_proof_ok[OF i(1,2) conjunct1[OF oj] fl wA vl kl _ _ wH] relj True
        show ?thesis by (simp add: gterm_def)
      next
        case False
        with fj have "?Ao = ?An" by simp
        moreover have "prf_ok ax ?H ?F e (rev Ns) (PBound (integer_of_nat ?k)) (rev Ns ! ?k)"
          using prf_ok.PBound[of "integer_of_nat ?k" "rev Ns" e ax ?H] kl wH nth_mem[OF kl]
          by (simp add: integer_of_nat_nonneg)
        ultimately show ?thesis
          using False relj typing_ap_wtp[OF conjunct1[OF oj] i(1,2)] by (auto intro: prf_ok.conv)
      qed
      then have "prf_ok ax ?H ?F e (rev Ns) (?f (?Ao, integer_of_nat ?k)) (ap \<rho>' ?\<sigma>r ?Ar)"
        using cv0 t0 by (blast intro: prf_ok.conv)
      then show "prf_ok ax ?H ?F e (rev Ns) (map ?f (zip (na_oldAs na) ?ks) ! j) (map (ap \<rho>' ?\<sigma>r) As0 ! j)"
        using j lold lAs0 by (simp add: length_downto0 nth_downto0)
    qed
    have pres: "list_all2 (\<lambda>a P. \<exists>P'. prf_ok ax ?H ?F e (rev Ns) a P' \<and> eqv (ceqs ?F) e P' P)
        (if 0 < n then [mk_asm_prf (the A1o) n ?m] else []) (map (ap \<rho>' ?\<sigma>r) Pre)"
      using A1o
    proof (elim disjE exE conjE)
      assume "Pre = []" "A1o = None" "n = 0"
      then show ?thesis by simp
    next
      fix A1 assume Pre: "Pre = [A1]" and A: "A1o = Some A1" and n1: "1 \<le> n"
      from pre[of A1] Pre obtain params asms concl asm where er: "eres_flg"
        and apb: "assum_problems (nlift + 1) A1 = (params, asms, concl)" and asm: "asm \<in> set asms"
        and nl: "nat_of_integer n \<le> length asms" and asmn: "asm = asms ! (nat_of_integer n - 1)"
        and ac: "(rlist_abs params asm, rlist_abs params concl) \<in> set tus"
        and cd: "(rlist_abs params concl, rlist_abs params asm) \<in> set dps"
        by auto
      have wA1: "wtp A1" using wP(1) Pre by simp
      have cvA: "eqv (ceqs ?F) e (ap \<rho>' \<sigma>' (rlist_abs params asm)) (ap \<rho>' \<sigma>' (rlist_abs params concl))"
        by (rule dsol[OF ac])
      have c: "ap \<rho>' ?\<sigma>r (rlist_abs params concl) = ap \<rho>' \<sigma>' (rlist_abs params concl)"
      proof (rule keep)
        fix v assume v: "v \<in> vars (rlist_abs params concl)"
        show "snd (fst v) \<le> smax \<or> ren_name tab (fst (fst v)) = fst (fst v)"
        proof (rule disjI2, rule ccontr)
          assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
          from bspec[OF conjunct1[OF ren[OF this]] cd]
          have "fst (fst v) \<notin> vnames (rlist_abs params concl)" by simp
          moreover have "fst (fst v) \<in> vnames (rlist_abs params concl)" using v by blast
          ultimately show False by blast
        qed
      qed
      have a: "ap \<rho>' ?\<sigma>r (rlist_abs params asm) = ap \<rho>' \<sigma>' (rlist_abs params asm)"
      proof (cases lifted)
        case True
        from lr0[OF True] obtain p Bi0 As0' where ls: "lsplit Bi = (p, Bi0)"
          and As: "Pre @ As0 = map (lift_pre p) As0'" by (auto simp: lifted_rule_def)
        from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
          and at: "atomic Bi0" by auto
        from As Pre obtain X1 where A1': "A1 = lift_pre p X1" by (cases As0') auto
        have "nlift + 1 = count_prems (strip_all_body Bi)" using er by (simp add: nlift_def)
        then have "set asms \<subseteq> set (phyps p)"
          using assum_problems_lift_pre[OF ok at _ apb[unfolded A1']] Bi n(4) by simp
        with asm have "vars asm \<subseteq> pvars p" by (auto dest: vars_phyps)
        with pv[OF ls] show ?thesis by (intro keep) auto
      next
        case False
        then show ?thesis using nren by (auto simp: ctx_sel)
      qed
      have nb: "n \<le> ilength asms" using nl n(1) by (simp add: ilength_eq integer_reps)
      have "\<exists>P'. prf_ok ax ?H ?F e (rev Ns) (mk_asm_prf A1 n ?m) P' \<and> eqv (ceqs ?F) e P' (ap \<rho>' ?\<sigma>r A1)"
        by (rule mk_asm_prf_ok[OF i(1) gr wA1 apb _ n1 nb]) (use n(4) cvA a c asmn in simp_all)
      then show ?thesis using Pre A n1 by simp
    qed
    have olds': "list_all2 (\<lambda>a P. \<exists>P'. prf_ok ax ?H ?F e (rev Ns) a P' \<and> eqv (ceqs ?F) e P' P)
        (map ?f (zip (na_oldAs na) ?ks)) (map (ap \<rho>' ?\<sigma>r) As0)"
      using olds by (rule list_all2_mono) (blast intro: eqv_refl prf_ok_typing)
    have args: "list_all2 (\<lambda>a P. \<exists>P'. prf_ok ax ?H ?F e (rev Ns) a P' \<and> eqv (ceqs ?F) e P' P)
        ((if 0 < n then [mk_asm_prf (the A1o) n ?m] else []) @ map ?f (zip (na_oldAs na) ?ks))
        (map (ap \<rho>' ?\<sigma>r) Pre @ map (ap \<rho>' ?\<sigma>r) As0)"
      by (rule list_all2_appendI[OF pres olds'])
    have S: "prf_ok ax ?H ?F e [] Sp
        (list_implies (map (ap \<rho>' \<sigma>') Bs @ [ap \<rho>' \<sigma>' Bi]) (ap \<rho>' \<sigma>' C))"
      using hS by (simp add: ap_list_implies)
    have R: "prf_ok ax ?H ?F e [] (prf_ap \<rho>' \<sigma>' rprf')
        (list_implies (map (ap \<rho>' ?\<sigma>r) Pre @ map (ap \<rho>' ?\<sigma>r) As0) (ap \<rho>' ?\<sigma>r B))"
      using hR' rAs by (simp add: ap_list_implies)
    from prf_ok_compose[OF S R cB lNs tNs NB args]
    have "prf_ok ax ?H ?F e [] (mk_AbsP Ns (core_prf flatten ?lb (na_oldAs na) A1o n ?m Sp (prf_ap \<rho>' \<sigma>' rprf')))
        (list_implies Ns (ap \<rho>' \<sigma>' C))"
      using lold by (simp add: core_prf_def)
    moreover have "mk_AbsP Ns = mk_AbsP (Bs @ na_As na)" using lNs by (intro ext mk_AbsP_length) simp
    moreover have "list_implies Ns (ap \<rho>' \<sigma>' C) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (br_prop r)"
    proof -
      have "e \<turnstile> list_implies Ns (ap \<rho>' \<sigma>' C) : propT" by (rule prf_ok_typing[OF calculation(1)])
      moreover have "e \<turnstile> list_implies Ns (ap \<rho> \<sigma> C') : propT"
        using tNs rc by (auto simp: gterm_def intro!: typing_list_impliesI)
      ultimately show ?thesis
        using conv_list_implies[OF conv_sym[OF conjunct2[OF rc]]] by (simp add: P Ns_def ap_list_implies)
    qed
    moreover have "e \<turnstile> ap \<rho> \<sigma> (br_prop r) : propT"
      using tNs rc by (auto simp: P Ns_def ap_list_implies gterm_def intro!: typing_list_impliesI)
    ultimately show ?thesis by (auto intro: prf_ok.conv)
  qed
  show ?thesis
  proof (rule prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    let ?F = "pmap (ap \<rho> \<sigma>) (set (br_tpairs r))"
    obtain \<rho>' \<sigma>' where ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
      and dsol: "\<And>t u e. (t, u) \<in> set tus \<Longrightarrow> eqv (ceqs ?F) e (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
      by (rule bresult_inst_eqv[OF its pa ur[folded sp_sel(5)] ad[folded sp_sel(2)] \<rho> \<sigma>]) blast
    note i = iextD[OF ie]
    have hS0: "prf_ok ax (set hs) (pmap (ap \<rho>' \<sigma>') (set stpairs)) e [] (prf_ap \<rho>' \<sigma>' sprf)
        (ap \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
      by (rule prf_validD[OF state(1) i(1,2)])
    have hS: "prf_ok ax (set hs) ?F e [] (prf_ap \<rho>' \<sigma>' sprf) (ap \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
      by (rule prf_ok_eqs[OF _ hS0]) (use dsol tus in auto)
    note core' = core[OF \<rho> \<sigma> ie dsol hS]
    have res': "bicompose_proof env' smax flatten Bs (na_As na) A1o (na_oldAs na) n ?m rprf' sprf = returnW p"
      using res by (simp add: rr newAs_n[OF na] nlift_def rprf'_def)
    let ?core = "\<lambda>s q. mk_AbsP (Bs @ na_As na) (core_prf flatten ?lb (na_oldAs na) A1o n ?m s q)"
    consider (empty) "env_is_empty env'" "bicompose_core env' flatten Bs (na_As na) A1o (na_oldAs na) n ?m sprf rprf' = returnW p"
      | (above) q where "\<not> env_is_empty env'" "above env' smax" "norm_proof_remove_types env' rprf' = returnW q"
          "bicompose_core env' flatten Bs (na_As na) A1o (na_oldAs na) n ?m sprf q = returnW p"
      | (all) x where "\<not> env_is_empty env'" "\<not> above env' smax"
          "bicompose_core env' flatten Bs (na_As na) A1o (na_oldAs na) n ?m sprf rprf' = returnW x"
          "norm_proof_remove_types env' x = returnW p"
      using res' unfolding bicompose_proof_def by (auto simp: bindP_eq_returnP split: if_splits)
    then show "prf_ok ax (set (hs @ hr)) ?F e [] (prf_ap \<rho> \<sigma> p) (ap \<rho> \<sigma> (br_prop r))"
    proof cases
      case empty
      have l: "vt_lookup (tyenv env') v = None" "vt_lookup (tenv env') x = None" for v x
        using empty(1) by (simp_all add: env_is_empty_def vt_is_empty_lookup)
      have "\<rho>' = \<rho>" "\<sigma>' = \<sigma>" by (intro ext; simp add: i(6) i(7) l)+
      with core' bicompose_core_returnP[OF empty(2)] show ?thesis
        by (simp add: prf_ap_mk_AbsP prf_ap_core_prf)
    next
      case (above q)
      have "prf_aeq (prf_ap \<rho>' \<sigma>' rprf') (prf_ap \<rho> \<sigma> q)"
        using norm_proof_ok[OF tac above(3)[unfolded norm_proof_remove_types_def]] ie by (simp add: nrel_def)
      moreover have eqS: "ap \<rho> \<sigma> X = ap \<rho>' \<sigma>' X" if "ibelow smax X" for X
        using iext_unb[OF ie above_unb[OF above(2) that]] by simp
      have "prf_ok ax (set hs) (pmap (ap \<rho> \<sigma>) (set stpairs)) e [] (prf_ap \<rho> \<sigma> sprf)
          (ap \<rho> \<sigma> (list_implies (Bs @ [Bi]) C))"
        by (rule prf_validD[OF state(1) \<rho> \<sigma>])
      then have "prf_ok ax (set hs) ?F e [] (prf_ap \<rho> \<sigma> sprf) (ap \<rho> \<sigma> (list_implies (Bs @ [Bi]) C))"
      proof (rule prf_ok_eqs[rotated])
        fix l r' e' assume "(l, r') \<in> pmap (ap \<rho> \<sigma>) (set stpairs)"
        then obtain t u where tu: "(t, u) \<in> set stpairs" and lr: "l = ap \<rho> \<sigma> t" "r' = ap \<rho> \<sigma> u" by auto
        then have "eqv (ceqs ?F) e' (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)" using dsol tus by auto
        with tu state(4) eqS lr show "eqv (ceqs ?F) e' l r'" by fastforce
      qed
      then have "prf_ok ax (set hs) ?F e [] (prf_ap \<rho> \<sigma> sprf) (ap \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
        using eqS[OF state(3)] by simp
      note core'' = core[OF \<rho> \<sigma> ie dsol this]
      ultimately have "prf_aeq (?core (prf_ap \<rho> \<sigma> sprf) (prf_ap \<rho>' \<sigma>' rprf')) (prf_ap \<rho> \<sigma> p)"
        using bicompose_core_returnP[OF above(4)]
        by (simp add: prf_ap_mk_AbsP prf_ap_core_prf prf_aeq_mk_AbsP prf_aeq_core_prf prf_aeq.refl)
      with core'' show ?thesis by (rule prf_ok_aeq)
    next
      case (all x)
      have "prf_aeq (prf_ap \<rho>' \<sigma>' x) (prf_ap \<rho> \<sigma> p)"
        using norm_proof_ok[OF tac all(4)[unfolded norm_proof_remove_types_def]] ie by (simp add: nrel_def)
      moreover have "prf_ap \<rho>' \<sigma>' x = ?core (prf_ap \<rho>' \<sigma>' sprf) (prf_ap \<rho>' \<sigma>' rprf')"
        using bicompose_core_returnP[OF all(3)] by (simp add: prf_ap_mk_AbsP prf_ap_core_prf)
      ultimately show ?thesis using core' by (auto intro: prf_ok_aeq)
    qed
  qed
qed

end

end
