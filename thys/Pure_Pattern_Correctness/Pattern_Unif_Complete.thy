section \<open>Completeness of the Unification Steps\<close>

theory Pattern_Unif_Complete
  imports Pattern_Patterns
begin

text \<open>
  Completeness of \<^const>\<open>unif\<close> relative to a given solution \<open>\<sigma>\<close>: \<^const>\<open>unif\<close> never raises
  \<open>Unif\<close> on well-typed terms unified by \<open>\<sigma>\<close>, and \<open>\<sigma>\<close> extends to a solution of every result.
  This yields completeness and soundness of the exception \<open>Unif\<close> (theory
  \<open>Pattern_Correctness\<close>). No pattern or \<open>\<beta>\<close>-normality assumptions are needed:
  \<^const>\<open>flexrigid\<close> raises \<open>Unif\<close> only for a rigid occurrence (\<^const>\<open>rigid_occurs\<close>) and gives
  up with \<open>Pattern\<close> otherwise.
\<close>

subsection \<open>Auxiliary lemmas\<close>

context csig
begin

lemma zip_eq_return: "length xs = length ys \<Longrightarrow> zip_eq xs ys = return (zip xs ys)"
  by (induction xs ys rule: zip_eq.induct) auto

lemma ext_sol_sol_ext:
  "ext_sol V \<tau>' \<sigma> env env' \<Longrightarrow> wf_env ar env' \<Longrightarrow> \<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
  by (auto simp: ext_sol_def sol_ext_def)


subsection \<open>Folding\<close>

lemma foldM_complete:
  assumes "foldM f xs e = Some r" "P g e"
    and "\<And>x g e r. x \<in> set xs \<Longrightarrow> P g e \<Longrightarrow> f x e = Some r \<Longrightarrow>
      no_unif (Some r) \<and> (\<forall>e1. r = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
  shows "no_unif (Some r) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
  using assms
proof (induction xs arbitrary: g e r)
  case Nil
  then show ?case by (auto simp: return_def)
next
  case (Cons x xs)
  have step: "no_unif (Some r) \<and> (\<forall>e1. r = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
    if "x' \<in> set xs" "P g e" "f x' e = Some r" for x' g e r
    using Cons.prems(3)[OF _ that(2,3)] that(1) by simp
  from Cons.prems(1) have "f x e \<bind> (\<lambda>b'. foldM f xs b') = Some r" by simp
  then show ?case
  proof (rule bindM_SomeE)
    fix ex assume "f x e = Some (Err ex)" "r = Err ex"
    with Cons.prems(3)[of x g e "Err ex"] Cons.prems(2) show ?thesis by simp
  next
    fix e1 assume fx: "f x e = Some (Ok e1)" and rest: "foldM f xs e1 = Some r"
    from Cons.prems(3)[of x g e, OF _ Cons.prems(2) fx] obtain g1 where "P g1 e1" by auto
    have "no_unif (Some r) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
      by (rule Cons.IH[OF rest \<open>P g1 e1\<close>], rule step, assumption+)
    then show ?thesis .
  qed
qed


subsection \<open>Completeness of the rigid occurs check\<close>

lemma strip_comb_acc_append:
  "strip_comb_acc t (ts @ us) = (fst (strip_comb_acc t ts), snd (strip_comb_acc t ts) @ us)"
  by (induction t ts rule: strip_comb_acc.induct) simp_all

lemma strip_comb_App: "strip_comb (f $ u) = (fst (strip_comb f), snd (strip_comb f) @ [u])"
  using strip_comb_acc_append[of f "[]" "[u]"] by (simp add: strip_comb_def)

lemma head_norm_rigid: "is_rigid h \<Longrightarrow> head_norm env (list_comb h ts) = return (list_comb h ts)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (subst head_norm.simps) (auto simp: is_rigid_def)
next
  case (snoc t ts)
  have nA: "\<not> is_Abs (list_comb h ts)" using snoc.prems
    by (cases ts rule: rev_cases) (auto simp: is_rigid_def list_comb_snoc)
  have "head_norm env (list_comb h ts $ t) = return (list_comb h ts $ t)"
    using snoc nA by (subst head_norm.simps) (auto split: pterm.splits)
  then show ?case by (simp add: list_comb_snoc)
qed

text \<open>Head normal forms do not have an abstraction as the head of their spine.\<close>

lemma head_norm_head:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> \<not> is_Abs t' \<Longrightarrow> \<not> is_Abs (fst (strip_comb t'))"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  from "1.hyps" "1.prems"(1) have h: "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
              pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
            | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    by simp
  note IH = "1.IH"[OF _ refl]
  show ?case
  proof (cases t)
    case (Var xi T)
    with h obtain r' where "ok (lookup env xi T) r'"
      and rest: "(case r' of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) = Some (Ok t')"
      by (auto elim!: bindM_SomeE)
    then show ?thesis using IH "1.prems"(2) Var
      by (cases r') (auto simp: strip_comb_def return_def)
  next
    case (Abs a T body)
    with h "1.prems"(2) show ?thesis by (auto elim!: bindM_SomeE simp: return_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where "f = pterm.Abs a T body" by (cases f) auto
      with h App IH "1.prems"(2) show ?thesis by simp
    next
      case False
      with h App have "hn env f \<bind> (\<lambda>nf. case nf of
              pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
            | _ \<Rightarrow> return (nf $ u)) = Some (Ok t')"
        by (cases f) simp_all
      then show ?thesis
      proof (rule bindM_SomeE)
        fix nf assume nf: "hn env f = Some (Ok nf)"
          and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
            | _ \<Rightarrow> return (nf $ u)) = Some (Ok t')"
        show ?thesis
        proof (cases "is_Abs nf")
          case True
          then obtain a T body where "nf = pterm.Abs a T body" by (cases nf) auto
          with rest IH "1.prems"(2) show ?thesis by simp
        next
          case nA: False
          with rest have "t' = nf $ u" by (cases nf) (simp_all add: return_def)
          with IH[OF nf nA] show ?thesis by (simp add: strip_comb_App)
        qed
      qed simp
    qed
  qed (use h "1.prems"(2) in \<open>auto simp: return_def strip_comb_def\<close>)
qed

lemma rigid_head_strip: "rigid_head t \<Longrightarrow> strip_comb t = (h, ts) \<Longrightarrow> is_rigid h"
proof -
  assume "rigid_head t" and s: "strip_comb t = (h, ts)"
  then obtain h0 ts0 where t: "t = list_comb h0 ts0" "is_rigid h0" by (auto simp: rigid_head_def)
  from strip_comb_list_comb[OF s] t have "list_comb h ts = list_comb h0 ts0" by simp
  with list_comb_eq_iff[OF strip_comb_head[OF s] is_rigid_not_App[OF t(2)]] t(2) show "is_rigid h"
    by simp
qed

lemma rigid_head_not_Abs: "rigid_head t \<Longrightarrow> \<not> is_Abs t"
  by (auto simp: rigid_head_def is_rigid_def list_comb_Abs_iff elim!: is_Abs.elims)

lemma rigid_head_head_norm: "rigid_head t \<Longrightarrow> head_norm env t = return t"
  by (auto simp: rigid_head_def head_norm_rigid)

lemma existsM_TrueE: "existsM P xs = Some (Ok True) \<Longrightarrow> \<exists>x\<in>set xs. P x = Some (Ok True)"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits res.splits if_splits)

text \<open>
  A rigid occurrence of \<open>F\<close> survives in every \<open>\<beta>\<close>-normal instance: the measure \<^const>\<open>ld\<close> of
  the instance is at least that of the value of \<open>F\<close>, and strictly larger below a rigid head.
  Unlike for \<^const>\<open>occurs\<close>, no pattern or normality assumptions are needed: head
  normalisation follows the bindings and contracts the redexes on the way.
\<close>

lemma rigid_occurs_ld:
  assumes "rigid_occurs F t env = Some r"
  shows "r = Ok True \<Longrightarrow> wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> solution V \<tau>' \<sigma> env \<Longrightarrow>
    \<beta>\<eta>cl (\<sigma> (code (AVar F))) nF \<Longrightarrow> normal nF \<Longrightarrow> proper t \<Longrightarrow> typs_ok ar t \<Longrightarrow> has_type V Ts t T \<Longrightarrow>
    v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t) \<Longrightarrow> no_redex v \<Longrightarrow> (bnd_env Ts, \<tau>') \<turnstile> v : trty T \<Longrightarrow>
    ld E \<tau>' nF (trty (V F)) \<le> ld (bnd_env Ts) \<tau>' v (trty T) \<and>
    (rigid_head t \<longrightarrow> ld E \<tau>' nF (trty (V F)) < ld (bnd_env Ts) \<tau>' v (trty T))"
  using assms
proof (induction F t env r arbitrary: Ts T v rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t env r)
  have rT: "r = Ok True" and wf: "wf_env ar env" and ety: "env_typed V env"
    and sol: "solution V \<tau>' \<sigma> env" and nF: "\<beta>\<eta>cl (\<sigma> (code (AVar F))) nF" "normal nF"
    and pt: "proper t" "typs_ok ar t" and tyt: "has_type V Ts t T" and veq: "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
    and vnr: "no_redex v" and vty: "(bnd_env Ts, \<tau>') \<turnstile> v : trty T"
    using "1.prems" by blast+
  note \<sigma> = solutionD[OF sol]
  note IH = "1.IH"[OF _ refl wf ety sol nF]
  let ?L = "ld E \<tau>' nF (trty (V F))"
  define B where "B = (\<lambda>t'. case t' of
        pterm.Abs _ _ u \<Rightarrow> ro F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              pterm.Var G _ \<Rightarrow>
                if G = F then
                  handle (ints_of' env ts \<bind> (\<lambda>_. return True))
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | pterm.Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts)))"
  from "1.hyps" rT have "head_norm env t \<bind> B = Some (Ok True)" by (simp add: B_def)
  then obtain t' where hn: "head_norm env t = Some (Ok t')" and Bt: "B t' = Some (Ok True)"
    by (auto elim!: bindM_SomeE)
  from head_norm_sound[OF hn refl wf pt] have pt': "proper t'" "typs_ok ar t'" and eqt: "env \<Turnstile> t \<approx> t'"
    by simp_all
  have tyt': "has_type V Ts t' T" by (rule head_norm_typed[OF hn refl wf ety tyt])
  have veq': "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t')" using veq env_equivD[OF eqt \<sigma>(1,4)] by (rule equiv_trans)
  have rh: "t' = t" if "rigid_head t" using hn rigid_head_head_norm[OF that] by (simp add: return_def)
  show ?case
  proof (cases "is_Abs t'")
    case True
    then obtain a U body where t'a: "t' = pterm.Abs a U body" by (cases t') auto
    from Bt t'a have ob: "ro F body env = Some (Ok True)" by (simp add: B_def)
    from tyt' t'a obtain W where T: "T = U \<rightarrow>\<^sub>T W" and tyb: "has_type V (U # Ts) body W"
      by (auto elim: has_type_elims)
    have pb: "proper body" "typs_ok ar body" using pt' t'a by simp_all
    have "(bnd_env (U # Ts), \<tau>') \<turnstile> mk_subst \<sigma> (tr body) : trty W" by (rule has_type_subst[OF tyb \<sigma>(2)])
    then obtain w where w: "\<beta>\<eta>cl (mk_subst \<sigma> (tr body)) w" "normal w" "(bnd_env (U # Ts), \<tau>') \<turnstile> w : trty W"
      by (rule nf_typed)
    from IH[OF ob pb tyb equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w(1)]] normal_no_redex[OF w(2)] w(3)]
    have "?L \<le> ld (bnd_env (U # Ts)) \<tau>' w (trty W)" by simp
    also have "\<dots> = ld (bnd_env Ts) \<tau>' (dB.Abs w) (trty T)" by (simp add: T bnd_env_Cons)
    also have "\<dots> = ld (bnd_env Ts) \<tau>' v (trty T)"
    proof (rule ld_equiv)
      have "mk_subst \<sigma> (tr t') \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs w" using w(1) t'a by (auto intro: equiv_Abs \<beta>\<eta>cl_into_equiv)
      then show "dB.Abs w \<equiv>\<^sub>\<beta>\<^sub>\<eta> v" using veq' by (meson equiv_sym equiv_trans)
      show "(bnd_env Ts, \<tau>') \<turnstile> dB.Abs w : trty T" using w(3) T by (auto simp: bnd_env_Cons)
    qed (use vty vnr normal_no_redex[OF w(2)] in auto)
    finally have le: "?L \<le> ld (bnd_env Ts) \<tau>' v (trty T)" .
    have "\<not> rigid_head t" using rh rigid_head_not_Abs t'a by fastforce
    with le show ?thesis by simp
  next
    case nA: False
    obtain h ts where sc: "strip_comb t' = (h, ts)" by force
    note t'e = strip_comb_list_comb[OF sc]
    have nAh: "\<not> is_Abs h" using head_norm_head[OF hn refl nA] sc by simp
    have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF sc])
    have rest: "(case h of
        pterm.Var G _ \<Rightarrow>
          if G = F then
            handle (ints_of' env ts \<bind> (\<lambda>_. return True))
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
          else return False
      | pterm.Abs _ _ _ \<Rightarrow> return False
      | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts) = Some (Ok True)"
      using Bt sc nA unfolding B_def by (cases t') simp_all
    have pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t" "proper h"
      using pt' t'e by (simp_all add: proper_list_comb typs_ok_list_comb)
    consider (V) G U where "h = pterm.Var G U" | (R) "is_rigid h"
      using nAh nApp pts(2) by (cases h) (auto simp: is_rigid_def)
    then show ?thesis
    proof cases
      case V
      from rest V have G: "G = F" and hd: "handle (ints_of' env ts \<bind> (\<lambda>_. return True))
          (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) = Some (Ok True)"
        by (auto split: if_splits)
      from hd obtain js where js: "ok (ints_of' env ts) js"
        by (auto simp: handle_def bindM_def return_def raise_def split: option.splits res.splits exn.splits)
      note iS = ints_of'_sound[OF js wf pts(1)]
      have tyF: "has_type V Ts (app (pterm.Var F U) js) T"
        using has_type_ints_of'[OF js wf ety] tyt' t'e V G by simp
      have eqF: "env \<Turnstile> t' \<approx> app (pterm.Var F U) js" using ints_of'_equiv[OF js wf pts(1)] t'e V G by simp
      note ti = has_type_app_Var[OF tyF]
      have \<sigma>F: "no_loose_bound (\<sigma> (code (AVar F))) 0" "\<And>e'. (e', \<tau>') \<turnstile> \<sigma> (code (AVar F)) : tau V (code (AVar F))"
        by (rule closed_onD[OF \<sigma>(1)], simp, rule typed_onD[OF \<sigma>(2)], simp)
      have "ld (bnd_env Ts) \<tau>' v (trty T) = ld E \<tau>' nF (tau V (code (AVar F)))"
      proof (rule ld_flex_occurrence[where \<sigma> = \<sigma> and F = "code (AVar F)" and \<tau> = "tau V", OF \<sigma>F nF])
        show "distinct (nats js)" using iS(1,2) by (rule distinct_nats)
        show "(bnd_env Ts, tau V) \<turnstile> dB.Var (code (AVar F)) \<degree>\<degree> map BVar (nats js) : trty T"
          using has_type_tr[OF tyF] by (simp add: tr_app')
        have "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (app (pterm.Var F U) js))"
          using veq' env_equivD[OF eqF \<sigma>(1,4)] by (rule equiv_trans)
        then show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar F)) \<degree>\<degree> map BVar (nats js)" by (simp add: tr_app' comp_def)
      qed (use vnr vty in auto)
      then have eq: "ld (bnd_env Ts) \<tau>' v (trty T) = ?L" using ti(2) by simp
      have "\<not> rigid_head t" using rh rigid_head_strip[of t' h ts] sc V by (auto simp: is_rigid_def)
      with eq show ?thesis by simp
    next
      case R
      from rest R have "existsM (\<lambda>u. ro F u env) ts = Some (Ok True)"
        by (cases h) (simp_all add: is_rigid_def)
      from existsM_TrueE[OF this] obtain i where i: "i < length ts" "ro F (ts ! i) env = Some (Ok True)"
        by (auto simp: in_set_conv_nth)
      from tyt' t'e obtain Us where tyh: "has_type V Ts h (foldr fun_type Us T)"
        and tyts: "list_all2 (has_type V Ts) ts Us"
        by (auto simp: has_type_list_comb)
      have lUs: "length Us = length ts" using list_all2_lengthD[OF tyts] by simp
      note ra = rigid_tr[OF R \<sigma>(3)]
      have th: "(bnd_env Ts, \<tau>') \<turnstile> tr h : map trty Us \<Rrightarrow> trty T"
        using has_type_subst[OF tyh \<sigma>(2)] ra by (simp add: trty_foldr)
      have targs: "(bnd_env Ts, \<tau>') \<tturnstile> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts : map trty Us"
        by (rule typings_map2) (use lUs list_all2_nthD[OF tyts] has_type_subst[OF _ \<sigma>(2)] in auto)
      from atom_apps_nf[OF conjunct2[OF ra] th targs] obtain ws
        where ws: "length ws = length (map (\<lambda>t. mk_subst \<sigma> (tr t)) ts)"
          "\<And>i. i < length (map (\<lambda>t. mk_subst \<sigma> (tr t)) ts) \<Longrightarrow>
            \<beta>\<eta>cl (map (\<lambda>t. mk_subst \<sigma> (tr t)) ts ! i) (ws ! i) \<and> normal (ws ! i) \<and>
            (bnd_env Ts, \<tau>') \<turnstile> ws ! i : map trty Us ! i"
          "tr h \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> ws" "no_redex (tr h \<degree>\<degree> ws)"
          "(bnd_env Ts, \<tau>') \<turnstile> tr h \<degree>\<degree> ws : trty T"
          "\<And>i. i < length (map (\<lambda>t. mk_subst \<sigma> (tr t)) ts) \<Longrightarrow>
            Suc (ld (bnd_env Ts) \<tau>' (ws ! i) (map trty Us ! i)) \<le> ld (bnd_env Ts) \<tau>' (tr h \<degree>\<degree> ws) (trty T)"
        by blast
      have tsubst: "mk_subst \<sigma> (tr t') = tr h \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
        using ra t'e by (simp add: tr_list_comb comp_def)
      have ldv: "ld (bnd_env Ts) \<tau>' v (trty T) = ld (bnd_env Ts) \<tau>' (tr h \<degree>\<degree> ws) (trty T)"
      proof (rule ld_equiv)
        show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> ws" using veq' tsubst ws(3) by (metis equiv_trans)
      qed (use vty vnr ws(4,5) in auto)
      from ws(2)[of i] i(1) have wi: "\<beta>\<eta>cl (mk_subst \<sigma> (tr (ts ! i))) (ws ! i)" "normal (ws ! i)"
        "(bnd_env Ts, \<tau>') \<turnstile> ws ! i : trty (Us ! i)"
        using lUs by simp_all
      have pti: "proper (ts ! i)" "typs_ok ar (ts ! i)" using pts(1) i(1) by simp_all
      have tyi: "has_type V Ts (ts ! i) (Us ! i)" using list_all2_nthD[OF tyts i(1)] .
      from IH[OF i(2) pti tyi equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF wi(1)]] normal_no_redex[OF wi(2)] wi(3)]
      have "?L \<le> ld (bnd_env Ts) \<tau>' (ws ! i) (trty (Us ! i))" by simp
      also have "\<dots> < ld (bnd_env Ts) \<tau>' v (trty T)" using ws(6)[of i] i(1) lUs ldv by simp
      finally show ?thesis by simp
    qed
  qed
qed

text \<open>A rigid occurrence of \<open>F\<close> in \<open>t\<close> rules out the unifiability of \<open>F x\<^sub>1 \<dots> x\<^sub>n\<close> and \<open>t\<close>.\<close>

lemma rigid_occurs_complete:
  assumes "ok (rigid_occurs F t env) True" "t = list_comb h ts" "is_rigid h"
    "wf_env ar env" "env_typed V env" "proper t" "typs_ok ar t" "has_type V Ts t T"
    "has_type V Ts (app (Var F Fty) is) T" "distinct is" "solution V \<tau>' \<sigma> env"
    "unifies \<sigma> (tr (app (Var F Fty) is)) (tr t)"
  shows False
proof -
  note \<sigma> = solutionD[OF assms(11)]
  have \<sigma>F: "no_loose_bound (\<sigma> (code (AVar F))) 0" "\<And>e'. (e', \<tau>') \<turnstile> \<sigma> (code (AVar F)) : tau V (code (AVar F))"
    by (rule closed_onD[OF \<sigma>(1)], simp, rule typed_onD[OF \<sigma>(2)], simp)
  obtain nF where nF: "\<beta>\<eta>cl (\<sigma> (code (AVar F))) nF" "normal nF" using normal_form_ex[OF \<sigma>F(2)] by blast
  have "(bnd_env Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr t) : trty T" by (rule has_type_subst[OF assms(8) \<sigma>(2)])
  then obtain v where v: "\<beta>\<eta>cl (mk_subst \<sigma> (tr t)) v" "normal v" "(bnd_env Ts, \<tau>') \<turnstile> v : trty T"
    by (rule nf_typed)
  have rh: "rigid_head t" using assms(2,3) by (auto simp: rigid_head_def)
  from rigid_occurs_ld[OF assms(1) refl assms(4,5,11) nF assms(6-8) equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF v(1)]]
      normal_no_redex[OF v(2)] v(3)] rh
  have lt: "ld E \<tau>' nF (trty (V F)) < ld (bnd_env Ts) \<tau>' v (trty T)" by simp
  note ti = has_type_app_Var[OF assms(9)]
  have "ld (bnd_env Ts) \<tau>' v (trty T) = ld E \<tau>' nF (tau V (code (AVar F)))"
  proof (rule ld_flex_occurrence[where \<sigma> = \<sigma> and F = "code (AVar F)" and \<tau> = "tau V", OF \<sigma>F nF])
    show "distinct (nats is)" using assms(10) ti(1) by (auto intro: distinct_nats)
    show "(bnd_env Ts, tau V) \<turnstile> dB.Var (code (AVar F)) \<degree>\<degree> map BVar (nats is) : trty T"
      using has_type_tr[OF assms(9)] by (simp add: tr_app')
    have "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)" by (rule equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF v(1)]])
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (app (Var F Fty) is))"
      using assms(12) by (simp add: unifies_def equiv_sym)
    finally show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar F)) \<degree>\<degree> map BVar (nats is)"
      by (simp add: tr_app' comp_def)
  qed (use v normal_no_redex in auto)
  with lt ti(2) show False by simp
qed

subsection \<open>Completeness\<close>

theorem unif_complete:
  assumes "unif alg binders s t env = Some r"
  shows "wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow> env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow>
    wf_term ar (length binders) s \<Longrightarrow> wf_term ar (length binders) t \<Longrightarrow>
    has_type V (map snd binders) s T \<Longrightarrow> has_type V (map snd binders) t T \<Longrightarrow>
    below (maxidx env) s \<Longrightarrow> below (maxidx env) t \<Longrightarrow>
    solution V \<tau>' \<sigma> env \<Longrightarrow> unifies \<sigma> (tr s) (tr t) \<Longrightarrow>
    no_unif (Some r) \<and> (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'))"
  using assms
proof (induction alg binders s t env r arbitrary: V \<sigma> T rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg binders s t env r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env"
    and ws: "wf_term ar (length binders) s" and wt: "wf_term ar (length binders) t"
    and tys: "has_type V (map snd binders) s T" and tyt: "has_type V (map snd binders) t T"
    and bs: "below (maxidx env) s" and bt: "below (maxidx env) t"
    and sol: "solution V \<tau>' \<sigma> env" and uni: "unifies \<sigma> (tr s) (tr t)"
    using "1.prems" by simp_all
  let ?Bs = "map snd binders" and ?n = "length binders"
  note \<sigma> = solutionD[OF sol]
  have vt: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wf])
  define R where "R = (\<lambda>s0 t0. if is_Abs s0 \<and> is_Abs t0 then
        (case (s0, t0) of
          (pterm.Abs ns Ts ts, pterm.Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            uni alg ((name, Ts) # binders) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s0 then
        (case s0 of
          pterm.Abs ns Ts ts \<Rightarrow> uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t0 then
        (case t0 of
          pterm.Abs nt Tt tt \<Rightarrow> uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s0; (ht, ts) = strip_comb t0 in
          if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (pterm.Var F Fty, pterm.Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env binders F Fty is js
                else flexflex2 env binders F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env binders F Fty is t0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env binders F Fty is s0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB binders i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env}
            | _ \<Rightarrow> rigid_clash binders hs ht)))"
  from "1.hyps" have "head_norm env s \<bind> (\<lambda>s0. head_norm env t \<bind> (\<lambda>t0. R s0 t0)) = Some r"
    unfolding R_def by (simp only:)
  then show ?case
  proof (rule bindM_SomeE)
    fix e assume "head_norm env s = Some (Err e)" "r = Err e"
    with no_unif_head_norm[OF vt, of s] show ?thesis by simp
  next
    fix s0 assume hs: "head_norm env s = Some (Ok s0)"
      and rest1: "head_norm env t \<bind> (\<lambda>t0. R s0 t0) = Some r"
    from rest1 show ?thesis
    proof (rule bindM_SomeE)
      fix e assume "head_norm env t = Some (Err e)" "r = Err e"
      with no_unif_head_norm[OF vt, of t] show ?thesis by simp
    next
      fix t0 assume ht: "head_norm env t = Some (Ok t0)" and rest0: "R s0 t0 = Some r"
      note rest = rest0[unfolded R_def]
      from head_norm_sound[OF hs refl wf] ws
      have ws0: "wf_term ar ?n s0" and s0: "env \<Turnstile> s \<approx> s0" by (auto simp: wf_term_def)
      from head_norm_sound[OF ht refl wf] wt
      have wt0: "wf_term ar ?n t0" and t0: "env \<Turnstile> t \<approx> t0" by (auto simp: wf_term_def)
      have tys0: "has_type V ?Bs s0 T" by (rule head_norm_typed[OF hs refl wf ety tys])
      have tyt0: "has_type V ?Bs t0 T" by (rule head_norm_typed[OF ht refl wf ety tyt])
      have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF hs refl wf fr bs])
      have bt0: "below (maxidx env) t0" by (rule below_head_norm[OF ht refl wf fr bt])
      have uni0: "unifies \<sigma> (tr s0) (tr t0)"
        using env_equivD[OF s0 \<sigma>(1,4)] env_equivD[OF t0 \<sigma>(1,4)] uni
        by (simp add: unifies_def) (meson equiv_sym equiv_trans)
      note IH = "1.IH"
      show ?thesis
      proof (cases "is_Abs s0")
        case sA: True
        then obtain ns Ts ts where s0a: "s0 = pterm.Abs ns Ts ts" by (cases s0) auto
        have gTs: "ground ar Ts" using ws0 s0a by (simp add: wf_term_def)
        from tys0 s0a obtain W where T: "T = Ts \<rightarrow>\<^sub>T W" and tyts: "has_type V (Ts # ?Bs) ts W"
          by (auto elim: has_type_elims)
        have bts: "below (maxidx env) ts" using bs0 s0a by simp
        have wts: "wf_term ar (Suc ?n) ts" using ws0 s0a by (simp add: wf_term_def)
        show ?thesis
        proof (cases "is_Abs t0")
          case True
          then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
          from tyt0 t0a T have Tt: "Tt = Ts" and tytt: "has_type V (Ts # ?Bs) tt W"
            by (auto elim: has_type_elims)
          define nm where "nm = (if ns = STR '''' then nt else ns)"
          from rest sA True s0a t0a have u: "uni alg ((nm, Ts) # binders) ts tt env = Some r"
            by (simp add: Let_def nm_def unify_types_ground[OF gTs gTs] Tt)
          have bok': "binders_ok ar ((nm, Ts) # binders)" using bok gTs by (simp add: binders_ok_def)
          have btt: "below (maxidx env) tt" using bt0 t0a by simp
          have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
          have uni': "unifies \<sigma> (tr ts) (tr tt)" using uni0 s0a t0a by (simp add: unifies_def fact5[symmetric])
          show ?thesis
            using IH[OF u wf bok' ety fr _ _ _ _ bts btt sol uni'] wts wtt tyts tytt by simp
        next
          case False
          from rest sA False s0a have u: "uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env = Some r"
            by simp
          have bok': "binders_ok ar ((ns, Ts) # binders)" using bok gTs by (simp add: binders_ok_def)
          have wi: "wf_term ar (Suc ?n) (incr t0 $ Bound 0)"
            using wt0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
              intro: no_loose_bound_lift)
          have tyi: "has_type V (Ts # ?Bs) (incr t0 $ Bound 0) W"
            using has_type_incr[OF tyt0, of Ts] T by (intro has_type.App[of _ _ _ Ts]) (auto simp: has_type_Bound_iff)
          have bi: "below (maxidx env) (incr t0 $ Bound 0)" using bt0 by (simp add: below_def vars_incr)
          have "mk_subst \<sigma> (tr (incr t0 $ Bound 0)) = lift (mk_subst \<sigma> (tr t0)) 0 \<degree> BVar 0"
            using wt0 \<sigma>(1) by (simp add: wf_term_def incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)
          then have uni': "unifies \<sigma> (tr ts) (tr (incr t0 $ Bound 0))"
            using uni0 s0a by (simp add: unifies_def fact6)
          show ?thesis
            using IH[OF u wf bok' ety fr _ _ _ _ bts bi sol uni'] wts wi tyts tyi by simp
        qed
      next
        case nsA: False
        show ?thesis
        proof (cases "is_Abs t0")
          case True
          then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
          have gTt: "ground ar Tt" using wt0 t0a by (simp add: wf_term_def)
          from tyt0 t0a obtain W where T: "T = Tt \<rightarrow>\<^sub>T W" and tytt: "has_type V (Tt # ?Bs) tt W"
            by (auto elim: has_type_elims)
          from rest nsA True t0a have u: "uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env = Some r"
            by simp
          have bok': "binders_ok ar ((nt, Tt) # binders)" using bok gTt by (simp add: binders_ok_def)
          have btt: "below (maxidx env) tt" using bt0 t0a by simp
          have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
          have wi: "wf_term ar (Suc ?n) (incr s0 $ Bound 0)"
            using ws0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
              intro: no_loose_bound_lift)
          have tyi: "has_type V (Tt # ?Bs) (incr s0 $ Bound 0) W"
            using has_type_incr[OF tys0, of Tt] T by (intro has_type.App[of _ _ _ Tt]) (auto simp: has_type_Bound_iff)
          have bi: "below (maxidx env) (incr s0 $ Bound 0)" using bs0 by (simp add: below_def vars_incr)
          have "mk_subst \<sigma> (tr (incr s0 $ Bound 0)) = lift (mk_subst \<sigma> (tr s0)) 0 \<degree> BVar 0"
            using ws0 \<sigma>(1) by (simp add: wf_term_def incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)
          moreover have "mk_subst \<sigma> (tr s0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (mk_subst \<sigma> (tr tt))"
            using uni0 t0a by (simp add: unifies_def)
          ultimately have uni': "unifies \<sigma> (tr (incr s0 $ Bound 0)) (tr tt)"
            using fact6[of "mk_subst \<sigma> (tr tt)" "mk_subst \<sigma> (tr s0)"] by (auto simp: unifies_def equiv_sym)
          show ?thesis
            using IH[OF u wf bok' ety fr _ _ _ _ bi btt sol uni'] wi wtt tyi tytt by simp
        next
          case nAt: False
          obtain hs ss where shs: "strip_comb s0 = (hs, ss)" by force
          obtain ht ts where sht: "strip_comb t0 = (ht, ts)" by force
          note s0e = strip_comb_list_comb[OF shs] and t0e = strip_comb_list_comb[OF sht]
          have wss: "wf_term ar ?n hs" "\<forall>t\<in>set ss. wf_term ar ?n t"
            using ws0 s0e by (simp_all add: wf_term_list_comb)
          have wts: "wf_term ar ?n ht" "\<forall>t\<in>set ts. wf_term ar ?n t"
            using wt0 t0e by (simp_all add: wf_term_list_comb)
          have pss: "\<forall>t\<in>set ss. proper t \<and> typs_ok ar t" and pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
            using wss(2) wts(2) by (auto simp: wf_term_def)
          have wt0': "proper t0" "typs_ok ar t0" and ws0': "proper s0" "typs_ok ar s0"
            using wt0 ws0 by (simp_all add: wf_term_def)
          have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
            using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
          have nAh: "\<not> is_Abs hs" "\<not> is_Abs ht"
            using head_norm_head[OF hs refl nsA] head_norm_head[OF ht refl nAt] shs sht by simp_all
          have rigI: "is_rigid h" if "\<not> is_Var h" "\<not> is_Abs h" "\<not> (\<exists>f u. h = f $ u)" "wf_term ar ?n h" for h
            using that by (cases h) (auto simp: is_rigid_def wf_term_def)
          have uni0': "mk_subst \<sigma> (tr (list_comb hs ss)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (list_comb ht ts))"
            using uni0 s0e t0e by (simp add: unifies_def)
          consider (VV) F Fty G Gty where "hs = pterm.Var F Fty" "ht = pterm.Var G Gty"
            | (VR) F Fty where "hs = pterm.Var F Fty" "\<not> is_Var ht"
            | (RV) G Gty where "\<not> is_Var hs" "ht = pterm.Var G Gty"
            | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
            by (cases hs; cases ht) auto
          then show ?thesis
          proof cases
            case VV
            from rest nsA nAt shs sht VV have ff0: "ints_of' env ss \<bind> (\<lambda>is. ints_of' env ts \<bind> (\<lambda>js.
                if F = G then flexflex1 env binders F Fty is js else flexflex2 env binders F Fty is G Gty js)) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ss = Some (Err e)" "r = Err e"
              with no_unif_ints_of'[OF vt, of ss] show ?thesis by simp
            next
              fix "is" assume iss: "ok (ints_of' env ss) is" and ff1: "ints_of' env ts \<bind> (\<lambda>js.
                if F = G then flexflex1 env binders F Fty is js else flexflex2 env binders F Fty is G Gty js) =
                Some r"
              from ff1 show ?thesis
              proof (rule bindM_SomeE)
                fix e assume "ints_of' env ts = Some (Err e)" "r = Err e"
                with no_unif_ints_of'[OF vt, of ts] show ?thesis by simp
              next
                fix js assume js: "ok (ints_of' env ts) js" and ff: "(if F = G then flexflex1 env binders F Fty is js
                  else flexflex2 env binders F Fty is G Gty js) = Some r"
                note iS = ints_of'_sound[OF iss wf pss] and jS = ints_of'_sound[OF js wf pts]
                have tyF: "has_type V ?Bs (app (pterm.Var F Fty) is) T"
                  using has_type_ints_of'[OF iss wf ety] tys0 s0e VV by simp
                have tyG: "has_type V ?Bs (app (pterm.Var G Gty) js) T"
                  using has_type_ints_of'[OF js wf ety] tyt0 t0e VV by simp
                have gF: "ground ar Fty" and gG: "ground ar Gty"
                  using wss(1) wts(1) VV by (simp_all add: wf_term_def)
                have Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env"
                  using bs0 bt0 s0e t0e VV by (simp_all add: below_list_comb)
                have eqs: "env \<Turnstile> s0 \<approx> app (pterm.Var F Fty) is"
                  using ints_of'_equiv[OF iss wf pss] s0e VV by simp
                have eqt: "env \<Turnstile> t0 \<approx> app (pterm.Var G Gty) js"
                  using ints_of'_equiv[OF js wf pts] t0e VV by simp
                have uniFG: "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr (app (pterm.Var G Gty) js))"
                  using uni0 env_equivD[OF eqs \<sigma>(1,4)] env_equivD[OF eqt \<sigma>(1,4)]
                  by (simp add: unifies_def) (meson equiv_sym equiv_trans)
                show ?thesis
                proof (cases "F = G")
                  case True
                  with ff have ff': "flexflex1 env binders F Fty is js = Some r" by simp
                  have GF: "Gty = Fty" using has_type_app_Var(2)[OF tyF] has_type_app_Var(2)[OF tyG] True by simp
                  then have tyG': "has_type V ?Bs (app (pterm.Var F Fty) js) T" using tyG True by simp
                  have uni': "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr (app (pterm.Var F Fty) js))"
                    using uniFG True GF by simp
                  note c = flexflex1_complete[OF ff' wf ety fr Fm tyF tyG' iS(1) jS(1) sol uni']
                  show ?thesis
                  proof (intro conjI allI impI c(1))
                    fix env' assume r: "r = Ok env'"
                    show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
                      using ext_sol_sol_ext[OF c(2)[OF r] flexflex1_sound(2)[OF ff'[unfolded r] wf gF bok]] .
                  qed
                next
                  case False
                  with ff have ff': "flexflex2 env binders F Fty is G Gty js = Some r" by simp
                  note c = flexflex2_complete[OF ff' wf ety fr Fm Gm False tyF tyG iS(1) jS(1) sol uniFG]
                  show ?thesis
                  proof (intro conjI allI impI c(1))
                    fix env' assume r: "r = Ok env'"
                    show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
                      using ext_sol_sol_ext[OF c(2)[OF r]
                        flexflex2_sound(2)[OF ff'[unfolded r] wf gF gG bok iS(2) jS(2)]] .
                  qed
                qed
              qed
            qed
          next
            case VR
            from rest nsA nAt shs sht VR have fr0: "ints_of' env ss \<bind> (\<lambda>is. flexrigid env binders F Fty is t0) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ss = Some (Err e)" "r = Err e"
              with no_unif_ints_of'[OF vt, of ss] show ?thesis by simp
            next
              fix "is" assume iss: "ok (ints_of' env ss) is" and frg: "flexrigid env binders F Fty is t0 = Some r"
              note iS = ints_of'_sound[OF iss wf pss]
              have tyF: "has_type V ?Bs (app (pterm.Var F Fty) is) T"
                using has_type_ints_of'[OF iss wf ety] tys0 s0e VR by simp
              have gF: "ground ar Fty" using wss(1) VR by (simp add: wf_term_def)
              have Fm: "snd F \<le> maxidx env" using bs0 s0e VR by (simp add: below_list_comb)
              have eqs: "env \<Turnstile> s0 \<approx> app (pterm.Var F Fty) is"
                using ints_of'_equiv[OF iss wf pss] s0e VR by simp
              have uniF: "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr t0)"
                using uni0 env_equivD[OF eqs \<sigma>(1,4)] by (simp add: unifies_def) (meson equiv_sym equiv_trans)
              have rig: "is_rigid ht" by (rule rigI[OF VR(2) nAh(2) nApp(2) wts(1)])
              have occ: "\<not> ok (rigid_occurs F t0 env) True"
                using rigid_occurs_complete[OF _ t0e rig wf ety wt0' tyt0 tyF iS(1) sol uniF] by blast
              note c = flexrigid_complete[OF frg wf bok ety fr Fm gF tyF tyt0 wt0' bt0 iS(1) sol uniF occ]
              show ?thesis using c by blast
            qed
          next
            case RV
            from rest nsA nAt shs sht RV have fr0: "ints_of' env ts \<bind> (\<lambda>js. flexrigid env binders G Gty js s0) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ts = Some (Err e)" "r = Err e"
              with no_unif_ints_of'[OF vt, of ts] show ?thesis by simp
            next
              fix js assume js: "ok (ints_of' env ts) js" and frg: "flexrigid env binders G Gty js s0 = Some r"
              note jS = ints_of'_sound[OF js wf pts]
              have tyG: "has_type V ?Bs (app (pterm.Var G Gty) js) T"
                using has_type_ints_of'[OF js wf ety] tyt0 t0e RV by simp
              have gG: "ground ar Gty" using wts(1) RV by (simp add: wf_term_def)
              have Gm: "snd G \<le> maxidx env" using bt0 t0e RV by (simp add: below_list_comb)
              have eqt: "env \<Turnstile> t0 \<approx> app (pterm.Var G Gty) js"
                using ints_of'_equiv[OF js wf pts] t0e RV by simp
              have uniG: "unifies \<sigma> (tr (app (pterm.Var G Gty) js)) (tr s0)"
                using uni0 env_equivD[OF eqt \<sigma>(1,4)] by (simp add: unifies_def) (meson equiv_sym equiv_trans)
              have rig: "is_rigid hs" by (rule rigI[OF RV(1) nAh(1) nApp(1) wss(1)])
              have occ: "\<not> ok (rigid_occurs G s0 env) True"
                using rigid_occurs_complete[OF _ s0e rig wf ety ws0' tys0 tyG jS(1) sol uniG] by blast
              note c = flexrigid_complete[OF frg wf bok ety fr Gm gG tyG tys0 ws0' bs0 jS(1) sol uniG occ]
              show ?thesis using c by blast
            qed
          next
            case RR
            have rs: "is_rigid hs" by (rule rigI[OF RR(1) nAh(1) nApp(1) wss(1)])
            have rt: "is_rigid ht" by (rule rigI[OF RR(2) nAh(2) nApp(2) wts(1)])
            have rigtr: "mk_subst \<sigma> (tr h) = tr h \<and> is_atom (tr h)" if "is_rigid h" for h
              using that by (auto simp: is_rigid_def rigid_substD[OF \<sigma>(3)])
            from uni0' have "tr hs \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ss \<equiv>\<^sub>\<beta>\<^sub>\<eta>
                tr ht \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
              using rigtr[OF rs(1)] rigtr[OF rt(1)] by (simp add: tr_list_comb comp_def)
            from atom_apps_equiv[OF conjunct2[OF rigtr[OF rs(1)]] conjunct2[OF rigtr[OF rt(1)]] this]
            have hh: "tr hs = tr ht"
              and args: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>t. mk_subst \<sigma> (tr t)) ss) (map (\<lambda>t. mk_subst \<sigma> (tr t)) ts)"
              by auto
            have hsht: "hs = ht" using hh rs(1) rt(1)
              by (auto simp: is_rigid_def integer_reps)
            have len: "length ss = length ts" using list_all2_lengthD[OF args] by simp
            have gh: "typs_ok ar hs" using wss(1) by (simp add: wf_term_def)
            have fo: "foldM (\<lambda>(s, t) env. uni alg binders s t env) (zip ss ts) env = Some r"
            proof -
              from rs(1) consider (C) c U where "hs = Const c U" | (Fr) c U where "hs = Free c U"
                | (B) i where "hs = Bound i" by (auto simp: is_rigid_def)
              then show ?thesis
              proof cases
                case C
                with gh have "ground ar U" by simp
                with rest nsA nAt shs sht C hsht len show ?thesis
                  by (simp add: unify_types_ground zip_eq_return)
              next
                case Fr
                with gh have "ground ar U" by simp
                with rest nsA nAt shs sht Fr hsht len show ?thesis
                  by (simp add: unify_types_ground zip_eq_return)
              next
                case B
                with hsht have hb: "hs = Bound i" "ht = Bound i" by simp_all
                from rest nsA nAt shs sht len show ?thesis by (simp add: hb zip_eq_return)
              qed
            qed
            from tys0 s0e obtain Us where tyhs: "has_type V ?Bs hs (foldr fun_type Us T)"
              and tyss: "list_all2 (has_type V ?Bs) ss Us"
              by (auto simp: has_type_list_comb)
            from tyt0 t0e obtain Us' where tyht: "has_type V ?Bs ht (foldr fun_type Us' T)"
              and tyts: "list_all2 (has_type V ?Bs) ts Us'"
              by (auto simp: has_type_list_comb)
            have "Us' = Us"
              using has_type_unique[OF tyhs tyht[folded hsht]] by (auto dest: foldr_fun_type_inj)
            note tyts = tyts[unfolded this]
            have bss: "\<forall>t\<in>set ss. below (maxidx env) t" using bs0 s0e by (simp add: below_list_comb)
            have bts: "\<forall>t\<in>set ts. below (maxidx env) t" using bt0 t0e by (simp add: below_list_comb)
            define P where "P = (\<lambda>(g :: (indexname \<Rightarrow> ptyp) \<times> (nat \<Rightarrow> dB)) e.
              sol_ext ar V \<tau>' \<sigma> env (fst g) (snd g) e)"
            have "no_unif (Some r) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
            proof (rule foldM_complete[OF fo, of P "(V, \<sigma>)"])
              show "P (V, \<sigma>) env" using sol ety fr wf by (simp add: P_def sol_ext_refl)
            next
              fix x g e r1
              assume x: "x \<in> set (zip ss ts)" and Pg: "P g e"
                and f: "(\<lambda>(s, t) env. uni alg binders s t env) x e = Some r1"
              from x obtain i where i: "i < length ss" "x = (ss ! i, ts ! i)"
                using len by (auto simp: in_set_zip)
              obtain V1 \<sigma>1 where g: "g = (V1, \<sigma>1)" by force
              from Pg have e1: "sol_ext ar V \<tau>' \<sigma> env V1 \<sigma>1 e" by (simp add: P_def g)
              have agV: "agreeV (maxidx env) V V1" and ag: "agree (maxidx env) \<sigma> \<sigma>1"
                and sol1: "solution V1 \<tau>' \<sigma>1 e" and ety1: "env_typed V1 e" and fr1: "fresh_env e"
                and wf1: "wf_env ar e" and mx: "maxidx env \<le> maxidx e"
                using e1 by (simp_all add: sol_ext_def)
              have ii: "i < length ts" using i(1) len by simp
              have u: "uni alg binders (ss ! i) (ts ! i) e = Some r1" using f i(2) by simp
              have ba: "below (maxidx env) (ss ! i)" and bb: "below (maxidx env) (ts ! i)"
                using bss bts i(1) ii by simp_all
              have tya: "has_type V1 ?Bs (ss ! i) (Us ! i)"
                using has_type_agreeV[OF _ ba agV] tyss i(1) by (simp add: list_all2_conv_all_nth)
              have tyb: "has_type V1 ?Bs (ts ! i) (Us ! i)"
                using has_type_agreeV[OF _ bb agV] tyts ii by (simp add: list_all2_conv_all_nth)
              have "mk_subst \<sigma> (tr (ss ! i)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (ts ! i))"
                using args i(1) len by (simp add: list_all2_conv_all_nth)
              then have uni1: "unifies \<sigma>1 (tr (ss ! i)) (tr (ts ! i))"
                using mk_subst_agree[OF ba ag] mk_subst_agree[OF bb ag] by (simp add: unifies_def)
              note IHi = IH[OF u wf1 bok ety1 fr1 _ _ tya tyb below_mono[OF ba mx] below_mono[OF bb mx]
                sol1 uni1]
              have "no_unif (Some r1) \<and> (\<forall>env'. r1 = Ok env' \<longrightarrow>
                  (\<exists>V' \<sigma>'. sol_ext ar V1 \<tau>' \<sigma>1 e V' \<sigma>' env'))"
                using IHi wss(2) wts(2) i(1) ii by simp
              then show "no_unif (Some r1) \<and> (\<forall>e1. r1 = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
                using sol_ext_trans[OF e1] by (fastforce simp: P_def)
            qed
            then show ?thesis by (auto simp: P_def)
          qed
        qed
      qed
    qed
  qed
qed

end

end
