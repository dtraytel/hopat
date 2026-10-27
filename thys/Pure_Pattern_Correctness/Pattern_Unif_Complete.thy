section \<open>Completeness of Pattern Unification\<close>

theory Pattern_Unif_Complete
  imports Pattern_Completeness
begin

text \<open>
  The occurs check of \<^const>\<open>flexrigid\<close> follows bindings in the environment and does not
  \<open>\<beta>\<close>-normalise: it is only complete for \<open>\<beta>\<close>-normal patterns in environments whose bindings are
  \<open>\<beta>\<close>-normal patterns. We therefore state completeness for such inputs.
\<close>

subsection \<open>\<open>\<beta>\<close>-normal patterns\<close>

definition is_rigid :: "pterm \<Rightarrow> bool" where
  "is_rigid h \<longleftrightarrow> (\<exists>c T. h = Const c T) \<or> (\<exists>c T. h = Free c T) \<or> (\<exists>i. h = Bound i \<and> 0 \<le> i)"

inductive ppat :: "pterm \<Rightarrow> bool" where
  ppat_Abs: "ppat t \<Longrightarrow> ppat (Abs a T t)"
| ppat_rigid: "is_rigid h \<Longrightarrow> \<forall>t\<in>set ts. ppat t \<Longrightarrow> ppat (list_comb h ts)"
| ppat_flex: "distinct is \<Longrightarrow> \<forall>i\<in>set is. 0 \<le> i \<Longrightarrow> ppat (app (Var x T) is)"

definition env_ppat :: "env \<Rightarrow> bool" where
  "env_ppat env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> ppat u)"

lemma env_ppatD: "env_ppat env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ppat u"
  by (cases x) (simp add: env_ppat_def)

lemma head_norm_ppat:
  "head_norm env t = Some (Ok t') \<Longrightarrow> wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow> ppat t'"
  sorry

lemma ppat_AbsD: "ppat (Abs a T t) \<Longrightarrow> ppat t"
  sorry

lemma ppat_incr_Bound0: "ppat t \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> ppat (incr t $ Bound 0)"
  sorry

lemma ppat_spine:
  assumes "ppat (list_comb h ts)" "\<not> (\<exists>f u. h = f $ u)" "\<not> is_Abs (list_comb h ts)"
  shows "is_rigid h \<and> (\<forall>t\<in>set ts. ppat t) \<or> (\<exists>x T. h = Var x T)"
  sorry

lemma occurs_complete:
  assumes "ok (occurs F t env) True" "ppat t" "t = list_comb h ts" "is_rigid h"
    "env_ppat env" "wf_env ar env" "env_typed V env" "has_type V Ts t T"
    "has_type V Ts (app (Var F Fty) is) T" "distinct is" "solution V \<tau>' \<sigma> env"
    "unifies \<sigma> (tr (app (Var F Fty) is)) (tr t)"
  shows False
  sorry

lemma flexflex1_ppat:
  "flexflex1 env binders F Fty is js = Some (Ok env') \<Longrightarrow> env_ppat env \<Longrightarrow> env_ppat env'"
  sorry

lemma flexflex2_ppat:
  "flexflex2 env binders F Fty is G Gty js = Some (Ok env') \<Longrightarrow> env_ppat env \<Longrightarrow>
    distinct is \<Longrightarrow> distinct js \<Longrightarrow> \<forall>i\<in>set is. 0 \<le> i \<Longrightarrow> \<forall>j\<in>set js. 0 \<le> j \<Longrightarrow> env_ppat env'"
  sorry

lemma flexrigid_ppat:
  "flexrigid env binders F Fty is t = Some (Ok env') \<Longrightarrow> wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow>
    ppat t \<Longrightarrow> env_ppat env'"
  sorry


lemma vars_incr_aux: "vars (incr_aux d t) = vars t"
  by (induction d t rule: incr_aux.induct) auto

lemma vars_incr: "vars (incr t) = vars t"
  by (simp add: incr_def vars_incr_aux)

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


subsection \<open>Completeness\<close>

theorem unif_complete:
  assumes "unif alg binders s t env = Some r"
  shows "wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow> env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow>
    env_ppat env \<Longrightarrow> wf_term ar (length binders) s \<Longrightarrow> wf_term ar (length binders) t \<Longrightarrow>
    ppat s \<Longrightarrow> ppat t \<Longrightarrow> has_type V (map snd binders) s T \<Longrightarrow> has_type V (map snd binders) t T \<Longrightarrow>
    below (maxidx env) s \<Longrightarrow> below (maxidx env) t \<Longrightarrow>
    solution V \<tau>' \<sigma> env \<Longrightarrow> unifies \<sigma> (tr s) (tr t) \<Longrightarrow>
    no_unif (Some r) \<and> (\<forall>env'. r = Ok env' \<longrightarrow> env_ppat env' \<and> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'))"
  using assms
proof (induction alg binders s t env r arbitrary: V \<sigma> T rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg binders s t env r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env" and epp: "env_ppat env"
    and ws: "wf_term ar (length binders) s" and wt: "wf_term ar (length binders) t"
    and pps: "ppat s" and ppt: "ppat t"
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
      have pps0: "ppat s0" by (rule head_norm_ppat[OF hs wf epp pps])
      have ppt0: "ppat t0" by (rule head_norm_ppat[OF ht wf epp ppt])
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
        have pts: "ppat ts" using pps0 s0a by (auto dest: ppat_AbsD)
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
          have ptt: "ppat tt" using ppt0 t0a by (auto dest: ppat_AbsD)
          have btt: "below (maxidx env) tt" using bt0 t0a by simp
          have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
          have uni': "unifies \<sigma> (tr ts) (tr tt)" using uni0 s0a t0a by (simp add: unifies_def fact5[symmetric])
          show ?thesis
            using IH[OF u wf bok' ety fr epp _ _ pts ptt _ _ bts btt sol uni'] wts wtt tyts tytt by simp
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
          have pi: "ppat (incr t0 $ Bound 0)" by (rule ppat_incr_Bound0[OF ppt0 False])
          have bi: "below (maxidx env) (incr t0 $ Bound 0)" using bt0 by (simp add: below_def vars_incr)
          have "mk_subst \<sigma> (tr (incr t0 $ Bound 0)) = lift (mk_subst \<sigma> (tr t0)) 0 \<degree> BVar 0"
            using wt0 \<sigma>(1) by (simp add: wf_term_def incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)
          then have uni': "unifies \<sigma> (tr ts) (tr (incr t0 $ Bound 0))"
            using uni0 s0a by (simp add: unifies_def fact6)
          show ?thesis
            using IH[OF u wf bok' ety fr epp _ _ pts pi _ _ bts bi sol uni'] wts wi tyts tyi by simp
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
          have ptt: "ppat tt" using ppt0 t0a by (auto dest: ppat_AbsD)
          have btt: "below (maxidx env) tt" using bt0 t0a by simp
          have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
          have wi: "wf_term ar (Suc ?n) (incr s0 $ Bound 0)"
            using ws0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
              intro: no_loose_bound_lift)
          have tyi: "has_type V (Tt # ?Bs) (incr s0 $ Bound 0) W"
            using has_type_incr[OF tys0, of Tt] T by (intro has_type.App[of _ _ _ Tt]) (auto simp: has_type_Bound_iff)
          have pi: "ppat (incr s0 $ Bound 0)" by (rule ppat_incr_Bound0[OF pps0 nsA])
          have bi: "below (maxidx env) (incr s0 $ Bound 0)" using bs0 by (simp add: below_def vars_incr)
          have "mk_subst \<sigma> (tr (incr s0 $ Bound 0)) = lift (mk_subst \<sigma> (tr s0)) 0 \<degree> BVar 0"
            using ws0 \<sigma>(1) by (simp add: wf_term_def incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)
          moreover have "mk_subst \<sigma> (tr s0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (mk_subst \<sigma> (tr tt))"
            using uni0 t0a by (simp add: unifies_def)
          ultimately have uni': "unifies \<sigma> (tr (incr s0 $ Bound 0)) (tr tt)"
            using fact6[of "mk_subst \<sigma> (tr tt)" "mk_subst \<sigma> (tr s0)"] by (auto simp: unifies_def equiv_sym)
          show ?thesis
            using IH[OF u wf bok' ety fr epp _ _ pi ptt _ _ bi btt sol uni'] wi wtt tyi tytt by simp
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
          note sps = ppat_spine[OF pps0[unfolded s0e] nApp(1) nsA[unfolded s0e]]
          note spt = ppat_spine[OF ppt0[unfolded t0e] nApp(2) nAt[unfolded t0e]]
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
                    show "env_ppat env'" using flexflex1_ppat[OF ff'[unfolded r] epp] .
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
                    show "env_ppat env'" using flexflex2_ppat[OF ff'[unfolded r] epp iS(1) jS(1) iS(2) jS(2)] .
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
              have rig: "is_rigid ht" using spt VR(2) by auto
              have occ: "\<not> ok (occurs F t0 env) True"
                using occurs_complete[OF _ ppt0 t0e rig epp wf ety tyt0 tyF iS(1) sol uniF] by blast
              note c = flexrigid_complete[OF frg wf bok ety fr Fm gF tyF tyt0 wt0' bt0 iS(1) sol uniF occ]
              show ?thesis
              proof (intro conjI allI impI c(1))
                fix env' assume r: "r = Ok env'"
                show "env_ppat env'" using flexrigid_ppat[OF frg[unfolded r] wf epp ppt0] .
                show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'" using c(2)[OF r] .
              qed
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
              have rig: "is_rigid hs" using sps RV(1) by auto
              have occ: "\<not> ok (occurs G s0 env) True"
                using occurs_complete[OF _ pps0 s0e rig epp wf ety tys0 tyG jS(1) sol uniG] by blast
              note c = flexrigid_complete[OF frg wf bok ety fr Gm gG tyG tys0 ws0' bs0 jS(1) sol uniG occ]
              show ?thesis
              proof (intro conjI allI impI c(1))
                fix env' assume r: "r = Ok env'"
                show "env_ppat env'" using flexrigid_ppat[OF frg[unfolded r] wf epp pps0] .
                show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'" using c(2)[OF r] .
              qed
            qed
          next
            case RR
            have rs: "is_rigid hs" "\<forall>t\<in>set ss. ppat t" using sps RR by auto
            have rt: "is_rigid ht" "\<forall>t\<in>set ts. ppat t" using spt RR by auto
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
              sol_ext ar V \<tau>' \<sigma> env (fst g) (snd g) e \<and> env_ppat e)"
            have "no_unif (Some r) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
            proof (rule foldM_complete[OF fo, of P "(V, \<sigma>)"])
              show "P (V, \<sigma>) env" using sol ety fr wf epp by (simp add: P_def sol_ext_refl)
            next
              fix x g e r1
              assume x: "x \<in> set (zip ss ts)" and Pg: "P g e"
                and f: "(\<lambda>(s, t) env. uni alg binders s t env) x e = Some r1"
              from x obtain i where i: "i < length ss" "x = (ss ! i, ts ! i)"
                using len by (auto simp: in_set_zip)
              obtain V1 \<sigma>1 where g: "g = (V1, \<sigma>1)" by force
              from Pg have e1: "sol_ext ar V \<tau>' \<sigma> env V1 \<sigma>1 e" and epp1: "env_ppat e" by (simp_all add: P_def g)
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
              note IHi = IH[OF u wf1 bok ety1 fr1 epp1 _ _ _ _ tya tyb below_mono[OF ba mx] below_mono[OF bb mx]
                sol1 uni1]
              have "no_unif (Some r1) \<and> (\<forall>env'. r1 = Ok env' \<longrightarrow> env_ppat env' \<and>
                  (\<exists>V' \<sigma>'. sol_ext ar V1 \<tau>' \<sigma>1 e V' \<sigma>' env'))"
                using IHi wss(2) wts(2) rs(2) rt(2) i(1) ii by simp
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
