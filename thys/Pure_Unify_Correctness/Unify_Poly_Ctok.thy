section \<open>Problems with Type Variables: Constants of the Environment\<close>

theory Unify_Poly_Ctok
  imports Unify_Poly_Simpl
begin

context csig
begin

text \<open>
  The terms of the environments that the unifiers compute have constants with instances of their
  declared types (\<^const>\<open>ctok\<close>) before the normalisation of their types: these terms are built
  from subterms of the problem and of the environment, variables, bound variables and
  abstractions. The typing invariants (\<^const>\<open>wt_env\<close>) give this only for the terms with
  normalised types. For pattern unification (\<^const>\<open>unify\<close>), whose correctness is shown via
  ground instances, it is shown here directly; the steps of \<open>hounifiers\<close> keep it via
  \<^const>\<open>twft\<close>.
\<close>

subsection \<open>Terms\<close>

lemma ctok_incr_bv[simp]: "ctok (incr_bv inc lev t) = ctok t"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma ctok_incr_boundvars[simp]: "ctok (incr_boundvars inc t) = ctok t"
  by (simp add: incr_boundvars_def)

lemma ctok_subst_bound_aux: "ctok t \<Longrightarrow> ctok arg \<Longrightarrow> ctok (subst_bound_aux arg lev t)"
  by (induction arg lev t rule: subst_bound_aux.induct) auto

lemma ctok_subst_bound: "ctok t \<Longrightarrow> ctok arg \<Longrightarrow> ctok (subst_bound arg t)"
  by (simp add: subst_bound_def ctok_subst_bound_aux)

lemma ctok_strip_comb: "strip_comb t = (h, ts) \<Longrightarrow> ctok t \<longleftrightarrow> ctok h \<and> (\<forall>u\<in>set ts. ctok u)"
  using strip_comb_list_comb[of t h ts] by (simp only: ctok_list_comb')

lemma ctok_incr_aux[simp]: "ctok (incr_aux d t) = ctok t"
  by (induction d t rule: incr_aux.induct) auto

lemma ctok_incr[simp]: "ctok (incr t) = ctok t"
  by (simp add: incr_def)

lemma ctok_app[simp]: "ctok (app s is) = ctok s"
  by (simp add: app_list_comb)

lemma ctok_mkabs: "ok (mkabs binders is t) t' \<Longrightarrow> ctok t' = ctok t"
  by (induction "is" arbitrary: t') (auto split: prod.splits)

lemma ctok_mk_hnf: "ok (mk_hnf binders is (Var G T) js) t \<Longrightarrow> ctok t"
  by (auto simp: mk_hnf_def dest: ctok_mkabs)


subsection \<open>Environments\<close>

lemma ctok_envD: "ctok_env env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ctok u"
  unfolding ctok_env_def by blast

lemma ctok_env_lookup: "ok (lookup env xi T) (Some u) \<Longrightarrow> ctok_env env \<Longrightarrow> ctok u"
  using ok_lookup_some[of env xi T "Some u"] by (auto intro: ctok_envD)

lemma ctok_env_update: "ok (update (F, T) t env) env' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok t \<Longrightarrow> ctok_env env'"
  using ok_update[of F T t env env'] by (auto simp: ctok_env_def)

lemma genvar_eq: "genvar a env T = (Envir (maxidx env + 1) (tenv env) (tyenv env), Var (a, maxidx env + 1) T)"
  by (cases env) (simp add: genvar_def)

lemma ctok_env_genvar: "genvar a env T = (env', G) \<Longrightarrow> ctok_env env' = ctok_env env \<and> ctok G"
  by (auto simp: genvar_eq ctok_env_def)

lemma not_ok_exn_case: "\<not> ok (case e of TUnify \<Rightarrow> raise x | _ \<Rightarrow> raise e) y"
  by (cases e) simp_all

lemma not_ok_exn_case2: "\<not> ok (case e of Unif x \<Rightarrow> raise y | _ \<Rightarrow> raise e) z"
  by (cases e) simp_all

lemma ctok_env_unify_types: "ok (unify_types alg T U env) env' \<Longrightarrow> tenv env' = tenv env"
  by (auto simp: unify_types_def ok_handle not_ok_exn_case split: prod.splits if_splits)

lemma ctok_env_mk_new_hnf: "ok (mk_new_hnf env binders is F T js) env' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok_env env'"
proof -
  assume m: "ok (mk_new_hnf env binders is F T js) env'" and c: "ctok_env env"
  from m obtain Gty t where t: "ok (mk_hnf binders is (Var (fst F, maxidx env + 1) Gty) js) t"
    and u: "ok (update (F, T) t (Envir (maxidx env + 1) (tenv env) (tyenv env))) env'"
    by (auto simp: mk_new_hnf_def Let_def genvar_eq)
  have "ctok_env (Envir (maxidx env + 1) (tenv env) (tyenv env))" using c by (simp add: ctok_env_def)
  from ctok_env_update[OF u this ctok_mk_hnf[OF t]] show ?thesis .
qed

lemma ctok_env_flexflex1: "ok (flexflex1 env binders F T is js) env' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok_env env'"
  by (auto simp: flexflex1_def split: if_splits intro: ctok_env_mk_new_hnf)

lemma ctok_env_ff: "ok (ff env binders F Fty is G Gty js) env' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok_env env'"
proof -
  assume f: "ok (ff env binders F Fty is G Gty js) env'" and c: "ctok_env env"
  show "ctok_env env'"
  proof (cases "subset js is")
    case True
    with f obtain ks t where "ok (mkabs binders is (app (Var G Gty) ks)) t" "ok (update (F, Fty) t env) env'"
      by (auto simp: ff_def)
    then show ?thesis using c by (auto intro: ctok_env_update dest: ctok_mkabs)
  next
    case False
    let ?env1 = "Envir (maxidx env + 1) (tenv env) (tyenv env)"
    from f False obtain Hty tG tF env2 ks1 ks2 where
      tG: "ok (mkabs binders js (app (Var (fst G, maxidx env + 1) Hty) ks1)) tG"
      and tF: "ok (mkabs binders is (app (Var (fst G, maxidx env + 1) Hty) ks2)) tF"
      and u1: "ok (update (F, Fty) tF ?env1) env2" and u2: "ok (update (G, Gty) tG env2) env'"
      by (auto simp: ff_def Let_def genvar_eq)
    have c1: "ctok_env ?env1" using c by (simp add: ctok_env_def)
    have H: "ctok (Var (fst G, maxidx env + 1) Hty)" by simp
    have "ctok tF" using tF H by (auto dest: ctok_mkabs)
    moreover have "ctok tG" using tG H by (auto dest: ctok_mkabs)
    ultimately show ?thesis using ctok_env_update[OF u2 ctok_env_update[OF u1 c1]] by simp
  qed
qed

lemma ctok_env_flexflex2: "ok (flexflex2 env binders F Fty is G Gty js) env' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok_env env'"
  by (auto simp: flexflex2_def split: if_splits intro: ctok_env_ff)


subsection \<open>Head normalisation and projection\<close>

lemma head_norm_ctok:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok t \<Longrightarrow> ctok t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have c: "ctok_env env" and t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest "1.prems" show ?thesis by auto
    next
      case (Some u)
      with lk c have u: "ctok u" by (auto intro: ctok_env_lookup)
      from Some rest have "hn env u = Some (Ok t')" by simp
      from "1.IH"[OF this refl c u] show ?thesis .
    qed
  next
    case (Abs a T body)
    with t' obtain b' where "hn env body = Some (Ok b')" "t' = pterm.Abs a T b'" by auto
    with "1.IH"[OF this(1) refl c] "1.prems" Abs show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      with t' App have "hn env (subst_bound u body) = Some (Ok t')" by simp
      from "1.IH"[OF this refl c] "1.prems" App f show ?thesis by (auto intro: ctok_subst_bound)
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from "1.IH"[OF nf refl c] "1.prems" App have cnf: "ctok nf" by auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have "hn env (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl c] "1.prems" App cnf nfa show ?thesis by (auto intro: ctok_subst_bound)
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with cnf "1.prems" App show ?thesis by simp
      qed
    qed
  qed (use t' "1.prems" in auto)
qed

lemma head_norm_ctok': "ok (head_norm env t) t' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok t \<Longrightarrow> ctok t'"
  using head_norm_ctok by blast

lemma pr_ctok:
  assumes "pr xs s env d binders = Some r"
  shows "r = Ok (s', env') \<Longrightarrow> ctok_env env \<Longrightarrow> ctok s \<Longrightarrow> ctok s' \<and> ctok_env env'"
  using assms
proof (induction xs s env d binders r arbitrary: s' env' rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d binders r)
  have c: "ctok_env env" and cs: "ctok s" using "1.prems" by simp_all
  from "1.hyps" "1.prems"(1) have "ok (head_norm env s \<bind> (\<lambda>s0.
      if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty \<Rightarrow> do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}
            | _ \<Rightarrow> raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')}))) (s', env')"
    by (simp only:)
  then obtain s0 where hn: "ok (head_norm env s) s0" and rest: "ok (
      if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty \<Rightarrow> do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}
            | _ \<Rightarrow> raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')})) (s', env')"
    unfolding ok_bindM by blast
  have c0: "ctok s0" by (rule head_norm_ctok'[OF hn c cs])
  show ?case
  proof (cases "is_Abs s0")
    case True
    then obtain a T t where s0a: "s0 = pterm.Abs a T t" by (cases s0) auto
    with rest True obtain t' where t': "ok (prr xs t env (d + 1) ((a, T) # binders)) (t', env')"
      and s': "s' = pterm.Abs a T t'"
      by (auto split: prod.splits)
    from "1.IH"[OF t' refl c] c0 s0a s' show ?thesis by simp
  next
    case nA: False
    obtain h ts where sc: "strip_comb s0 = (h, ts)" by force
    have ch: "ctok h" and cts: "\<forall>u\<in>set ts. ctok u" using ctok_strip_comb[OF sc] c0 by simp_all
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain F Fty where h: "h = pterm.Var F Fty" by (cases h) auto
      let ?env1 = "Envir (maxidx env + 1) (tenv env) (tyenv env)"
      from rest nA sc h obtain js js' Hty t where
        t: "ok (mk_hnf binders js (Var (fst F, maxidx env + 1) Hty) (mk_proj_list js')) t"
        and u: "ok (update (F, Fty) t ?env1) env'"
        and s': "s' = app (Var (fst F, maxidx env + 1) Hty) (List.map_filter id js')"
        by (auto simp: Let_def genvar_eq)
      have c1: "ctok_env ?env1" using c by (simp add: ctok_env_def)
      have cH: "ctok (Var (fst F, maxidx env + 1) Hty)" by simp
      from t have "ctok t" by (rule ctok_mk_hnf)
      from ctok_env_update[OF u c1 this] s' cH show ?thesis by simp
    next
      case nV: False
      show ?thesis
      proof (cases "is_Abs h")
        case True
        with rest nA sc nV show ?thesis by simp
      next
        case nAh: False
        from rest nA sc nV nAh obtain h' ts' where
          h': "ok (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h) h'"
          and m: "ok (mapAccM (\<lambda>s env. prr xs s env d binders) ts env) (ts', env')"
          and s': "s' = list_comb h' ts'"
          by (auto split: prod.splits)
        have ch': "ctok h'" using h' ch by (cases h) auto
        have "ctok_env env' \<and> (\<lambda>e e'. True) env' env \<and> list_all2 (\<lambda>x y. (\<lambda>x y e. ctok x \<longrightarrow> ctok y) x y env') ts ts'"
        proof (rule mapAccM_ok[OF m, where P = ctok_env and R = "\<lambda>e e'. True"])
          fix x e y e1
          assume x: "x \<in> set ts" and e1: "ok (prr xs x e d binders) (y, e1)" and e: "ctok_env e"
          from "1.IH"[OF e1 refl e] cts x show "ctok_env e1 \<and> True \<and> (ctok x \<longrightarrow> ctok y)" by simp
        qed (use c in simp_all)
        then have "ctok_env env'" "list_all2 (\<lambda>x y. ctok x \<longrightarrow> ctok y) ts ts'" by simp_all
        moreover from this(2) cts have "\<forall>u\<in>set ts'. ctok u"
          by (induction rule: list_all2_induct) auto
        ultimately show ?thesis using s' ch' by simp
      qed
    qed
  qed
qed

lemma proj_ctok: "ok (proj s env binders is) (s', env') \<Longrightarrow> ctok_env env \<Longrightarrow> ctok s \<Longrightarrow> ctok s' \<and> ctok_env env'"
  by (auto simp: proj_def split: if_splits dest: pr_ctok)

lemma flexrigid_ctok:
  "ok (flexrigid env binders F Fty is t) env' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok t \<Longrightarrow> ctok_env env'"
proof -
  assume f: "ok (flexrigid env binders F Fty is t) env'" and c: "ctok_env env" and ct: "ctok t"
  from f obtain u env1 u' where p: "ok (proj t env binders is) (u, env1)" and m: "ok (mkabs binders is u) u'"
    and up: "ok (update (F, Fty) u' env1) env'"
    by (auto simp: flexrigid_def ok_handle not_ok_exn_case2 split: if_splits prod.splits)
  from proj_ctok[OF p c ct] have "ctok u" "ctok_env env1" by simp_all
  with ctok_mkabs[OF m] show ?thesis by (auto intro: ctok_env_update[OF up])
qed


subsection \<open>Unification\<close>

theorem unif_ctok:
  assumes "unif alg binders s t env = Some r"
  shows "r = Ok env' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok s \<Longrightarrow> ctok t \<Longrightarrow> ctok_env env'"
  using assms
proof (induction alg binders s t env r arbitrary: env' rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg binders s t env r)
  have c: "ctok_env env" and cs: "ctok s" and ct: "ctok t" using "1.prems" by simp_all
  from "1.hyps" "1.prems"(1) have "ok (do {
      s' \<leftarrow> head_norm env s;
      t' \<leftarrow> head_norm env t;
      if is_Abs s' \<and> is_Abs t' then
        (case (s', t') of
          (pterm.Abs ns Ts ts, pterm.Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            uni alg ((name, Ts) # binders) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s' then
        (case s' of
          pterm.Abs ns Ts ts \<Rightarrow> uni alg ((ns, Ts) # binders) ts (incr t' $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t' then
        (case t' of
          pterm.Abs nt Tt tt \<Rightarrow> uni alg ((nt, Tt) # binders) (incr s' $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s'; (ht, ts) = strip_comb t' in
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
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env binders F Fty is t'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env binders F Fty is s'}
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
            | _ \<Rightarrow> rigid_clash binders hs ht))
    }) env'"
    by (simp only:)
  then obtain s0 t0 where hs: "ok (head_norm env s) s0" and ht: "ok (head_norm env t) t0"
    and rest: "ok (
      if is_Abs s0 \<and> is_Abs t0 then
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
            | _ \<Rightarrow> rigid_clash binders hs ht))) env'"
    unfolding ok_bindM by blast
  have cs0: "ctok s0" by (rule head_norm_ctok'[OF hs c cs])
  have ct0: "ctok t0" by (rule head_norm_ctok'[OF ht c ct])
  text \<open>The arguments of rigid heads.\<close>
  have fo: "ctok_env env2"
    if f: "ok (foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env1) env2" and c1: "ctok_env env1"
      and p: "\<forall>(a, b)\<in>set ps. ctok a \<and> ctok b" for ps env1 env2
  proof -
    have "ctok_env env2 \<and> True \<and> (\<forall>x\<in>set ps. True)"
    proof (rule foldM_ok[OF f, where P = ctok_env and R = "\<lambda>_ _. True" and Q = "\<lambda>_ _. True"])
      fix x e e1 assume x: "x \<in> set ps" and e1: "ok ((\<lambda>(s, t) env. uni alg binders s t env) x e) e1"
        and e: "ctok_env e"
      obtain a b where xab: "x = (a, b)" by force
      from "1.IH"[of alg binders a b e _ e1] e1 xab e p x show "ctok_env e1 \<and> True \<and> True" by auto
    qed (use c1 in simp_all)
    then show ?thesis by simp
  qed
  show ?case
  proof (cases "is_Abs s0")
    case sA: True
    then obtain ns Ts ts where s0a: "s0 = pterm.Abs ns Ts ts" by (cases s0) auto
    show ?thesis
    proof (cases "is_Abs t0")
      case True
      then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
      from rest s0a t0a obtain env1 where u1: "ok (unify_types alg Ts Tt env) env1"
        and u: "ok (uni alg ((if ns = STR '''' then nt else ns, Ts) # binders) ts tt env1) env'"
        by (auto simp: Let_def)
      have c1: "ctok_env env1" using c ctok_env_unify_types[OF u1] by (simp add: ctok_env_def)
      from "1.IH"[OF u refl c1] cs0 ct0 s0a t0a show ?thesis by simp
    next
      case False
      from rest sA False s0a have u: "ok (uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env) env'"
        by simp
      from "1.IH"[OF u refl c] cs0 ct0 s0a show ?thesis by simp
    qed
  next
    case nsA: False
    show ?thesis
    proof (cases "is_Abs t0")
      case True
      then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
      from rest nsA True t0a have u: "ok (uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env) env'"
        by simp
      from "1.IH"[OF u refl c] cs0 ct0 t0a show ?thesis by simp
    next
      case nAt: False
      obtain hs ss where shs: "strip_comb s0 = (hs, ss)" by force
      obtain ht ts where sht: "strip_comb t0 = (ht, ts)" by force
      have chs: "ctok hs" "\<forall>u\<in>set ss. ctok u" using ctok_strip_comb[OF shs] cs0 by simp_all
      have cht: "ctok ht" "\<forall>u\<in>set ts. ctok u" using ctok_strip_comb[OF sht] ct0 by simp_all
      consider (VV) F Fty G Gty where "hs = pterm.Var F Fty" "ht = pterm.Var G Gty"
        | (VR) F Fty where "hs = pterm.Var F Fty" "\<not> is_Var ht"
        | (RV) G Gty where "\<not> is_Var hs" "ht = pterm.Var G Gty"
        | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
        by (cases hs; cases ht) auto
      then show ?thesis
      proof cases
        case VV
        from rest nsA nAt shs sht VV obtain "is" js where
          ff: "ok (if F = G then flexflex1 env binders F Fty is js
            else flexflex2 env binders F Fty is G Gty js) env'"
          by auto
        then show ?thesis using c by (auto split: if_splits intro: ctok_env_flexflex1 ctok_env_flexflex2)
      next
        case VR
        from rest nsA nAt shs sht VR obtain "is" where fr: "ok (flexrigid env binders F Fty is t0) env'"
          by auto
        from flexrigid_ctok[OF fr c ct0] show ?thesis .
      next
        case RV
        from rest nsA nAt shs sht RV obtain js where fr: "ok (flexrigid env binders G Gty js s0) env'"
          by auto
        from flexrigid_ctok[OF fr c cs0] show ?thesis .
      next
        case RR
        have nAbs: "\<not> is_Abs hs" "\<not> is_Abs ht"
          using rest nsA nAt shs sht RR by (auto split: if_splits)
        from rest nsA nAt shs sht RR nAbs
        have rest': "ok (case (hs, ht) of
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
            | _ \<Rightarrow> rigid_clash binders hs ht) env'"
          by simp
        obtain env1 ps where u1: "tenv env1 = tenv env" and ps: "ok (zip_eq ss ts) ps"
          and f: "ok (foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env1) env'"
          using rest'
          by (cases hs; cases ht)
            (auto simp: not_ok_rigid_clash split: if_splits dest: ctok_env_unify_types)
        have c1: "ctok_env env1" using c u1 by (simp add: ctok_env_def)
        from ps have "ps = zip ss ts" by (simp add: ok_zip_eq)
        then have "\<forall>(a, b)\<in>set ps. ctok a \<and> ctok b"
          using chs(2) cht(2) by (auto dest: set_zip_leftD set_zip_rightD)
        from fo[OF f c1 this] show ?thesis .
      qed
    qed
  qed
qed

theorem unify_ctok: "ok (unify alg s t env) env' \<Longrightarrow> ctok_env env \<Longrightarrow> ctok s \<Longrightarrow> ctok t \<Longrightarrow> ctok_env env'"
  unfolding unify_def using unif_ctok by blast

end

end
