section \<open>Correctness of Polymorphic Unification\<close>

theory Poly_Unif_Correct
  imports Poly_Unif
begin

context csig
begin

subsection \<open>One step of unification\<close>

text \<open>The body of \<^const>\<open>unif\<close> after head normalisation, parametric in the recursive call.\<close>

definition ustep :: "(algebra \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> env M) \<Rightarrow> algebra \<Rightarrow> binders \<Rightarrow>
    pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> env M" where
  "ustep uni alg binders s' t' env =
      (if is_Abs s' \<and> is_Abs t' then
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
            | _ \<Rightarrow> rigid_clash binders hs ht)))"

lemma unif_ustep: "unif alg bs s t env = head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. ustep unif alg bs s' t' env))"
  unfolding ustep_def by (rule unif.simps)

text \<open>The flexible cases.\<close>

definition flexstep :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env M" where
  "flexstep env binders s' t' =
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
      else
        (case ht of
          pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env binders F Fty is s'}
        | _ \<Rightarrow> raise (Failure (STR ''unif''))))"

lemma ustep_flexstep:
  assumes "\<not> is_Abs s'" "\<not> is_Abs t'" "is_Var (fst (strip_comb s')) \<or> is_Var (fst (strip_comb t'))"
  shows "ustep uni alg bs s' t' env = flexstep env bs s' t'"
  using assms by (auto simp: ustep_def flexstep_def split: prod.splits)

lemma flexstep_relJ:
  assumes h: "hyp \<rho> env (vps s0 \<union> vps t0)"
  shows "relJ \<rho> (tfree_on \<rho> (tyenv env)) (instE \<rho>) (flexstep env bs s0 t0)
    (flexstep (instE \<rho> env) (instb \<rho> bs) (inst \<rho> s0) (inst \<rho> t0))"
proof -
  obtain hs ss where shs: "strip_comb s0 = (hs, ss)" by force
  obtain ht ts where sht: "strip_comb t0 = (ht, ts)" by force
  have shs': "strip_comb (inst \<rho> s0) = (inst \<rho> hs, map (inst \<rho>) ss)" using strip_comb_inst[of \<rho> s0] shs by simp
  have sht': "strip_comb (inst \<rho> t0) = (inst \<rho> ht, map (inst \<rho>) ts)" using strip_comb_inst[of \<rho> t0] sht by simp
  note vs = vps_strip_comb[OF shs] and vt = vps_strip_comb[OF sht]
  note ok = hypD(1)[OF h] and sol = hypD(2)[OF h] and d = hyp_lkdec[OF h]
  have io: "ints_of' (instE \<rho> env) (map (inst \<rho>) us) = instM \<rho> id (ints_of' env us)"
    if "set us \<subseteq> set ss \<union> set ts" for us
  proof (rule ints_of'_inst[OF ok], intro ballI)
    fix u assume "u \<in> set us"
    with that have "vps u \<union> bvps env \<subseteq> vps s0 \<union> vps t0 \<union> bvps env" using vs vt by auto
    then show "lkdec \<rho> env (vps u \<union> bvps env)" by (rule lkdec_mono[OF d])
  qed
  have tc: "tcons (tyenv env) T" if "(x, T) \<in> vps s0 \<union> vps t0" for x T
    using d that unfolding lkdec_def by blast
  consider (VV) F Fty G Gty where "hs = Var F Fty" "ht = Var G Gty"
    | (VR) F Fty where "hs = Var F Fty" "\<not> is_Var ht"
    | (RV) G Gty where "\<not> is_Var hs" "ht = Var G Gty"
    | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
    by (cases hs; cases ht) auto
  then show ?thesis
  proof cases
    case VV
    have tF: "tcons (tyenv env) Fty" by (rule tc[of F]) (use vs VV in auto)
    have tG: "tcons (tyenv env) Gty" by (rule tc[of G]) (use vt VV in auto)
    show ?thesis
      unfolding flexstep_def shs sht shs' sht' Let_def VV
      apply simp
      apply (rule relJ_bindM[OF relJ_eq[OF io]], simp, unfold id_apply)
      apply (rule relJ_bindM[OF relJ_eq[OF io]], simp, unfold id_apply)
      using flexflex1_relJ[OF ok tF sol] flexflex2_relJ[OF ok tF tG sol] by simp
  next
    case VR
    have "hyp \<rho> env (vps t0 \<union> {})" by (rule hyp_mono[OF h]) auto
    note fr = flexrigid_relJ[OF this]
    have "\<not> is_Var (inst \<rho> ht)" using VR by simp
    then show ?thesis
      unfolding flexstep_def shs sht shs' sht' Let_def VR
      apply simp
      apply (rule relJ_bindM[OF relJ_eq[OF io]], simp, unfold id_apply)
      by (rule fr)
  next
    case RV
    have "hyp \<rho> env (vps s0 \<union> {})" by (rule hyp_mono[OF h]) auto
    note fr = flexrigid_relJ[OF this]
    have "\<not> is_Var (inst \<rho> hs)" using RV by simp
    then show ?thesis
      unfolding flexstep_def shs sht shs' sht' Let_def RV
      apply simp
      apply (rule relJ_bindM[OF relJ_eq[OF io]], simp, unfold id_apply)
      by (rule fr)
  next
    case RR
    then show ?thesis unfolding flexstep_def shs sht shs' sht' Let_def
      by (cases hs; cases ht) (auto intro: relJ_eq)
  qed
qed


subsection \<open>The steps extend the environment\<close>

definition ext :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "ext e' e \<longleftrightarrow> extends e' e \<and> maxidx e \<le> maxidx e' \<and> tyenv e' = tyenv e"

lemma ext_refl[simp]: "ext e e"
  by (simp add: ext_def)

lemma ext_trans: "ext e2 e1 \<Longrightarrow> ext e1 e \<Longrightarrow> ext e2 e"
  unfolding ext_def using extends_trans by auto

lemma update_ext: "update (F, T) t e = Some (Ok e') \<Longrightarrow> ext e' e"
  unfolding ext_def using ok_update_extends[of F T t e e'] ok_update(3,4)[of F T t e e'] by simp

lemma genvar_ext: "genvar a e T = (e', G) \<Longrightarrow> ext e' e"
  unfolding ext_def using genvar_extends[of a e T e' G] genvar_simps(2,3)[of a e T e' G] by simp

lemma prvar_ext: "prvar xs d bs env F Fty ts = Some (Ok (t', e')) \<Longrightarrow> ext e' env"
  unfolding prvar_def Let_def
  by (auto simp: bindM_def return_def split: option.splits res.splits prod.splits
      intro: ext_trans[OF update_ext genvar_ext])

lemma mapAccM_ext:
  assumes "mapAccM g ts env = Some (Ok (ts', e'))"
    and "\<And>s env t' e'. s \<in> set ts \<Longrightarrow> g s env = Some (Ok (t', e')) \<Longrightarrow> ext e' env"
  shows "ext e' env"
  using assms
proof (induction ts arbitrary: env ts')
  case (Cons s ts)
  from Cons.prems(1) obtain t1 e1 ys where g: "g s env = Some (Ok (t1, e1))"
    and m: "mapAccM g ts e1 = Some (Ok (ys, e'))"
    by (auto simp: bindM_def return_def split: option.splits res.splits prod.splits)
  have "ext e1 env" by (rule Cons.prems(2)[OF _ g]) simp
  moreover have "ext e' e1" by (rule Cons.IH[OF m]) (rule Cons.prems(2), simp_all)
  ultimately show ?case by (rule ext_trans[rotated])
qed (simp add: return_def)

lemma pr_ext:
  assumes "pr xs s env d bs = Some r"
  shows "r = Ok (t', e') \<Longrightarrow> ext e' env"
  using assms
proof (induction xs s env d bs r arbitrary: t' e' rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d bs r)
  have "head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs) = Some r"
    unfolding pr_step_def prvar_def by (rule "1.hyps")
  with "1.prems" obtain s0 where st: "pr_step prr xs s0 env d bs = Some (Ok (t', e'))"
    by (cases "head_norm env s") (auto simp: bindM_def split: res.splits)
  show ?case
  proof (cases "is_Abs s0")
    case True
    then obtain a T u where s0: "s0 = Abs a T u" by (cases s0) auto
    from st s0 obtain u' where "prr xs u env (d + 1) ((a, T) # bs) = Some (Ok (u', e'))"
      by (auto simp: pr_step_def bindM_def return_def split: option.splits res.splits prod.splits)
    from "1.IH"[OF this refl] show ?thesis .
  next
    case False
    obtain hd ts where sc: "strip_comb s0 = (hd, ts)" by force
    show ?thesis
    proof (cases "is_Var hd")
      case True
      then obtain F Fty where hd: "hd = Var F Fty" by (cases hd) auto
      from st False sc hd have "prvar xs d bs env F Fty ts = Some (Ok (t', e'))"
        by (simp add: pr_step_def)
      then show ?thesis by (rule prvar_ext)
    next
      case nV: False
      show ?thesis
      proof (cases "is_Abs hd")
        case True
        with st False sc nV show ?thesis by (simp add: pr_step_def raise_def)
      next
        case nA: False
        define hm where "hm = (\<lambda>h. case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h)"
        have "pr_step prr xs s0 env d bs = hm hd \<bind>
            (\<lambda>h'. mapAccM (\<lambda>s env. prr xs s env d bs) ts env \<bind> (\<lambda>(ts', env'). return (list_comb h' ts', env')))"
          using False sc nV nA by (simp add: pr_step_def hm_def)
        with st obtain ts' where m: "mapAccM (\<lambda>s env. prr xs s env d bs) ts env = Some (Ok (ts', e'))"
          by (auto simp: bindM_def return_def split: option.splits res.splits prod.splits)
        show ?thesis by (rule mapAccM_ext[OF m]) (rule "1.IH"[OF _ refl])
      qed
    qed
  qed
qed

lemma proj_ext: "proj s env bs is = Some (Ok (t', e')) \<Longrightarrow> ext e' env"
  unfolding proj_def using pr_ext[of "is" s env 0 bs _ t' e'] by (auto simp: return_def split: if_splits)

lemma flexrigid_ext: "flexrigid env bs F Fty is t = Some (Ok e') \<Longrightarrow> ext e' env"
  unfolding flexrigid_def
  by (auto simp: bindM_def return_def raise_def handle_def
      split: option.splits res.splits prod.splits if_splits exn.splits
      intro: ext_trans[OF update_ext proj_ext])

lemma mk_new_hnf_ext: "mk_new_hnf env bs is F Fty js = Some (Ok e') \<Longrightarrow> ext e' env"
  unfolding mk_new_hnf_def Let_def
  by (auto simp: bindM_def split: option.splits res.splits prod.splits
      intro: ext_trans[OF update_ext genvar_ext])

lemma flexflex1_ext: "flexflex1 env bs F Fty is js = Some (Ok e') \<Longrightarrow> ext e' env"
  unfolding flexflex1_def using mk_new_hnf_ext
  by (auto simp: return_def bindM_def split: if_splits option.splits res.splits)

lemma ff_ext: "ff env bs F Fty is G Gty js = Some (Ok e') \<Longrightarrow> ext e' env"
  unfolding ff_def Let_def
  by (auto simp: bindM_def split: option.splits res.splits prod.splits if_splits
      intro: ext_trans[OF update_ext] ext_trans[OF update_ext genvar_ext])

lemma flexflex2_ext: "flexflex2 env bs F Fty is G Gty js = Some (Ok e') \<Longrightarrow> ext e' env"
  unfolding flexflex2_def using ff_ext by (simp split: if_splits)

lemma flexstep_ext: "flexstep env bs s t = Some (Ok e') \<Longrightarrow> ext e' env"
  unfolding flexstep_def Let_def
  by (simp add: bindM_def raise_def split: option.splits res.splits prod.splits if_splits pterm.splits;
      blast intro: flexflex1_ext flexflex2_ext flexrigid_ext)

lemma flexstep_tys:
  assumes fs: "flexstep env bs s t = Some (Ok e')" and P: "\<forall>T\<in>tys s \<union> tys t \<union> etys env \<union> snd ` set bs. P T"
    and cl: "tyclosed P (tyenv env)"
  shows "\<forall>T\<in>etys e'. P T"
proof -
  obtain hs ss where shs: "strip_comb s = (hs, ss)" by force
  obtain ht ts where sht: "strip_comb t = (ht, ts)" by force
  note ts = tys_strip_comb[OF shs] tys_strip_comb[OF sht]
  have Pe: "\<forall>T\<in>etys env \<union> snd ` set bs. P T" using P by blast
  consider (VV) F Fty G Gty where "hs = Var F Fty" "ht = Var G Gty"
    | (VR) F Fty where "hs = Var F Fty" "\<not> is_Var ht"
    | (RV) G Gty where "\<not> is_Var hs" "ht = Var G Gty"
    | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
    by (cases hs; cases ht) auto
  then show ?thesis
  proof cases
    case VV
    have PF: "P Fty" and PG: "P Gty" using P ts VV by auto
    from fs VV shs sht obtain "is" js where
      "(F = G \<and> flexflex1 env bs F Fty is js = Some (Ok e')) \<or>
       (F \<noteq> G \<and> flexflex2 env bs F Fty is G Gty js = Some (Ok e'))"
      unfolding flexstep_def by (auto simp: bindM_def split: option.splits res.splits if_splits)
    then show ?thesis using flexflex1_tys[OF _ PF Pe cl] flexflex2_tys[OF _ PF PG Pe cl] by blast
  next
    case VR
    have PF: "P Fty" using P ts VR by auto
    from fs VR shs sht obtain "is" where "flexrigid env bs F Fty is t = Some (Ok e')"
      unfolding flexstep_def by (auto simp: bindM_def split: option.splits res.splits)
    from flexrigid_tys[OF this PF _ cl] P show ?thesis by blast
  next
    case RV
    have PG: "P Gty" using P ts RV by auto
    from fs RV shs sht obtain "is" where "flexrigid env bs G Gty is s = Some (Ok e')"
      unfolding flexstep_def by (cases hs) (auto simp: bindM_def split: option.splits res.splits)
    from flexrigid_tys[OF this PG _ cl] P show ?thesis by blast
  next
    case RR
    with fs shs sht show ?thesis unfolding flexstep_def by (cases hs; cases ht) (simp_all add: raise_def)
  qed
qed


subsection \<open>The result of polymorphic unification\<close>

text \<open>
  The properties of a result \<open>r\<close> of the polymorphic problem \<open>s =?= t\<close> under binders \<open>bs\<close>
  established by induction: only the exceptions \<open>Unif\<close> and \<open>Pattern\<close> are raised, \<open>Pattern\<close>
  only on non-patterns, and \<open>Unif\<close> only if no ground instance of the problem is unifiable.
\<close>

definition post :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow>
    env \<Rightarrow> env res \<Rightarrow> bool" where
  "post alg ar A bs s t env r \<longleftrightarrow> fails_ok (Some r) \<and>
    (ppat s \<and> ppat t \<and> env_ppat env \<longrightarrow> r \<noteq> Err Pattern) \<and>
    (\<forall>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<longrightarrow> inst_ok ar W \<rho> bs s t env \<longrightarrow> solution W \<tau>' \<sigma> (instE \<rho> env) \<longrightarrow>
      unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t)) \<longrightarrow> no_unif (Some r))"

text \<open>
  A returned environment \<open>env'\<close> extends \<open>env\<close>, satisfies the invariants again, its ground instances
  unify the instances of \<open>s\<close> and \<open>t\<close>, and every unifier of a ground instance of the problem extends
  to a solution of a ground instance of \<open>env'\<close>.
\<close>

definition postok :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow>
    env \<Rightarrow> env \<Rightarrow> bool" where
  "postok alg ar A bs s t env env' \<longleftrightarrow>
    textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
    tinv ar (maxidx env') (tyenv env') A \<and> tsorted alg (tyenv env') \<and>
    (tcert alg (tvars_env (tyenv env) \<union> A) \<longrightarrow> tcert alg (tvars_env (tyenv env'))) \<and>
    (\<forall>T\<in>etys env'. tyw ar (tyenv env') A T) \<and>
    (ppat s \<and> ppat t \<and> env_ppat env \<longrightarrow> env_ppat env') \<and>
    (\<forall>\<rho>. gsol alg ar (tyenv env') \<rho> \<longrightarrow> instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t) \<and>
    (\<forall>\<rho> W. gsol alg ar (tyenv env') \<rho> \<longrightarrow> inst_ok ar W \<rho> bs s t env \<longrightarrow>
      (\<exists>W'. ty_ext ar W (instE \<rho> env) W' (instE \<rho> env'))) \<and>
    (\<forall>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<longrightarrow> inst_ok ar W \<rho> bs s t env \<longrightarrow> solution W \<tau>' \<sigma> (instE \<rho> env) \<longrightarrow>
      unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t)) \<longrightarrow>
      (\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
        sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' env')))"

definition post_all :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow>
    env \<Rightarrow> env res \<Rightarrow> bool" where
  "post_all alg ar A bs s t env r \<longleftrightarrow> post alg ar A bs s t env r \<and>
    (\<forall>env'. r = Ok env' \<longrightarrow> postok alg ar A bs s t env env')"

lemma inst_okD:
  assumes "inst_ok ar W \<rho> bs s t env"
  shows "wf_env ar (instE \<rho> env)" "env_typed W (instE \<rho> env)" "fresh_env (instE \<rho> env)"
    "binders_ok ar (instb \<rho> bs)" "wf_term ar (length (instb \<rho> bs)) (inst \<rho> s)"
    "wf_term ar (length (instb \<rho> bs)) (inst \<rho> t)"
    "\<exists>U. has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U \<and> has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U"
  using assms by (simp_all add: inst_ok_def)

text \<open>
  The same notions for lists of equations, as they arise from the arguments of rigid terms.
\<close>

definition ptys :: "(pterm \<times> pterm) list \<Rightarrow> ptyp set" where
  "ptys ps = (\<Union>(s, t)\<in>set ps. tys s \<union> tys t)"

lemma ptys_simps[simp]: "ptys [] = {}" "ptys ((s, t) # ps) = tys s \<union> tys t \<union> ptys ps"
  by (auto simp: ptys_def)

definition inst_okl :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> tinst \<Rightarrow> binders \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow>
    env \<Rightarrow> bool" where
  "inst_okl ar W \<rho> bs ps env \<longleftrightarrow> wf_env ar (instE \<rho> env) \<and> env_typed W (instE \<rho> env) \<and>
    fresh_env (instE \<rho> env) \<and> binders_ok ar (instb \<rho> bs) \<and>
    (\<forall>(s, t)\<in>set ps. wf_term ar (length bs) (inst \<rho> s) \<and> wf_term ar (length bs) (inst \<rho> t) \<and>
      (\<exists>U. has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U \<and> has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U))"

definition prel :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> binders \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow>
    env \<Rightarrow> bool" where
  "prel alg ar A bs ps env \<longleftrightarrow> tinv ar (maxidx env) (tyenv env) A \<and> tsorted alg (tyenv env) \<and>
    (\<forall>T\<in>snd ` set bs \<union> ptys ps \<union> etys env. tyw ar (tyenv env) A T) \<and>
    (\<forall>(s, t)\<in>set ps. below (maxidx env) s \<and> below (maxidx env) t) \<and>
    (\<forall>\<rho>. gsol alg ar (tyenv env) \<rho> \<longrightarrow> (\<exists>W. inst_okl ar W \<rho> bs ps env))"

definition postl :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> binders \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow>
    env \<Rightarrow> env res \<Rightarrow> bool" where
  "postl alg ar A bs ps env r \<longleftrightarrow> fails_ok (Some r) \<and>
    ((\<forall>(s, t)\<in>set ps. ppat s \<and> ppat t) \<and> env_ppat env \<longrightarrow> r \<noteq> Err Pattern) \<and>
    (\<forall>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<longrightarrow> inst_okl ar W \<rho> bs ps env \<longrightarrow> solution W \<tau>' \<sigma> (instE \<rho> env) \<longrightarrow>
      (\<forall>(s, t)\<in>set ps. unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))) \<longrightarrow> no_unif (Some r))"

definition postokl :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> binders \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow>
    env \<Rightarrow> env \<Rightarrow> bool" where
  "postokl alg ar A bs ps env env' \<longleftrightarrow>
    textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and> extends env' env \<and>
    tinv ar (maxidx env') (tyenv env') A \<and> tsorted alg (tyenv env') \<and>
    (tcert alg (tvars_env (tyenv env) \<union> A) \<longrightarrow> tcert alg (tvars_env (tyenv env'))) \<and>
    (\<forall>T\<in>etys env'. tyw ar (tyenv env') A T) \<and>
    ((\<forall>(s, t)\<in>set ps. ppat s \<and> ppat t) \<and> env_ppat env \<longrightarrow> env_ppat env') \<and>
    (\<forall>\<rho>. gsol alg ar (tyenv env') \<rho> \<longrightarrow> (\<forall>(s, t)\<in>set ps. instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t)) \<and>
    (\<forall>\<rho> W. gsol alg ar (tyenv env') \<rho> \<longrightarrow> inst_okl ar W \<rho> bs ps env \<longrightarrow>
      (\<exists>W'. ty_ext ar W (instE \<rho> env) W' (instE \<rho> env'))) \<and>
    (\<forall>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<longrightarrow> inst_okl ar W \<rho> bs ps env \<longrightarrow> solution W \<tau>' \<sigma> (instE \<rho> env) \<longrightarrow>
      (\<forall>(s, t)\<in>set ps. unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))) \<longrightarrow>
      (\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
        sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' env')))"

definition post_alll :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> binders \<Rightarrow>
    (pterm \<times> pterm) list \<Rightarrow> env \<Rightarrow> env res \<Rightarrow> bool" where
  "post_alll alg ar A bs ps env r \<longleftrightarrow> postl alg ar A bs ps env r \<and>
    (\<forall>env'. r = Ok env' \<longrightarrow> postokl alg ar A bs ps env env')"

lemma inst_okl_single[simp]: "inst_okl ar W \<rho> bs [(s, t)] env \<longleftrightarrow> inst_ok ar W \<rho> bs s t env"
  by (simp add: inst_okl_def inst_ok_def)

lemma prel_single: "prel alg ar A bs [(s, t)] env \<longleftrightarrow> pre alg ar A bs s t env"
  by (auto simp: prel_def pre_def)

lemma post_alll_single: "post_alll alg ar A bs [(s, t)] env r \<longleftrightarrow> post_all alg ar A bs s t env r"
  by (simp add: post_alll_def postl_def postokl_def post_all_def post_def postok_def)

text \<open>Instantiations agreeing on the types of a term or environment.\<close>

lemma vt_eqI: "(\<And>k. vt_lookup t k = vt_lookup t' k) \<Longrightarrow> t = t'"
  by transfer auto

lemma inst_tagree: "\<forall>T\<in>tys t. tsubst \<rho>' T = tsubst \<rho> T \<Longrightarrow> inst \<rho>' t = inst \<rho> t"
  by (induction t) auto

lemma instb_tagree: "\<forall>T\<in>snd ` set bs. tsubst \<rho>' T = tsubst \<rho> T \<Longrightarrow> instb \<rho>' bs = instb \<rho> bs"
  by (induction bs) auto

lemma instE_tagree: "\<forall>T\<in>etys env. tsubst \<rho>' T = tsubst \<rho> T \<Longrightarrow> instE \<rho>' env = instE \<rho> env"
proof -
  assume ag: "\<forall>T\<in>etys env. tsubst \<rho>' T = tsubst \<rho> T"
  have "vt_lookup (tenv (instE \<rho>' env)) x = vt_lookup (tenv (instE \<rho> env)) x" for x
  proof (cases "vt_lookup (tenv env) x")
    case (Some b)
    obtain U u where b: "b = (U, u)" by force
    from etysI[of env x U u] Some b ag show ?thesis by (auto intro!: inst_tagree)
  qed simp
  then show ?thesis by (simp add: instE_def vt_eqI)
qed

lemma tyw_tagree: "tinv ar n \<theta> A \<Longrightarrow> tyw ar \<theta> A T \<Longrightarrow> tagree n \<rho> \<rho>' \<Longrightarrow> tsubst \<rho>' T = tsubst \<rho> T"
  by (rule tagree_tsubst) (auto simp: tyw_def tinv_def)

text \<open>Instances of environments with the same bindings and a larger counter.\<close>

lemma instE_same_tenv: "tenv env1 = tenv env \<Longrightarrow> tenv (instE \<rho> env1) = tenv (instE \<rho> env)"
  by (simp add: instE_def)

lemma fresh_env_same: "tenv e1 = tenv e \<Longrightarrow> maxidx e \<le> maxidx e1 \<Longrightarrow> fresh_env e \<Longrightarrow> fresh_env e1"
  unfolding fresh_env_def by (metis below_mono order_trans)

lemma sol_ext_same:
  assumes "tenv e1 = tenv e" "tyenv e1 = tyenv e" "maxidx e \<le> maxidx e1"
    and "solution V \<tau>' \<sigma> e" "env_typed V e" "fresh_env e" "wf_env ar e"
  shows "sol_ext ar V \<tau>' \<sigma> e V \<sigma> e1"
  using assms fresh_env_same[OF assms(1,3,6)]
  by (simp add: sol_ext_def solution_def sat_def env_typed_def wf_env_def)

lemma ty_ext_same:
  assumes "tenv e1 = tenv e" "tyenv e1 = tyenv e" "maxidx e \<le> maxidx e1"
    and "env_typed V e" "fresh_env e" "wf_env ar e"
  shows "ty_ext ar V e V e1"
  using assms fresh_env_same[OF assms(1,3,5)]
  by (simp add: ty_ext_def env_typed_def wf_env_def extends_def)

text \<open>Moving well-formed instances to agreeing instantiations and typings and to extended environments.\<close>

lemma inst_okl_transport:
  assumes i: "inst_okl ar W \<rho> bs ps env"
    and ag: "\<forall>T\<in>snd ` set bs \<union> ptys ps. tsubst \<rho>' T = tsubst \<rho> T"
    and bl: "\<forall>(s, t)\<in>set ps. below (maxidx env) s \<and> below (maxidx env) t"
    and aV: "agreeV (maxidx env) W W'"
    and e: "wf_env ar (instE \<rho>' e)" "env_typed W' (instE \<rho>' e)" "fresh_env (instE \<rho>' e)"
  shows "inst_okl ar W' \<rho>' bs ps e"
proof -
  have b: "instb \<rho>' bs = instb \<rho> bs" using ag by (intro instb_tagree) blast
  have "inst \<rho>' s = inst \<rho> s \<and> inst \<rho>' t = inst \<rho> t \<and> below (maxidx env) s \<and> below (maxidx env) t"
    if "(s, t) \<in> set ps" for s t
    using that ag bl by (auto simp: ptys_def intro!: inst_tagree)
  then show ?thesis
    using i e b unfolding inst_okl_def by (fastforce intro: has_type_agreeV[OF _ _ aV])
qed

end

context wf_csig
begin

lemma faithful_tfree:
  assumes "tinv ar n \<theta> A" "tsorted alg \<theta>"
  obtains \<rho> where "gsol alg ar \<theta> \<rho>" "tfree_on \<rho> \<theta>"
  using faithful_exists[OF assms finite.emptyI finite.emptyI] by metis

text \<open>
  Results that are related to the results of the monomorphic algorithm on all ground instances
  (as the flexible cases are) satisfy the properties.
\<close>

lemma post_inst:
  assumes pre: "pre alg ar A bs s t env"
    and rel: "\<And>\<rho>. gsol alg ar (tyenv env) \<rho> \<Longrightarrow>
      relJ \<rho> (tfree_on \<rho> (tyenv env)) (instE \<rho>) (Some r) (unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env))"
    and okr: "\<And>env'. r = Ok env' \<Longrightarrow> ext env' env \<and> (\<forall>T\<in>etys env'. tyw ar (tyenv env) A T)"
  shows "post_all alg ar A bs s t env r"
proof -
  note inv = preD(1,2)[OF pre] and bl = preD(4,5)[OF pre]
  obtain \<rho>f where gf: "gsol alg ar (tyenv env) \<rho>f" and tf: "tfree_on \<rho>f (tyenv env)"
    by (rule faithful_tfree[OF inv])
  from preD(6)[OF pre gf] obtain Wf Uf where i_f: "inst_ok ar Wf \<rho>f bs s t env"
    and tyf: "has_type Wf (map snd (instb \<rho>f bs)) (inst \<rho>f s) Uf" "has_type Wf (map snd (instb \<rho>f bs)) (inst \<rho>f t) Uf"
    by (auto simp: inst_ok_def)
  have "relJ \<rho>f True (instE \<rho>f) (Some r) (unif alg (instb \<rho>f bs) (inst \<rho>f s) (inst \<rho>f t) (instE \<rho>f env))"
    using rel[OF gf] tf by simp
  from relJ_exact[OF this]
  have rf: "unif alg (instb \<rho>f bs) (inst \<rho>f s) (inst \<rho>f t) (instE \<rho>f env) = Some (instr \<rho>f (instE \<rho>f) r)"
    by (simp add: instM_def)
  have bi: "below (maxidx (instE \<rho> env)) (inst \<rho> s)" "below (maxidx (instE \<rho> env)) (inst \<rho> t)" for \<rho>
    using bl by simp_all
  note exf0 = unif_exn[OF rf inst_okD(1,4,2,3,5,6)[OF i_f] tyf bi]
  have exf: "fails_ok (Some (instr \<rho>f (instE \<rho>f) r))"
    "ppat s \<and> ppat t \<and> env_ppat env \<Longrightarrow> instr \<rho>f (instE \<rho>f) r \<noteq> Err Pattern"
    "\<And>env'. instr \<rho>f (instE \<rho>f) r = Ok env' \<Longrightarrow> ppat s \<and> ppat t \<and> env_ppat env \<Longrightarrow> env_ppat env'"
    using exf0 by simp_all
  have fo: "fails_ok (Some r)"
    using exf(1) by (cases r) (auto simp: fails_ok_def exn_ok_def)
  have m: "unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) = Some (instr \<rho> (instE \<rho>) r)"
    if g: "gsol alg ar (tyenv env) \<rho>" for \<rho>
  proof -
    have "\<forall>s. r \<noteq> Err (Failure s)" using fo by (auto simp: fails_ok_def exn_ok_def)
    with rel[OF g, THEN relJ_relI_Some] show ?thesis by (auto simp: relI_def instM_def)
  qed
  have "r \<noteq> Err Pattern" if "ppat s \<and> ppat t \<and> env_ppat env"
    using exf(2)[OF that] by (cases r) auto
  moreover have "no_unif (Some r)"
    if g: "gsol alg ar (tyenv env) \<rho>" and i: "inst_ok ar W \<rho> bs s t env"
      and sol: "solution W \<tau>' \<sigma> (instE \<rho> env)" and uni: "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    for \<rho> W \<tau>' \<sigma>
  proof -
    note u = m[OF g]
    from inst_okD(7)[OF i] obtain U where ty: "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U"
      "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U" by blast
    have "no_unif (Some (instr \<rho> (instE \<rho>) r))"
      using unif_complete[OF u inst_okD(1,4,2,3,5,6)[OF i] ty bi sol uni] by simp
    then show ?thesis by (cases r) (auto simp: no_unif_def)
  qed
  moreover have "postok alg ar A bs s t env env'" if r: "r = Ok env'" for env'
  proof -
    from okr[OF r] have e: "extends env' env" "maxidx env \<le> maxidx env'" "tyenv env' = tyenv env"
      and tw: "\<forall>T\<in>etys env'. tyw ar (tyenv env) A T" by (auto simp: ext_def)
    have mo: "unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) = Some (Ok (instE \<rho> env'))"
      if g: "gsol alg ar (tyenv env) \<rho>" for \<rho>
      using m[OF g] r by simp
    have "instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t" if g: "gsol alg ar (tyenv env') \<rho>" for \<rho>
    proof -
      from g e(3) have g': "gsol alg ar (tyenv env) \<rho>" by simp
      from preD(6)[OF pre g'] obtain W where i: "inst_ok ar W \<rho> bs s t env" by blast
      show ?thesis using unif_sound[OF mo[OF g'] refl inst_okD(1,4,5,6)[OF i]] by simp
    qed
    moreover have "\<exists>W'. ty_ext ar W (instE \<rho> env) W' (instE \<rho> env')"
      if g: "gsol alg ar (tyenv env') \<rho>" and i: "inst_ok ar W \<rho> bs s t env" for \<rho> W
    proof -
      from g e(3) have g': "gsol alg ar (tyenv env) \<rho>" by simp
      from inst_okD(7)[OF i] obtain U where ty: "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U"
        "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U" by blast
      show ?thesis using unif_exn[OF mo[OF g'] inst_okD(1,4,2,3,5,6)[OF i] ty bi] by simp
    qed
    moreover have "\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
        sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' env')"
      if g: "gsol alg ar (tyenv env) \<rho>" and i: "inst_ok ar W \<rho> bs s t env"
        and sol: "solution W \<tau>' \<sigma> (instE \<rho> env)" and uni: "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
      for \<rho> W \<tau>' \<sigma>
    proof -
      from inst_okD(7)[OF i] obtain U where ty: "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U"
        "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U" by blast
      have "\<exists>V' \<sigma>'. sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) V' \<sigma>' (instE \<rho> env')"
        using unif_complete[OF mo[OF g] inst_okD(1,4,2,3,5,6)[OF i] ty bi sol uni] by simp
      with g e(3) show ?thesis by (intro exI[of _ \<rho>]) auto
    qed
    moreover have "env_ppat env'" if "ppat s \<and> ppat t \<and> env_ppat env" using exf(3)[OF _ that] r by simp
    ultimately show ?thesis
      using e tw inv tinv_mono[OF inv(1) e(2)] unfolding postok_def by simp
  qed
  ultimately show ?thesis using fo unfolding post_all_def post_def by blast
qed

subsection \<open>Head normalisation\<close>

lemma extends_instE: "extends e' e \<Longrightarrow> extends (instE \<rho> e') (instE \<rho> e)"
  by (auto simp: extends_def)

lemma unifies_equiv:
  assumes "solution W \<tau>' \<sigma> e" "e \<Turnstile> s \<approx> s'" "e \<Turnstile> t \<approx> t'" "unifies \<sigma> (tr s) (tr t)"
  shows "unifies \<sigma> (tr s') (tr t')"
  using env_equivD[OF assms(2) solutionD(1,4)[OF assms(1)]] env_equivD[OF assms(3) solutionD(1,4)[OF assms(1)]]
    assms(4)
  by (simp add: unifies_def) (meson equiv_sym equiv_trans)

lemma head_norm_inst_ok:
  assumes pre: "pre alg ar A bs s t env" and hs: "head_norm env s = Some (Ok s0)"
    and ht: "head_norm env t = Some (Ok t0)" and g: "gsol alg ar (tyenv env) \<rho>"
    and i: "inst_ok ar W \<rho> bs s t env"
  shows "inst_ok ar W \<rho> bs s0 t0 env" "instE \<rho> env \<Turnstile> inst \<rho> s \<approx> inst \<rho> s0"
    "instE \<rho> env \<Turnstile> inst \<rho> t \<approx> inst \<rho> t0"
proof -
  have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  have hs': "head_norm (instE \<rho> env) (inst \<rho> s) = Some (Ok (inst \<rho> s0))"
    and ht': "head_norm (instE \<rho> env) (inst \<rho> t) = Some (Ok (inst \<rho> t0))"
    using pre_head_norm_inst[OF pre sol] hs ht by simp_all
  from inst_okD(7)[OF i] obtain U where ty: "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U"
    "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U" by blast
  note wf = inst_okD(1)[OF i] and e = inst_okD(2)[OF i]
  note ss = head_norm_sound[OF hs' refl wf] and st = head_norm_sound[OF ht' refl wf]
  have "wf_term ar (length bs) (inst \<rho> s0)" "wf_term ar (length bs) (inst \<rho> t0)"
    using ss st inst_okD(5,6)[OF i] by (auto simp: wf_term_def)
  moreover have "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s0) U"
    "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t0) U"
    by (rule head_norm_typed[OF hs' refl wf e ty(1)], rule head_norm_typed[OF ht' refl wf e ty(2)])
  ultimately show "inst_ok ar W \<rho> bs s0 t0 env" using i by (auto simp: inst_ok_def)
  show "instE \<rho> env \<Turnstile> inst \<rho> s \<approx> inst \<rho> s0" "instE \<rho> env \<Turnstile> inst \<rho> t \<approx> inst \<rho> t0"
    using ss st inst_okD(5,6)[OF i] by (auto simp: wf_term_def)
qed

lemma post_head_norm:
  assumes pre: "pre alg ar A bs s t env" and hs: "head_norm env s = Some (Ok s0)"
    and ht: "head_norm env t = Some (Ok t0)" and p: "post_all alg ar A bs s0 t0 env r"
  shows "post_all alg ar A bs s t env r"
proof -
  note hi = head_norm_inst_ok[OF pre hs ht]
  note q = p[unfolded post_all_def post_def postok_def]
  have pp: "ppat s0 \<and> ppat t0" if "ppat s \<and> ppat t \<and> env_ppat env"
  proof -
    obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" using gsol_exists[OF preD(1,2)[OF pre]] .
    from preD(6)[OF pre g] obtain W where i: "inst_ok ar W \<rho> bs s t env" by blast
    have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
    have "head_norm (instE \<rho> env) (inst \<rho> s) = Some (Ok (inst \<rho> s0))"
      "head_norm (instE \<rho> env) (inst \<rho> t) = Some (Ok (inst \<rho> t0))"
      using pre_head_norm_inst[OF pre sol] hs ht by simp_all
    from head_norm_ppat[OF this(1) inst_okD(1)[OF i]] head_norm_ppat[OF this(2) inst_okD(1)[OF i]] that
    show ?thesis by simp
  qed
  have cpl: "inst_ok ar W \<rho> bs s0 t0 env \<and> unifies \<sigma> (tr (inst \<rho> s0)) (tr (inst \<rho> t0))"
    if g: "gsol alg ar (tyenv env) \<rho>" and i: "inst_ok ar W \<rho> bs s t env"
      and sol: "solution W \<tau>' \<sigma> (instE \<rho> env)" and u: "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    for \<rho> W \<tau>' \<sigma>
    using hi[OF g i] unifies_equiv[OF sol _ _ u] by blast
  have "post alg ar A bs s t env r"
    unfolding post_def using q pp cpl by blast
  moreover have "postok alg ar A bs s t env env'" if r: "r = Ok env'" for env'
  proof -
    from p r have o2: "postok alg ar A bs s0 t0 env env'" by (simp add: post_all_def)
    note o3 = o2[unfolded postok_def]
    from q r have o: "textends (tyenv env) (tyenv env')" "extends env' env" by simp_all
    have h1: "\<forall>\<rho>. gsol alg ar (tyenv env') \<rho> \<longrightarrow> instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t"
    proof (intro allI impI)
      fix \<rho> assume g: "gsol alg ar (tyenv env') \<rho>"
      have g0: "gsol alg ar (tyenv env) \<rho>" by (rule gsol_textends[OF o(1) g])
      from preD(6)[OF pre g0] obtain W where i: "inst_ok ar W \<rho> bs s t env" by blast
      have ex: "extends (instE \<rho> env') (instE \<rho> env)" by (rule extends_instE[OF o(2)])
      have "instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> s0" "instE \<rho> env' \<Turnstile> inst \<rho> t \<approx> inst \<rho> t0"
        using env_equiv_extends[OF hi(2)[OF g0 i] ex] env_equiv_extends[OF hi(3)[OF g0 i] ex] by simp_all
      moreover have "instE \<rho> env' \<Turnstile> inst \<rho> s0 \<approx> inst \<rho> t0" using q r g by blast
      ultimately show "instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t" by (meson env_equiv_sym env_equiv_trans)
    qed
    have h2: "\<forall>\<rho> W. gsol alg ar (tyenv env') \<rho> \<longrightarrow> inst_ok ar W \<rho> bs s t env \<longrightarrow>
        (\<exists>W'. ty_ext ar W (instE \<rho> env) W' (instE \<rho> env'))"
      using o3 hi(1)[OF gsol_textends[OF o(1)]] by blast
    have h3: "ppat s \<and> ppat t \<and> env_ppat env \<longrightarrow> env_ppat env'" using o3 pp by blast
    have h4: "\<forall>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<longrightarrow> inst_ok ar W \<rho> bs s t env \<longrightarrow>
        solution W \<tau>' \<sigma> (instE \<rho> env) \<longrightarrow> unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t)) \<longrightarrow>
        (\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
          sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' env'))"
      using o3 cpl by blast
    show ?thesis using o3 h1 h2 h3 h4 unfolding postok_def by simp
  qed
  ultimately show ?thesis by (simp add: post_all_def)
qed

subsection \<open>Decomposition\<close>

lemma post_all_Unif:
  assumes "\<And>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<Longrightarrow> inst_ok ar W \<rho> bs s t env \<Longrightarrow>
      solution W \<tau>' \<sigma> (instE \<rho> env) \<Longrightarrow> unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t)) \<Longrightarrow> False"
  shows "post_all alg ar A bs s t env (Err (Unif u))"
  using assms by (auto simp: post_all_def post_def fails_ok_def)

lemma tstep_gsol:
  assumes st: "tstep alg ar A P \<theta> n \<theta>' n'" and g: "gsol alg ar \<theta> \<rho>" and P: "P \<rho>"
  obtains \<rho>' where "gsol alg ar \<theta>' \<rho>'" "tagree n \<rho> \<rho>'"
proof -
  from g have ws: "wsinst alg \<rho>" and sol: "tsol \<theta> \<rho>" and gr: "\<forall>v S. ground ar (\<rho> v S)"
    by (simp_all add: gsol_def)
  from tstepD(5)[OF st ws sol P] obtain \<rho>1 where "wsinst alg \<rho>1" "tsol \<theta>' \<rho>1" "tagree n \<rho> \<rho>1" by blast
  from gsol_tstep[OF this(1,2) tstepD(3)[OF st] gr this(3)] that show ?thesis by blast
qed

lemma pre_tagree:
  assumes pre: "pre alg ar A bs s t env" and ag: "tagree (maxidx env) \<rho> \<rho>'"
  shows "inst \<rho>' s = inst \<rho> s" "inst \<rho>' t = inst \<rho> t" "instb \<rho>' bs = instb \<rho> bs" "instE \<rho>' env = instE \<rho> env"
proof -
  have "tsubst \<rho>' T = tsubst \<rho> T" if "T \<in> snd ` set bs \<union> tys s \<union> tys t \<union> etys env" for T
    using tyw_tagree[OF preD(1)[OF pre] _ ag] preD(3)[OF pre] that by blast
  then show "inst \<rho>' s = inst \<rho> s" "inst \<rho>' t = inst \<rho> t" "instb \<rho>' bs = instb \<rho> bs" "instE \<rho>' env = instE \<rho> env"
    by (auto intro!: inst_tagree instb_tagree instE_tagree)
qed

lemma inst_okl_lift:
  assumes i: "inst_okl ar W \<rho> bs ps env" and te: "tenv env1 = tenv env" and mx: "maxidx env \<le> maxidx env1"
  shows "inst_okl ar W \<rho> bs ps env1"
proof -
  have e: "tenv (instE \<rho> env1) = tenv (instE \<rho> env)" by (rule instE_same_tenv[OF te])
  have "fresh_env (instE \<rho> env1)" using fresh_env_same[OF e] mx i by (simp add: inst_okl_def)
  with i e show ?thesis by (simp add: inst_okl_def wf_env_def env_typed_def)
qed

text \<open>
  A problem that reduces, after a step on the type environment establishing \<open>P\<close>, to a list of
  equations: each of its ground solutions satisfying \<open>P\<close> solves the equations, and solutions
  of the equations solve the problem.
\<close>

lemma post_decomp:
  assumes pre: "pre alg ar A bs s t env"
    and te: "tenv env1 = tenv env"
    and st: "tstep alg ar A P (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
    and srt1: "tsorted alg (tyenv env1)"
    and tw: "\<forall>T\<in>snd ` set bs' \<union> ptys ps. tyw ar (tyenv env) A T"
    and bl: "\<forall>(u, v)\<in>set ps. below (maxidx env) u \<and> below (maxidx env) v"
    and iok: "\<And>\<rho> W. gsol alg ar (tyenv env1) \<rho> \<Longrightarrow> inst_ok ar W \<rho> bs s t env \<Longrightarrow> inst_okl ar W \<rho> bs' ps env"
    and sound: "\<And>\<rho> W e. gsol alg ar (tyenv env1) \<rho> \<Longrightarrow> inst_ok ar W \<rho> bs s t env \<Longrightarrow>
      \<forall>(u, v)\<in>set ps. e \<Turnstile> inst \<rho> u \<approx> inst \<rho> v \<Longrightarrow> e \<Turnstile> inst \<rho> s \<approx> inst \<rho> t"
    and compl: "\<And>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<Longrightarrow> inst_ok ar W \<rho> bs s t env \<Longrightarrow>
      solution W \<tau>' \<sigma> (instE \<rho> env) \<Longrightarrow> unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t)) \<Longrightarrow>
      P \<rho> \<and> (\<forall>(u, v)\<in>set ps. unifies \<sigma> (tr (inst \<rho> u)) (tr (inst \<rho> v)))"
    and pp: "ppat s \<Longrightarrow> ppat t \<Longrightarrow> \<forall>(u, v)\<in>set ps. ppat u \<and> ppat v"
  shows "prel alg ar A bs' ps env1" and "post_alll alg ar A bs' ps env1 r \<Longrightarrow> post_all alg ar A bs s t env r"
proof -
  note inv = preD(1,2)[OF pre]
  have tx: "textends (tyenv env) (tyenv env1)" and mx: "maxidx env \<le> maxidx env1"
    and inv1: "tinv ar (maxidx env1) (tyenv env1) A" using tstepD(1-3)[OF st] by simp_all
  have et: "etys env1 = etys env" using te by (simp add: etys_def)
  have ep: "env_ppat env1 \<longleftrightarrow> env_ppat env" using te by (simp add: env_ppat_def)
  have ext1: "extends env1 env" using te by (simp add: extends_def)
  have ie: "tenv (instE \<rho> env1) = tenv (instE \<rho> env)" for \<rho> by (rule instE_same_tenv[OF te])
  have ok1: "inst_okl ar W \<rho> bs' ps env1" if g: "gsol alg ar (tyenv env1) \<rho>" and i: "inst_ok ar W \<rho> bs s t env"
    for \<rho> W
    by (rule inst_okl_lift[OF iok[OF g i] te mx])
  show pre1: "prel alg ar A bs' ps env1"
    unfolding prel_def
  proof (intro conjI allI impI)
    show "\<forall>T\<in>snd ` set bs' \<union> ptys ps \<union> etys env1. tyw ar (tyenv env1) A T"
      using tw preD(3)[OF pre] tyw_textends[OF tinv_tacyc[OF inv1] tx] et by blast
    show "\<forall>(u, v)\<in>set ps. below (maxidx env1) u \<and> below (maxidx env1) v"
      using bl below_mono[OF _ mx] by fastforce
    fix \<rho> assume g: "gsol alg ar (tyenv env1) \<rho>"
    from preD(6)[OF pre gsol_textends[OF tx g]] obtain W where "inst_ok ar W \<rho> bs s t env" by blast
    with ok1[OF g] show "\<exists>W. inst_okl ar W \<rho> bs' ps env1" by blast
  qed (use inv1 srt1 in simp_all)
  assume q0: "post_alll alg ar A bs' ps env1 r"
  note q = q0[unfolded post_alll_def postl_def postokl_def]
  have mv: "\<exists>\<rho>''. gsol alg ar (tyenv env1) \<rho>'' \<and> tagree (maxidx env) \<rho> \<rho>'' \<and> inst_okl ar W \<rho>'' bs' ps env1 \<and>
      sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W \<sigma> (instE \<rho>'' env1) \<and>
      (\<forall>(u, v)\<in>set ps. unifies \<sigma> (tr (inst \<rho>'' u)) (tr (inst \<rho>'' v)))"
    if g: "gsol alg ar (tyenv env) \<rho>" and i: "inst_ok ar W \<rho> bs s t env"
      and sol: "solution W \<tau>' \<sigma> (instE \<rho> env)" and u: "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    for \<rho> W \<tau>' \<sigma>
  proof -
    from compl[OF g i sol u] have P: "P \<rho>" and us: "\<forall>(u, v)\<in>set ps. unifies \<sigma> (tr (inst \<rho> u)) (tr (inst \<rho> v))"
      by simp_all
    obtain \<rho>'' where g'': "gsol alg ar (tyenv env1) \<rho>''" and ag: "tagree (maxidx env) \<rho> \<rho>''"
      by (rule tstep_gsol[OF st g P])
    note a = pre_tagree[OF pre ag]
    have i'': "inst_ok ar W \<rho>'' bs s t env" using i a by (simp add: inst_ok_def)
    have us'': "\<forall>(u, v)\<in>set ps. unifies \<sigma> (tr (inst \<rho>'' u)) (tr (inst \<rho>'' v))"
    proof (intro ballI, clarify)
      fix u v assume uv: "(u, v) \<in> set ps"
      have "\<forall>T\<in>tys u \<union> tys v. tsubst \<rho>'' T = tsubst \<rho> T"
        using tw uv tyw_tagree[OF inv(1) _ ag] by (auto simp: ptys_def)
      then have "inst \<rho>'' u = inst \<rho> u" "inst \<rho>'' v = inst \<rho> v" by (simp_all add: inst_tagree)
      with us uv show "unifies \<sigma> (tr (inst \<rho>'' u)) (tr (inst \<rho>'' v))" by auto
    qed
    have "sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W \<sigma> (instE \<rho>'' env1)"
      by (rule sol_ext_same) (use ie[of \<rho>''] a(4) mx sol i in \<open>simp_all add: inst_ok_def\<close>)
    with g'' ag ok1[OF g'' i''] us'' show ?thesis by blast
  qed
  have "post alg ar A bs s t env r"
    unfolding post_def
  proof (intro conjI allI impI)
    show "fails_ok (Some r)" using q by simp
    show "r \<noteq> Err Pattern" if "ppat s \<and> ppat t \<and> env_ppat env" using q pp that ep by simp
  next
    fix \<rho> W \<tau>' \<sigma> assume "gsol alg ar (tyenv env) \<rho>" "inst_ok ar W \<rho> bs s t env"
      "solution W \<tau>' \<sigma> (instE \<rho> env)" "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
    from mv[OF this] q show "no_unif (Some r)" by (auto simp: sol_ext_def)
  qed
  moreover have "postok alg ar A bs s t env env'" if r: "r = Ok env'" for env'
  proof -
    from q r have o: "postokl alg ar A bs' ps env1 env'" by (simp add: postokl_def)
    note o' = o[unfolded postokl_def]
    have tx': "textends (tyenv env1) (tyenv env')" using o' by simp
    have h1: "\<forall>\<rho>. gsol alg ar (tyenv env') \<rho> \<longrightarrow> instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t"
    proof (intro allI impI)
      fix \<rho> assume g: "gsol alg ar (tyenv env') \<rho>"
      have g1: "gsol alg ar (tyenv env1) \<rho>" by (rule gsol_textends[OF tx' g])
      from preD(6)[OF pre gsol_textends[OF tx g1]] obtain W where i: "inst_ok ar W \<rho> bs s t env" by blast
      show "instE \<rho> env' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t" by (rule sound[OF g1 i]) (use o' g in blast)
    qed
    have h2: "\<forall>\<rho> W. gsol alg ar (tyenv env') \<rho> \<longrightarrow> inst_ok ar W \<rho> bs s t env \<longrightarrow>
        (\<exists>W'. ty_ext ar W (instE \<rho> env) W' (instE \<rho> env'))"
    proof (intro allI impI)
      fix \<rho> W assume g: "gsol alg ar (tyenv env') \<rho>" and i: "inst_ok ar W \<rho> bs s t env"
      have g1: "gsol alg ar (tyenv env1) \<rho>" by (rule gsol_textends[OF tx' g])
      from o' g ok1[OF g1 i] obtain W' where "ty_ext ar W (instE \<rho> env1) W' (instE \<rho> env')" by blast
      moreover have "ty_ext ar W (instE \<rho> env) W (instE \<rho> env1)"
        by (rule ty_ext_same) (use ie[of \<rho>] mx i in \<open>simp_all add: inst_ok_def\<close>)
      ultimately show "\<exists>W'. ty_ext ar W (instE \<rho> env) W' (instE \<rho> env')" by (blast intro: ty_ext_trans)
    qed
    have h3: "ppat s \<and> ppat t \<and> env_ppat env \<longrightarrow> env_ppat env'" using o' pp ep by simp
    have h4: "\<forall>\<rho> W \<tau>' \<sigma>. gsol alg ar (tyenv env) \<rho> \<longrightarrow> inst_ok ar W \<rho> bs s t env \<longrightarrow>
        solution W \<tau>' \<sigma> (instE \<rho> env) \<longrightarrow> unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t)) \<longrightarrow>
        (\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
          sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' env'))"
    proof (intro allI impI)
      fix \<rho> W \<tau>' \<sigma> assume a: "gsol alg ar (tyenv env) \<rho>" "inst_ok ar W \<rho> bs s t env"
        "solution W \<tau>' \<sigma> (instE \<rho> env)" "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
      from mv[OF a] obtain \<rho>1 where g1: "gsol alg ar (tyenv env1) \<rho>1" and ag1: "tagree (maxidx env) \<rho> \<rho>1"
        and i1: "inst_okl ar W \<rho>1 bs' ps env1" and se1: "sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W \<sigma> (instE \<rho>1 env1)"
        and u1: "\<forall>(u, v)\<in>set ps. unifies \<sigma> (tr (inst \<rho>1 u)) (tr (inst \<rho>1 v))" by blast
      have "solution W \<tau>' \<sigma> (instE \<rho>1 env1)" using se1 by (simp add: sol_ext_def)
      with o' g1 i1 u1 obtain \<rho>2 W2 \<sigma>2 where "gsol alg ar (tyenv env') \<rho>2" "tagree (maxidx env1) \<rho>1 \<rho>2"
        "sol_ext ar W \<tau>' \<sigma> (instE \<rho>1 env1) W2 \<sigma>2 (instE \<rho>2 env')" by blast
      with ag1 se1 mx show "\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv env') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
          sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' env')"
        by (blast intro: tagree_trans sol_ext_trans)
    qed
    have "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'" "extends env' env"
      using o' tx mx ext1 by (auto intro: textends_trans extends_trans)
    moreover have "tcert alg (tvars_env (tyenv env) \<union> A) \<longrightarrow> tcert alg (tvars_env (tyenv env'))"
      using o' tstepD(6)[OF st] by simp
    ultimately show ?thesis using o' h1 h2 h3 h4 unfolding postok_def by simp
  qed
  ultimately show "post_all alg ar A bs s t env r" by (simp add: post_all_def)
qed

subsection \<open>Sequences of equations\<close>

lemma inst_okl_Cons[simp]:
  "inst_okl ar W \<rho> bs ((s, t) # ps) env \<longleftrightarrow> inst_ok ar W \<rho> bs s t env \<and> inst_okl ar W \<rho> bs ps env"
  by (auto simp: inst_okl_def inst_ok_def)

lemma prel_ConsD: "prel alg ar A bs ((s, t) # ps) env \<Longrightarrow> pre alg ar A bs s t env"
  by (auto simp: prel_def pre_def)

lemma prel_step:
  assumes pre: "prel alg ar A bs ((s, t) # ps) env" and ok: "postok alg ar A bs s t env e"
  shows "prel alg ar A bs ps e"
proof -
  note p = pre[unfolded prel_def] and o = ok[unfolded postok_def]
  have tx: "textends (tyenv env) (tyenv e)" and mx: "maxidx env \<le> maxidx e" using o by simp_all
  have "\<exists>W. inst_okl ar W \<rho> bs ps e" if g: "gsol alg ar (tyenv e) \<rho>" for \<rho>
  proof -
    from p gsol_textends[OF tx g] obtain W where i: "inst_okl ar W \<rho> bs ((s, t) # ps) env" by blast
    then have i1: "inst_ok ar W \<rho> bs s t env" and i2: "inst_okl ar W \<rho> bs ps env" by simp_all
    from o g i1 obtain W' where te: "ty_ext ar W (instE \<rho> env) W' (instE \<rho> e)" by blast
    have "inst_okl ar W' \<rho> bs ps e"
      by (rule inst_okl_transport[OF i2]) (use p te in \<open>auto simp: ty_ext_def\<close>)
    then show ?thesis by blast
  qed
  moreover have "\<forall>T\<in>snd ` set bs \<union> ptys ps \<union> etys e. tyw ar (tyenv e) A T"
  proof
    fix T assume "T \<in> snd ` set bs \<union> ptys ps \<union> etys e"
    then consider "T \<in> snd ` set bs \<union> ptys ps" | "T \<in> etys e" by blast
    then show "tyw ar (tyenv e) A T"
    proof cases
      case 1
      have "tacyc (tyenv e)" using o tinv_tacyc by blast
      with p 1 show ?thesis by (auto intro: tyw_textends[OF _ tx])
    next
      case 2
      with o show ?thesis by blast
    qed
  qed
  moreover have "\<forall>(u, v)\<in>set ps. below (maxidx e) u \<and> below (maxidx e) v"
    using p below_mono[OF _ mx] by fastforce
  ultimately show ?thesis using o by (simp add: prel_def)
qed

lemma post_alll_Nil: "prel alg ar A bs [] env \<Longrightarrow> post_alll alg ar A bs [] env (Ok env)"
  by (fastforce simp: prel_def post_alll_def postl_def postokl_def fails_ok_def no_unif_def inst_okl_def
    intro: ty_ext_refl sol_ext_refl)

lemma post_alll_Cons_Err:
  "post_all alg ar A bs s t env (Err x) \<Longrightarrow> post_alll alg ar A bs ((s, t) # ps) env (Err x)"
  by (auto simp: post_all_def post_def post_alll_def postl_def)

lemma post_alll_Cons_Ok:
  assumes pre: "prel alg ar A bs ((s, t) # ps) env" and ok: "postok alg ar A bs s t env e"
    and p2: "post_alll alg ar A bs ps e r"
  shows "post_alll alg ar A bs ((s, t) # ps) env r"
proof -
  note p = pre[unfolded prel_def] and o = ok[unfolded postok_def]
    and q = p2[unfolded post_alll_def postl_def postokl_def]
  have tx: "textends (tyenv env) (tyenv e)" and mx: "maxidx env \<le> maxidx e" and ex: "extends e env"
    using o by simp_all
  have step: "\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv e) \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' e) \<and> inst_okl ar W' \<rho>' bs ps e \<and>
      (\<forall>(u, v)\<in>set ps. unifies \<sigma>' (tr (inst \<rho>' u)) (tr (inst \<rho>' v)))"
    if g: "gsol alg ar (tyenv env) \<rho>" and i: "inst_okl ar W \<rho> bs ((s, t) # ps) env"
      and sol: "solution W \<tau>' \<sigma> (instE \<rho> env)"
      and u: "\<forall>(u, v)\<in>set ((s, t) # ps). unifies \<sigma> (tr (inst \<rho> u)) (tr (inst \<rho> v))" for \<rho> W \<tau>' \<sigma>
  proof -
    from i have i1: "inst_ok ar W \<rho> bs s t env" and i2: "inst_okl ar W \<rho> bs ps env" by simp_all
    from u have u1: "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))" by simp
    from o g i1 sol u1 obtain \<rho>' W' \<sigma>' where g': "gsol alg ar (tyenv e) \<rho>'"
      and ag: "tagree (maxidx env) \<rho> \<rho>'" and se: "sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' e)"
      by blast
    have agT: "\<forall>T\<in>snd ` set bs \<union> ptys ps. tsubst \<rho>' T = tsubst \<rho> T"
    proof
      fix T assume "T \<in> snd ` set bs \<union> ptys ps"
      with p have "tyw ar (tyenv env) A T" by auto
      with p show "tsubst \<rho>' T = tsubst \<rho> T" by (blast intro: tyw_tagree[OF _ _ ag])
    qed
    have bl: "\<forall>(u, v)\<in>set ps. below (maxidx env) u \<and> below (maxidx env) v" using p by simp
    have i': "inst_okl ar W' \<rho>' bs ps e"
      by (rule inst_okl_transport[OF i2 agT bl]) (use se in \<open>simp_all add: sol_ext_def\<close>)
    have "unifies \<sigma>' (tr (inst \<rho>' a)) (tr (inst \<rho>' b))" if ab: "(a, b) \<in> set ps" for a b
    proof -
      have "inst \<rho>' a = inst \<rho> a" "inst \<rho>' b = inst \<rho> b"
        using agT ab by (auto simp: ptys_def intro!: inst_tagree)
      moreover have "below (maxidx env) (inst \<rho> a)" "below (maxidx env) (inst \<rho> b)" using bl ab by auto
      moreover have "agree (maxidx env) \<sigma> \<sigma>'" using se by (simp add: sol_ext_def)
      ultimately show ?thesis using u ab by (auto simp: unifies_def mk_subst_agree)
    qed
    with g' ag se i' show ?thesis by blast
  qed
  have "postl alg ar A bs ((s, t) # ps) env r"
    unfolding postl_def
  proof (intro conjI allI impI)
    show "fails_ok (Some r)" using q by simp
  next
    assume "(\<forall>(u, v)\<in>set ((s, t) # ps). ppat u \<and> ppat v) \<and> env_ppat env"
    with o q show "r \<noteq> Err Pattern" by auto
  next
    fix \<rho> W \<tau>' \<sigma> assume "gsol alg ar (tyenv env) \<rho>" "inst_okl ar W \<rho> bs ((s, t) # ps) env"
      "solution W \<tau>' \<sigma> (instE \<rho> env)" "\<forall>(u, v)\<in>set ((s, t) # ps). unifies \<sigma> (tr (inst \<rho> u)) (tr (inst \<rho> v))"
    from step[OF this] q show "no_unif (Some r)" by (auto simp: sol_ext_def)
  qed
  moreover have "postokl alg ar A bs ((s, t) # ps) env e'" if r: "r = Ok e'" for e'
  proof -
    from q r have q': "postokl alg ar A bs ps e e'" by (simp add: postokl_def)
    note o' = q'[unfolded postokl_def]
    have tx': "textends (tyenv e) (tyenv e')" using o' by simp
    have "instE \<rho> e' \<Turnstile> inst \<rho> s \<approx> inst \<rho> t" if g: "gsol alg ar (tyenv e') \<rho>" for \<rho>
    proof (rule env_equiv_extends)
      show "instE \<rho> e \<Turnstile> inst \<rho> s \<approx> inst \<rho> t" using o gsol_textends[OF tx' g] by blast
      show "extends (instE \<rho> e') (instE \<rho> e)" using o' by (simp add: extends_instE)
    qed
    moreover have "\<exists>W'. ty_ext ar W (instE \<rho> env) W' (instE \<rho> e')"
      if g: "gsol alg ar (tyenv e') \<rho>" and i: "inst_okl ar W \<rho> bs ((s, t) # ps) env" for \<rho> W
    proof -
      from i have i1: "inst_ok ar W \<rho> bs s t env" and i2: "inst_okl ar W \<rho> bs ps env" by simp_all
      from o gsol_textends[OF tx' g] i1 obtain W1 where te: "ty_ext ar W (instE \<rho> env) W1 (instE \<rho> e)" by blast
      have "inst_okl ar W1 \<rho> bs ps e"
        by (rule inst_okl_transport[OF i2]) (use p te in \<open>auto simp: ty_ext_def\<close>)
      with o' g obtain W2 where "ty_ext ar W1 (instE \<rho> e) W2 (instE \<rho> e')" by blast
      with te show ?thesis by (blast intro: ty_ext_trans)
    qed
    moreover have "\<exists>\<rho>' W' \<sigma>'. gsol alg ar (tyenv e') \<rho>' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
        sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W' \<sigma>' (instE \<rho>' e')"
      if "gsol alg ar (tyenv env) \<rho>" "inst_okl ar W \<rho> bs ((s, t) # ps) env"
        "solution W \<tau>' \<sigma> (instE \<rho> env)" "\<forall>(u, v)\<in>set ((s, t) # ps). unifies \<sigma> (tr (inst \<rho> u)) (tr (inst \<rho> v))"
      for \<rho> W \<tau>' \<sigma>
    proof -
      from step[OF that] obtain \<rho>1 W1 \<sigma>1 where g1: "gsol alg ar (tyenv e) \<rho>1" and ag1: "tagree (maxidx env) \<rho> \<rho>1"
        and se1: "sol_ext ar W \<tau>' \<sigma> (instE \<rho> env) W1 \<sigma>1 (instE \<rho>1 e)" and i1: "inst_okl ar W1 \<rho>1 bs ps e"
        and u1: "\<forall>(u, v)\<in>set ps. unifies \<sigma>1 (tr (inst \<rho>1 u)) (tr (inst \<rho>1 v))" by blast
      have "solution W1 \<tau>' \<sigma>1 (instE \<rho>1 e)" using se1 by (simp add: sol_ext_def)
      with o' g1 i1 u1 obtain \<rho>2 W2 \<sigma>2 where "gsol alg ar (tyenv e') \<rho>2" "tagree (maxidx e) \<rho>1 \<rho>2"
        "sol_ext ar W1 \<tau>' \<sigma>1 (instE \<rho>1 e) W2 \<sigma>2 (instE \<rho>2 e')" by blast
      with ag1 se1 mx show ?thesis by (blast intro: tagree_trans sol_ext_trans)
    qed
    moreover have "tcert alg (tvars_env (tyenv env) \<union> A) \<longrightarrow> tcert alg (tvars_env (tyenv e'))"
      using o o' by simp
    ultimately show ?thesis
      using o o' by (auto simp: postokl_def intro: textends_trans extends_trans)
  qed
  ultimately show ?thesis by (simp add: post_alll_def)
qed

lemma foldM_post:
  assumes "foldM (\<lambda>(s, t) e. f s t e) ps env = Some r" "prel alg ar A bs ps env"
    and "\<And>s t e r. (s, t) \<in> set ps \<Longrightarrow> f s t e = Some r \<Longrightarrow> pre alg ar A bs s t e \<Longrightarrow>
      post_all alg ar A bs s t e r"
  shows "post_alll alg ar A bs ps env r"
  using assms
proof (induction ps arbitrary: env)
  case Nil
  then show ?case by (auto simp: return_def post_alll_Nil)
next
  case (Cons p ps)
  obtain s t where p: "p = (s, t)" by force
  note pre = Cons.prems(2)[unfolded p]
  from Cons.prems(1) p have "f s t env \<bind> (\<lambda>e. foldM (\<lambda>(s, t) e. f s t e) ps e) = Some r" by simp
  then show ?case
  proof (rule bindM_SomeE)
    fix x assume "f s t env = Some (Err x)" "r = Err x"
    with Cons.prems(3)[of s t env] prel_ConsD[OF pre] p show ?thesis by (simp add: post_alll_Cons_Err)
  next
    fix e assume f: "f s t env = Some (Ok e)" and rest: "foldM (\<lambda>(s, t) e. f s t e) ps e = Some r"
    have "post_all alg ar A bs s t env (Ok e)" using Cons.prems(3)[OF _ f prel_ConsD[OF pre]] p by simp
    then have ok: "postok alg ar A bs s t env e" by (simp add: post_all_def)
    have "post_alll alg ar A bs ps e r"
      using Cons.IH[OF rest prel_step[OF pre ok]] Cons.prems(3) by simp
    with post_alll_Cons_Ok[OF pre ok] p show ?thesis by simp
  qed
qed

subsection \<open>Rigid terms\<close>

lemma rigid_unifies:
  assumes shs: "strip_comb s = (h, ss)" and sht: "strip_comb t = (h', ts)"
    and rh: "is_rigid h" "is_rigid h'"
    and sol: "solution W \<tau>' \<sigma> e" and u: "unifies \<sigma> (tr s) (tr t)"
  shows "h = h'" "list_all2 (\<lambda>u v. unifies \<sigma> (tr u) (tr v)) ss ts"
proof -
  note \<sigma> = solutionD[OF sol]
  have rigtr: "mk_subst \<sigma> (tr g) = tr g \<and> is_atom (tr g)" if "is_rigid g" for g
    using that by (auto simp: is_rigid_def rigid_substD[OF \<sigma>(3)])
  from u have "mk_subst \<sigma> (tr (list_comb h ss)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (list_comb h' ts))"
    using strip_comb_list_comb[OF shs] strip_comb_list_comb[OF sht] by (simp add: unifies_def)
  then have "tr h \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ss \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h' \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
    using rigtr[OF rh(1)] rigtr[OF rh(2)] by (simp add: tr_list_comb comp_def)
  from atom_apps_equiv[OF conjunct2[OF rigtr[OF rh(1)]] conjunct2[OF rigtr[OF rh(2)]] this]
  have hh: "tr h = tr h'"
    and args: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>t. mk_subst \<sigma> (tr t)) ss) (map (\<lambda>t. mk_subst \<sigma> (tr t)) ts)"
    by auto
  show "h = h'" using hh rh by (auto simp: is_rigid_def integer_reps)
  show "list_all2 (\<lambda>u v. unifies \<sigma> (tr u) (tr v)) ss ts"
    using args by (simp add: list_all2_map1 list_all2_map2 unifies_def)
qed

lemma ppat_rigid_args: "ppat (list_comb h ts) \<Longrightarrow> is_rigid h \<Longrightarrow> \<forall>t\<in>set ts. ppat t"
  using ppat_spine[of h ts] is_rigid_not_App[of h]
  by (cases ts rule: rev_cases) (auto simp: is_rigid_def list_comb_def)

lemma rigid_decomp:
  assumes pre: "pre alg ar A bs s t env"
    and shs: "strip_comb s = (h, ss)" and sht: "strip_comb t = (h', ts)"
    and rh: "is_rigid h" "is_rigid h'"
    and te: "tenv env1 = tenv env"
    and st: "tstep alg ar A (\<lambda>\<rho>. inst \<rho> h = inst \<rho> h') (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
    and srt1: "tsorted alg (tyenv env1)"
    and eq1: "\<And>\<rho>. gsol alg ar (tyenv env1) \<rho> \<Longrightarrow> inst \<rho> h = inst \<rho> h'"
  shows "length ss = length ts" and "prel alg ar A bs (zip ss ts) env1"
    and "post_alll alg ar A bs (zip ss ts) env1 r \<Longrightarrow> post_all alg ar A bs s t env r"
proof -
  let ?Bs = "\<lambda>\<rho>. map snd (instb \<rho> bs)"
  have tx: "textends (tyenv env) (tyenv env1)" and inv1: "tinv ar (maxidx env1) (tyenv env1) A"
    using tstepD(1,3)[OF st] by simp_all
  have se: "s = list_comb h ss" "t = list_comb h' ts"
    using strip_comb_list_comb[OF shs] strip_comb_list_comb[OF sht] by simp_all
  have shs': "strip_comb (inst \<rho> s) = (inst \<rho> h, map (inst \<rho>) ss)"
    and sht': "strip_comb (inst \<rho> t) = (inst \<rho> h', map (inst \<rho>) ts)" for \<rho>
    using strip_comb_inst[of \<rho> s] strip_comb_inst[of \<rho> t] shs sht by simp_all
  have args: "length ss = length ts \<and> (\<forall>i<length ss. \<exists>U. has_type W (?Bs \<rho>) (inst \<rho> (ss ! i)) U \<and>
      has_type W (?Bs \<rho>) (inst \<rho> (ts ! i)) U)"
    if i: "inst_ok ar W \<rho> bs s t env" and hh: "inst \<rho> h = inst \<rho> h'" for \<rho> W
  proof -
    from inst_okD(7)[OF i] obtain U where
      "has_type W (?Bs \<rho>) (list_comb (inst \<rho> h) (map (inst \<rho>) ss)) U"
      "has_type W (?Bs \<rho>) (list_comb (inst \<rho> h') (map (inst \<rho>) ts)) U"
      by (auto simp: se inst_list_comb)
    then obtain Us Us' where h1: "has_type W (?Bs \<rho>) (inst \<rho> h) (foldr fun_type Us U)"
      and a1: "list_all2 (has_type W (?Bs \<rho>)) (map (inst \<rho>) ss) Us"
      and h2: "has_type W (?Bs \<rho>) (inst \<rho> h') (foldr fun_type Us' U)"
      and a2: "list_all2 (has_type W (?Bs \<rho>)) (map (inst \<rho>) ts) Us'"
      by (auto simp: has_type_list_comb)
    have "Us' = Us" using has_type_unique[OF h1 h2[folded hh]] by (auto dest: foldr_fun_type_inj)
    with a1 a2 show ?thesis by (auto simp: list_all2_conv_all_nth) blast
  qed
  obtain \<rho>1 where g1: "gsol alg ar (tyenv env1) \<rho>1" using gsol_exists[OF inv1 srt1] .
  from preD(6)[OF pre gsol_textends[OF tx g1]] obtain W1 where "inst_ok ar W1 \<rho>1 bs s t env" by blast
  from args[OF this eq1[OF g1]] show len: "length ss = length ts" by simp
  have zs: "(u, v) \<in> set (zip ss ts) \<longleftrightarrow> (\<exists>i<length ss. u = ss ! i \<and> v = ts ! i)" for u v
    using len by (auto simp: in_set_zip)
  have tw: "\<forall>T\<in>snd ` set bs \<union> ptys (zip ss ts). tyw ar (tyenv env) A T"
  proof
    fix T assume "T \<in> snd ` set bs \<union> ptys (zip ss ts)"
    then have "T \<in> snd ` set bs \<union> tys s \<union> tys t"
      using tys_strip_comb[OF shs] tys_strip_comb[OF sht]
      by (auto simp: ptys_def dest: set_zip_leftD set_zip_rightD)
    then show "tyw ar (tyenv env) A T" using preD(3)[OF pre] by blast
  qed
  have bl: "\<forall>(u, v)\<in>set (zip ss ts). below (maxidx env) u \<and> below (maxidx env) v"
    using preD(4,5)[OF pre] se by (auto simp: below_list_comb dest: set_zip_leftD set_zip_rightD)
  have iok: "inst_okl ar W \<rho> bs (zip ss ts) env"
    if g: "gsol alg ar (tyenv env1) \<rho>" and i: "inst_ok ar W \<rho> bs s t env" for \<rho> W
  proof -
    have "wf_term ar (length bs) (inst \<rho> u)" if "u \<in> set ss \<union> set ts" for u
      using inst_okD(5,6)[OF i] that by (auto simp: se inst_list_comb wf_term_list_comb)
    with args[OF i eq1[OF g]] i show ?thesis by (auto simp: inst_okl_def inst_ok_def zs)
  qed
  have sound: "e \<Turnstile> inst \<rho> s \<approx> inst \<rho> t"
    if g: "gsol alg ar (tyenv env1) \<rho>" and i: "inst_ok ar W \<rho> bs s t env"
      and eqs: "\<forall>(u, v)\<in>set (zip ss ts). e \<Turnstile> inst \<rho> u \<approx> inst \<rho> v" for \<rho> W e
  proof -
    have "list_all2 (env_equiv e) (map (inst \<rho>) ss) (map (inst \<rho>) ts)"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (inst \<rho>) ss) = length (map (inst \<rho>) ts)" using len by simp
      fix i assume i: "i < length (map (inst \<rho>) ss)"
      then have "(ss ! i, ts ! i) \<in> set (zip ss ts)" using zs by auto
      with eqs i len show "e \<Turnstile> map (inst \<rho>) ss ! i \<approx> map (inst \<rho>) ts ! i" by auto
    qed
    from env_equiv_list_comb[OF _ this, of "inst \<rho> h" "inst \<rho> h'"] eq1[OF g]
    show ?thesis by (simp add: se inst_list_comb)
  qed
  have compl: "inst \<rho> h = inst \<rho> h' \<and> (\<forall>(u, v)\<in>set (zip ss ts). unifies \<sigma> (tr (inst \<rho> u)) (tr (inst \<rho> v)))"
    if "gsol alg ar (tyenv env) \<rho>" "inst_ok ar W \<rho> bs s t env"
      "solution W \<tau>' \<sigma> (instE \<rho> env)" "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))" for \<rho> W \<tau>' \<sigma>
  proof -
    have "is_rigid (inst \<rho> h)" "is_rigid (inst \<rho> h')" using rh by (auto simp: is_rigid_def)
    from rigid_unifies[OF shs' sht' this that(3,4)] show ?thesis
      by (auto simp: list_all2_conv_all_nth zs)
  qed
  have pp: "\<forall>(u, v)\<in>set (zip ss ts). ppat u \<and> ppat v" if "ppat s" "ppat t"
    using ppat_rigid_args[OF that(1)[unfolded se(1)] rh(1)] ppat_rigid_args[OF that(2)[unfolded se(2)] rh(2)]
    by (auto dest: set_zip_leftD set_zip_rightD)
  show "prel alg ar A bs (zip ss ts) env1"
    by (rule post_decomp(1)[OF pre te st srt1 tw bl]) (fact iok | fact sound | fact compl | fact pp)+
  show "post_all alg ar A bs s t env r" if q: "post_alll alg ar A bs (zip ss ts) env1 r"
    by (rule post_decomp(2)[OF pre te st srt1 tw bl]) (fact iok | fact sound | fact compl | fact pp | fact q)+
qed

lemma post_rigid:
  assumes pre: "pre alg ar A bs s t env"
    and shs: "strip_comb s = (h, ss)" and sht: "strip_comb t = (h', ts)"
    and rh: "is_rigid h" "is_rigid h'"
    and te: "tenv env1 = tenv env"
    and st: "tstep alg ar A (\<lambda>\<rho>. inst \<rho> h = inst \<rho> h') (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
    and srt1: "tsorted alg (tyenv env1)"
    and eq1: "\<And>\<rho>. gsol alg ar (tyenv env1) \<rho> \<Longrightarrow> inst \<rho> h = inst \<rho> h'"
    and r: "zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. f s t e) ps env1) = Some r"
    and IH: "\<And>s t e r. (s, t) \<in> set (zip ss ts) \<Longrightarrow> f s t e = Some r \<Longrightarrow> pre alg ar A bs s t e \<Longrightarrow>
      post_all alg ar A bs s t e r"
  shows "post_all alg ar A bs s t env r"
proof -
  have len: "length ss = length ts" by (rule rigid_decomp(1)[OF pre shs sht rh te st srt1]) (fact eq1)
  have pre1: "prel alg ar A bs (zip ss ts) env1" by (rule rigid_decomp(2)[OF pre shs sht rh te st srt1]) (fact eq1)
  from r len have fo: "foldM (\<lambda>(s, t) e. f s t e) (zip ss ts) env1 = Some r" by (simp add: zip_eq_return)
  have q: "post_alll alg ar A bs (zip ss ts) env1 r" by (rule foldM_post[OF fo pre1]) (fact IH)
  show ?thesis by (rule rigid_decomp(3)[OF pre shs sht rh te st srt1]) (fact eq1 | fact q)+
qed

lemma unify_types_cases:
  assumes "tinv ar (maxidx env) (tyenv env) A" "tsorted alg (tyenv env)"
    "tyw ar (tyenv env) A T" "tyw ar (tyenv env) A U"
  obtains (Ok) env1 where "unify_types alg T U env = Some (Ok env1)" "tenv env1 = tenv env"
      "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
      "\<And>\<rho>. tsol (tyenv env1) \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U" "tsorted alg (tyenv env1)"
  | (Err) u where "unify_types alg T U env = Some (Err (Unif u))"
      "\<And>\<rho>. wsinst alg \<rho> \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> tsubst \<rho> T \<noteq> tsubst \<rho> U"
  using unify_types_poly[OF assms] by blast


subsection \<open>Abstractions\<close>

lemma unifies_commute: "unifies \<sigma> s t \<longleftrightarrow> unifies \<sigma> t s"
  by (auto simp: unifies_def intro: equiv_sym)

lemma env_equiv_commute: "e \<Turnstile> s \<approx> t \<longleftrightarrow> e \<Turnstile> t \<approx> s"
  by (auto intro: env_equiv_sym)

lemma inst_ok_commute: "inst_ok ar W \<rho> bs t s env \<longleftrightarrow> inst_ok ar W \<rho> bs s t env"
  by (auto simp: inst_ok_def)

lemma pre_commute: "pre alg ar A bs t s env \<longleftrightarrow> pre alg ar A bs s t env"
  by (auto simp: pre_def inst_ok_commute)

lemma post_all_commute: "post_all alg ar A bs t s env r \<longleftrightarrow> post_all alg ar A bs s t env r"
  by (auto simp: post_all_def post_def postok_def inst_ok_commute unifies_commute env_equiv_commute)

lemma AA_types:
  assumes i: "inst_ok ar W \<rho> bs (pterm.Abs ns Ts ts) (pterm.Abs nt Tt tt) env"
  shows "tsubst \<rho> Ts = tsubst \<rho> Tt" "inst_ok ar W \<rho> ((nm, Ts) # bs) ts tt env"
proof -
  let ?Bs = "map snd (instb \<rho> bs)"
  from inst_okD(7)[OF i] obtain U where "has_type W ?Bs (pterm.Abs ns (tsubst \<rho> Ts) (inst \<rho> ts)) U"
    "has_type W ?Bs (pterm.Abs nt (tsubst \<rho> Tt) (inst \<rho> tt)) U" by auto
  then obtain V1 V2 where "U = tsubst \<rho> Ts \<rightarrow>\<^sub>T V1" "has_type W (tsubst \<rho> Ts # ?Bs) (inst \<rho> ts) V1"
    "U = tsubst \<rho> Tt \<rightarrow>\<^sub>T V2" "has_type W (tsubst \<rho> Tt # ?Bs) (inst \<rho> tt) V2"
    by (auto elim!: has_type_elims)
  moreover have "ground ar (tsubst \<rho> Ts)" using inst_okD(5)[OF i] by (simp add: wf_term_def)
  ultimately show "tsubst \<rho> Ts = tsubst \<rho> Tt" "inst_ok ar W \<rho> ((nm, Ts) # bs) ts tt env"
    using i by (auto simp: inst_ok_def wf_term_def binders_ok_def)
qed

lemma AA_decomp:
  assumes pre: "pre alg ar A bs (pterm.Abs ns Ts ts) (pterm.Abs nt Tt tt) env"
    and te: "tenv env1 = tenv env"
    and st: "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> Ts = tsubst \<rho> Tt) (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
    and srt1: "tsorted alg (tyenv env1)"
  shows "pre alg ar A ((nm, Ts) # bs) ts tt env1"
    and "post_all alg ar A ((nm, Ts) # bs) ts tt env1 r \<Longrightarrow>
      post_all alg ar A bs (pterm.Abs ns Ts ts) (pterm.Abs nt Tt tt) env r"
proof -
  let ?s = "pterm.Abs ns Ts ts" and ?t = "pterm.Abs nt Tt tt"
  have tw: "\<forall>T\<in>snd ` set ((nm, Ts) # bs) \<union> ptys [(ts, tt)]. tyw ar (tyenv env) A T"
    using preD(3)[OF pre] by auto
  have bl: "\<forall>(u, v)\<in>set [(ts, tt)]. below (maxidx env) u \<and> below (maxidx env) v"
    using preD(4,5)[OF pre] by simp
  have iok: "inst_okl ar W \<rho> ((nm, Ts) # bs) [(ts, tt)] env"
    if "gsol alg ar (tyenv env1) \<rho>" "inst_ok ar W \<rho> bs ?s ?t env" for \<rho> W
    using AA_types(2)[OF that(2)] by simp
  have sound: "e \<Turnstile> inst \<rho> ?s \<approx> inst \<rho> ?t"
    if "gsol alg ar (tyenv env1) \<rho>" "inst_ok ar W \<rho> bs ?s ?t env"
      "\<forall>(u, v)\<in>set [(ts, tt)]. e \<Turnstile> inst \<rho> u \<approx> inst \<rho> v" for \<rho> W e
    using that(3) by (simp add: env_equiv_Abs)
  have compl: "tsubst \<rho> Ts = tsubst \<rho> Tt \<and> (\<forall>(u, v)\<in>set [(ts, tt)]. unifies \<sigma> (tr (inst \<rho> u)) (tr (inst \<rho> v)))"
    if "gsol alg ar (tyenv env) \<rho>" "inst_ok ar W \<rho> bs ?s ?t env" "solution W \<tau>' \<sigma> (instE \<rho> env)"
      "unifies \<sigma> (tr (inst \<rho> ?s)) (tr (inst \<rho> ?t))" for \<rho> W \<tau>' \<sigma>
    using AA_types(1)[OF that(2)] that(4) by (simp add: unifies_def fact5[symmetric])
  have pp: "\<forall>(u, v)\<in>set [(ts, tt)]. ppat u \<and> ppat v" if "ppat ?s" "ppat ?t"
    using that by (auto dest: ppat_AbsD)
  have "prel alg ar A ((nm, Ts) # bs) [(ts, tt)] env1"
    by (rule post_decomp(1)[OF pre te st srt1 tw bl]) (fact iok | fact sound | fact compl | fact pp)+
  then show "pre alg ar A ((nm, Ts) # bs) ts tt env1" by (simp add: prel_single)
  show "post_all alg ar A bs ?s ?t env r" if "post_all alg ar A ((nm, Ts) # bs) ts tt env1 r"
  proof -
    have q: "post_alll alg ar A ((nm, Ts) # bs) [(ts, tt)] env1 r" using that by (simp add: post_alll_single)
    show ?thesis
      by (rule post_decomp(2)[OF pre te st srt1 tw bl]) (fact iok | fact sound | fact compl | fact pp | fact q)+
  qed
qed

lemma post_AA:
  assumes pre: "pre alg ar A bs (pterm.Abs ns Ts ts) (pterm.Abs nt Tt tt) env"
    and r: "unify_types alg Ts Tt env \<bind> f = Some r"
    and IH: "\<And>env' r. f env' = Some r \<Longrightarrow> pre alg ar A ((nm, Ts) # bs) ts tt env' \<Longrightarrow>
      post_all alg ar A ((nm, Ts) # bs) ts tt env' r"
  shows "post_all alg ar A bs (pterm.Abs ns Ts ts) (pterm.Abs nt Tt tt) env r"
proof -
  have twT: "tyw ar (tyenv env) A Ts" "tyw ar (tyenv env) A Tt" using preD(3)[OF pre] by auto
  from preD(1,2)[OF pre] twT show ?thesis
  proof (cases rule: unify_types_cases)
    case (Ok env1)
    note d = AA_decomp[OF pre Ok(2,3,5), where nm = nm]
    have "f env1 = Some r" using r Ok(1) by simp
    from d(2)[OF IH[OF this d(1)]] show ?thesis .
  next
    case (Err u)
    have "r = Err (Unif u)" using r Err(1) by simp
    moreover have "post_all alg ar A bs (pterm.Abs ns Ts ts) (pterm.Abs nt Tt tt) env (Err (Unif u))"
    proof (rule post_all_Unif)
      fix \<rho> W \<tau>' \<sigma> assume "gsol alg ar (tyenv env) \<rho>"
        and "inst_ok ar W \<rho> bs (pterm.Abs ns Ts ts) (pterm.Abs nt Tt tt) env"
      with AA_types(1)[of W \<rho> bs ns Ts ts nt Tt tt env] Err(2) show False by (auto simp: gsol_def)
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma A1_decomp:
  assumes pre: "pre alg ar A bs (pterm.Abs ns Ts ts) t env" and nA: "\<not> is_Abs t"
  shows "pre alg ar A ((ns, Ts) # bs) ts (incr t $ Bound 0) env"
    and "post_all alg ar A ((ns, Ts) # bs) ts (incr t $ Bound 0) env r \<Longrightarrow>
      post_all alg ar A bs (pterm.Abs ns Ts ts) t env r"
proof -
  let ?s = "pterm.Abs ns Ts ts" and ?u = "incr t $ Bound 0"
  note inv = preD(1,2)[OF pre]
  have te: "tenv env = tenv env" ..
  note st = tstep_refl[OF inv(1), of alg "\<lambda>_. True"]
  have tw: "\<forall>T\<in>snd ` set ((ns, Ts) # bs) \<union> ptys [(ts, ?u)]. tyw ar (tyenv env) A T"
    using preD(3)[OF pre] by auto
  have bl: "\<forall>(u, v)\<in>set [(ts, ?u)]. below (maxidx env) u \<and> below (maxidx env) v"
    using preD(4,5)[OF pre] by (simp add: below_def vars_incr)
  have iok: "inst_okl ar W \<rho> ((ns, Ts) # bs) [(ts, ?u)] env"
    if "gsol alg ar (tyenv env) \<rho>" "inst_ok ar W \<rho> bs ?s t env" for \<rho> W
  proof -
    note i = that(2)
    let ?Bs = "map snd (instb \<rho> bs)"
    from inst_okD(7)[OF i] obtain U where "has_type W ?Bs (pterm.Abs ns (tsubst \<rho> Ts) (inst \<rho> ts)) U"
      and tyt: "has_type W ?Bs (inst \<rho> t) U" by auto
    then obtain V where U: "U = tsubst \<rho> Ts \<rightarrow>\<^sub>T V" and tys: "has_type W (tsubst \<rho> Ts # ?Bs) (inst \<rho> ts) V"
      by (auto elim!: has_type_elims)
    have tyu: "has_type W (tsubst \<rho> Ts # ?Bs) (incr (inst \<rho> t) $ Bound 0) V"
      using has_type_incr[OF tyt, of "tsubst \<rho> Ts"] U
      by (intro has_type.App[of _ _ _ "tsubst \<rho> Ts"]) (auto simp: has_type_Bound_iff)
    have wt: "wf_term ar (length bs) (inst \<rho> t)" using inst_okD(6)[OF i] by (simp add: instb_def)
    have "wf_term ar (Suc (length bs)) (incr (inst \<rho> t) $ Bound 0)"
      using wt by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
        intro: no_loose_bound_lift)
    moreover have "ground ar (tsubst \<rho> Ts)" using inst_okD(5)[OF i] by (simp add: wf_term_def)
    ultimately show ?thesis using i tys tyu by (auto simp: inst_ok_def wf_term_def binders_ok_def inst_incr)
  qed
  have sound: "e \<Turnstile> inst \<rho> ?s \<approx> inst \<rho> t"
    if "gsol alg ar (tyenv env) \<rho>" "inst_ok ar W \<rho> bs ?s t env"
      "\<forall>(u, v)\<in>set [(ts, ?u)]. e \<Turnstile> inst \<rho> u \<approx> inst \<rho> v" for \<rho> W e
  proof -
    have "proper (inst \<rho> t)" using inst_okD(6)[OF that(2)] by (simp add: wf_term_def)
    with that(3) show ?thesis by (simp add: inst_incr env_equiv_eta)
  qed
  have compl: "True \<and> (\<forall>(u, v)\<in>set [(ts, ?u)]. unifies \<sigma> (tr (inst \<rho> u)) (tr (inst \<rho> v)))"
    if "gsol alg ar (tyenv env) \<rho>" "inst_ok ar W \<rho> bs ?s t env" "solution W \<tau>' \<sigma> (instE \<rho> env)"
      "unifies \<sigma> (tr (inst \<rho> ?s)) (tr (inst \<rho> t))" for \<rho> W \<tau>' \<sigma>
  proof -
    have wt: "wf_term ar (length bs) (inst \<rho> t)" using inst_okD(6)[OF that(2)] by (simp add: instb_def)
    have "mk_subst \<sigma> (tr (incr (inst \<rho> t) $ Bound 0)) = lift (mk_subst \<sigma> (tr (inst \<rho> t))) 0 \<degree> BVar 0"
      using wt solutionD(1)[OF that(3)]
      by (simp add: wf_term_def incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)
    then show ?thesis using that(4) by (simp add: unifies_def fact6 inst_incr)
  qed
  have pp: "\<forall>(u, v)\<in>set [(ts, ?u)]. ppat u \<and> ppat v" if "ppat ?s" "ppat t"
    using that ppat_incr_Bound0[OF _ nA] by (auto dest: ppat_AbsD)
  have "prel alg ar A ((ns, Ts) # bs) [(ts, ?u)] env"
    by (rule post_decomp(1)[OF pre te st inv(2) tw bl]) (fact iok | fact sound | fact compl | fact pp)+
  then show "pre alg ar A ((ns, Ts) # bs) ts ?u env" by (simp add: prel_single)
  show "post_all alg ar A bs ?s t env r" if "post_all alg ar A ((ns, Ts) # bs) ts ?u env r"
  proof -
    have q: "post_alll alg ar A ((ns, Ts) # bs) [(ts, ?u)] env r" using that by (simp add: post_alll_single)
    show ?thesis
      by (rule post_decomp(2)[OF pre te st inv(2) tw bl]) (fact iok | fact sound | fact compl | fact pp | fact q)+
  qed
qed

lemma post_A1:
  assumes pre: "pre alg ar A bs (pterm.Abs ns Ts ts) t env" and nA: "\<not> is_Abs t"
    and IH: "pre alg ar A ((ns, Ts) # bs) ts (incr t $ Bound 0) env \<Longrightarrow>
      post_all alg ar A ((ns, Ts) # bs) ts (incr t $ Bound 0) env r"
  shows "post_all alg ar A bs (pterm.Abs ns Ts ts) t env r"
  using A1_decomp[OF pre nA] IH by blast

lemma A2_decomp:
  assumes pre: "pre alg ar A bs s (pterm.Abs nt Tt tt) env" and nA: "\<not> is_Abs s"
  shows "pre alg ar A ((nt, Tt) # bs) (incr s $ Bound 0) tt env"
    and "post_all alg ar A ((nt, Tt) # bs) (incr s $ Bound 0) tt env r \<Longrightarrow>
      post_all alg ar A bs s (pterm.Abs nt Tt tt) env r"
proof -
  note p = pre_commute[THEN iffD2, OF pre]
  show "pre alg ar A ((nt, Tt) # bs) (incr s $ Bound 0) tt env"
    using A1_decomp(1)[OF p nA] by (simp add: pre_commute)
  show "post_all alg ar A bs s (pterm.Abs nt Tt tt) env r"
    if "post_all alg ar A ((nt, Tt) # bs) (incr s $ Bound 0) tt env r"
    using A1_decomp(2)[OF p nA, of r] that by (simp add: post_all_commute)
qed

lemma post_A2:
  assumes pre: "pre alg ar A bs s (pterm.Abs nt Tt tt) env" and nA: "\<not> is_Abs s"
    and IH: "pre alg ar A ((nt, Tt) # bs) (incr s $ Bound 0) tt env \<Longrightarrow>
      post_all alg ar A ((nt, Tt) # bs) (incr s $ Bound 0) tt env r"
  shows "post_all alg ar A bs s (pterm.Abs nt Tt tt) env r"
  using A2_decomp[OF pre nA] IH by blast


subsection \<open>The remaining cases\<close>

lemma pre_head_norm_Ok:
  assumes pre: "pre alg ar A bs s t env" and hs: "head_norm env s = Some rs"
  shows "\<exists>s0. rs = Ok s0"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" using gsol_exists[OF preD(1,2)[OF pre]] .
  then have sol: "tsol (tyenv env) \<rho>" by (simp add: gsol_def)
  from preD(6)[OF pre g] obtain W where i: "inst_ok ar W \<rho> bs s t env" by blast
  from inst_okD(7)[OF i] obtain U where "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U" by blast
  from head_norm_no_exn[OF inst_okD(1,2)[OF i] this] pre_head_norm_inst(1)[OF pre sol] hs
  show ?thesis by (cases rs) (auto simp: no_exn_def)
qed

lemma unif_inst_head_norm:
  assumes pre: "pre alg ar A bs s t env" and hs: "head_norm env s = Some (Ok s0)"
    and ht: "head_norm env t = Some (Ok t0)" and sol: "tsol (tyenv env) \<rho>"
  shows "unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) =
    ustep unif alg (instb \<rho> bs) (inst \<rho> s0) (inst \<rho> t0) (instE \<rho> env)"
  using pre_head_norm_inst[OF pre sol] hs ht by (subst unif_ustep) simp

text \<open>The flexible cases relate to the monomorphic algorithm on all instances.\<close>

lemma post_flex:
  assumes pre: "pre alg ar A bs s t env" and hs: "head_norm env s = Some (Ok s0)"
    and ht: "head_norm env t = Some (Ok t0)" and nA: "\<not> is_Abs s0" "\<not> is_Abs t0"
    and fl: "is_Var (fst (strip_comb s0)) \<or> is_Var (fst (strip_comb t0))"
    and r: "flexstep env bs s0 t0 = Some r"
  shows "post_all alg ar A bs s t env r"
proof -
  from pre_head_norm[OF pre hs ht] have pre0: "pre alg ar A bs s0 t0 env" by blast
  show ?thesis
  proof (rule post_inst[OF pre])
    fix \<rho> assume g: "gsol alg ar (tyenv env) \<rho>"
    then have sol: "tsol (tyenv env) \<rho>" by (simp add: gsol_def)
    have fl': "is_Var (fst (strip_comb (inst \<rho> s0))) \<or> is_Var (fst (strip_comb (inst \<rho> t0)))"
      using fl by (simp add: strip_comb_inst)
    have "unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) =
        flexstep (instE \<rho> env) (instb \<rho> bs) (inst \<rho> s0) (inst \<rho> t0)"
      using unif_inst_head_norm[OF pre hs ht sol] ustep_flexstep[OF _ _ fl'] nA by simp
    then show "relJ \<rho> (tfree_on \<rho> (tyenv env)) (instE \<rho>) (Some r)
        (unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env))"
      using flexstep_relJ[OF pre_hyp[OF pre0 sol], of bs] r by simp
  next
    fix env' assume "r = Ok env'"
    with r have fs: "flexstep env bs s0 t0 = Some (Ok env')" by simp
    have P: "\<forall>T\<in>tys s0 \<union> tys t0 \<union> etys env \<union> snd ` set bs. tyw ar (tyenv env) A T"
      using preD(3)[OF pre0] by blast
    show "ext env' env \<and> (\<forall>T\<in>etys env'. tyw ar (tyenv env) A T)"
      using flexstep_ext[OF fs] flexstep_tys[OF fs P tyclosed_tyw[OF preD(1)[OF pre0]]] by blast
  qed
qed

text \<open>Clashes of rigid heads are computed identically on all instances.\<close>

definition same_head :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "same_head h h' \<longleftrightarrow> (\<exists>a T U. h = Const a T \<and> h' = Const a U) \<or> (\<exists>a T U. h = Free a T \<and> h' = Free a U) \<or>
    (\<exists>i. h = Bound i \<and> h' = Bound i)"

lemma ustep_clash:
  assumes "\<not> is_Abs s0" "\<not> is_Abs t0" "strip_comb s0 = (h, ss)" "strip_comb t0 = (h', ts)"
    "\<not> is_Var h" "\<not> is_Var h'" "\<not> same_head h h'"
  shows "ustep uni' alg (instb \<rho> bs) (inst \<rho> s0) (inst \<rho> t0) e = instM \<rho> f (ustep uni alg bs s0 t0 env)"
    and "ustep uni alg bs s0 t0 env \<noteq> Some (Ok env')"
  using assms strip_comb_inst[of \<rho> s0] strip_comb_inst[of \<rho> t0] rigid_clash_inst[of \<rho> bs h h' f]
    not_ok_rigid_clash[of bs h h' env']
  by (cases h; cases h'; simp add: ustep_def same_head_def Let_def)+

lemma post_clash:
  assumes pre: "pre alg ar A bs s t env" and hs: "head_norm env s = Some (Ok s0)"
    and ht: "head_norm env t = Some (Ok t0)"
    and c: "\<not> is_Abs s0" "\<not> is_Abs t0" "strip_comb s0 = (h, ss)" "strip_comb t0 = (h', ts)"
      "\<not> is_Var h" "\<not> is_Var h'" "\<not> same_head h h'"
    and r: "ustep uni alg bs s0 t0 env = Some r"
  shows "post_all alg ar A bs s t env r"
proof (rule post_inst[OF pre])
  fix \<rho> assume "gsol alg ar (tyenv env) \<rho>"
  then have sol: "tsol (tyenv env) \<rho>" by (simp add: gsol_def)
  show "relJ \<rho> (tfree_on \<rho> (tyenv env)) (instE \<rho>) (Some r)
      (unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env))"
    by (rule relJ_eq) (simp add: unif_inst_head_norm[OF pre hs ht sol] ustep_clash(1)[OF c, where uni = uni and f = "instE \<rho>" and env = env] r)
next
  fix env' assume "r = Ok env'"
  with r ustep_clash(2)[OF c, where uni = uni and bs = bs and env = env and env' = env'] show "ext env' env \<and> (\<forall>T\<in>etys env'. tyw ar (tyenv env) A T)"
    by simp
qed

text \<open>Equal rigid heads with types.\<close>

lemma post_rigid_types:
  assumes pre: "pre alg ar A bs s t env"
    and shs: "strip_comb s = (h, ss)" and sht: "strip_comb t = (h', ts)"
    and rh: "is_rigid h" "is_rigid h'" and Ta: "Ta \<in> tys h" and Tb: "Tb \<in> tys h'"
    and hh: "\<And>\<rho>. inst \<rho> h = inst \<rho> h' \<longleftrightarrow> tsubst \<rho> Ta = tsubst \<rho> Tb"
    and r: "unify_types alg Ta Tb env \<bind> (\<lambda>env'. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. f s t e) ps env')) = Some r"
    and IH: "\<And>s t e r. (s, t) \<in> set (zip ss ts) \<Longrightarrow> f s t e = Some r \<Longrightarrow> pre alg ar A bs s t e \<Longrightarrow>
      post_all alg ar A bs s t e r"
  shows "post_all alg ar A bs s t env r"
proof -
  have tw: "tyw ar (tyenv env) A Ta" "tyw ar (tyenv env) A Tb"
    using preD(3)[OF pre] tys_strip_comb[OF shs] tys_strip_comb[OF sht] Ta Tb by auto
  from preD(1,2)[OF pre] tw show ?thesis
  proof (cases rule: unify_types_cases)
    case (Ok env1)
    have st: "tstep alg ar A (\<lambda>\<rho>. inst \<rho> h = inst \<rho> h') (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
      by (rule tstep_mono[OF Ok(3)]) (simp add: hh)
    show ?thesis
    proof (rule post_rigid[OF pre shs sht rh Ok(2) st Ok(5)])
      show "inst \<rho> h = inst \<rho> h'" if "gsol alg ar (tyenv env1) \<rho>" for \<rho>
        using Ok(4) that by (simp add: gsol_def hh)
      show "zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. f s t e) ps env1) = Some r" using r Ok(1) by simp
    qed (rule IH)
  next
    case (Err u)
    have "r = Err (Unif u)" using r Err(1) by simp
    moreover have "post_all alg ar A bs s t env (Err (Unif u))"
    proof (rule post_all_Unif)
      fix \<rho> W \<tau>' \<sigma> assume g: "gsol alg ar (tyenv env) \<rho>" and "inst_ok ar W \<rho> bs s t env"
        and sol: "solution W \<tau>' \<sigma> (instE \<rho> env)" and uu: "unifies \<sigma> (tr (inst \<rho> s)) (tr (inst \<rho> t))"
      have "strip_comb (inst \<rho> s) = (inst \<rho> h, map (inst \<rho>) ss)" "strip_comb (inst \<rho> t) = (inst \<rho> h', map (inst \<rho>) ts)"
        using strip_comb_inst[of \<rho> s] strip_comb_inst[of \<rho> t] shs sht by simp_all
      moreover have "is_rigid (inst \<rho> h)" "is_rigid (inst \<rho> h')" using rh by (auto simp: is_rigid_def)
      ultimately have "inst \<rho> h = inst \<rho> h'" using rigid_unifies(1)[OF _ _ _ _ sol uu] by blast
      with Err(2) g hh show False by (simp add: gsol_def)
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma pre_Bound_rigid:
  assumes pre: "pre alg ar A bs s t env" and sc: "strip_comb s = (Bound i, ss)"
  shows "is_rigid (Bound i)"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" using gsol_exists[OF preD(1,2)[OF pre]] .
  from preD(6)[OF pre g] obtain W where i: "inst_ok ar W \<rho> bs s t env" by blast
  have "wf_term ar (length (instb \<rho> bs)) (inst \<rho> s)" by (rule inst_okD(5)[OF i])
  then have "proper (Bound i)"
    using strip_comb_list_comb[OF sc] by (simp add: inst_list_comb wf_term_list_comb) (simp add: wf_term_def)
  then show ?thesis by (simp add: is_rigid_def)
qed


subsection \<open>Partial correctness\<close>

theorem unif_post:
  assumes "unif alg' bs s t env = Some r" "alg' = alg" "pre alg ar A bs s t env"
  shows "post_all alg ar A bs s t env r"
  using assms
proof (induction alg' bs s t env r rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg' bs s t env r)
  have pre: "pre alg ar A bs s t env" using "1.prems" by simp
  have IH: "post_all alg ar A bs' s' t' e r'"
    if "uni alg bs' s' t' e = Some r'" "pre alg ar A bs' s' t' e" for bs' s' t' e r'
    using "1.IH"[of alg bs' s' t' e r'] that by simp
  have u: "head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. ustep uni alg bs s' t' env)) = Some r"
    using "1.hyps" "1.prems"(1) unfolding ustep_def by (simp only:)
  from u obtain rs where hs: "head_norm env s = Some rs" by (cases "head_norm env s") (auto simp: bindM_def)
  from pre_head_norm_Ok[OF pre hs] obtain s0 where rs: "rs = Ok s0" by blast
  from u hs rs obtain rt where ht: "head_norm env t = Some rt"
    by (cases "head_norm env t") (auto simp: bindM_def)
  from pre_head_norm_Ok[OF pre_commute[THEN iffD2, OF pre] ht] obtain t0 where rt: "rt = Ok t0" by blast
  note hs = hs[unfolded rs] and ht = ht[unfolded rt]
  from u hs ht have ust: "ustep uni alg bs s0 t0 env = Some r" by simp
  from pre_head_norm[OF pre hs ht] have pre0: "pre alg ar A bs s0 t0 env" by blast
  note lift = post_head_norm[OF pre hs ht]
  show ?case
  proof (cases "is_Abs s0")
    case sA: True
    then obtain ns Ts ts where s0a: "s0 = pterm.Abs ns Ts ts" by (cases s0) auto
    show ?thesis
    proof (cases "is_Abs t0")
      case True
      then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
      define nm where "nm = (if ns = STR '''' then nt else ns)"
      from ust have "unify_types alg Ts Tt env \<bind> (\<lambda>env'. uni alg ((nm, Ts) # bs) ts tt env') = Some r"
        by (simp add: ustep_def s0a t0a Let_def nm_def)
      from post_AA[OF pre0[unfolded s0a t0a] this IH] show ?thesis by (intro lift) (simp add: s0a t0a)
    next
      case False
      from ust have "uni alg ((ns, Ts) # bs) ts (incr t0 $ Bound 0) env = Some r"
        by (simp add: ustep_def s0a False)
      with post_A1[OF pre0[unfolded s0a] False] IH show ?thesis by (intro lift) (simp add: s0a)
    qed
  next
    case nsA: False
    show ?thesis
    proof (cases "is_Abs t0")
      case True
      then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
      from ust nsA have "uni alg ((nt, Tt) # bs) (incr s0 $ Bound 0) tt env = Some r"
        by (simp add: ustep_def t0a)
      with post_A2[OF pre0[unfolded t0a] nsA] IH show ?thesis by (intro lift) (simp add: t0a)
    next
      case nAt: False
      obtain hs' ss where shs: "strip_comb s0 = (hs', ss)" by force
      obtain ht' ts where sht: "strip_comb t0 = (ht', ts)" by force
      consider (Flex) "is_Var hs' \<or> is_Var ht'" | (Clash) "\<not> is_Var hs'" "\<not> is_Var ht'" "\<not> same_head hs' ht'"
        | (Rigid) "\<not> is_Var hs'" "\<not> is_Var ht'" "same_head hs' ht'"
        by blast
      then show ?thesis
      proof cases
        case Flex
        then have fl: "is_Var (fst (strip_comb s0)) \<or> is_Var (fst (strip_comb t0))" using shs sht by simp
        have "flexstep env bs s0 t0 = Some r" using ust ustep_flexstep[OF nsA nAt fl] by simp
        from post_flex[OF pre hs ht nsA nAt fl this] show ?thesis .
      next
        case Clash
        show ?thesis by (rule post_clash[OF pre hs ht nsA nAt shs sht Clash ust])
      next
        case Rigid
        from Rigid(3) consider (C) a Ta Tb where "hs' = Const a Ta" "ht' = Const a Tb"
          | (F) a Ta Tb where "hs' = Free a Ta" "ht' = Free a Tb" | (B) i where "hs' = Bound i" "ht' = Bound i"
          by (auto simp: same_head_def)
        then show ?thesis
        proof cases
          case C
          from ust have r: "unify_types alg Ta Tb env \<bind> (\<lambda>env'. zip_eq ss ts \<bind>
              (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg bs s t e) ps env')) = Some r"
            by (simp add: ustep_def nsA nAt shs sht C Let_def)
          have "post_all alg ar A bs s0 t0 env r"
            by (rule post_rigid_types[OF pre0 shs sht _ _ _ _ _ r]) (auto simp: C is_rigid_def intro: IH)
          then show ?thesis by (rule lift)
        next
          case F
          from ust have r: "unify_types alg Ta Tb env \<bind> (\<lambda>env'. zip_eq ss ts \<bind>
              (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg bs s t e) ps env')) = Some r"
            by (simp add: ustep_def nsA nAt shs sht F Let_def)
          have "post_all alg ar A bs s0 t0 env r"
            by (rule post_rigid_types[OF pre0 shs sht _ _ _ _ _ r]) (auto simp: F is_rigid_def intro: IH)
          then show ?thesis by (rule lift)
        next
          case B
          from ust have r: "zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg bs s t e) ps env) = Some r"
            by (simp add: ustep_def nsA nAt shs sht B Let_def)
          have rig: "is_rigid (Bound i)" by (rule pre_Bound_rigid[OF pre0 shs[unfolded B(1)]])
          have "post_all alg ar A bs s0 t0 env r"
          proof (rule post_rigid[OF pre0 shs sht _ _ refl tstep_refl[OF preD(1)[OF pre0]] preD(2)[OF pre0]])
            show "is_rigid hs'" "is_rigid ht'" using rig B by simp_all
            show "inst \<rho> hs' = inst \<rho> ht'" for \<rho> using B by simp
            show "zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg bs s t e) ps env) = Some r" by (rule r)
          qed (rule IH)
          then show ?thesis by (rule lift)
        qed
      qed
    qed
  qed
qed

end

end
