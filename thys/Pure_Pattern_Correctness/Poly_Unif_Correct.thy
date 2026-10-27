section \<open>Correctness of Polymorphic Unification\<close>

theory Poly_Unif_Correct
  imports Poly_Unif
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

end
