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

end
