section \<open>Soundness of the Search\<close>

theory Unify_Pull_Sound
  imports Unify_Match_Sound Unify_Flexflex_Sound
begin

context pure_sig
begin

text \<open>
  Every unifier that \<open>hounifiers\<close> enumerates is a step from the input problem to its flex-flex
  pairs (\<^const>\<open>dstep\<close>). The elements produced by pulling a sequence are elements in the sense of
  \<^const>\<open>ev\<close>, and the elements of a sequence satisfying the invariant \<^const>\<open>sinv\<close> satisfy the
  invariant of their goal (\<^const>\<open>elem_ok\<close>).
\<close>

subsection \<open>Pulling yields elements\<close>

lemma addunify_cases':
  assumes "okW (handleW
    (bindW (whenW b1 (emit e1)) (\<lambda>_. bindW (SIMPL alg' env dps) (\<lambda>(env', ffs, frs).
      case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg') ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R))))
    (\<lambda>e. case e of CANTUNIFY \<Rightarrow> bindW (whenW b4 (emit e4)) (\<lambda>_. Q) | _ \<Rightarrow> raiseW e)) z"
  shows "okW Q z \<or>
    (\<exists>env' ffs env'' tps. okW (SIMPL alg' env dps) (env', ffs, []) \<and>
      okW (foldrW (add_ffpair alg') ffs (env', [])) (env'', tps) \<and> z = Some (El_R env'' tps, reseq)) \<or>
    (\<exists>env' ffs dp frigid' ms. okW (SIMPL alg' env dps) (env', ffs, dp # frigid') \<and> \<not> b2 \<and>
      okW (MATCH cfg env' dp (frigid' @ ffs)) ms \<and> okW (R ms) z)"
proof -
  from okW_handle_CANTUNIFY[OF assms] show ?thesis
  proof (elim disjE)
    assume "okW (bindW (whenW b1 (emit e1)) (\<lambda>_. bindW (SIMPL alg' env dps) (\<lambda>(env', ffs, frs).
      case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg') ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)))) z"
    from okW_bind_triple[OF okW_whenW_then[OF this]] obtain env' ffs frs where
      S: "okW (SIMPL alg' env dps) (env', ffs, frs)"
      and c: "okW (case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg') ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)) z"
      by blast
    show ?thesis
    proof (cases frs)
      case Nil
      with c obtain r where r: "okW (foldrW (add_ffpair alg') ffs (env', [])) r"
        "z = Some (El_R (fst r) (snd r), reseq)" by auto
      obtain env'' tps where "r = (env'', tps)" by (cases r)
      with r have "okW (foldrW (add_ffpair alg') ffs (env', [])) (env'', tps)"
        "z = Some (El_R env'' tps, reseq)" by simp_all
      with S Nil show ?thesis by blast
    next
      case (Cons dp frigid')
      show ?thesis
      proof (cases b2)
        case True
        with c Cons have "okW Q z" by (auto dest: okW_emit_then)
        then show ?thesis by blast
      next
        case False
        with c Cons have "okW (bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)) z" by simp
        from okW_whenW_then[OF this] obtain ms where "okW (MATCH cfg env' dp (frigid' @ ffs)) ms"
          "okW (R ms) z" unfolding okW_bindW by blast
        with S Cons False show ?thesis by blast
      qed
    qed
  next
    assume "okW (bindW (whenW b4 (emit e4)) (\<lambda>_. Q)) z"
    from okW_whenW_then[OF this] show ?thesis by blast
  qed
qed


lemma ev_split:
  "ev cfg s x \<Longrightarrow>
    (\<forall>td env dps R. s = S_AddUnify td env dps R \<longrightarrow> ev cfg R x \<or> (\<forall>R'. ev cfg (S_AddUnify td env dps R') x)) \<and>
    (\<forall>td ms R. s = S_ItRight td ms R \<longrightarrow> ev cfg R x \<or> (\<forall>R'. ev cfg (S_ItRight td ms R') x))"
proof (induction rule: ev.induct)
  case (au_res env dps env' ffs r td reseq)
  then show ?case by (auto intro: ev.au_res)
next
  case (au_match env dps env' ffs dp frs td ms reseq x)
  then show ?case by (auto intro: ev.au_match)
next
  case (ir_head xq env dps td x yq)
  then show ?case by (auto intro: ev.ir_head)
qed auto

lemma ev_AddUnify_split:
  "ev cfg (S_AddUnify td env dps R) x \<Longrightarrow> ev cfg R x \<or> (\<forall>R'. ev cfg (S_AddUnify td env dps R') x)"
  using ev_split by blast

lemma ev_ItRight_mono:
  assumes "ev cfg (S_ItRight td q yq) z" "\<And>y. ev cfg q y \<Longrightarrow> ev cfg xq y"
  shows "ev cfg (S_ItRight td xq yq) z"
  using assms(1)
proof (rule ev_ItRightE)
  assume "ev cfg yq z"
  then show ?thesis by (rule ev.ir_tail)
next
  fix env dps assume "ev cfg q (El_E env dps)" "\<And>R. ev cfg (S_AddUnify td env dps R) z"
  then show ?thesis by (intro ev.ir_head[of cfg xq env dps td z yq]) (auto intro: assms(2))
qed

lemma ev_Maps_mono:
  "ev cfg (S_Maps vname rb targs uarg q) z \<Longrightarrow> (\<And>y. ev cfg q y \<Longrightarrow> ev cfg xq y) \<Longrightarrow>
    ev cfg (S_Maps vname rb targs uarg xq) z"
  by (erule ev_MapsE) (auto intro: ev.intros)

lemma okW_some: "okW m r \<Longrightarrow> \<exists>evs. m = Some (evs, UOk r)"
  by blast

lemma pull_some_ev:
  assumes "pull cfg s = Some r"
  shows "snd r = UOk (Some (x, s')) \<Longrightarrow> ev cfg s x \<and> (\<forall>y. ev cfg s' y \<longrightarrow> ev cfg s y)"
  using assms
proof (induction cfg s r arbitrary: x s' rule: pull.raw_induct[rotated, consumes 1])
  case (1 P cfg s r)
  have IH: "ev cfg s1 x \<and> (\<forall>y. ev cfg s' y \<longrightarrow> ev cfg s1 y)" if "okW (P cfg s1) (Some (x, s'))" for s1 x s'
  proof -
    from that obtain evs where "P cfg s1 = Some (evs, UOk (Some (x, s')))" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  note hyps = okW_of[OF "1.hyps" "1.prems"]
  show ?case
  proof (cases s)
    case S_Empty
    with hyps show ?thesis by simp
  next
    case (S_Single y)
    with hyps show ?thesis by (auto intro: ev.single elim: ev_EmptyE)
  next
    case (S_AddUnify td env dps reseq)
    note h = hyps[unfolded S_AddUnify seq.case]
    from addunify_cases'[OF h]
    consider (fail) "okW (P cfg reseq) (Some (x, s'))"
      | (fin) env' ffs env'' tps where "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, [])"
        "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) (env'', tps)"
        "Some (x, s') = Some (El_R env'' tps, reseq)"
      | (mtch) env' ffs dp frs ms where "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)"
        "\<not> td > cfg_search_bound cfg" "okW (MATCH cfg env' dp (frs @ ffs)) ms"
        "okW (P cfg (S_ItRight (td + 1) ms reseq)) (Some (x, s'))"
      by blast
    then show ?thesis
    proof cases
      case fail
      from IH[OF this] show ?thesis by (auto simp: S_AddUnify intro: ev.au_tail)
    next
      case (fin env' ffs env'' tps)
      from ev.au_res[OF fin(1,2), of td reseq] fin(3) show ?thesis
        by (auto simp: S_AddUnify intro: ev.au_tail)
    next
      case (mtch env' ffs dp frs ms)
      from IH[OF mtch(4)] ev.au_match[OF mtch(1) mtch(2) mtch(3)] show ?thesis
        by (auto simp: S_AddUnify)
    qed
  next
    case (S_ItRight td xq yq)
    from okW_bind_E[OF hyps[unfolded S_ItRight seq.case]]
    consider (n) "okW (P cfg xq) None" "okW (P cfg yq) (Some (x, s'))"
      | (s) a b q where "okW (P cfg xq) (Some (El_E a b, q))"
        "okW (P cfg (S_AddUnify td a b (S_ItRight td q yq))) (Some (x, s'))"
      by blast
    then show ?thesis
    proof cases
      case n
      from IH[OF n(2)] show ?thesis by (auto simp: S_ItRight intro: ev.ir_tail)
    next
      case (s a b q)
      note I1 = IH[OF s(1)] and I2 = IH[OF s(2)]
      have lift: "ev cfg (S_ItRight td xq yq) z" if "ev cfg (S_AddUnify td a b (S_ItRight td q yq)) z" for z
      proof -
        from ev_AddUnify_split[OF that] show ?thesis
        proof
          assume "ev cfg (S_ItRight td q yq) z"
          from ev_ItRight_mono[OF this] I1 show ?thesis by blast
        next
          assume "\<forall>R'. ev cfg (S_AddUnify td a b R') z"
          from ev.ir_head[of cfg xq a b td z yq] I1 this show ?thesis by blast
        qed
      qed
      from I2 lift show ?thesis by (auto simp: S_ItRight)
    qed
  next
    case (S_MapNewDset vT Ts xq)
    from okW_bind_opt_C[OF hyps[unfolded S_MapNewDset seq.case]]
    obtain b e d q y where s1: "okW (P cfg xq) (Some (El_C b e d, q))"
      and nd: "okW (new_dset vT Ts b e d) y" and xs: "x = y" "s' = S_MapNewDset vT Ts q"
      by auto
    note I = IH[OF s1]
    have "ev cfg (S_MapNewDset vT Ts xq) z" if "ev cfg (S_MapNewDset vT Ts q) z" for z
      using that by (rule ev_MapNewDsetE) (use I in \<open>auto intro: ev.new_dset\<close>)
    with I nd xs show ?thesis by (auto simp: S_MapNewDset intro: ev.new_dset)
  next
    case (S_MapAbs a T xq)
    from okW_bind_opt_C[OF hyps[unfolded S_MapAbs seq.case]]
    obtain b e d q where s1: "okW (P cfg xq) (Some (El_C b e d, q))"
      and xs: "x = El_C (Abs a T b) e d" "s' = S_MapAbs a T q"
      by auto
    note I = IH[OF s1]
    have "ev cfg (S_MapAbs a T xq) z" if "ev cfg (S_MapAbs a T q) z" for z
      using that by (rule ev_MapAbsE) (use I in \<open>auto intro: ev.map_abs\<close>)
    with I xs show ?thesis by (auto simp: S_MapAbs intro: ev.map_abs)
  next
    case (S_Proj vname env Ts Us targs rb u dpairs head targ tail)
    note h = hyps[unfolded S_Proj seq.case]
    from okW_handle_CANTUNIFY[OF h]
    consider (fail) "okW (P cfg tail) (Some (x, s'))"
      | (ok) "okW (let (env', args) = make_args vname Ts env Us;
            dp = (rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) in
          do {st \<leftarrow> SIMPL (cfg_alg cfg) env' (dp # dpairs);
            case st of (env2, frigid, fflex) \<Rightarrow>
              returnW (Some (El_C (list_comb head args) env2 (frigid @ fflex), tail))}) (Some (x, s'))"
      by blast
    then show ?thesis
    proof cases
      case fail
      from IH[OF this] show ?thesis by (auto simp: S_Proj intro: ev.proj_tail)
    next
      case ok
      obtain env' args where ma: "make_args vname Ts env Us = (env', args)" by fastforce
      from ok ma obtain env2 frigid fflex where
        S: "okW (SIMPL (cfg_alg cfg) env' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs))
          (env2, frigid, fflex)"
        and xs: "x = El_C (list_comb head args) env2 (frigid @ fflex)" "s' = tail"
        by (auto simp: Let_def)
      from xs show ?thesis by (auto simp: S_Proj intro: ev.proj[OF ma S] ev.proj_tail)
    qed
  next
    case (S_MapJoin uhead xq)
    from okW_bind_opt_D[OF hyps[unfolded S_MapJoin seq.case]]
    obtain b e d q where s1: "okW (P cfg xq) (Some (El_D b e d, q))"
      and xs: "x = El_C (list_comb uhead b) e d" "s' = S_MapJoin uhead q"
      by auto
    note I = IH[OF s1]
    have "ev cfg (S_MapJoin uhead xq) z" if "ev cfg (S_MapJoin uhead q) z" for z
      using that by (rule ev_MapJoinE) (use I in \<open>auto intro: ev.map_join\<close>)
    with I xs show ?thesis by (auto simp: S_MapJoin intro: ev.map_join)
  next
    case (S_Maps vname rb targs uarg xq)
    from okW_bind_opt_D[OF hyps[unfolded S_Maps seq.case]]
    obtain b e d q cs where s1: "okW (P cfg xq) (Some (El_D b e d, q))"
      and cc: "okW (copycons cfg vname rb targs uarg b e d) cs"
      and s2: "okW (P cfg (S_Append cs (S_Maps vname rb targs uarg q))) (Some (x, s'))"
      by auto
    note I1 = IH[OF s1] and I2 = IH[OF s2]
    have lift: "ev cfg (S_Maps vname rb targs uarg xq) z" if "ev cfg (S_Append cs (S_Maps vname rb targs uarg q)) z" for z
      using that
    proof (rule ev_AppendE)
      assume "ev cfg cs z"
      from ev.maps[OF I1[THEN conjunct1] cc this] show ?thesis .
    next
      assume "ev cfg (S_Maps vname rb targs uarg q) z"
      from ev_Maps_mono[OF this] I1 show ?thesis by blast
    qed
    from I2 lift show ?thesis by (auto simp: S_Maps)
  next
    case (S_Append xq yq)
    from okW_bind_opt[OF hyps[unfolded S_Append seq.case]]
    consider (n) "okW (P cfg xq) None" "okW (P cfg yq) (Some (x, s'))"
      | (s) q where "okW (P cfg xq) (Some (x, q))" "s' = S_Append q yq"
      by auto
    then show ?thesis
    proof cases
      case n
      from IH[OF n(2)] show ?thesis by (auto simp: S_Append intro: ev.append_r)
    next
      case (s q)
      note I = IH[OF s(1)]
      have "ev cfg (S_Append xq yq) z" if "ev cfg (S_Append q yq) z" for z
        using that by (rule ev_AppendE) (use I in \<open>auto intro: ev.append_l ev.append_r\<close>)
      with I s(2) show ?thesis by (auto simp: S_Append intro: ev.append_l)
    qed
  next
    case (S_MapCons uargs xq)
    from okW_bind_opt_C[OF hyps[unfolded S_MapCons seq.case]]
    obtain b e d q where s1: "okW (P cfg xq) (Some (El_C b e d, q))"
      and xs: "x = El_D (b # uargs) e d" "s' = S_MapCons uargs q"
      by auto
    note I = IH[OF s1]
    have "ev cfg (S_MapCons uargs xq) z" if "ev cfg (S_MapCons uargs q) z" for z
      using that by (rule ev_MapConsE) (use I in \<open>auto intro: ev.map_cons\<close>)
    with I xs show ?thesis by (auto simp: S_MapCons intro: ev.map_cons)
  qed
qed

text \<open>The elements of a complete enumeration are elements of the sequence:\<close>

lemma evals_ev_set: "evals cfg s xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> ev cfg s x"
proof (induction rule: evals.induct)
  case (Cons s evs y s' xs)
  note p = pull_some_ev[OF Cons.hyps(1), of y s', simplified]
  show ?case
  proof (cases "x = y")
    case True
    with p show ?thesis by simp
  next
    case False
    with Cons.prems have "x \<in> set xs" by simp
    with Cons.IH p show ?thesis by blast
  qed
qed simp



subsection \<open>The elements of sequences satisfying the invariant\<close>

inductive_cases sinv_SingleE: "sinv G (S_Single x)"
inductive_cases sinv_AddUnifyE: "sinv G (S_AddUnify td env dps reseq)"
inductive_cases sinv_ItRightE: "sinv G (S_ItRight td xq yq)"
inductive_cases sinv_MapNewDsetE: "sinv G (S_MapNewDset vT Ts xq)"
inductive_cases sinv_MapAbsE: "sinv G (S_MapAbs a T xq)"
inductive_cases sinv_ProjE: "sinv G (S_Proj vname env Ts Us targs rb u dps head targ tail)"
inductive_cases sinv_MapJoinE: "sinv G (S_MapJoin uhead xq)"
inductive_cases sinv_MapsE: "sinv G (S_Maps vname rb targs uarg xq)"
inductive_cases sinv_AppendE: "sinv G (S_Append xq yq)"
inductive_cases sinv_MapConsE: "sinv G (S_MapCons uargs xq)"

lemma sinv_hounifiers: "sinv (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) (hounifiers rb env tus)"
  unfolding hounifiers_def by (rule sinv.AddUnify[OF dstep_refl sinv.Empty])

text \<open>
  The soundness of the search rests on two properties of the model that are stated as
  hypotheses: \<open>SIMPL\<close> returns flex-rigid pairs that satisfy the hypothesis \<^const>\<open>MATCH_ok\<close> of
  \<^const>\<open>MATCH\<close>, and the normalization of an argument in \<^const>\<open>copycons\<close> yields a saturated
  term (\<^const>\<open>satd\<close>).
\<close>

context
  assumes match_hyp: "\<And>alg' env dps env' ffs dp frs. okW (SIMPL alg' env dps) (env', ffs, dp # frs) \<Longrightarrow>
    MATCH_ok env' dp"
    and eta_hyp: "\<And>env rb t u1 u2. ok (head_norm env t) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow> satd env rb u2"
begin

theorem ev_sound: "ev cfg s x \<Longrightarrow> sinv G s \<Longrightarrow> elem_ok G x"
proof (induction arbitrary: G rule: ev.induct)
  case (single x)
  then show ?case by (auto elim: sinv_SingleE)
next
  case (au_tail reseq x td env dps)
  from au_tail.prems show ?case by (rule sinv_AddUnifyE) (auto intro: au_tail.IH)
next
  case (au_res env dps env' ffs r td reseq)
  from au_res.prems obtain env0 dps0 where G: "G = GR env0 dps0" and d0: "dstep env0 dps0 env dps"
    by (rule sinv_AddUnifyE) blast
  have d1: "dstep env dps env' ffs" using SIMPL_sound[OF au_res.hyps(1)] by simp
  have d2: "dstep env' ffs (fst r) (tdps (snd r))"
    using foldrW_add_ffpair_sound[of "cfg_alg cfg" ffs env' "[]" "fst r" "snd r"] au_res.hyps(2) by simp
  show ?case using dstep_trans[OF dstep_trans[OF d0 d1] d2] by (simp add: G)
next
  case (au_match env dps env' ffs dp frs td ms reseq x)
  from au_match.prems obtain env0 dps0 where G: "G = GR env0 dps0" and d0: "dstep env0 dps0 env dps"
    and rs: "sinv (GR env0 dps0) reseq"
    by (rule sinv_AddUnifyE) blast
  have d1: "dstep env dps env' (dp # frs @ ffs)" using SIMPL_sound[OF au_match.hyps(1)] by simp
  have "sinv (GE env' (dp # frs @ ffs)) ms" by (rule MATCH_sound[OF au_match.hyps(3) match_hyp[OF au_match.hyps(1)]])
  from sinv_GE_dstep[OF this refl dstep_trans[OF d0 d1]]
  have "sinv (GR env0 dps0) (S_ItRight (td + 1) ms reseq)" by (rule sinv.ItRight[OF _ rs])
  with au_match.IH show ?case by (simp add: G)
next
  case (ir_tail yq x td xq)
  from ir_tail.prems show ?case by (rule sinv_ItRightE) (auto intro: ir_tail.IH)
next
  case (ir_head xq env dps td x yq)
  from ir_head.prems obtain env0 dps0 where G: "G = GR env0 dps0" and xs: "sinv (GE env0 dps0) xq"
    by (rule sinv_ItRightE) blast
  from ir_head.IH(1)[OF xs] have "dstep env0 dps0 env dps" by simp
  then have "sinv (GR env0 dps0) (S_AddUnify td env dps S_Empty)" by (rule sinv.AddUnify[OF _ sinv.Empty])
  from ir_head.IH(2)[OF this] show ?case by (simp add: G)
next
  case (new_dset xq u' env' dps' vT Ts y)
  from new_dset.prems show ?case
  proof (rule sinv_MapNewDsetE)
    fix env0 dps0 env1 rb t u dps1 v T targs
    assume G: "G = GE env0 dps0" and vT: "vT = (v, T)" and d0: "dstep env0 dps0 env1 ((rb, t, u) # dps1)"
      and st: "strip_comb t = (Var v T, targs)" and ta: "targs_ok env1 rb t targs Ts"
      and xs: "sinv (GC env1 rb targs Ts u dps1) xq"
    from new_dset.IH[OF xs] have "astep env1 rb targs Ts [u] dps1 [u'] env' dps'" by simp
    from new_dset_sound[OF new_dset.hyps(2)[unfolded vT] d0 st ta this] show ?thesis by (simp add: G)
  next
    fix env0 dps0 env1 dps1 v T
    assume G: "G = GE env0 dps0" and vT: "vT = (v, T)" and d0: "dstep env0 dps0 env1 dps1"
      and vin: "(v, T) \<in> dvars dps1" and xs: "sinv (GS env1 dps1 Ts T) xq"
    from new_dset.IH[OF xs] have "sstep env1 dps1 Ts T u' env' dps'" by simp
    from new_dset_sound1[OF new_dset.hyps(2)[unfolded vT] d0 vin this] show ?thesis by (simp add: G)
  qed
next
  case (map_abs xq body' env' dps' a T)
  from map_abs.prems show ?case
  proof (rule sinv_MapAbsE)
    fix env0 rb targs Ts body dps0
    assume G: "G = GC env0 rb targs Ts (Abs a T body) dps0"
      and xs: "sinv (GC env0 ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) (Ts @ [T]) body dps0) xq"
    from map_abs.IH[OF xs] astep_abs show ?thesis by (simp add: G)
  qed
next
  case (proj vname Ts env Us env' args rb targ targs u dpairs env2 frigid fflex head tail)
  from proj.prems show ?case
  proof (rule sinv_ProjE)
    fix env0 Ts0 assume G: "G = GC env0 rb targs Ts0 u dpairs"
      and po: "proj_ok env0 rb targs Ts0 u env Ts Us head targ"
    from astep_proj[OF po proj.hyps(1,2)] show ?thesis by (simp add: G)
  qed
next
  case (proj_tail tail x vname env Ts Us targs rb u dpairs head targ)
  from proj_tail.prems show ?case by (rule sinv_ProjE) (auto intro: proj_tail.IH)
next
  case (map_join xq uargs' env' dps' uhead)
  from map_join.prems show ?case
  proof (rule sinv_MapJoinE)
    fix env0 rb targs Ts uargs dps0
    assume G: "G = GC env0 rb targs Ts (uhead \<degree>\<degree> uargs) dps0" and c: "closed uhead" and vh: "vars uhead = {}"
      and xs: "sinv (GD env0 rb targs Ts uargs dps0) xq"
    from map_join.IH[OF xs] have "astep env0 rb targs Ts uargs dps0 uargs' env' dps'" by simp
    from astep_join[OF this c vh] show ?thesis by (simp add: G list_comb_apps)
  qed
next
  case (maps xq uargs env dps vname rb targs uarg cs x)
  from maps.prems show ?case
  proof (rule sinv_MapsE)
    fix env0 Ts uargs0 dps0
    assume G: "G = GD env0 rb targs Ts (uarg # uargs0) dps0" and xs: "sinv (GD env0 rb targs Ts uargs0 dps0) xq"
    from maps.IH(1)[OF xs] have "astep env0 rb targs Ts uargs0 dps0 uargs env dps" by simp
    from copycons_sinv[OF maps.hyps(2) this eta_hyp] maps.IH(2) show ?thesis by (simp add: G)
  qed
next
  case (append_l xq x yq)
  from append_l.prems show ?case by (rule sinv_AppendE) (rule append_l.IH)
next
  case (append_r yq x xq)
  from append_r.prems show ?case by (rule sinv_AppendE) (rule append_r.IH)
next
  case (map_cons xq uarg' env' dps' uargs)
  from map_cons.prems show ?case
  proof (rule sinv_MapConsE)
    fix env0 rb targs Ts uargs0 dps0 env dps uarg u2
    assume G: "G = GD env0 rb targs Ts (uarg # uargs0) dps0"
      and a: "astep env0 rb targs Ts uargs0 dps0 uargs env dps" and tc: "tconv env rb uarg u2"
      and xs: "sinv (GC env rb targs Ts u2 dps) xq"
    from map_cons.IH[OF xs] have "astep env rb targs Ts [u2] dps [uarg'] env' dps'" by simp
    from astep_cons[OF a tc this] show ?thesis by (simp add: G)
  qed
qed

text \<open>Pulling a sequence yields an element of its goal, and the rest of the sequence has only such
  elements:\<close>

theorem pull_sound:
  assumes "pull cfg s = Some (evs, UOk (Some (x, s')))" "sinv G s"
  shows "elem_ok G x" "ev cfg s' y \<Longrightarrow> elem_ok G y"
  using pull_some_ev[OF assms(1)] ev_sound[OF _ assms(2)] by auto

text \<open>Every unifier enumerated by \<open>hounifiers\<close> is a step from the input pairs to its flex-flex pairs:\<close>

theorem hounifiers_sound:
  assumes "evals cfg (hounifiers rb env tus) xs" "x \<in> set xs"
  shows "\<exists>env' tps. x = El_R env' tps \<and> dstep env (map (\<lambda>(t, u). (rb, t, u)) tus) env' (tdps tps)"
proof -
  have "elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x"
    by (rule ev_sound[OF evals_ev_set[OF assms] sinv_hounifiers])
  then show ?thesis by (cases x) auto
qed

end

end

end
