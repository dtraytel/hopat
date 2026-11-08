section \<open>Soundness of the Search\<close>

theory Unify_Pull_Sound
  imports Unify_Shape_Sound Unify_Flexflex_Sound
begin

context pure_sig
begin

text \<open>
  The elements produced by pulling a sequence are elements in the sense of \<^const>\<open>ev\<close>, and the
  elements of a sequence of \<open>MATCH\<close> satisfying the invariant \<^const>\<open>seqinv\<close> satisfy the invariant
  of their goal (\<^const>\<open>elem_ok\<close>). Together with the invariant of the termination proof, which
  gives the hypothesis of \<open>MATCH\<close>, this yields the soundness of the search (theory
  \<open>Unify_Pull_Fin\<close>).
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
  "ev cfg (S_Maps vname env0 rb targs G uarg q) z \<Longrightarrow> (\<And>y. ev cfg q y \<Longrightarrow> ev cfg xq y) \<Longrightarrow>
    ev cfg (S_Maps vname env0 rb targs G uarg xq) z"
  by (erule ev_MapsE) (auto intro: ev.intros)

lemma pull_some_ev:
  assumes "pull cfg s = Some r"
  shows "snd r = Ok (Some (x, s')) \<Longrightarrow> ev cfg s x \<and> (\<forall>y. ev cfg s' y \<longrightarrow> ev cfg s y)"
  using assms
proof (induction cfg s r arbitrary: x s' rule: pull.raw_induct[rotated, consumes 1])
  case (1 P cfg s r)
  have IH: "ev cfg s1 x \<and> (\<forall>y. ev cfg s' y \<longrightarrow> ev cfg s1 y)" if "okW (P cfg s1) (Some (x, s'))" for s1 x s'
  proof -
    from that obtain evs where "P cfg s1 = Some (evs, Ok (Some (x, s')))" by blast
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
    case (S_Proj vname env Ts Us targs rb u dpairs head targ X tail)
    note h = hyps[unfolded S_Proj seq.case]
    from okW_handle_CANTUNIFY[OF h]
    consider (fail) "okW (P cfg tail) (Some (x, s'))"
      | (ok) "okW (let (env', args) = make_args vname Ts env Us;
            dp = (rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) in
          do {env'' \<leftarrow> liftM (update X (types_abs Ts (list_comb head args)) env');
            st \<leftarrow> SIMPL (cfg_alg cfg) env'' (dp # dpairs);
            case st of (env2, frigid, fflex) \<Rightarrow> returnW (Some (El_E env2 (frigid @ fflex), tail))})
          (Some (x, s'))"
      by blast
    then show ?thesis
    proof cases
      case fail
      from IH[OF this] show ?thesis by (auto simp: S_Proj intro: ev.proj_tail)
    next
      case ok
      obtain env' args where ma: "make_args vname Ts env Us = (env', args)" by fastforce
      from ok ma obtain env'' env2 frigid fflex where
        up: "ok (update X (types_abs Ts (list_comb head args)) env') env''"
        and S: "okW (SIMPL (cfg_alg cfg) env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs))
          (env2, frigid, fflex)"
        and xs: "x = El_E env2 (frigid @ fflex)" "s' = tail"
        by (auto simp: Let_def)
      from xs show ?thesis by (auto simp: S_Proj intro: ev.proj[OF ma up S] ev.proj_tail)
    qed
  next
    case (S_Maps vname env0 rb targs G uarg xq)
    from okW_bind_E[OF hyps[unfolded S_Maps seq.case]]
    obtain e d q cs where s1: "okW (P cfg xq) (Some (El_E e d, q))"
      and cc: "okW (copycons cfg vname env0 rb targs G uarg e d) cs"
      and s2: "okW (P cfg (S_Append cs (S_Maps vname env0 rb targs G uarg q))) (Some (x, s'))"
      by auto
    note I1 = IH[OF s1] and I2 = IH[OF s2]
    have lift: "ev cfg (S_Maps vname env0 rb targs G uarg xq) z"
      if "ev cfg (S_Append cs (S_Maps vname env0 rb targs G uarg q)) z" for z
      using that
    proof (rule ev_AppendE)
      assume "ev cfg cs z"
      from ev.maps[OF I1[THEN conjunct1] cc this] show ?thesis .
    next
      assume "ev cfg (S_Maps vname env0 rb targs G uarg q) z"
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

inductive_cases seqinv_SingleE: "seqinv G (S_Single x)"
inductive_cases seqinv_ProjE: "seqinv G (S_Proj vname env Ts Us targs rb u dps head targ X tail)"
inductive_cases seqinv_MapsE: "seqinv G (S_Maps vname envM rb targs G' uarg xq)"
inductive_cases seqinv_AppendE: "seqinv G (S_Append xq yq)"

text \<open>
  The copies of an argument (\<^const>\<open>S_Maps\<close>) are sound by \<^const>\<open>copycons\<close>: the normalization of
  the argument yields a saturated term (@{thm [source] head_norm_eta_norm_satd}).
\<close>

theorem ev_sound: "ev cfg s x \<Longrightarrow> seqinv G s \<Longrightarrow> elem_ok G x"
proof (induction arbitrary: G rule: ev.induct)
  case (single x)
  then show ?case by (auto elim: seqinv_SingleE)
next
  case (proj vname Ts env Us env' args X head env'' rb targ targs u dpairs env2 frigid fflex tail)
  from proj.prems show ?case
  proof (rule seqinv_ProjE)
    fix env0 dps0 assume G: "G = GE env0 dps0"
      and d: "\<forall>env1 args. make_args vname Ts env Us = (env1, args) \<longrightarrow>
        (\<forall>env2. ok (update X (types_abs Ts (list_comb head args)) env1) env2 \<longrightarrow>
          dstep env0 dps0 env2 ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs))"
    from d proj.hyps(1,2)
    have d1: "dstep env0 dps0 env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs)"
      by blast
    have "dstep env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs) env2
        (frigid @ fflex)"
      by (rule dstep_set[OF SIMPL_sound[OF proj.hyps(3)]]) auto
    from dstep_trans[OF d1 this] show ?thesis by (simp add: G)
  qed
next
  case (proj_tail tail x vname env Ts Us targs rb u dpairs head targ X)
  from proj_tail.prems show ?case by (rule seqinv_ProjE) (auto intro: proj_tail.IH)
next
  case (maps xq env dps vname envM rb targs G' uarg cs x)
  from maps.prems show ?case
  proof (rule seqinv_MapsE)
    fix env0 dps0 env1 dps1 y U
    assume G: "G = GE env0 dps0" and Gv: "G' = Var y U"
      and d0': "dstep env0 dps0 env1 ((rb, Var y U \<degree>\<degree> targs, uarg) # dps1)"
      and xs: "seqinv (GE env1 dps1) xq" and extM: "extends envM env1"
    from d0' Gv have d0: "dstep env0 dps0 env1 ((rb, G' \<degree>\<degree> targs, uarg) # dps1)" by simp
    from maps.IH(1)[OF xs] have d1: "dstep env1 dps1 env dps" by simp
    have ext: "extends envM env" by (rule extends_trans[OF extM dstepD(1)[OF d1]])
    have d2: "dstep env1 ((rb, G' \<degree>\<degree> targs, uarg) # dps1) env ((rb, G' \<degree>\<degree> targs, uarg) # dps)"
      by (rule dstep_set[OF dstep_frame[OF d1, where fs = "[(rb, G' \<degree>\<degree> targs, uarg)]"]]) auto
    have "seqinv (GE env ((rb, G' \<degree>\<degree> targs, uarg) # dps)) cs"
      by (rule copycons_sinv[OF maps.hyps(2) ext head_norm_eta_norm_satd])
    from maps.IH(2)[OF this] have "elem_ok (GE env ((rb, G' \<degree>\<degree> targs, uarg) # dps)) x" .
    then show ?thesis using dstep_trans[OF d0 d2] by (cases x) (auto simp: G intro: dstep_trans)
  qed
next
  case (append_l xq x yq)
  from append_l.prems show ?case by (rule seqinv_AppendE) (rule append_l.IH)
next
  case (append_r yq x xq)
  from append_r.prems show ?case by (rule seqinv_AppendE) (rule append_r.IH)
qed (auto elim: seqinv.cases)

text \<open>Pulling a sequence yields an element of its goal, and the rest of the sequence has only such
  elements:\<close>

theorem pull_sound:
  assumes "pull cfg s = Some (evs, Ok (Some (x, s')))" "seqinv G s"
  shows "elem_ok G x" "ev cfg s' y \<Longrightarrow> elem_ok G y"
  using pull_some_ev[OF assms(1)] ev_sound[OF _ assms(2)] by auto

end

end
