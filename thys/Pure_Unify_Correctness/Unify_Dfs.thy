section \<open>Pulling a Sequence Yields All Its Elements\<close>

theory Unify_Dfs
  imports Unify_Search
begin

text \<open>
  The depth-first search of \<^const>\<open>Pure_Unify.pull\<close> is adequate for the elements of a sequence
  (\<^const>\<open>ev\<close>): pulling a sequence that has an element \<open>x\<close> either yields \<open>x\<close>, or yields another
  element and a rest that still has \<open>x\<close>. Hence a finite enumeration of a sequence contains
  all its elements. The handlers for \<open>CANTUNIFY\<close> in \<^const>\<open>Pure_Unify.pull\<close> do not lose elements,
  since no \<open>CANTUNIFY\<close> escapes from pulling a sequence.
\<close>

subsection \<open>Computations that do not raise \<open>CANTUNIFY\<close>\<close>

definition noCU :: "'a W \<Rightarrow> bool" where
  "noCU m \<longleftrightarrow> (\<forall>evs. m \<noteq> Some (evs, UErr CANTUNIFY))"

lemma noCU_simps[simp]:
  "noCU (returnW x)" "noCU None" "noCU (emit evt)" "noCU (liftM m')" "noCU pull_fail"
  "noCU (raiseW e) \<longleftrightarrow> e \<noteq> CANTUNIFY"
  by (auto simp: noCU_def returnW_def raiseW_def emit_def liftM_def pull_fail_def split: option.splits res.splits)

lemma noCU_whenW: "noCU m \<Longrightarrow> noCU (whenW b m)"
  by (simp add: whenW_def)

lemma noCU_bindW: "noCU m \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> noCU (f x)) \<Longrightarrow> noCU (bindW m f)"
  by (fastforce simp: noCU_def bindW_def split: option.splits ures.splits)

lemma noCU_handleW: "(\<And>evs e. m = Some (evs, UErr e) \<Longrightarrow> noCU (h e)) \<Longrightarrow> noCU (handleW m h)"
  by (fastforce simp: noCU_def handleW_def split: option.splits ures.splits)

lemma noCU_CANTUNIFY_handler: "noCU m \<Longrightarrow> noCU (case e of CANTUNIFY \<Rightarrow> m | _ \<Rightarrow> raiseW e)"
  by (cases e) simp_all

lemma noCU_make_projs: "noCU (make_projs u targs0 Ts targs)"
  by (induction u targs0 Ts targs rule: make_projs.induct) (auto intro!: noCU_bindW)

lemma noCU_foldrW: "(\<And>x b. noCU (f x b)) \<Longrightarrow> noCU (foldrW f xs b)"
  by (induction xs arbitrary: b) (auto intro!: noCU_bindW)

lemma noCU_projenv: "noCU (projenv cfg vname rb targs u env dpairs base Ts head Usb targ p tail)"
  unfolding projenv_def
  by (auto split: prod.splits intro!: noCU_handleW noCU_CANTUNIFY_handler noCU_bindW)

lemma noCU_liftM_bind: "(\<And>x. ok m x \<Longrightarrow> noCU (f x)) \<Longrightarrow> noCU (bindW (liftM m) f)"
  by (rule noCU_bindW) simp_all

lemma noCU_matchfun: "noCU (matchfun cfg vname rb targs u env dpairs uhead uargs base Ts projs)"
proof (induction cfg vname rb targs u env dpairs uhead uargs base Ts projs rule: matchfun.induct)
  case (1 cfg vname rb targs u env dpairs uhead uargs base Ts bvar T targ projs)
  show ?case
  proof (simp only: matchfun.simps, rule noCU_liftM_bind)
    fix Usb assume "ok (strip_type env T) Usb"
    with 1 have "noCU (matchfun cfg vname rb targs u env dpairs uhead uargs base Ts projs)"
      by (simp only: okW_liftM)
    then show "noCU (matchfun cfg vname rb targs u env dpairs uhead uargs base Ts projs \<bind>
        foldrW (projenv cfg vname rb targs u env dpairs base Ts bvar Usb targ) (arity_guesses cfg (snd Usb)))"
      by (intro noCU_bindW noCU_foldrW noCU_projenv)
  qed
qed simp

lemma noCU_mc: "noCU (mc cfg vname rb targs u env dpairs)"
proof (induction "size u" arbitrary: rb targs u rule: less_induct)
  case less
  have IH: "noCU (mc cfg vname rb' targs' body env dpairs)" if "fst (strip_comb u) = Abs a T body" for rb' targs' a T body
    using less strip_comb_Abs_size[OF that] by blast
  show ?case
    by (subst mc.simps)
      (auto simp: Let_def intro!: noCU_bindW noCU_make_projs noCU_matchfun IH split: pterm.splits prod.splits)
qed

lemma noCU_match1_projs: "noCU (match1_projs cfg vname env dpairs base Ts projs tail)"
proof (induction projs)
  case (Cons p projs)
  obtain bv T targ where p: "p = (bv, T, targ)" by (cases p)
  show ?case unfolding p match1_projs.simps
    by (auto simp: match1_proj_def
      intro!: noCU_bindW noCU_foldrW noCU_handleW noCU_CANTUNIFY_handler Cons split: prod.splits)
qed simp

lemma noCU_match1: "noCU (match1 cfg vname rb targs u env dpairs)"
  unfolding match1_def Let_def
  by (auto intro!: noCU_bindW noCU_make_projs noCU_match1_projs split: pterm.splits prod.splits)

lemma noCU_match_pair: "noCU (match_pair cfg env dp dpairs)"
  unfolding match_pair_def by (auto intro!: noCU_bindW noCU_mc noCU_match1 split: prod.splits pterm.splits)

lemma noCU_match_eta: "noCU (match_eta cfg env dp dpairs B j tail)"
  unfolding match_eta_def
  by (auto intro!: noCU_bindW noCU_match_pair noCU_handleW noCU_CANTUNIFY_handler split: prod.splits)

lemma noCU_MATCH: "noCU (MATCH cfg env dp dpairs)"
  unfolding MATCH_def
  by (auto intro!: noCU_bindW noCU_match_pair noCU_foldrW noCU_match_eta split: prod.splits pterm.splits)

lemma noCU_copycons: "noCU (copycons cfg vname rb targs uarg uargs env dpairs)"
  unfolding copycons_def by (auto intro!: noCU_bindW noCU_mc split: prod.splits)

lemma noCU_new_dset: "noCU (new_dset vT Ts u' env' dpairs')"
  unfolding new_dset_def by (auto intro!: noCU_bindW split: option.splits)

lemma noCU_D: "noCU m \<Longrightarrow> m = Some r \<Longrightarrow> snd r \<noteq> UErr CANTUNIFY"
  by (cases r) (auto simp: noCU_def)

lemma noCU_case_handler:
  "noCU m \<Longrightarrow> (\<And>e. e \<noteq> CANTUNIFY \<Longrightarrow> noCU (h e)) \<Longrightarrow> noCU (case e of CANTUNIFY \<Rightarrow> m | _ \<Rightarrow> h e)"
  by (cases e) auto

subsection \<open>Pulling keeps the elements\<close>

inductive_cases ev_EmptyE: "ev cfg S_Empty x"
inductive_cases ev_SingleE: "ev cfg (S_Single y) x"
inductive_cases ev_AddUnifyE: "ev cfg (S_AddUnify td env dps reseq) x"
inductive_cases ev_ItRightE: "ev cfg (S_ItRight td xq yq) x"
inductive_cases ev_MapNewDsetE: "ev cfg (S_MapNewDset vT Ts xq) x"
inductive_cases ev_MapAbsE: "ev cfg (S_MapAbs a T xq) x"
inductive_cases ev_ProjE: "ev cfg (S_Proj vname env Ts Us targs rb u dpairs head targ tail) x"
inductive_cases ev_MapJoinE: "ev cfg (S_MapJoin uhead xq) x"
inductive_cases ev_MapsE: "ev cfg (S_Maps vname rb targs uarg xq) x"
inductive_cases ev_AppendE: "ev cfg (S_Append xq yq) x"
inductive_cases ev_MapConsE: "ev cfg (S_MapCons uargs xq) x"

lemma okW_det: "okW m x \<Longrightarrow> okW m y \<Longrightarrow> x = y"
  by auto

lemma okW_not_err: "okW m x \<Longrightarrow> m \<noteq> Some (evs, UErr e)"
  by auto

lemma okW_bind_opt_C:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> returnW None
    | Some (y, q) \<Rightarrow> (case y of El_C a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail))) z"
  shows "(okW m None \<and> z = None) \<or> (\<exists>a b c q. okW m (Some (El_C a b c, q)) \<and> okW (f a b c q) z)"
proof -
  from okW_bind_opt[OF assms] consider "okW m None" "z = None"
    | y q where "okW m (Some (y, q))" "okW (case y of El_C a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail) z"
    by auto
  then show ?thesis by cases (auto split: elem.splits)
qed

lemma okW_bind_opt_D:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> returnW None
    | Some (y, q) \<Rightarrow> (case y of El_D a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail))) z"
  shows "(okW m None \<and> z = None) \<or> (\<exists>a b c q. okW m (Some (El_D a b c, q)) \<and> okW (f a b c q) z)"
proof -
  from okW_bind_opt[OF assms] consider "okW m None" "z = None"
    | y q where "okW m (Some (y, q))" "okW (case y of El_D a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail) z"
    by auto
  then show ?thesis by cases (auto split: elem.splits)
qed

lemma pull_ev_aux:
  assumes "pull cfg s = Some r"
  shows "snd r \<noteq> UErr CANTUNIFY \<and>
    (\<forall>x res. ev cfg s x \<longrightarrow> snd r = UOk res \<longrightarrow> (\<exists>y s'. res = Some (y, s') \<and> (y = x \<or> ev cfg s' x)))"
  using assms
proof (induction cfg s r rule: pull.raw_induct[rotated, consumes 1])
  case (1 P cfg s r)
  have IHnc: "noCU (P c s1)" for c s1
    using "1.IH"[of c s1] by (fastforce simp: noCU_def)
  have IH: "\<exists>y s'. res = Some (y, s') \<and> (y = x \<or> ev cfg s' x)" if "okW (P cfg s1) res" "ev cfg s1 x"
    for s1 res x
  proof -
    from that(1) obtain evs where "P cfg s1 = Some (evs, UOk res)" by blast
    from "1.IH"[OF this] that(2) show ?thesis by simp
  qed
  have nc: "snd r \<noteq> UErr CANTUNIFY"
    by (rule noCU_D[OF _ "1.hyps"], cases s)
      (auto simp: Let_def intro!: noCU_bindW noCU_handleW noCU_whenW noCU_CANTUNIFY_handler IHnc
        noCU_MATCH noCU_copycons noCU_new_dset split: prod.splits list.splits option.splits elem.splits)
  have "\<exists>y s'. res = Some (y, s') \<and> (y = x \<or> ev cfg s' x)" if ev: "ev cfg s x" and rr: "snd r = UOk res" for x res
  proof -
    note hyps = okW_of[OF "1.hyps" rr]
    show ?thesis
    proof (cases s)
      case S_Empty
      with ev show ?thesis by (auto elim: ev_EmptyE)
    next
      case (S_Single y)
      with ev hyps show ?thesis by (auto elim: ev_SingleE)
    next
      case (S_AddUnify td env dps reseq)
      note h = hyps[unfolded S_AddUnify seq.case]
      from ev[unfolded S_AddUnify] consider (tl) "ev cfg reseq x"
        | (fin) env' ffs r where "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, [])"
          "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) r" "x = El_R (fst r) (snd r)"
        | (mtch) env' ffs dp frs ms where "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)"
          "\<not> td > cfg_search_bound cfg" "okW (MATCH cfg env' dp (frs @ ffs)) ms"
          "ev cfg (S_ItRight (td + 1) ms reseq) x"
        by (rule ev_AddUnifyE) blast+
      then show ?thesis
      proof cases
        case tl
        from addunify_cases[OF h]
        consider (fail) "okW (P cfg reseq) res"
          | (fin) env'' tps where "res = Some (El_R env'' tps, reseq)"
          | (mtch) ms where "okW (P cfg (S_ItRight (td + 1) ms reseq)) res"
          by blast
        then show ?thesis
        proof cases
          case fail
          from IH[OF this tl] show ?thesis .
        next
          case fin
          with tl show ?thesis by simp
        next
          case (mtch ms)
          from IH[OF this ev.ir_tail[OF tl]] show ?thesis .
        qed
      next
        case (fin env' ffs r)
        from fin(1,2) obtain evs1 evs2 where "SIMPL (cfg_alg cfg) env dps = Some (evs1, UOk (env', ffs, []))"
          "foldrW (add_ffpair (cfg_alg cfg)) ffs (env', []) = Some (evs2, UOk r)"
          by blast
        with h fin(3) show ?thesis
          by (auto simp: handleW_def bindW_def whenW_def emit_def returnW_def split: if_splits)
      next
        case (mtch env' ffs dp frs ms)
        from mtch(1,3) obtain evs1 evs3 where "SIMPL (cfg_alg cfg) env dps = Some (evs1, UOk (env', ffs, dp # frs))"
          "MATCH cfg env' dp (frs @ ffs) = Some (evs3, UOk ms)"
          by blast
        with h mtch(2) IHnc[of cfg "S_ItRight (td + 1) ms reseq"]
        have "okW (P cfg (S_ItRight (td + 1) ms reseq)) res"
          by (auto simp: handleW_def bindW_def whenW_def emit_def returnW_def raiseW_def noCU_def
            split: if_splits option.splits ures.splits uexn.splits)
        from IH[OF this mtch(4)] show ?thesis .
      qed
    next
      case (S_ItRight td xq yq)
      from ev[unfolded S_ItRight] have evc: "ev cfg yq x \<or>
          (\<exists>env dps. ev cfg xq (El_E env dps) \<and> (\<forall>R. ev cfg (S_AddUnify td env dps R) x))"
        by (rule ev_ItRightE) blast+
      from okW_bind_E[OF hyps[unfolded S_ItRight seq.case]]
      consider (n) "okW (P cfg xq) None" "okW (P cfg yq) res"
        | (s) a b q where "okW (P cfg xq) (Some (El_E a b, q))"
          "okW (P cfg (S_AddUnify td a b (S_ItRight td q yq))) res"
        by blast
      then show ?thesis
      proof cases
        case n
        from evc show ?thesis
        proof (elim disjE exE conjE)
          assume "ev cfg yq x"
          from IH[OF n(2) this] show ?thesis .
        next
          fix env dps assume "ev cfg xq (El_E env dps)"
          from IH[OF n(1) this] show ?thesis by simp
        qed
      next
        case (s a b q)
        from evc have "ev cfg (S_AddUnify td a b (S_ItRight td q yq)) x"
        proof (elim disjE exE conjE)
          assume "ev cfg yq x"
          then show ?thesis by (intro ev.au_tail ev.ir_tail)
        next
          fix env dps assume e1: "ev cfg xq (El_E env dps)" and e2: "\<forall>R. ev cfg (S_AddUnify td env dps R) x"
          from IH[OF s(1) e1] have "El_E a b = El_E env dps \<or> ev cfg q (El_E env dps)" by simp
          then show ?thesis
          proof
            assume "El_E a b = El_E env dps"
            with e2 show ?thesis by simp
          next
            assume "ev cfg q (El_E env dps)"
            from ev.ir_head[OF this] e2 have "ev cfg (S_ItRight td q yq) x" by blast
            then show ?thesis by (rule ev.au_tail)
          qed
        qed
        from IH[OF s(2) this] show ?thesis .
      qed
    next
      case (S_MapNewDset vT Ts xq)
      from ev S_MapNewDset obtain b e d where evx: "ev cfg xq (El_C b e d)"
        and x: "okW (new_dset vT Ts b e d) x"
        by (auto elim: ev_MapNewDsetE)
      from okW_bind_opt_C[OF hyps[unfolded S_MapNewDset seq.case]]
      consider (n) "okW (P cfg xq) None"
        | (s) b' e' d' q y where "okW (P cfg xq) (Some (El_C b' e' d', q))"
          "okW (new_dset vT Ts b' e' d') y" "res = Some (y, S_MapNewDset vT Ts q)"
        by auto
      then show ?thesis
      proof cases
        case n
        with IH[OF n evx] show ?thesis by simp
      next
        case (s b' e' d' q y)
        from IH[OF s(1) evx] have "El_C b' e' d' = El_C b e d \<or> ev cfg q (El_C b e d)" by simp
        then show ?thesis
        proof
          assume "El_C b' e' d' = El_C b e d"
          with s(2) x have "y = x" by auto
          with s(3) show ?thesis by simp
        next
          assume "ev cfg q (El_C b e d)"
          from ev.new_dset[OF this x] s(3) show ?thesis by simp
        qed
      qed
    next
      case (S_MapAbs a T xq)
      from ev S_MapAbs obtain b e d where evx: "ev cfg xq (El_C b e d)" and x: "x = El_C (Abs a T b) e d"
        by (auto elim: ev_MapAbsE)
      from okW_bind_opt_C[OF hyps[unfolded S_MapAbs seq.case]]
      consider (n) "okW (P cfg xq) None"
        | (s) b' e' d' q where "okW (P cfg xq) (Some (El_C b' e' d', q))"
          "res = Some (El_C (Abs a T b') e' d', S_MapAbs a T q)"
        by auto
      then show ?thesis
      proof cases
        case n
        with IH[OF n evx] show ?thesis by simp
      next
        case (s b' e' d' q)
        from IH[OF s(1) evx] have "El_C b' e' d' = El_C b e d \<or> ev cfg q (El_C b e d)" by simp
        with s(2) x show ?thesis by (auto intro: ev.map_abs)
      qed
    next
      case (S_Proj vname env Ts Us targs rb u dpairs head targ tail)
      note h = hyps[unfolded S_Proj seq.case]
      from ev[unfolded S_Proj] consider (tl) "ev cfg tail x"
        | (pr) env' args env2 frigid fflex where "make_args vname Ts env Us = (env', args)"
          "okW (SIMPL (cfg_alg cfg) env'
            ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs))
            (env2, frigid, fflex)"
          "x = El_C (list_comb head args) env2 (frigid @ fflex)"
        by (rule ev_ProjE) blast+
      then show ?thesis
      proof cases
        case tl
        from h consider (fail) "okW (P cfg tail) res" | (ok) y where "res = Some (y, tail)"
          by (auto simp: okW_handleW Let_def split: prod.splits dest!: okW_CANTUNIFY_handler')
        then show ?thesis
        proof cases
          case fail
          from IH[OF this tl] show ?thesis .
        qed (use tl in simp)
      next
        case (pr env' args env2 frigid fflex)
        from pr(2) obtain evs where "SIMPL (cfg_alg cfg) env'
            ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs) =
          Some (evs, UOk (env2, frigid, fflex))"
          by blast
        with h pr(1,3) show ?thesis
          by (auto simp: handleW_def bindW_def returnW_def Let_def)
      qed
    next
      case (S_MapJoin uhead xq)
      from ev S_MapJoin obtain b e d where evx: "ev cfg xq (El_D b e d)" and x: "x = El_C (list_comb uhead b) e d"
        by (auto elim: ev_MapJoinE)
      from okW_bind_opt_D[OF hyps[unfolded S_MapJoin seq.case]]
      consider (n) "okW (P cfg xq) None"
        | (s) b' e' d' q where "okW (P cfg xq) (Some (El_D b' e' d', q))"
          "res = Some (El_C (list_comb uhead b') e' d', S_MapJoin uhead q)"
        by auto
      then show ?thesis
      proof cases
        case n
        with IH[OF n evx] show ?thesis by simp
      next
        case (s b' e' d' q)
        from IH[OF s(1) evx] have "El_D b' e' d' = El_D b e d \<or> ev cfg q (El_D b e d)" by simp
        with s(2) x show ?thesis by (auto intro: ev.map_join)
      qed
    next
      case (S_Maps vname rb targs uarg xq)
      from ev S_Maps obtain b e d cs0 where evx: "ev cfg xq (El_D b e d)"
        and cs0: "okW (copycons cfg vname rb targs uarg b e d) cs0" and evc: "ev cfg cs0 x"
        by (auto elim: ev_MapsE)
      from okW_bind_opt_D[OF hyps[unfolded S_Maps seq.case]]
      consider (n) "okW (P cfg xq) None"
        | (s) b' e' d' q cs where "okW (P cfg xq) (Some (El_D b' e' d', q))"
          "okW (copycons cfg vname rb targs uarg b' e' d') cs"
          "okW (P cfg (S_Append cs (S_Maps vname rb targs uarg q))) res"
        by auto
      then show ?thesis
      proof cases
        case n
        with IH[OF n evx] show ?thesis by simp
      next
        case (s b' e' d' q cs)
        from IH[OF s(1) evx] have "El_D b' e' d' = El_D b e d \<or> ev cfg q (El_D b e d)" by simp
        then have "ev cfg (S_Append cs (S_Maps vname rb targs uarg q)) x"
        proof
          assume "El_D b' e' d' = El_D b e d"
          with s(2) cs0 have "cs = cs0" by auto
          with evc show ?thesis by (simp add: ev.append_l)
        next
          assume "ev cfg q (El_D b e d)"
          from ev.append_r[OF ev.maps[OF this cs0 evc]] show ?thesis .
        qed
        from IH[OF s(3) this] show ?thesis .
      qed
    next
      case (S_Append xq yq)
      from okW_bind_opt[OF hyps[unfolded S_Append seq.case]]
      consider (n) "okW (P cfg xq) None" "okW (P cfg yq) res"
        | (s) y q where "okW (P cfg xq) (Some (y, q))" "res = Some (y, S_Append q yq)"
        by auto
      then show ?thesis
      proof cases
        case n
        with ev S_Append IH[of xq None x] IH[of yq res x] show ?thesis by (auto elim: ev_AppendE)
      next
        case (s y q)
        with ev S_Append IH[of xq "Some (y, q)" x] show ?thesis
          by (auto elim!: ev_AppendE intro: ev.append_l ev.append_r)
      qed
    next
      case (S_MapCons uargs xq)
      from ev S_MapCons obtain b e d where evx: "ev cfg xq (El_C b e d)" and x: "x = El_D (b # uargs) e d"
        by (auto elim: ev_MapConsE)
      from okW_bind_opt_C[OF hyps[unfolded S_MapCons seq.case]]
      consider (n) "okW (P cfg xq) None"
        | (s) b' e' d' q where "okW (P cfg xq) (Some (El_C b' e' d', q))"
          "res = Some (El_D (b' # uargs) e' d', S_MapCons uargs q)"
        by auto
      then show ?thesis
      proof cases
        case n
        with IH[OF n evx] show ?thesis by simp
      next
        case (s b' e' d' q)
        from IH[OF s(1) evx] have "El_C b' e' d' = El_C b e d \<or> ev cfg q (El_C b e d)" by simp
        with s(2) x show ?thesis by (auto intro: ev.map_cons)
      qed
    qed
  qed
  with nc show ?case by blast
qed

text \<open>No \<open>CANTUNIFY\<close> escapes from pulling a sequence.\<close>

theorem pull_not_CANTUNIFY: "pull cfg s = Some (evs, UErr e) \<Longrightarrow> e \<noteq> CANTUNIFY"
  using pull_ev_aux by fastforce

text \<open>Pulling an element either yields it or keeps it in the rest of the sequence.\<close>

theorem pull_ev:
  assumes "ev cfg s x" "pull cfg s = Some (evs, UOk r)"
  shows "\<exists>y s'. r = Some (y, s') \<and> (y = x \<or> ev cfg s' x)"
  using pull_ev_aux[OF assms(2)] assms(1) by simp

text \<open>Pulling a sequence until it is exhausted yields all its elements.\<close>

inductive evals :: "cfg \<Rightarrow> seq \<Rightarrow> elem list \<Rightarrow> bool" for cfg where
  Nil: "pull cfg s = Some (evs, UOk None) \<Longrightarrow> evals cfg s []"
| Cons: "pull cfg s = Some (evs, UOk (Some (x, s'))) \<Longrightarrow> evals cfg s' xs \<Longrightarrow> evals cfg s (x # xs)"

theorem evals_ev: "evals cfg s xs \<Longrightarrow> ev cfg s x \<Longrightarrow> x \<in> set xs"
proof (induction rule: evals.induct)
  case (Nil s evs)
  from pull_ev[OF Nil(2,1)] show ?case by simp
next
  case (Cons s evs y s' xs)
  from pull_ev[OF Cons(4,1)] Cons(3) show ?case by auto
qed

end
