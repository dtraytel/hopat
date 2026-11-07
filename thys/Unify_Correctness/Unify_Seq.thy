section \<open>Evaluation of the Search Sequences\<close>

theory Unify_Seq
  imports Unify_Monad
begin

text \<open>
  The lazy sequences of \<open>unify.ML\<close> are represented by the closures \<^typ>\<open>seq\<close> that
  \<^const>\<open>Pure_Unify.pull\<close> evaluates. This theory is independent of the semantics of terms:
  \<^item> the decomposition of successful evaluations of the closures;
  \<^item> the elements of a sequence (\<open>ev\<close>), independently of the order of the depth-first search,
    and the adequacy of the search: pulling a sequence until it is exhausted (\<open>evals\<close>) yields
    all its elements;
  \<^item> finite enumerations (\<open>fin\<close>) and how the closures compose them.
\<close>


subsection \<open>Decomposing the evaluation of the closures\<close>

lemma okW_of: "m = Some r \<Longrightarrow> snd r = UOk x \<Longrightarrow> okW m x"
  by (cases r) auto

lemma not_okW_pull_fail[simp]: "\<not> okW pull_fail y"
  by (simp add: pull_fail_def)

lemma okW_CANTUNIFY_handler':
  "okW (case e of CANTUNIFY \<Rightarrow> m | _ \<Rightarrow> raiseW e) y \<Longrightarrow> okW m y"
  by (cases e) auto

lemma okW_bind_opt:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> A | Some (y, q) \<Rightarrow> B y q)) z"
  shows "(okW m None \<and> okW A z) \<or> (\<exists>y q. okW m (Some (y, q)) \<and> okW (B y q) z)"
proof -
  from assms obtain r where r: "okW m r" "okW (case r of None \<Rightarrow> A | Some (y, q) \<Rightarrow> B y q) z"
    unfolding okW_bindW by blast
  show ?thesis
  proof (cases r)
    case None
    with r show ?thesis by simp
  next
    case (Some p)
    with r show ?thesis by (cases p) auto
  qed
qed

lemma okW_bind_E:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> A
    | Some (y, q) \<Rightarrow> (case y of El_E a b \<Rightarrow> f a b q | _ \<Rightarrow> pull_fail))) z"
  shows "(okW m None \<and> okW A z) \<or> (\<exists>a b q. okW m (Some (El_E a b, q)) \<and> okW (f a b q) z)"
proof -
  from okW_bind_opt[OF assms] consider (n) "okW m None \<and> okW A z"
    | (s) y q where "okW m (Some (y, q))" "okW (case y of El_E a b \<Rightarrow> f a b q | _ \<Rightarrow> pull_fail) z"
    by blast
  then show ?thesis
  proof cases
    case (s y q)
    then show ?thesis by (cases y) auto
  qed simp
qed

lemma okW_whenW_then: "okW (bindW (whenW b (emit e)) (\<lambda>_. M)) z \<Longrightarrow> okW M z"
  by (auto simp: okW_whenW split: if_splits)

lemma okW_emit_then: "okW (bindW (emit e) (\<lambda>_. M)) z \<Longrightarrow> okW M z"
  by auto

lemma okW_handle_CANTUNIFY:
  assumes "okW (handleW M (\<lambda>e. case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e)) z"
  shows "okW M z \<or> okW N z"
proof -
  from assms have "okW M z \<or> (\<exists>evs e. M = Some (evs, UErr e) \<and>
      okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z)"
    by (simp only: okW_handleW)
  then show ?thesis
  proof (elim disjE)
    assume "\<exists>evs e. M = Some (evs, UErr e) \<and> okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z"
    then obtain e where "okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z" by metis
    from okW_CANTUNIFY_handler'[OF this] show ?thesis ..
  qed (rule disjI1)
qed

lemma okW_bind_triple:
  assumes "okW (bindW m (\<lambda>(a, b, c). f a b c)) z"
  shows "\<exists>a b c. okW m (a, b, c) \<and> okW (f a b c) z"
proof -
  from assms obtain st where "okW m st" "okW ((\<lambda>(a, b, c). f a b c) st) z" unfolding okW_bindW by blast
  then show ?thesis by (cases st) auto
qed

text \<open>The successful evaluations of the closure of \<^const>\<open>S_AddUnify\<close>:\<close>

lemma addunify_cases:
  assumes "okW (handleW
    (bindW (whenW b1 (emit e1)) (\<lambda>_. bindW (SIMPL alg env dps) (\<lambda>(env', ffs, frs).
      case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R))))
    (\<lambda>e. case e of CANTUNIFY \<Rightarrow> bindW (whenW b4 (emit e4)) (\<lambda>_. Q) | _ \<Rightarrow> raiseW e)) z"
  shows "okW Q z \<or>
    (\<exists>env' ffs env'' tps. okW (SIMPL alg env dps) (env', ffs, []) \<and>
      okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps) \<and> z = Some (El_R env'' tps, reseq)) \<or>
    (\<exists>env' ffs dp frigid' ms. okW (SIMPL alg env dps) (env', ffs, dp # frigid') \<and>
      okW (MATCH cfg env' dp (frigid' @ ffs)) ms \<and> okW (R ms) z)"
proof -
  from okW_handle_CANTUNIFY[OF assms] show ?thesis
  proof (elim disjE)
    assume "okW (bindW (whenW b1 (emit e1)) (\<lambda>_. bindW (SIMPL alg env dps) (\<lambda>(env', ffs, frs).
      case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)))) z"
    from okW_bind_triple[OF okW_whenW_then[OF this]] obtain env' ffs frs where
      S: "okW (SIMPL alg env dps) (env', ffs, frs)"
      and c: "okW (case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)) z"
      by blast
    show ?thesis
    proof (cases frs)
      case Nil
      with c obtain r where r: "okW (foldrW (add_ffpair alg) ffs (env', [])) r"
        "z = Some (El_R (fst r) (snd r), reseq)" by auto
      obtain env'' tps where "r = (env'', tps)" by (cases r)
      with r have "okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps)"
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
        with S Cons show ?thesis by blast
      qed
    qed
  next
    assume "okW (bindW (whenW b4 (emit e4)) (\<lambda>_. Q)) z"
    from okW_whenW_then[OF this] show ?thesis by blast
  qed
qed


subsection \<open>The elements of a sequence\<close>

text \<open>
  \<open>ev cfg s x\<close>: \<open>x\<close> is an element of \<open>s\<close>, with one rule per way in which
  \<^const>\<open>Pure_Unify.pull\<close> produces an element. Every rule requires the computations on the way
  to the element to succeed.
\<close>

inductive ev :: "cfg \<Rightarrow> seq \<Rightarrow> elem \<Rightarrow> bool" for cfg where
  single: "ev cfg (S_Single x) x"
| au_tail: "ev cfg reseq x \<Longrightarrow> ev cfg (S_AddUnify td env dps reseq) x"
| au_res: "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, []) \<Longrightarrow>
    okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) r \<Longrightarrow>
    ev cfg (S_AddUnify td env dps reseq) (El_R (fst r) (snd r))"
| au_match: "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> \<not> td > cfg_search_bound cfg \<Longrightarrow>
    okW (MATCH cfg env' dp (frs @ ffs)) ms \<Longrightarrow> ev cfg (S_ItRight (td + 1) ms reseq) x \<Longrightarrow>
    ev cfg (S_AddUnify td env dps reseq) x"
| ir_tail: "ev cfg yq x \<Longrightarrow> ev cfg (S_ItRight td xq yq) x"
| ir_head: "ev cfg xq (El_E env dps) \<Longrightarrow> (\<And>R. ev cfg (S_AddUnify td env dps R) x) \<Longrightarrow>
    ev cfg (S_ItRight td xq yq) x"
| proj: "make_args vname Ts env Us = (env', args) \<Longrightarrow>
    ok (update X (types_abs Ts (list_comb head args)) env') env'' \<Longrightarrow>
    okW (SIMPL (cfg_alg cfg) env''
      ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs))
      (env2, frigid, fflex) \<Longrightarrow>
    ev cfg (S_Proj vname env Ts Us targs rb u dpairs head targ X tail) (El_E env2 (frigid @ fflex))"
| proj_tail: "ev cfg tail x \<Longrightarrow> ev cfg (S_Proj vname env Ts Us targs rb u dpairs head targ X tail) x"
| maps: "ev cfg xq (El_E env dps) \<Longrightarrow> okW (copycons cfg vname env0 rb targs G uarg env dps) cs \<Longrightarrow>
    ev cfg cs x \<Longrightarrow> ev cfg (S_Maps vname env0 rb targs G uarg xq) x"
| append_l: "ev cfg xq x \<Longrightarrow> ev cfg (S_Append xq yq) x"
| append_r: "ev cfg yq x \<Longrightarrow> ev cfg (S_Append xq yq) x"

inductive_cases ev_EmptyE: "ev cfg S_Empty x"
inductive_cases ev_SingleE: "ev cfg (S_Single y) x"
inductive_cases ev_AddUnifyE: "ev cfg (S_AddUnify td env dps reseq) x"
inductive_cases ev_ItRightE: "ev cfg (S_ItRight td xq yq) x"
inductive_cases ev_ProjE: "ev cfg (S_Proj vname env Ts Us targs rb u dpairs head targ X tail) x"
inductive_cases ev_MapsE: "ev cfg (S_Maps vname env0 rb targs G uarg xq) x"
inductive_cases ev_AppendE: "ev cfg (S_Append xq yq) x"


subsection \<open>Computations that do not raise \<open>CANTUNIFY\<close>\<close>

text \<open>
  The handlers for \<open>CANTUNIFY\<close> in \<^const>\<open>Pure_Unify.pull\<close> do not lose elements, since no
  \<open>CANTUNIFY\<close> escapes from pulling a sequence. (\<^const>\<open>MATCH\<close> may raise \<open>CANTUNIFY\<close>, in the
  normalisation of the pair by \<^const>\<open>head_norm_dpair\<close>, but it is only called under the
  handler of \<^const>\<open>S_AddUnify\<close>.)
\<close>

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

lemma noCU_D: "noCU m \<Longrightarrow> m = Some r \<Longrightarrow> snd r \<noteq> UErr CANTUNIFY"
  by (cases r) (auto simp: noCU_def)

lemma noCU_foldrW: "(\<And>x b. noCU (f x b)) \<Longrightarrow> noCU (foldrW f xs b)"
  by (induction xs arbitrary: b) (auto intro!: noCU_bindW)

lemma noCU_liftM_bind: "(\<And>x. ok m x \<Longrightarrow> noCU (f x)) \<Longrightarrow> noCU (bindW (liftM m) f)"
  by (rule noCU_bindW) simp_all

lemma noCU_make_projs: "noCU (make_projs u targs0 Ts targs)"
  by (induction u targs0 Ts targs rule: make_projs.induct) (auto intro!: noCU_bindW)

lemma noCU_projenv: "noCU (projenv cfg vname rb targs u env dpairs X base Ts head Usb targ p tail)"
  unfolding projenv_def
  by (auto split: prod.splits intro!: noCU_handleW noCU_CANTUNIFY_handler noCU_bindW)

lemma noCU_imitate: "noCU (imitate vname env0 rb targs env dpairs X Ts uhead uargs)"
  unfolding imitate_def by (auto intro!: noCU_bindW split: prod.splits)

lemma noCU_matchfun: "noCU (matchfun cfg vname env0 rb targs u env dpairs X uhead uargs base Ts projs)"
proof (induction cfg vname env0 rb targs u env dpairs X uhead uargs base Ts projs rule: matchfun.induct)
  case (1 cfg vname env0 rb targs u env dpairs X uhead uargs base Ts bvar T targ projs)
  show ?case
  proof (simp only: matchfun.simps, rule noCU_liftM_bind)
    fix Usb assume "ok (strip_type env T) Usb"
    with 1 have "noCU (matchfun cfg vname env0 rb targs u env dpairs X uhead uargs base Ts projs)"
      by (simp only: okW_liftM)
    then show "noCU (matchfun cfg vname env0 rb targs u env dpairs X uhead uargs base Ts projs \<bind>
        foldrW (projenv cfg vname rb targs u env dpairs X base Ts bvar Usb targ) (arity_guesses cfg (snd Usb)))"
      by (intro noCU_bindW noCU_foldrW noCU_projenv)
  qed
qed (simp add: noCU_imitate split: pterm.split)

lemma noCU_dest_Var: "noCU (dest_Var t)"
  by (cases t) simp_all

lemma noCU_mc: "noCU (mc cfg vname env0 X rb targs u env dpairs)"
proof (induction "size u" arbitrary: X rb targs u env rule: less_induct)
  case less
  have IH: "noCU (mc cfg vname env0 X' rb' targs' body env' dpairs)"
    if "size body < size u" for X' rb' targs' body env'
    using less that by blast
  have sz: "size b < size u \<longleftrightarrow> True" if "fst (strip_comb u) = Abs a T b" for a T b
    using strip_comb_Abs_size[OF that] by simp
  show ?case
    by (subst mc.simps)
      (auto simp: Let_def sz intro!: noCU_bindW noCU_make_projs noCU_matchfun noCU_dest_Var IH
        split: pterm.splits prod.splits)
qed

lemma noCU_match_pair: "noCU (match_pair cfg env dp dpairs)"
  unfolding match_pair_def by (auto intro!: noCU_mc split: prod.splits pterm.splits)

lemma noCU_copycons: "noCU (copycons cfg vname env0 rb targs G uarg env dpairs)"
  unfolding copycons_def by (auto intro!: noCU_bindW noCU_mc noCU_dest_Var split: prod.splits)


subsection \<open>Pulling keeps the elements\<close>

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
        noCU_copycons split: prod.splits list.splits option.splits elem.splits)
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
      case (S_Proj vname env Ts Us targs rb u dpairs head targ X tail)
      note h = hyps[unfolded S_Proj seq.case]
      from ev[unfolded S_Proj] consider (tl) "ev cfg tail x"
        | (pr) env' args env'' env2 frigid fflex where "make_args vname Ts env Us = (env', args)"
          "ok (update X (types_abs Ts (list_comb head args)) env') env''"
          "okW (SIMPL (cfg_alg cfg) env''
            ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs))
            (env2, frigid, fflex)"
          "x = El_E env2 (frigid @ fflex)"
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
        case (pr env' args env'' env2 frigid fflex)
        from pr(3) obtain evs where "SIMPL (cfg_alg cfg) env''
            ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs) =
          Some (evs, UOk (env2, frigid, fflex))"
          by blast
        with h pr(1,2,4) show ?thesis
          by (auto simp: handleW_def bindW_def returnW_def Let_def liftM_def)
      qed
    next
      case (S_Maps vname env0 rb targs G uarg xq)
      from ev S_Maps obtain e d cs0 where evx: "ev cfg xq (El_E e d)"
        and cs0: "okW (copycons cfg vname env0 rb targs G uarg e d) cs0" and evc: "ev cfg cs0 x"
        by (auto elim: ev_MapsE)
      from okW_bind_E[OF hyps[unfolded S_Maps seq.case]]
      consider (n) "okW (P cfg xq) None" "res = None"
        | (s) e' d' q cs where "okW (P cfg xq) (Some (El_E e' d', q))"
          "okW (copycons cfg vname env0 rb targs G uarg e' d') cs"
          "okW (P cfg (S_Append cs (S_Maps vname env0 rb targs G uarg q))) res"
        by auto
      then show ?thesis
      proof cases
        case n
        with IH[OF n(1) evx] show ?thesis by simp
      next
        case (s e' d' q cs)
        from IH[OF s(1) evx] have "El_E e' d' = El_E e d \<or> ev cfg q (El_E e d)" by simp
        then have "ev cfg (S_Append cs (S_Maps vname env0 rb targs G uarg q)) x"
        proof
          assume "El_E e' d' = El_E e d"
          with s(2) cs0 have "cs = cs0" by auto
          with evc show ?thesis by (simp add: ev.append_l)
        next
          assume "ev cfg q (El_E e d)"
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
    qed
  qed
  with nc show ?case by blast
qed

text \<open>No \<open>CANTUNIFY\<close> escapes from pulling a sequence.\<close>

corollary noCU_pull: "noCU (pull cfg s)"
  using pull_ev_aux[of cfg s] by (auto simp: noCU_def)

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

text \<open>The enumeration is unique:\<close>

lemma evals_det: "evals cfg s xs \<Longrightarrow> evals cfg s ys \<Longrightarrow> xs = ys"
proof (induction arbitrary: ys rule: evals.induct)
  case (Nil s evs)
  from Nil.prems show ?case
  proof cases
    case (Cons evs' y s'' ys')
    with Nil.hyps show ?thesis by simp
  qed simp
next
  case (Cons s evs x s' xs)
  from Cons.prems show ?case
  proof cases
    case (Nil evs')
    with Cons.hyps(1) show ?thesis by simp
  next
    case (Cons evs' y s'' ys')
    with Cons.hyps(1) have "y = x" "s'' = s'" by simp_all
    with Cons.IH[of ys'] Cons show ?thesis by simp
  qed
qed


subsection \<open>Finite enumerations\<close>

text \<open>
  \<open>fin cfg s Q\<close>: pulling \<open>s\<close> repeatedly terminates without an exception, after finitely many
  elements, all of which satisfy \<open>Q\<close>. For each constructor of \<^typ>\<open>seq\<close>, the enumeration is
  finite if those of the sequences it pulls are. Only the result of a computation matters for
  the enumeration, not the trace events it emits.
\<close>

definition fin :: "cfg \<Rightarrow> seq \<Rightarrow> (elem \<Rightarrow> bool) \<Rightarrow> bool" where
  "fin cfg s Q \<longleftrightarrow> (\<exists>xs. evals cfg s xs \<and> (\<forall>x\<in>set xs. Q x))"

lemma fin_mono: "fin cfg s P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> fin cfg s Q"
  by (auto simp: fin_def)

lemma evals_res:
  assumes "\<And>r. resW (pull cfg s') r \<longleftrightarrow> resW (pull cfg s) r"
  shows "evals cfg s xs \<Longrightarrow> evals cfg s' xs"
proof (erule evals.cases)
  fix s0 evs assume "s = s0" "xs = []" "pull cfg s0 = Some (evs, UOk None)"
  with assms[of "UOk None"] show "evals cfg s' xs" by (auto simp: resW_def intro: evals.Nil)
next
  fix s0 evs x s1 xs' assume "s = s0" "xs = x # xs'" "pull cfg s0 = Some (evs, UOk (Some (x, s1)))"
    "evals cfg s1 xs'"
  with assms[of "UOk (Some (x, s1))"] show "evals cfg s' xs" by (auto simp: resW_def intro: evals.Cons)
qed

lemma fin_res:
  "(\<And>r. resW (pull cfg s') r \<longleftrightarrow> resW (pull cfg s) r) \<Longrightarrow> fin cfg s Q \<Longrightarrow> fin cfg s' Q"
  by (auto simp: fin_def intro: evals_res)

lemma fin_pull_ok: "fin cfg s Q \<Longrightarrow> \<exists>v. resW (pull cfg s) (UOk v)"
  by (auto simp: fin_def resW_def elim: evals.cases)


subsection \<open>Results of computations\<close>

lemma resW_whenW_emit: "resW (bindW (whenW b (emit e)) (\<lambda>_. m)) r \<longleftrightarrow> resW m r"
  by (cases b) (auto simp: resW_def whenW_def emit_def bindW_def returnW_def)

lemma resW_emit: "resW (bindW (emit e) (\<lambda>_. m)) r \<longleftrightarrow> resW m r"
  by (auto simp: resW_def emit_def bindW_def)

lemma resW_eq: "(\<And>r. resW m r \<longleftrightarrow> resW m' r) \<Longrightarrow> map_option snd m = map_option snd m'"
  by (cases m; cases m') (auto simp: resW_def)

lemma resW_eq': "map_option snd m = map_option snd m' \<Longrightarrow> resW m r \<longleftrightarrow> resW m' r"
  by (cases m; cases m') (auto simp: resW_def)

lemma resW_cong_handleW:
  assumes "\<And>r. resW m r \<longleftrightarrow> resW m' r" "\<And>e r. resW (h e) r \<longleftrightarrow> resW (h' e) r"
  shows "resW (handleW m h) r \<longleftrightarrow> resW (handleW m' h') r"
  using resW_eq[OF assms(1)] resW_eq[OF assms(2)] by (intro resW_eq')
    (cases m; cases m'; auto simp: handleW_def option.map_comp comp_def split_def split: ures.splits)

text \<open>A handler is not invoked when the computation behaves like a finite enumeration.\<close>

lemma resW_handleW_fin:
  assumes "\<And>r. resW m r \<longleftrightarrow> resW (pull cfg X) r" "fin cfg X Q"
  shows "resW (handleW m h) r \<longleftrightarrow> resW (pull cfg X) r"
proof -
  from fin_pull_ok[OF assms(2)] obtain v where "resW (pull cfg X) (UOk v)" ..
  with assms(1) obtain evs where "m = Some (evs, UOk v)" by (auto simp: resW_def)
  then show ?thesis using assms(1) by (simp add: handleW_def)
qed


subsection \<open>Unfolding \<^const>\<open>pull\<close>\<close>

lemma pull_simps:
  "pull cfg S_Empty = returnW None"
  "pull cfg (S_Single x) = returnW (Some (x, S_Empty))"
  "pull cfg (S_Append xq yq) = do {
      r \<leftarrow> pull cfg xq;
      case r of None \<Rightarrow> pull cfg yq | Some (x, xq') \<Rightarrow> returnW (Some (x, S_Append xq' yq))}"
  "pull cfg (S_Maps vname env0 rbinder targs G uarg xq) = do {
      r \<leftarrow> pull cfg xq;
      case r of
        None \<Rightarrow> returnW None
      | Some (x, xq') \<Rightarrow>
          (case x of
            El_E env dpairs \<Rightarrow> do {
              cs \<leftarrow> copycons cfg vname env0 rbinder targs G uarg env dpairs;
              pull cfg (S_Append cs (S_Maps vname env0 rbinder targs G uarg xq'))}
          | _ \<Rightarrow> pull_fail)}"
  "pull cfg (S_ItRight tdepth xq yq) = do {
      r \<leftarrow> pull cfg xq;
      case r of
        None \<Rightarrow> pull cfg yq
      | Some (x, xq') \<Rightarrow>
          (case x of
            El_E env dpairs \<Rightarrow> pull cfg (S_AddUnify tdepth env dpairs (S_ItRight tdepth xq' yq))
          | _ \<Rightarrow> pull_fail)}"
  by (subst pull.simps; simp)+

lemma pull_Proj:
  "pull cfg (S_Proj vname env Ts Us targs rbinder u dpairs head targ X tail) =
    handleW
      (do {
        let (env', args) = make_args vname Ts env Us;
        let dp = (rbinder, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u);
        env'' \<leftarrow> liftM (update X (types_abs Ts (list_comb head args)) env');
        st \<leftarrow> SIMPL (cfg_alg cfg) env'' (dp # dpairs);
        case st of (env2, frigid, fflex) \<Rightarrow>
          returnW (Some (El_E env2 (frigid @ fflex), tail))})
      (\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg tail | _ \<Rightarrow> raiseW e)"
  by (subst pull.simps) simp

lemma pull_AddUnify:
  "pull cfg (S_AddUnify tdepth env dpairs reseq) =
    handleW
      (do {
        whenW (tdepth > cfg_trace_bound cfg \<and> cfg_trace_simp cfg)
          (emit (Ev_Dpairs (STR ''Enter SIMPL'') env dpairs));
        st \<leftarrow> SIMPL (cfg_alg cfg) env dpairs;
        case st of (env', ffs, frs) \<Rightarrow>
          (case frs of
            [] \<Rightarrow> do {
              r \<leftarrow> foldrW (add_ffpair (cfg_alg cfg)) ffs (env', []);
              returnW (Some (El_R (fst r) (snd r), reseq))}
          | dp # frigid' \<Rightarrow>
              if tdepth > cfg_search_bound cfg then do {
                emit Ev_Bound_Exceeded;
                pull cfg reseq}
              else do {
                whenW (tdepth > cfg_trace_bound cfg)
                  (emit (Ev_Dpairs (STR ''Enter MATCH'') env' (frs @ ffs)));
                ms \<leftarrow> MATCH cfg env' dp (frigid' @ ffs);
                pull cfg (S_ItRight (tdepth + 1) ms reseq)})})
      (\<lambda>e. case e of
        CANTUNIFY \<Rightarrow> do {
          whenW (tdepth > cfg_trace_bound cfg) (emit Ev_Failure_Node);
          pull cfg reseq}
      | _ \<Rightarrow> raiseW e)"
  by (subst pull.simps) simp

text \<open>The body of \<^const>\<open>S_AddUnify\<close> after the simplification, without its trace events.\<close>

definition au_cont :: "cfg \<Rightarrow> integer \<Rightarrow> seq \<Rightarrow> sstate \<Rightarrow> (elem \<times> seq) option W" where
  "au_cont cfg tdepth reseq st =
    (case st of (env', ffs, frs) \<Rightarrow>
      (case frs of
        [] \<Rightarrow> do {
          r \<leftarrow> foldrW (add_ffpair (cfg_alg cfg)) ffs (env', []);
          returnW (Some (El_R (fst r) (snd r), reseq))}
      | dp # frigid' \<Rightarrow>
          if tdepth > cfg_search_bound cfg then do {
            emit Ev_Bound_Exceeded;
            pull cfg reseq}
          else do {
            whenW (tdepth > cfg_trace_bound cfg)
              (emit (Ev_Dpairs (STR ''Enter MATCH'') env' (frs @ ffs)));
            ms \<leftarrow> MATCH cfg env' dp (frigid' @ ffs);
            pull cfg (S_ItRight (tdepth + 1) ms reseq)}))"

lemma resW_pull_AddUnify:
  "resW (pull cfg (S_AddUnify tdepth env dps reseq)) r \<longleftrightarrow>
    resW (handleW (bindW (SIMPL (cfg_alg cfg) env dps) (au_cont cfg tdepth reseq))
      (\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg reseq | _ \<Rightarrow> raiseW e)) r"
  unfolding pull_AddUnify
  by (rule resW_cong_handleW)
    (simp_all add: resW_whenW_emit au_cont_def[abs_def] split: uexn.split)

lemma depth_measure: "\<not> sb < td \<Longrightarrow>
    nat (int_of_integer (sb + 1 - (td + 1))) < nat (int_of_integer (sb + 1 - td))"
  by (simp add: less_integer.rep_eq)


subsection \<open>Composition\<close>

lemma fin_Empty[simp]: "fin cfg S_Empty Q"
  by (auto simp: fin_def pull_simps returnW_def intro!: exI[of _ "[]"] evals.Nil)

lemma fin_Single: "Q x \<Longrightarrow> fin cfg (S_Single x) Q"
  by (auto simp: fin_def pull_simps returnW_def intro!: exI[of _ "[x]"] evals.Cons evals.Nil)

lemma evals_Append: "evals cfg xq xs \<Longrightarrow> evals cfg yq ys \<Longrightarrow> evals cfg (S_Append xq yq) (xs @ ys)"
proof (induction arbitrary: ys rule: evals.induct)
  case (Nil s evs)
  have "resW (pull cfg (S_Append s yq)) r \<longleftrightarrow> resW (pull cfg yq) r" for r
    using Nil(1) by (simp add: pull_simps resW_bindW_ok)
  with Nil(2) show ?case using evals_res by auto
next
  case (Cons s evs x s' xs)
  have "pull cfg (S_Append s yq) = Some (evs, UOk (Some (x, S_Append s' yq)))"
    using Cons(1) by (simp add: pull_simps bindW_def returnW_def)
  with Cons(3)[OF Cons(4)] show ?case by (auto intro: evals.Cons)
qed

lemma fin_Append: "fin cfg xq Q \<Longrightarrow> fin cfg yq Q \<Longrightarrow> fin cfg (S_Append xq yq) Q"
  unfolding fin_def using evals_Append by fastforce

text \<open>The sequences that map the elements of an inner sequence:\<close>

lemma fin_map_aux:
  assumes step: "\<And>xq x xq' evs. pull cfg xq = Some (evs, UOk (Some (x, xq'))) \<Longrightarrow> P x \<Longrightarrow>
      \<exists>y. resW (pull cfg (F xq)) (UOk (Some (y, F xq'))) \<and> Q y"
    and nil: "\<And>xq evs. pull cfg xq = Some (evs, UOk None) \<Longrightarrow> resW (pull cfg (F xq)) (UOk None)"
  shows "evals cfg xq xs \<Longrightarrow> \<forall>x\<in>set xs. P x \<Longrightarrow> \<exists>ys. evals cfg (F xq) ys \<and> (\<forall>y\<in>set ys. Q y)"
proof (induction rule: evals.induct)
  case (Nil s evs)
  from nil[OF Nil(1)] show ?case by (auto simp: resW_def intro: evals.Nil)
next
  case (Cons s evs x s' xs)
  from step[OF Cons(1)] Cons(4) obtain y where y: "resW (pull cfg (F s)) (UOk (Some (y, F s')))" "Q y"
    by auto
  from Cons(3) Cons(4) obtain ys where ys: "evals cfg (F s') ys" "\<forall>y\<in>set ys. Q y" by auto
  from y(1) obtain evs' where "pull cfg (F s) = Some (evs', UOk (Some (y, F s')))" by (auto simp: resW_def)
  from evals.Cons[OF this ys(1)] y(2) ys(2) show ?case by (intro exI[of _ "y # ys"]) simp
qed

text \<open>\<^const>\<open>S_Maps\<close>: the copies of an argument for each copy of the other arguments.\<close>

lemma fin_Maps_aux:
  "evals cfg xq xs \<Longrightarrow>
    \<forall>x\<in>set xs. \<exists>env dps cs. x = El_E env dps \<and>
      okW (copycons cfg vname env0 rb targs G uarg env dps) cs \<and> fin cfg cs Q \<Longrightarrow>
    fin cfg (S_Maps vname env0 rb targs G uarg xq) Q"
proof (induction rule: evals.induct)
  case (Nil s evs)
  have "resW (pull cfg (S_Maps vname env0 rb targs G uarg s)) (UOk None)"
    using Nil(1) by (simp add: pull_simps resW_bindW_ok)
  then show ?case by (auto simp: fin_def resW_def intro!: exI[of _ "[]"] evals.Nil)
next
  case (Cons s evs x s' xs)
  from Cons(4) obtain env dps cs where x: "x = El_E env dps"
    and cc: "okW (copycons cfg vname env0 rb targs G uarg env dps) cs" and fc: "fin cfg cs Q"
    by auto
  have IH: "fin cfg (S_Maps vname env0 rb targs G uarg s') Q" using Cons(3,4) by simp
  have "resW (pull cfg (S_Maps vname env0 rb targs G uarg s)) r \<longleftrightarrow>
      resW (pull cfg (S_Append cs (S_Maps vname env0 rb targs G uarg s'))) r" for r
    using Cons(1) cc x by (subst pull_simps(4)) (simp add: resW_bindW_ok)
  from fin_res[OF this fin_Append[OF fc IH]] show ?case .
qed

lemma fin_Maps:
  "fin cfg xq (\<lambda>x. \<exists>env dps cs. x = El_E env dps \<and>
      okW (copycons cfg vname env0 rb targs G uarg env dps) cs \<and> fin cfg cs Q) \<Longrightarrow>
    fin cfg (S_Maps vname env0 rb targs G uarg xq) Q"
  unfolding fin_def[of cfg xq] using fin_Maps_aux by blast

text \<open>A computation succeeds with a result satisfying \<open>P\<close> or fails with \<open>CANTUNIFY\<close>:\<close>

definition cuok :: "'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "cuok m P \<longleftrightarrow> (\<exists>evs. m = Some (evs, UErr CANTUNIFY)) \<or> (\<exists>x. okW m x \<and> P x)"

lemma cuok_mono: "cuok m P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> cuok m Q"
  by (auto simp: cuok_def)

lemma cuok_mono_ok: "cuok m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> cuok m Q"
  by (auto simp: cuok_def)

lemma cuok_raiseW[simp]: "cuok (raiseW CANTUNIFY) P"
  by (simp add: cuok_def raiseW_def)

lemma cuok_returnW[simp]: "cuok (returnW x) P \<longleftrightarrow> P x"
  by (auto simp: cuok_def returnW_def)

lemma cuok_bindW:
  "cuok m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> cuok (f x) Q) \<Longrightarrow> cuok (bindW m f) Q"
  unfolding cuok_def by (auto simp: bindW_def split: option.splits ures.splits)

text \<open>A projection: the copy if the simplification succeeds, followed by the other copies.\<close>

lemma fin_Proj:
  assumes ma: "make_args vname Ts env Us = (env', args)"
    and up: "ok (update X (types_abs Ts (list_comb head args)) env') env''"
    and s: "cuok (SIMPL (cfg_alg cfg) env''
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (\<lambda>(env2, fr, ff). Q (El_E env2 (fr @ ff)))"
    and t: "fin cfg tail Q"
  shows "fin cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail) Q"
proof -
  let ?S = "SIMPL (cfg_alg cfg) env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)"
  from up have "okW (liftM (update X (types_abs Ts (list_comb head args)) env')) env''" by simp
  then obtain evs0 where up': "liftM (update X (types_abs Ts (list_comb head args)) env') = Some (evs0, UOk env'')"
    by blast
  from s consider (cu) evs where "?S = Some (evs, UErr CANTUNIFY)"
    | (ok) env2 fr ff where "okW ?S (env2, fr, ff)" "Q (El_E env2 (fr @ ff))"
    unfolding cuok_def by fast
  then show ?thesis
  proof cases
    case cu
    have "resW (pull cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail)) r \<longleftrightarrow> resW (pull cfg tail) r" for r
      using cu ma up' by (simp add: pull_Proj Let_def bindW_def resW_handleW_err)
    from fin_res[OF this t] show ?thesis .
  next
    case ok
    from ok(1) obtain evs where S: "?S = Some (evs, UOk (env2, fr, ff))" by blast
    have "resW (pull cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail))
        (UOk (Some (El_E env2 (fr @ ff), tail)))"
      using S ma up' by (simp add: pull_Proj Let_def bindW_def handleW_def returnW_def resW_def)
    then obtain evs' where P: "pull cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail) =
        Some (evs', UOk (Some (El_E env2 (fr @ ff), tail)))"
      by (auto simp: resW_def)
    from t obtain ys where ys: "evals cfg tail ys" "\<forall>y\<in>set ys. Q y" by (auto simp: fin_def)
    from evals.Cons[OF P ys(1)] ok(2) ys(2) show ?thesis
      unfolding fin_def by (intro exI[of _ "El_E env2 (fr @ ff) # ys"]) simp
  qed
qed

text \<open>\<^const>\<open>S_ItRight\<close>: the search below each element, followed by the rest.\<close>

lemma fin_ItRight_aux:
  "evals cfg xq xs \<Longrightarrow>
    \<forall>x\<in>set xs. \<exists>env dps. x = El_E env dps \<and> (\<forall>R. fin cfg R Q \<longrightarrow> fin cfg (S_AddUnify td env dps R) Q) \<Longrightarrow>
    fin cfg yq Q \<Longrightarrow> fin cfg (S_ItRight td xq yq) Q"
proof (induction rule: evals.induct)
  case (Nil s evs)
  have "resW (pull cfg (S_ItRight td s yq)) r \<longleftrightarrow> resW (pull cfg yq) r" for r
    using Nil(1) by (subst pull_simps(5)) (simp add: resW_bindW_ok)
  from fin_res[OF this Nil(3)] show ?case .
next
  case (Cons s evs x s' xs)
  from Cons(4) obtain env dps where x: "x = El_E env dps"
    and au: "\<And>R. fin cfg R Q \<Longrightarrow> fin cfg (S_AddUnify td env dps R) Q"
    by auto
  have IH: "fin cfg (S_ItRight td s' yq) Q" using Cons(3,4,5) by simp
  have "resW (pull cfg (S_ItRight td s yq)) r \<longleftrightarrow> resW (pull cfg (S_AddUnify td env dps (S_ItRight td s' yq))) r" for r
    using Cons(1) x by (subst pull_simps(5)) (simp add: resW_bindW_ok)
  from fin_res[OF this au[OF IH]] show ?case .
qed

lemma fin_ItRight:
  "fin cfg xq (\<lambda>x. \<exists>env dps. x = El_E env dps \<and> (\<forall>R. fin cfg R Q \<longrightarrow> fin cfg (S_AddUnify td env dps R) Q)) \<Longrightarrow>
    fin cfg yq Q \<Longrightarrow> fin cfg (S_ItRight td xq yq) Q"
  unfolding fin_def[of cfg xq] using fin_ItRight_aux by blast

end
