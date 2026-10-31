section \<open>Finite Enumerations of Sequences\<close>

theory Unify_Fin
  imports Unify_Simpl_Term
begin

context csig
begin

text \<open>
  \<open>fin cfg s Q\<close>: pulling \<open>s\<close> repeatedly terminates without an exception, after finitely many
  elements, all of which satisfy \<open>Q\<close>. We show how the closures of the sequences compose finite
  enumerations: for each constructor of \<^typ>\<open>seq\<close>, the enumeration is finite if those of the
  sequences it pulls are. Only the result of a computation matters for the enumeration, not
  the trace events it emits.
\<close>

definition fin :: "cfg \<Rightarrow> seq \<Rightarrow> (elem \<Rightarrow> bool) \<Rightarrow> bool" where
  "fin cfg s Q \<longleftrightarrow> (\<exists>xs. evals cfg s xs \<and> (\<forall>x\<in>set xs. Q x))"

lemma fin_mono: "fin cfg s P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> fin cfg s Q"
  by (auto simp: fin_def)

text \<open>The result of a computation, ignoring its events:\<close>

definition resW :: "'a W \<Rightarrow> 'a ures \<Rightarrow> bool" where
  "resW m r \<longleftrightarrow> (\<exists>evs. m = Some (evs, r))"

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

lemma resW_bindW_ok: "m = Some (evs, UOk x) \<Longrightarrow> resW (bindW m f) r \<longleftrightarrow> resW (f x) r"
  by (auto simp: resW_def bindW_def map_option_eq_Some)

lemma resW_handleW_err: "m = Some (evs, UErr e) \<Longrightarrow> resW (handleW m h) r \<longleftrightarrow> resW (h e) r"
  by (auto simp: resW_def handleW_def map_option_eq_Some)


subsection \<open>Unfolding \<^const>\<open>pull\<close>\<close>

lemma pull_simps:
  "pull cfg S_Empty = returnW None"
  "pull cfg (S_Single x) = returnW (Some (x, S_Empty))"
  "pull cfg (S_Append xq yq) = do {
      r \<leftarrow> pull cfg xq;
      case r of None \<Rightarrow> pull cfg yq | Some (x, xq') \<Rightarrow> returnW (Some (x, S_Append xq' yq))}"
  "pull cfg (S_MapAbs a T xq) = do {
      r \<leftarrow> pull cfg xq;
      case r of
        None \<Rightarrow> returnW None
      | Some (x, xq') \<Rightarrow>
          (case x of
            El_C body' env' dpairs' \<Rightarrow> returnW (Some (El_C (Abs a T body') env' dpairs', S_MapAbs a T xq'))
          | _ \<Rightarrow> pull_fail)}"
  "pull cfg (S_MapJoin uhead xq) = do {
      r \<leftarrow> pull cfg xq;
      case r of
        None \<Rightarrow> returnW None
      | Some (x, xq') \<Rightarrow>
          (case x of
            El_D uargs' env' dpairs' \<Rightarrow>
              returnW (Some (El_C (list_comb uhead uargs') env' dpairs', S_MapJoin uhead xq'))
          | _ \<Rightarrow> pull_fail)}"
  "pull cfg (S_MapCons uargs xq) = do {
      r \<leftarrow> pull cfg xq;
      case r of
        None \<Rightarrow> returnW None
      | Some (x, xq') \<Rightarrow>
          (case x of
            El_C uarg' env' dpairs' \<Rightarrow> returnW (Some (El_D (uarg' # uargs) env' dpairs', S_MapCons uargs xq'))
          | _ \<Rightarrow> pull_fail)}"
  "pull cfg (S_MapNewDset vT Ts xq) = do {
      r \<leftarrow> pull cfg xq;
      case r of
        None \<Rightarrow> returnW None
      | Some (x, xq') \<Rightarrow>
          (case x of
            El_C u' env' dpairs' \<Rightarrow> do {
              y \<leftarrow> new_dset vT Ts u' env' dpairs';
              returnW (Some (y, S_MapNewDset vT Ts xq'))}
          | _ \<Rightarrow> pull_fail)}"
  "pull cfg (S_Maps vname rbinder targs uarg xq) = do {
      r \<leftarrow> pull cfg xq;
      case r of
        None \<Rightarrow> returnW None
      | Some (x, xq') \<Rightarrow>
          (case x of
            El_D uargs env dpairs \<Rightarrow> do {
              cs \<leftarrow> copycons cfg vname rbinder targs uarg uargs env dpairs;
              pull cfg (S_Append cs (S_Maps vname rbinder targs uarg xq'))}
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

lemma fin_MapAbs:
  "fin cfg xq (\<lambda>x. \<exists>u env dps. x = El_C u env dps \<and> Q (El_C (Abs a T u) env dps)) \<Longrightarrow>
    fin cfg (S_MapAbs a T xq) Q"
  unfolding fin_def
  by (elim exE conjE, rule fin_map_aux[where F = "S_MapAbs a T"])
    (auto simp: pull_simps bindW_def returnW_def resW_def)

lemma fin_MapJoin:
  "fin cfg xq (\<lambda>x. \<exists>uargs env dps. x = El_D uargs env dps \<and> Q (El_C (list_comb uhead uargs) env dps)) \<Longrightarrow>
    fin cfg (S_MapJoin uhead xq) Q"
  unfolding fin_def
  by (elim exE conjE, rule fin_map_aux[where F = "S_MapJoin uhead"])
    (auto simp: pull_simps bindW_def returnW_def resW_def)

lemma fin_MapCons:
  "fin cfg xq (\<lambda>x. \<exists>u env dps. x = El_C u env dps \<and> Q (El_D (u # uargs) env dps)) \<Longrightarrow>
    fin cfg (S_MapCons uargs xq) Q"
  unfolding fin_def
  by (elim exE conjE, rule fin_map_aux[where F = "S_MapCons uargs"])
    (auto simp: pull_simps bindW_def returnW_def resW_def)

lemma fin_MapNewDset:
  "fin cfg xq (\<lambda>x. \<exists>u env dps y. x = El_C u env dps \<and> okW (new_dset vT Ts u env dps) y \<and> Q y) \<Longrightarrow>
    fin cfg (S_MapNewDset vT Ts xq) Q"
  unfolding fin_def
  by (elim exE conjE, rule fin_map_aux[where F = "S_MapNewDset vT Ts"])
    (auto simp: pull_simps bindW_def returnW_def resW_def map_option_eq_Some)

lemma pull_Proj:
  "pull cfg (S_Proj vname env Ts Us targs rbinder u dpairs head targ tail) =
    handleW
      (do {
        let (env', args) = make_args vname Ts env Us;
        let dp = (rbinder, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u);
        st \<leftarrow> SIMPL (cfg_alg cfg) env' (dp # dpairs);
        case st of (env2, frigid, fflex) \<Rightarrow>
          returnW (Some (El_C (list_comb head args) env2 (frigid @ fflex), tail))})
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

lemma resW_whenW_emit: "resW (bindW (whenW b (emit e)) (\<lambda>_. m)) r \<longleftrightarrow> resW m r"
  by (cases b) (auto simp: resW_def whenW_def emit_def bindW_def returnW_def map_option_eq_Some)

lemma resW_emit: "resW (bindW (emit e) (\<lambda>_. m)) r \<longleftrightarrow> resW m r"
  by (auto simp: resW_def emit_def bindW_def map_option_eq_Some)

text \<open>\<^const>\<open>S_Maps\<close>: the copies of an argument for each copy of the other arguments.\<close>

lemma fin_Maps_aux:
  "evals cfg xq xs \<Longrightarrow>
    \<forall>x\<in>set xs. \<exists>uargs env dps cs. x = El_D uargs env dps \<and>
      okW (copycons cfg vname rb targs uarg uargs env dps) cs \<and> fin cfg cs Q \<Longrightarrow>
    fin cfg (S_Maps vname rb targs uarg xq) Q"
proof (induction rule: evals.induct)
  case (Nil s evs)
  have "resW (pull cfg (S_Maps vname rb targs uarg s)) (UOk None)"
    using Nil(1) by (simp add: pull_simps resW_bindW_ok returnW_def resW_def)
  then show ?case by (auto simp: fin_def resW_def intro!: exI[of _ "[]"] evals.Nil)
next
  case (Cons s evs x s' xs)
  from Cons(4) obtain uargs env dps cs where x: "x = El_D uargs env dps"
    and cc: "okW (copycons cfg vname rb targs uarg uargs env dps) cs" and fc: "fin cfg cs Q"
    by auto
  from cc obtain evs' where cc': "copycons cfg vname rb targs uarg uargs env dps = Some (evs', UOk cs)" by blast
  have IH: "fin cfg (S_Maps vname rb targs uarg s') Q" using Cons(3,4) by simp
  have "resW (pull cfg (S_Maps vname rb targs uarg s)) r \<longleftrightarrow>
      resW (pull cfg (S_Append cs (S_Maps vname rb targs uarg s'))) r" for r
    using Cons(1) cc' x by (subst pull_simps(8)) (simp add: resW_bindW_ok)
  from fin_res[OF this fin_Append[OF fc IH]] show ?case .
qed

lemma fin_Maps:
  "fin cfg xq (\<lambda>x. \<exists>uargs env dps cs. x = El_D uargs env dps \<and>
      okW (copycons cfg vname rb targs uarg uargs env dps) cs \<and> fin cfg cs Q) \<Longrightarrow>
    fin cfg (S_Maps vname rb targs uarg xq) Q"
  unfolding fin_def[of cfg xq] using fin_Maps_aux by blast

text \<open>A projection: the copy if the simplification succeeds, followed by the other copies.\<close>

lemma fin_Proj:
  assumes ma: "make_args vname Ts env Us = (env', args)"
    and s: "cuok (SIMPL (cfg_alg cfg) env'
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (\<lambda>(env2, fr, ff). Q (El_C (list_comb head args) env2 (fr @ ff)))"
    and t: "fin cfg tail Q"
  shows "fin cfg (S_Proj vname env Ts Us targs rb u dps head targ tail) Q"
proof -
  let ?S = "SIMPL (cfg_alg cfg) env' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)"
  from s consider (cu) evs where "?S = Some (evs, UErr CANTUNIFY)"
    | (ok) env2 fr ff where "okW ?S (env2, fr, ff)" "Q (El_C (list_comb head args) env2 (fr @ ff))"
    unfolding cuok_def by fast
  then show ?thesis
  proof cases
    case cu
    have "resW (pull cfg (S_Proj vname env Ts Us targs rb u dps head targ tail)) r \<longleftrightarrow> resW (pull cfg tail) r" for r
      using cu ma by (simp add: pull_Proj Let_def bindW_def resW_handleW_err)
    from fin_res[OF this t] show ?thesis .
  next
    case ok
    from ok(1) obtain evs where S: "?S = Some (evs, UOk (env2, fr, ff))" by blast
    have "resW (pull cfg (S_Proj vname env Ts Us targs rb u dps head targ tail))
        (UOk (Some (El_C (list_comb head args) env2 (fr @ ff), tail)))"
      using S ma by (simp add: pull_Proj Let_def bindW_def handleW_def returnW_def resW_def)
    then obtain evs' where P: "pull cfg (S_Proj vname env Ts Us targs rb u dps head targ tail) =
        Some (evs', UOk (Some (El_C (list_comb head args) env2 (fr @ ff), tail)))"
      by (auto simp: resW_def)
    from t obtain ys where ys: "evals cfg tail ys" "\<forall>y\<in>set ys. Q y" by (auto simp: fin_def)
    from evals.Cons[OF P ys(1)] ok(2) ys(2) show ?thesis
      unfolding fin_def by (intro exI[of _ "El_C (list_comb head args) env2 (fr @ ff) # ys"]) simp
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
    using Nil(1) by (subst pull_simps(9)) (simp add: resW_bindW_ok)
  from fin_res[OF this Nil(3)] show ?case .
next
  case (Cons s evs x s' xs)
  from Cons(4) obtain env dps where x: "x = El_E env dps"
    and au: "\<And>R. fin cfg R Q \<Longrightarrow> fin cfg (S_AddUnify td env dps R) Q"
    by auto
  have IH: "fin cfg (S_ItRight td s' yq) Q" using Cons(3,4,5) by simp
  have "resW (pull cfg (S_ItRight td s yq)) r \<longleftrightarrow> resW (pull cfg (S_AddUnify td env dps (S_ItRight td s' yq))) r" for r
    using Cons(1) x by (subst pull_simps(9)) (simp add: resW_bindW_ok)
  from fin_res[OF this au[OF IH]] show ?case .
qed

lemma fin_ItRight:
  "fin cfg xq (\<lambda>x. \<exists>env dps. x = El_E env dps \<and> (\<forall>R. fin cfg R Q \<longrightarrow> fin cfg (S_AddUnify td env dps R) Q)) \<Longrightarrow>
    fin cfg yq Q \<Longrightarrow> fin cfg (S_ItRight td xq yq) Q"
  unfolding fin_def[of cfg xq] using fin_ItRight_aux by blast


subsection \<open>Flex-flex pairs are solvable\<close>

text \<open>
  The canonical solution of an environment maps each unbound variable to a free variable. Mapping
  it instead to a constant function, whose body is a free variable of its result type, solves
  every flex-flex pair whose heads are unbound: both sides reduce to the free variable of their
  common base type.
\<close>

definition smash_atom :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> indexname \<Rightarrow> dB" where
  "smash_atom W x = Abs_m (length (arg_types (W x))) (dB.Var (code (AFree STR '''' (res_type (W x)))))"

definition smash_sol :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> nat \<Rightarrow> dB" where
  "smash_sol env W = env_map env (smash_atom W)"

lemma smash_atom_props:
  "no_loose_bound (smash_atom W x) 0 \<and> (\<forall>e. (e, tau W) \<turnstile> smash_atom W x : trty (W x))"
proof (intro conjI allI)
  show "no_loose_bound (smash_atom W x) 0" by (simp add: smash_atom_def loose_bound_Abs_m)
  fix e
  let ?As = "arg_types (W x)" and ?R = "res_type (W x)"
  have "(env_ext e (map trty ?As), tau W) \<turnstile> dB.Var (code (AFree STR '''' ?R)) : trty ?R"
    by (rule typing.Var) simp
  from typing_Abs_m[OF this] show "(e, tau W) \<turnstile> smash_atom W x : trty (W x)"
    using trty_foldr[of ?As ?R] arg_res_type[of "W x"] by (simp add: smash_atom_def)
qed

context
  fixes env W
  assumes ac: "acyc env" and ety: "env_typed W env"
begin

theorem smash_solution: "wf_env ar env \<Longrightarrow> solution W (tau W) (smash_sol env W) env"
  unfolding solution_def smash_sol_def
  using env_map_closed[OF ac ety _ smash_atom_props] env_map_typed[OF ac ety _ smash_atom_props]
    env_map_rigid_subst[OF ac ety] env_map_sat[OF ac ety] by blast

lemma smash_side:
  assumes ty: "has_type W Bs t B" and nf: "\<not> is_funT B" and h: "head_of t = Var x T"
    and unb: "vt_lookup (tenv env) x = None"
  shows "mk_subst (smash_sol env W) (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var (code (AFree STR '''' B))"
proof -
  let ?args = "snd (strip_comb t)"
  have t: "t = list_comb (Var x T) ?args" using head_of_list_comb[of t] h by simp
  from ty t obtain As where hv: "has_type W Bs (Var x T) (foldr fun_type As B)"
    and As: "list_all2 (has_type W Bs) ?args As"
    by (metis has_type_list_comb)
  from hv have Wx: "W x = foldr fun_type As B" by (auto elim: has_type.cases)
  have m: "length (arg_types (W x)) = length (map (mk_subst (smash_sol env W) \<circ> tr) ?args)"
    and r: "res_type (W x) = B"
    using arg_res_type_fun[OF nf, of As] list_all2_lengthD[OF As] Wx by simp_all
  have "mk_subst (smash_sol env W) (tr t) =
      smash_atom W x \<degree>\<degree> map (mk_subst (smash_sol env W) \<circ> tr) ?args"
    by (subst t) (simp add: tr_list_comb mk_subst_list_app smash_sol_def env_map_unbound[OF ac ety unb])
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var (code (AFree STR '''' B))"
    using Abs_m_apps_closed_head[of "dB.Var (code (AFree STR '''' B))" _ _ "[]", OF _ m[symmetric]] r
    by (simp add: smash_atom_def)
  finally show ?thesis .
qed

lemma smash_dsolved:
  assumes "ff_shape W dp" "heads_unb env dp"
  shows "dsolved (smash_sol env W) dp"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from assms(1) obtain B where nf: "\<not> is_funT B" and ty: "has_type W (map snd rb) t B"
    "has_type W (map snd rb) u B" and vt: "is_Var (head_of t)" and vu: "is_Var (head_of u)"
    by (auto simp: dp ff_shape_def)
  obtain x T y U where h: "head_of t = Var x T" "head_of u = Var y U"
    using vt vu by (cases "head_of t"; cases "head_of u") auto
  have unb: "vt_lookup (tenv env) x = None" "vt_lookup (tenv env) y = None"
    using assms(2)[unfolded dp heads_unb_def prod.case] h by blast+
  have "mk_subst (smash_sol env W) (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (smash_sol env W) (tr u)"
    using equiv_trans[OF smash_side[OF ty(1) nf h(1) unb(1)] equiv_sym[OF smash_side[OF ty(2) nf h(2) unb(2)]]] .
  then show ?thesis
    by (simp add: dp dsolved_dsolvedB dsolvedB_def equiv_Abs_m)
qed

end

text \<open>
  Hence the flex-flex pairs of a simplification are always solvable, and the flex-flex phase of
  \<^const>\<open>add_ffpair\<close> always terminates normally.
\<close>

lemma smash_cinv:
  assumes "tyinv ar V env ffs" "\<And>dp. dp \<in> set ffs \<Longrightarrow> ff_shape V dp \<and> heads_unb env dp"
  shows "cinv ar V (tau V) (smash_sol env V) env ffs"
proof -
  note ei = env_invD[OF tyinvD(1)[OF assms(1)]]
  show ?thesis
    using assms smash_solution[OF ei(1,3,2)] smash_dsolved[OF ei(1,3)]
    by (auto simp: cinv_def dest: tyinvD)
qed

theorem foldrW_add_ffpair_term:
  assumes "tyinv ar V env ffs" "\<And>dp. dp \<in> set ffs \<Longrightarrow> ff_shape V dp \<and> heads_unb env dp"
  shows "\<exists>r. okW (foldrW (add_ffpair alg) ffs (env, [])) r"
  using foldrW_add_ffpair_complete[OF smash_cinv[OF assms], of alg] assms(2) by blast


subsection \<open>The search\<close>

lemma resW_eq: "(\<And>r. resW m r \<longleftrightarrow> resW m' r) \<Longrightarrow> map_option snd m = map_option snd m'"
  by (cases m; cases m') (auto simp: resW_def)

lemma resW_eq': "map_option snd m = map_option snd m' \<Longrightarrow> resW m r \<longleftrightarrow> resW m' r"
  by (cases m; cases m') (auto simp: resW_def)

lemma resW_cong_bindW:
  assumes "\<And>r. resW m r \<longleftrightarrow> resW m' r" "\<And>x r. resW (f x) r \<longleftrightarrow> resW (f' x) r"
  shows "resW (bindW m f) r \<longleftrightarrow> resW (bindW m' f') r"
  using resW_eq[OF assms(1)] resW_eq[OF assms(2)] by (intro resW_eq')
    (cases m; cases m'; auto simp: bindW_def option.map_comp comp_def split_def split: ures.splits)

lemma resW_cong_handleW:
  assumes "\<And>r. resW m r \<longleftrightarrow> resW m' r" "\<And>e r. resW (h e) r \<longleftrightarrow> resW (h' e) r"
  shows "resW (handleW m h) r \<longleftrightarrow> resW (handleW m' h') r"
  using resW_eq[OF assms(1)] resW_eq[OF assms(2)] by (intro resW_eq')
    (cases m; cases m'; auto simp: handleW_def option.map_comp comp_def split_def split: ures.splits)

lemma resW_bindW_err: "m = Some (evs, UErr e) \<Longrightarrow> resW (bindW m f) r \<longleftrightarrow> r = UErr e"
  by (auto simp: resW_def bindW_def)

lemma resW_handleW_ok: "m = Some (evs, UOk x) \<Longrightarrow> resW (handleW m h) r \<longleftrightarrow> r = UOk x"
  by (auto simp: resW_def handleW_def)

lemma resW_returnW: "resW (returnW x) r \<longleftrightarrow> r = UOk x"
  by (auto simp: resW_def returnW_def)

lemma resW_raiseW: "resW (raiseW e) r \<longleftrightarrow> r = UErr e"
  by (auto simp: resW_def raiseW_def)

lemma fin_pull_ok: "fin cfg s Q \<Longrightarrow> \<exists>v. resW (pull cfg s) (UOk v)"
  by (auto simp: fin_def resW_def elim: evals.cases)

text \<open>A handler is not invoked when the computation behaves like a finite enumeration.\<close>

lemma resW_handleW_fin:
  assumes "\<And>r. resW m r \<longleftrightarrow> resW (pull cfg X) r" "fin cfg X Q"
  shows "resW (handleW m h) r \<longleftrightarrow> resW (pull cfg X) r"
proof -
  from fin_pull_ok[OF assms(2)] obtain v where "resW (pull cfg X) (UOk v)" ..
  with assms(1) obtain evs where "m = Some (evs, UOk v)" by (auto simp: resW_def)
  then show ?thesis using assms(1) by (simp add: handleW_def)
qed

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
  apply (rule resW_cong_handleW)
  subgoal by (simp add: resW_whenW_emit au_cont_def[abs_def])
  subgoal for e by (cases e) (simp_all add: resW_whenW_emit)
  done

text \<open>
  \<open>match_fin\<close>: \<^const>\<open>MATCH\<close> on a flex-rigid pair yields, unless it fails, a finite
  enumeration of new problems that satisfy the invariant.
\<close>

definition match_fin :: "cfg \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> bool" where
  "match_fin cfg ar \<longleftrightarrow> (\<forall>V env dp dps. tyinv ar V env (dp # dps) \<longrightarrow> fr_shape V dp \<longrightarrow> heads_unb env dp \<longrightarrow>
    cuok (MATCH cfg env dp dps) (\<lambda>ms. fin cfg ms (\<lambda>x. \<exists>env' dps' V'. x = El_E env' dps' \<and> tyinv ar V' env' dps')))"

lemma match_finD:
  "match_fin cfg ar \<Longrightarrow> tyinv ar V env (dp # dps) \<Longrightarrow> fr_shape V dp \<Longrightarrow> heads_unb env dp \<Longrightarrow>
    cuok (MATCH cfg env dp dps) (\<lambda>ms. fin cfg ms (\<lambda>x. \<exists>env' dps' V'. x = El_E env' dps' \<and> tyinv ar V' env' dps'))"
  unfolding match_fin_def by blast

lemma depth_measure: "\<not> sb < td \<Longrightarrow>
    nat (int_of_integer (sb + 1 - (td + 1))) < nat (int_of_integer (sb + 1 - td))"
  by (simp add: less_integer.rep_eq)

lemma tyinv_set: "set dps = set dps' \<Longrightarrow> tyinv ar V env dps \<longleftrightarrow> tyinv ar V env dps'"
  by (simp add: tyinv_def)

lemma fin_AddUnify_aux:
  assumes M: "match_fin cfg ar"
    and QR: "\<And>V env ffs r. tyinv ar V env ffs \<Longrightarrow> (\<And>dp. dp \<in> set ffs \<Longrightarrow> ff_shape V dp \<and> heads_unb env dp) \<Longrightarrow>
      okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env, [])) r \<Longrightarrow> Q (El_R (fst r) (snd r))"
  shows "tyinv ar V env dps \<Longrightarrow> fin cfg R Q \<Longrightarrow> fin cfg (S_AddUnify td env dps R) Q"
proof (induction "nat (int_of_integer (cfg_search_bound cfg + 1 - td))" arbitrary: td V env dps R rule: less_induct)
  case less
  let ?S = "SIMPL (cfg_alg cfg) env dps"
  let ?H = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg R | _ \<Rightarrow> raiseW e"
  have red: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW (bindW ?S (au_cont cfg td R)) ?H) r" for r
    by (rule resW_pull_AddUnify)
  from SIMPL_term[OF less.prems(1), of "cfg_alg cfg"] consider (cu) evs where "?S = Some (evs, UErr CANTUNIFY)"
    | (ok) st where "okW ?S st" "tsimpl_res ar V dps env st"
    unfolding cuok_def by blast
  then show ?case
  proof cases
    case cu
    have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
      using cu by (simp add: red bindW_def resW_handleW_err)
    from fin_res[OF this less.prems(2)] show ?thesis .
  next
    case ok
    obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
    from ok(1) obtain evs where S: "?S = Some (evs, UOk st)" by blast
    have red': "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW (au_cont cfg td R st) ?H) r" for r
      unfolding red by (rule resW_cong_handleW) (simp_all add: resW_bindW_ok[OF S])
    from ok(2) have inv': "tyinv ar V env' (ffs @ frs)" and ffsh: "\<And>dp. dp \<in> set ffs \<Longrightarrow> ff_shape V dp"
      and frsh: "\<And>dp. dp \<in> set frs \<Longrightarrow> fr_shape V dp" and hu: "\<And>dp. dp \<in> set (ffs @ frs) \<Longrightarrow> heads_unb env' dp"
      by (auto simp: st tsimpl_res_def)
    show ?thesis
    proof (cases frs)
      case Nil
      from foldrW_add_ffpair_term[of ar V env' ffs "cfg_alg cfg"] inv' ffsh hu Nil
      obtain r evs2 where f: "foldrW (add_ffpair (cfg_alg cfg)) ffs (env', []) = Some (evs2, UOk r)"
        by auto
      have "resW (pull cfg (S_AddUnify td env dps R)) (UOk (Some (El_R (fst r) (snd r), R)))"
        unfolding red' by (simp add: st Nil au_cont_def f handleW_def bindW_def returnW_def resW_def)
      then obtain evs' where P: "pull cfg (S_AddUnify td env dps R) =
          Some (evs', UOk (Some (El_R (fst r) (snd r), R)))"
        by (auto simp: resW_def)
      from less.prems(2) obtain ys where ys: "evals cfg R ys" "\<forall>y\<in>set ys. Q y" by (auto simp: fin_def)
      have "Q (El_R (fst r) (snd r))" by (rule QR[of V env' ffs]) (use inv' ffsh hu Nil f in auto)
      from evals.Cons[OF P ys(1)] this ys(2) show ?thesis
        unfolding fin_def by (intro exI[of _ "El_R (fst r) (snd r) # ys"]) simp
    next
      case (Cons dp frs')
      show ?thesis
      proof (cases "cfg_search_bound cfg < td")
        case True
        have "resW (au_cont cfg td R st) r \<longleftrightarrow> resW (pull cfg R) r" for r
          by (simp add: au_cont_def st Cons True resW_emit)
        then have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
          unfolding red' by (rule resW_handleW_fin[OF _ less.prems(2)])
        from fin_res[OF this less.prems(2)] show ?thesis .
      next
        case False
        have "set (dp # frs' @ ffs) = set (ffs @ frs)" by (auto simp: Cons)
        from tyinv_set[OF this] inv' have invM: "tyinv ar V env' (dp # frs' @ ffs)" by blast
        let ?M = "MATCH cfg env' dp (frs' @ ffs)"
        from match_finD[OF M invM frsh[of dp] hu[of dp]] Cons consider (cu) evs where "?M = Some (evs, UErr CANTUNIFY)"
          | (mok) ms where "okW ?M ms" "fin cfg ms (\<lambda>x. \<exists>env' dps' V'. x = El_E env' dps' \<and> tyinv ar V' env' dps')"
          unfolding cuok_def by auto
        then show ?thesis
        proof cases
          case cu
          have "resW (au_cont cfg td R st) r \<longleftrightarrow> resW (raiseW CANTUNIFY) r" for r
            by (simp add: au_cont_def st Cons False resW_whenW_emit resW_bindW_err[OF cu] resW_raiseW)
          then have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
            unfolding red' by (subst resW_cong_handleW[of _ "raiseW CANTUNIFY" ?H ?H])
              (simp_all add: raiseW_def resW_handleW_err)
          from fin_res[OF this less.prems(2)] show ?thesis .
        next
          case mok
          from mok(1) obtain evs where Mok: "?M = Some (evs, UOk ms)" by blast
          have IH: "fin cfg (S_AddUnify (td + 1) env'' dps'' R') Q"
            if "tyinv ar V'' env'' dps''" "fin cfg R' Q" for V'' env'' dps'' R'
            using less.hyps[OF depth_measure[OF False] that] .
          have "fin cfg (S_ItRight (td + 1) ms R) Q"
            by (rule fin_ItRight[OF fin_mono[OF mok(2)] less.prems(2)]) (use IH in blast)
          moreover have "resW (au_cont cfg td R st) r \<longleftrightarrow> resW (pull cfg (S_ItRight (td + 1) ms R)) r" for r
            by (simp add: au_cont_def st Cons False resW_whenW_emit resW_bindW_ok[OF Mok])
          ultimately have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg (S_ItRight (td + 1) ms R)) r" for r
            unfolding red' by (intro resW_handleW_fin)
          from fin_res[OF this] \<open>fin cfg (S_ItRight (td + 1) ms R) Q\<close> show ?thesis by blast
        qed
      qed
    qed
  qed
qed

text \<open>
  The unifiers that the search returns: an environment in the invariant and remaining flex-flex
  pairs as in @{const tpok}, relative to an environment \<open>env0\<close> that it extends by flexible
  bindings only.
\<close>

definition rres :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "rres ar env tps \<longleftrightarrow> (\<exists>V env0. env_inv ar V env \<and> flexb env0 env \<and> extends env0 env \<and> fresh_env env0 \<and>
    maxidx env0 \<le> maxidx env \<and> (\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab))"

lemma foldrW_add_ffpair_rres:
  assumes "tyinv ar V env ffs" "\<And>dp. dp \<in> set ffs \<Longrightarrow> ff_shape V dp \<and> heads_unb env dp"
    and r: "okW (foldrW (add_ffpair alg) ffs (env, [])) r"
  shows "rres ar (fst r) (snd r)"
proof -
  from foldrW_add_ffpair_complete[OF smash_cinv[OF assms(1,2)], of alg] assms(2)
  obtain env' tps' V' \<sigma>' where c: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps')"
    "cinv ar V' (tau V) \<sigma>' env' []" "maxidx env \<le> maxidx env'" "extends env env'" "flexb env env'"
    "\<forall>ab\<in>set tps'. tpok ar V' env (maxidx env') ab"
    by blast
  from c(1) r have "r = (env', tps')" by auto
  moreover have "fresh_env env" by (rule env_invD(4)[OF tyinvD(1)[OF assms(1)]])
  ultimately show ?thesis using cinvD(1)[OF c(2)] c(3-6) unfolding rres_def by auto
qed

text \<open>Hence \<^const>\<open>hounifiers\<close> and \<^const>\<open>unifiers\<close> enumerate finitely many unifiers, if \<^const>\<open>MATCH\<close> does.\<close>

theorem hounifiers_fin_match:
  assumes "match_fin cfg ar" "tyinv ar V env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> rres ar env' tps)"
  unfolding hounifiers_def
  by (rule fin_AddUnify_aux[OF assms(1) _ assms(2) fin_Empty]) (use foldrW_add_ffpair_rres in blast)

theorem unifiers_fin_match:
  assumes "match_fin cfg ar" "tyinv ar V env (dps_of tus)"
  obtains s where "unifiers alg env tus = Some (Ok s)"
    "fin cfg s (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> rres ar env' tps)"
proof (rule unifiers_cases[OF assms(2), of alg])
  fix env'
  assume ok: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some (Ok env')"
    "unifiers alg env tus = Some (Ok (S_Single (El_R env' [])))"
  from foldM_unify[OF assms(2), of alg] ok(1) obtain V' where ei: "env_inv ar V' env'" by auto
  have "rres ar env' []" unfolding rres_def
    by (intro exI[of _ V'] exI[of _ env']) (simp add: ei extends_refl env_invD(4)[OF ei])
  then show thesis using ok(2) by (auto intro: that fin_Single)
qed (auto intro: that hounifiers_fin_match[OF assms])

end

end
