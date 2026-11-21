section \<open>Finite Enumerations with Names at Two Types\<close>

theory Unify_Seq_Dfd
  imports Unify_Flexflex_Dfd Unify_Match_Fin
begin

text \<open>
  With names at two types, pulling a sequence of \<open>MATCH\<close> or of the search may end with one of the
  exceptions that the computations can raise without the hypothesis on the names: the clash of
  \<^const>\<open>var_clash\<close>, or \<open>TERM\<close> from \<open>add_ffpair\<close> (\<open>ffexn\<close>). No handler catches them.
  \<open>cfin cfg s Q\<close>: pulling \<open>s\<close> repeatedly terminates after finitely many elements, all of which
  satisfy \<open>Q\<close>, at the end of the sequence or with one of these exceptions.
\<close>

context pure_sig_gen
begin

definition gexn :: "uexn \<Rightarrow> bool" where
  "gexn e \<longleftrightarrow> clashW e \<or> (loose \<noteq> {} \<and> ffexn e)"

lemma gexn_simps [simp]: "\<not> gexn CANTUNIFY" "\<not> gexn ASSIGN" "\<not> gexn CHANGE_FAIL" "\<not> gexn Bind"
  by (simp_all add: gexn_def ffexn_def confW_def)

lemma gexn_clashW: "clashW e \<Longrightarrow> gexn e" and gexn_ffexn: "loose \<noteq> {} \<Longrightarrow> ffexn e \<Longrightarrow> gexn e"
  by (simp_all add: gexn_def)

lemma gexn_PExn: "gexn e \<Longrightarrow> \<exists>x. e = PExn x"
  by (auto simp: gexn_def clashW_def ffexn_def confW_def)

inductive evalx :: "cfg \<Rightarrow> seq \<Rightarrow> elem list \<Rightarrow> bool" for cfg where
  Nil: "pull cfg s = Some (evs, Ok None) \<Longrightarrow> evalx cfg s []"
| Exn: "pull cfg s = Some (evs, Err e) \<Longrightarrow> gexn e \<Longrightarrow> evalx cfg s []"
| Cons: "pull cfg s = Some (evs, Ok (Some (x, s'))) \<Longrightarrow> evalx cfg s' xs \<Longrightarrow> evalx cfg s (x # xs)"

definition cfin :: "cfg \<Rightarrow> seq \<Rightarrow> (elem \<Rightarrow> bool) \<Rightarrow> bool" where
  "cfin cfg s Q \<longleftrightarrow> (\<exists>xs. evalx cfg s xs \<and> (\<forall>x\<in>set xs. Q x))"

lemma evals_evalx: "evals cfg s xs \<Longrightarrow> evalx cfg s xs"
  by (induction rule: evals.induct) (auto intro: evalx.intros)

text \<open>Without loose names no exception of \<^const>\<open>gexn\<close> occurs, and the enumeration is total:\<close>

lemma gexn_loose: "gexn e \<Longrightarrow> loose \<noteq> {}"
  by (auto simp: gexn_def clashW_def clashx_def)

lemma evalx_evals: "evalx cfg s xs \<Longrightarrow> loose = {} \<Longrightarrow> evals cfg s xs"
proof (induction rule: evalx.induct)
  case (Exn s evs e)
  from gexn_loose[OF Exn(2)] Exn(3) show ?case by blast
qed (auto intro: evals.intros)

lemma cfin_fin: "loose = {} \<Longrightarrow> cfin cfg s Q \<Longrightarrow> fin cfg s Q"
  unfolding fin_def cfin_def using evalx_evals by blast

lemma fin_cfin: "fin cfg s Q \<Longrightarrow> cfin cfg s Q"
  unfolding fin_def cfin_def using evals_evalx by blast

lemma cfin_mono: "cfin cfg s P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> cfin cfg s Q"
  by (auto simp: cfin_def)

lemma evalx_res:
  assumes "\<And>r. resW (pull cfg s') r \<longleftrightarrow> resW (pull cfg s) r"
  shows "evalx cfg s xs \<Longrightarrow> evalx cfg s' xs"
proof (erule evalx.cases)
  fix s0 evs assume "s = s0" "xs = []" "pull cfg s0 = Some (evs, Ok None)"
  with assms[of "Ok None"] show "evalx cfg s' xs" by (auto simp: resW_def intro: evalx.Nil)
next
  fix s0 evs e assume "s = s0" "xs = []" "pull cfg s0 = Some (evs, Err e)" "gexn e"
  with assms[of "Err e"] show "evalx cfg s' xs" by (auto simp: resW_def intro: evalx.Exn)
next
  fix s0 evs x s1 xs' assume "s = s0" "xs = x # xs'" "pull cfg s0 = Some (evs, Ok (Some (x, s1)))"
    "evalx cfg s1 xs'"
  with assms[of "Ok (Some (x, s1))"] show "evalx cfg s' xs" by (auto simp: resW_def intro: evalx.Cons)
qed

lemma cfin_res:
  "(\<And>r. resW (pull cfg s') r \<longleftrightarrow> resW (pull cfg s) r) \<Longrightarrow> cfin cfg s Q \<Longrightarrow> cfin cfg s' Q"
  by (auto simp: cfin_def intro: evalx_res)

lemma cfin_raise: "pull cfg s = Some (evs, Err e) \<Longrightarrow> gexn e \<Longrightarrow> cfin cfg s Q"
  by (auto simp: cfin_def intro!: exI[of _ "[]"] evalx.Exn)

lemma cfin_Empty [simp]: "cfin cfg S_Empty Q"
  by (rule fin_cfin) simp

lemma cfin_Single: "Q x \<Longrightarrow> cfin cfg (S_Single x) Q"
  by (rule fin_cfin) (rule fin_Single)

lemma evalx_Append: "evalx cfg xq xs \<Longrightarrow> \<forall>x\<in>set xs. Q x \<Longrightarrow> cfin cfg yq Q \<Longrightarrow> cfin cfg (S_Append xq yq) Q"
proof (induction rule: evalx.induct)
  case (Nil s evs)
  have "resW (pull cfg (S_Append s yq)) r \<longleftrightarrow> resW (pull cfg yq) r" for r
    using Nil(1) by (simp add: pull_simps resW_bindW_ok)
  from cfin_res[OF this Nil(3)] show ?case .
next
  case (Exn s evs e)
  have "pull cfg (S_Append s yq) = Some (evs, Err e)" using Exn(1) by (simp add: pull_simps bindW_def)
  from cfin_raise[OF this Exn(2)] show ?case .
next
  case (Cons s evs x s' xs)
  have "pull cfg (S_Append s yq) = Some (evs, Ok (Some (x, S_Append s' yq)))"
    using Cons(1) by (simp add: pull_simps bindW_def returnW_def)
  moreover from Cons(3) Cons(4,5) obtain zs where "evalx cfg (S_Append s' yq) zs" "\<forall>z\<in>set zs. Q z"
    by (auto simp: cfin_def)
  ultimately show ?case using Cons(4) unfolding cfin_def by (intro exI[of _ "x # zs"]) (auto intro: evalx.Cons)
qed

lemma cfin_Append: "cfin cfg xq Q \<Longrightarrow> cfin cfg yq Q \<Longrightarrow> cfin cfg (S_Append xq yq) Q"
  unfolding cfin_def[of cfg xq] using evalx_Append by blast

text \<open>\<^const>\<open>S_Maps\<close>: the copies of an argument for each copy of the other arguments.\<close>

lemma cfin_Maps_aux:
  "evalx cfg xq xs \<Longrightarrow>
    \<forall>x\<in>set xs. \<exists>env dps. x = El_E env dps \<and>
      cxokE (\<lambda>_. False) (copycons cfg vname env0 rb targs G uarg env dps) (\<lambda>cs. cfin cfg cs Q) \<Longrightarrow>
    cfin cfg (S_Maps vname env0 rb targs G uarg xq) Q"
proof (induction rule: evalx.induct)
  case (Nil s evs)
  have "resW (pull cfg (S_Maps vname env0 rb targs G uarg s)) (Ok None)"
    using Nil(1) by (simp add: pull_simps resW_bindW_ok)
  then show ?case by (auto simp: cfin_def resW_def intro!: exI[of _ "[]"] evalx.Nil)
next
  case (Exn s evs e)
  have "pull cfg (S_Maps vname env0 rb targs G uarg s) = Some (evs, Err e)"
    using Exn(1) by (simp add: pull_simps bindW_def)
  from cfin_raise[OF this Exn(2)] show ?case .
next
  case (Cons s evs x s' xs)
  from Cons(4) obtain env dps where x: "x = El_E env dps"
    and cc: "cxokE (\<lambda>_. False) (copycons cfg vname env0 rb targs G uarg env dps) (\<lambda>cs. cfin cfg cs Q)"
    by auto
  have IH: "cfin cfg (S_Maps vname env0 rb targs G uarg s') Q" using Cons(3,4) by simp
  from cc consider (err) evs' e where "copycons cfg vname env0 rb targs G uarg env dps = Some (evs', Err e)" "clashW e"
    | (ok) cs where "okW (copycons cfg vname env0 rb targs G uarg env dps) cs" "cfin cfg cs Q"
    unfolding cxokE_def by blast
  then show ?case
  proof cases
    case err
    have "resW (pull cfg (S_Maps vname env0 rb targs G uarg s)) (Err e)"
      using Cons(1) x err(1) by (subst pull_simps(4)) (simp add: resW_bindW_ok resW_def bindW_def)
    then obtain evs'' where "pull cfg (S_Maps vname env0 rb targs G uarg s) = Some (evs'', Err e)"
      by (auto simp: resW_def)
    from cfin_raise[OF this gexn_clashW[OF err(2)]] show ?thesis .
  next
    case ok
    have "resW (pull cfg (S_Maps vname env0 rb targs G uarg s)) r \<longleftrightarrow>
        resW (pull cfg (S_Append cs (S_Maps vname env0 rb targs G uarg s'))) r" for r
      using Cons(1) ok(1) x by (subst pull_simps(4)) (simp add: resW_bindW_ok)
    from cfin_res[OF this cfin_Append[OF ok(2) IH]] show ?thesis .
  qed
qed

lemma cfin_Maps:
  "cfin cfg xq (\<lambda>x. \<exists>env dps. x = El_E env dps \<and>
      cxokE (\<lambda>_. False) (copycons cfg vname env0 rb targs G uarg env dps) (\<lambda>cs. cfin cfg cs Q)) \<Longrightarrow>
    cfin cfg (S_Maps vname env0 rb targs G uarg xq) Q"
  unfolding cfin_def[of cfg xq] using cfin_Maps_aux by blast

text \<open>A projection: the copy if the simplification succeeds, followed by the other copies.\<close>

lemma cfin_Proj:
  assumes ma: "make_args vname Ts env Us = (env', args)"
    and up: "ok (update X (types_abs Ts (list_comb head args)) env') env''"
    and s: "ccuok (SIMPL (cfg_alg cfg) env''
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (\<lambda>(env2, fr, ff). Q (El_E env2 (fr @ ff)))"
    and t: "cfin cfg tail Q"
  shows "cfin cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail) Q"
proof -
  let ?S = "SIMPL (cfg_alg cfg) env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)"
  from up have "okW (liftM (update X (types_abs Ts (list_comb head args)) env')) env''" by simp
  then obtain evs0 where up': "liftM (update X (types_abs Ts (list_comb head args)) env') = Some (evs0, Ok env'')"
    by blast
  from s consider (cu) evs where "?S = Some (evs, Err CANTUNIFY)"
    | (cl) evs e where "?S = Some (evs, Err e)" "clashW e"
    | (ok) env2 fr ff where "okW ?S (env2, fr, ff)" "Q (El_E env2 (fr @ ff))"
    unfolding cxokE_def by fast
  then show ?thesis
  proof cases
    case cu
    have "resW (pull cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail)) r \<longleftrightarrow> resW (pull cfg tail) r" for r
      using cu ma up' by (simp add: pull_Proj Let_def bindW_def resW_handleW_err)
    from cfin_res[OF this t] show ?thesis .
  next
    case cl
    then obtain x where ex: "e = PExn x" by (auto simp: clashW_def)
    have "resW (pull cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail)) (Err e)"
      using cl(1) ma up' ex by (simp add: pull_Proj Let_def bindW_def handleW_def raiseW_def resW_def)
    then obtain evs' where "pull cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail) = Some (evs', Err e)"
      by (auto simp: resW_def)
    from cfin_raise[OF this gexn_clashW[OF cl(2)]] show ?thesis .
  next
    case ok
    from ok(1) obtain evs where S: "?S = Some (evs, Ok (env2, fr, ff))" by blast
    have "resW (pull cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail))
        (Ok (Some (El_E env2 (fr @ ff), tail)))"
      using S ma up' by (simp add: pull_Proj Let_def bindW_def handleW_def returnW_def resW_def)
    then obtain evs' where P: "pull cfg (S_Proj vname env Ts Us targs rb u dps head targ X tail) =
        Some (evs', Ok (Some (El_E env2 (fr @ ff), tail)))"
      by (auto simp: resW_def)
    from t obtain ys where ys: "evalx cfg tail ys" "\<forall>y\<in>set ys. Q y" by (auto simp: cfin_def)
    from evalx.Cons[OF P ys(1)] ok(2) ys(2) show ?thesis
      unfolding cfin_def by (intro exI[of _ "El_E env2 (fr @ ff) # ys"]) simp
  qed
qed

text \<open>\<^const>\<open>S_ItRight\<close>: the search below each element, followed by the rest.\<close>

lemma cfin_ItRight_aux:
  "evalx cfg xq xs \<Longrightarrow>
    \<forall>x\<in>set xs. \<exists>env dps. x = El_E env dps \<and> (\<forall>R. cfin cfg R Q \<longrightarrow> cfin cfg (S_AddUnify td env dps R) Q) \<Longrightarrow>
    cfin cfg yq Q \<Longrightarrow> cfin cfg (S_ItRight td xq yq) Q"
proof (induction rule: evalx.induct)
  case (Nil s evs)
  have "resW (pull cfg (S_ItRight td s yq)) r \<longleftrightarrow> resW (pull cfg yq) r" for r
    using Nil(1) by (subst pull_simps(5)) (simp add: resW_bindW_ok)
  from cfin_res[OF this Nil(3)] show ?case .
next
  case (Exn s evs e)
  have "pull cfg (S_ItRight td s yq) = Some (evs, Err e)"
    using Exn(1) by (simp add: pull_simps bindW_def)
  from cfin_raise[OF this Exn(2)] show ?case .
next
  case (Cons s evs x s' xs)
  from Cons(4) obtain env dps where x: "x = El_E env dps"
    and au: "\<And>R. cfin cfg R Q \<Longrightarrow> cfin cfg (S_AddUnify td env dps R) Q"
    by auto
  have IH: "cfin cfg (S_ItRight td s' yq) Q" using Cons(3,4,5) by simp
  have "resW (pull cfg (S_ItRight td s yq)) r \<longleftrightarrow> resW (pull cfg (S_AddUnify td env dps (S_ItRight td s' yq))) r" for r
    using Cons(1) x by (subst pull_simps(5)) (simp add: resW_bindW_ok)
  from cfin_res[OF this au[OF IH]] show ?case .
qed

lemma cfin_ItRight:
  "cfin cfg xq (\<lambda>x. \<exists>env dps. x = El_E env dps \<and> (\<forall>R. cfin cfg R Q \<longrightarrow> cfin cfg (S_AddUnify td env dps R) Q)) \<Longrightarrow>
    cfin cfg yq Q \<Longrightarrow> cfin cfg (S_ItRight td xq yq) Q"
  unfolding cfin_def[of cfg xq] using cfin_ItRight_aux by blast

subsection \<open>Computations that return a sequence\<close>

lemma cxokE_liftM_return: "m = return x \<Longrightarrow> cxokE Xe (f x) Q \<Longrightarrow> cxokE Xe (bindW (liftM m) f) Q"
  by (simp add: liftM_def return_def bindW_def option.map_id)

lemma cxokE_handle_CANTUNIFY_ret:
  assumes "ccuok m P" "\<And>x. P x \<Longrightarrow> Q x" "Q r"
  shows "ccuok (handleW m (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e)) Q"
proof (rule cxokE_handleW[OF cxokE_mono[OF assms(1) assms(2)]])
  show "ccuok ((\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e) CANTUNIFY) Q" using assms(3) by simp
qed (auto simp: clashW_def)

lemma cxokE_noCU: "ccuok m P \<Longrightarrow> noCU m \<Longrightarrow> cxokE (\<lambda>_. False) m P"
  unfolding cxokE_def noCU_def by auto

lemma cxokE_bind_okW:
  assumes "okW m x" "cxokE Xe (k x) Q"
  shows "cxokE Xe (bindW m k) Q"
  by (rule cxokE_bindW[where P = "\<lambda>y. y = x", OF cxokE_okI[OF assms(1) refl]]) (use assms(2) in simp)

lemma foldrW_cxokE_cfin:
  assumes "\<And>x b. x \<in> set xs \<Longrightarrow> cfin cfg b Q \<Longrightarrow> cxokE Xe (f x b) (\<lambda>s. cfin cfg s Q)" "cfin cfg b0 Q"
  shows "cxokE Xe (foldrW f xs b0) (\<lambda>s. cfin cfg s Q)"
  using assms(1) by (induction xs) (auto intro: assms(2) cxokE_bindW)

lemma cfin_mres_mono:
  "cfin cfg s (mres A1 env1) \<Longrightarrow> A0 \<subseteq> A1 \<Longrightarrow> tnew A0 env0 A1 env1 \<Longrightarrow> maxidx env0 \<le> maxidx env1 \<Longrightarrow>
    cfin cfg s (mres A0 env0)"
  by (erule cfin_mono) (rule mres_mono)

end

end
