section \<open>The Outcomes of Unification on Problems with a Name at Two Types\<close>

theory Unify_Outcome
  imports Unify_Results_Complete Unify_Smash_Typed Unify_Complete_Two_Types
begin

text \<open>
  The unifiers identify schematic variables by their names. If a name occurs with two types,
  soundness holds for typed solutions (theories \<open>Pattern_Typed_Unifier\<close>, \<open>Unify_Typed_Results\<close>),
  but completeness does not: \<open>unify_incomplete_L\<close> is a solvable problem on which pattern
  unification fails with \<open>Unif\<close>, without an exception that would tell the failure from a
  problem without solutions. So there is no theorem of the form ``the unifier is complete, or
  it raises an exception''.

  This theory states what does hold, in one theorem per unifier and without a parameter for the
  loose names. On a well-formed problem pattern unification terminates with one of five outcomes
  (\<open>unify_outcome\<close>). The two exceptions \<open>TYPE "Variable has two distinct types"\<close> and
  \<open>Fail "mk_ff_list"\<close> occur only if a name has two types that the type environment does not
  identify. A result is sound for every certified solution of its type environment; it is most
  general among the solutions that give every name one type, and \<open>Unif\<close> means that there is
  no such solution. For such a solution \<open>TYPE\<close> can still be raised (\<open>unify_clash_solvable\<close>).
  The solutions that keep a name at two types are outside the completeness statement:
  \<open>unify_incomplete_L\<close> is a problem with such a solution on which the unifier fails with
  \<open>Unif\<close>, and \<open>unify_fail_solvable\<close> one on which it raises \<open>Fail\<close>.

  For \<open>Unify.unifiers\<close> the theorem is \<open>unifiers_outcome\<close>: the sequence is made and its
  enumeration ends, possibly with one of three exceptions; every unifier of the enumeration is
  sound for typed solutions; exceptions occur only if the names are not consistent, and for
  consistent names the enumeration is complete within the bounds of the configuration.
  Completeness of \<open>Unify.unifiers\<close> for the one-type solutions of a problem whose names are not
  consistent is not proved.
\<close>


subsection \<open>Pattern unification\<close>

context pure_sig
begin

text \<open>
  A well-formed problem: the invariants of the type environment, an acyclic term environment
  that is well-typed under every certified solution of the type environment, two closed terms
  of one type under each such solution, and indices below the maximal index. Nothing is asked
  of the types of the names.
\<close>

definition wfprob :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "wfprob A env s t \<longleftrightarrow> finite A \<and> tvinv A env \<and> scert alg (tyenv env) \<and>
    tcert alg (tvars_env (tyenv env) \<union> A) \<and> tsorted alg (tyenv env) \<and> acyc env \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow>
      wt_env \<rho> env \<and> (\<exists>e T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T)) \<and>
    below (maxidx env) (vars s \<union> vars t \<union> evars env) \<and>
    ttvars s \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<and> closed s \<and> closed t"

text \<open>The names of a set of variables and of the environment are consistent: every name has one
  type under every certified solution of the type environment.\<close>

definition ncons :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "ncons env X \<longleftrightarrow> (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> vcons \<rho> (X \<union> evars env))"

text \<open>A solution of the problem that gives every name one type:\<close>

definition sol1 :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "sol1 \<rho> \<sigma> env s t \<longleftrightarrow> solution \<rho> \<sigma> env \<and> wt_env \<rho> env \<and> vcons \<rho> (vars s \<union> vars t \<union> evars env) \<and>
    (\<exists>e T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T) \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"

text \<open>
  The outcomes of \<^const>\<open>unify\<close> on a well-formed problem. A result is an acyclic extension of
  the environment; it is sound for every certified solution of its type environment, with no
  hypothesis on the names; and every solution of the problem that gives every name one type
  agrees, up to the maximal index, with a solution of the result. \<open>Unif\<close> is raised only if
  there is no such solution, and the exceptions of the last two cases only if the names are not
  consistent. No other exception is raised.
\<close>

theorem unify_outcome:
  assumes wf: "wfprob A env s t"
  obtains (Success) env' where "unify alg s t env = return env'" "extends env env'" "acyc env'"
      "\<And>\<rho>. wsinst alg \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> tsol (tyenv env') \<rho> \<Longrightarrow>
        \<exists>\<sigma>. solution \<rho> \<sigma> env' \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
      "\<And>\<rho> \<sigma>. sol1 \<rho> \<sigma> env s t \<Longrightarrow>
        \<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
    | (No_Unifier) v where "unify alg s t env = raise (Unif v)" "\<And>\<rho> \<sigma>. \<not> sol1 \<rho> \<sigma> env s t"
    | (Not_Pattern) "unify alg s t env = raise Pattern"
    | (Clash) ts where "unify alg s t env = raise (Type_Error (STR ''Variable has two distinct types'') [] ts)"
        "\<not> ncons env (vars s \<union> vars t)"
    | (Fail) "unify alg s t env = raise (Failure (STR ''mk_ff_list''))" "\<not> ncons env (vars s \<union> vars t)"
proof -
  let ?X = "vars s \<union> vars t"
  from wf have fin: "finite A" and tv: "tvinv A env" "scert alg (tyenv env)" "tcert alg (tvars_env (tyenv env) \<union> A)"
    and srt: "tsorted alg (tyenv env)" and ac: "acyc env"
    and wte: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> wt_env \<rho> env"
    and ty: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
    and bl: "below (maxidx env) (?X \<union> evars env)"
    and tvs: "ttvars s \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A" and cl: "closed s" "closed t"
    unfolding wfprob_def by blast+
  interpret G: pure_sig_gen alg ar ctab "UNIV :: indexname set"
    by (rule pure_sig_gen_axioms)
  have wi: "G.winv env ?X"
    unfolding G.winv_def G.vinv_def G.vcons_def using wte bl by simp
  have "\<exists>r. unify alg s t env = Some r \<and> (\<forall>e. r = Err e \<longrightarrow> G.perr e) \<and>
      (\<forall>env'. r = Ok env' \<longrightarrow> extends env env' \<and> acyc env')"
  proof (rule G.unify_terminates_c[OF fin tv srt ac wi tvs cl], goal_cases)
    case (1 \<rho>)
    then show ?case by (rule ty)
  next
    case (2 r)
    have "unify alg s t env = Some r" using 2(1) by (simp add: G.dcut_def)
    moreover have "\<forall>e. r = Err e \<longrightarrow> G.perr e" using 2(2) by blast
    moreover have "\<forall>env'. r = Ok env' \<longrightarrow> extends env env' \<and> acyc env'" using 2(3) by blast
    ultimately show ?case by blast
  qed
  then obtain r where r: "unify alg s t env = Some r" and err: "\<And>e. r = Err e \<Longrightarrow> G.perr e"
    and post: "\<And>env'. r = Ok env' \<Longrightarrow> extends env env' \<and> acyc env'"
    by blast
  text \<open>With consistent names only \<open>Unif\<close> and \<open>Pattern\<close> are raised:\<close>
  have nc: "(\<exists>u. e = Unif u) \<or> e = Pattern" if c: "ncons env (vars s \<union> vars t)" and e: "r = Err e" for e
  proof -
    have wi1: "winv env ?X"
      unfolding winv_def vinv_def using wte bl c by (simp add: ncons_def Un_assoc)
    from unify_terminates[OF fin tv srt ac wi1 tvs cl ty] r e show ?thesis by auto
  qed
  text \<open>A one-type solution:\<close>
  have cp: "no_unif (Some r)" "r = Ok env' \<Longrightarrow> \<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      sagree (maxidx env) \<sigma> \<sigma>'"
    if s1: "sol1 \<rho> \<sigma> env s t" for \<rho> \<sigma> env'
  proof -
    from s1 obtain e T where sol: "solution \<rho> \<sigma> env" and w: "wt_env \<rho> env"
      and vc: "vcons \<rho> (?X \<union> evars env)" and ty1: "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T"
      and eq: "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
      unfolding sol1_def by blast
    have vi: "vinv \<rho> env ?X" unfolding vinv_def using vc bl by simp
    note uc = unify_complete[OF r sol w vi tv(1) tvs ty1 cl eq]
    show "no_unif (Some r)" by (rule uc(1))
    show "r = Ok env' \<Longrightarrow> \<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
      using uc(2) by blast
  qed
  show thesis
  proof (cases r)
    case (Ok env')
    have u: "unify alg s t env = return env'" using r Ok by (simp add: return_def)
    have un: "ok (unify alg s t env) env'" using r Ok by simp
    note p = post[OF Ok]
    have snd: "\<exists>\<sigma>. solution \<rho> \<sigma> env' \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
      if \<rho>: "wsinst alg \<rho>" "cert_inst \<rho>" "tsol (tyenv env') \<rho>" for \<rho>
    proof -
      have t0: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF \<rho>(3) conjunct1[OF p]])
      from ty[OF t0 \<rho>(2)] obtain e T where ty1: "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" by blast
      show ?thesis by (rule unify_typed_unifier[OF un \<rho>(1,3) wte[OF t0 \<rho>(2)] ty1 cl bl ac])
    qed
    show ?thesis by (rule Success[OF u conjunct1[OF p] conjunct2[OF p] snd cp(2)[OF _ Ok]])
  next
    case (Err e)
    have u: "unify alg s t env = raise e" using r Err by (simp add: raise_def)
    from err[OF Err] consider (a) v where "e = Unif v" | (b) "e = Pattern"
      | (c) ts where "e = Type_Error (STR ''Variable has two distinct types'') [] ts"
      | (d) "e = Failure (STR ''mk_ff_list'')"
      by (auto simp: G.clashx_def)
    then show ?thesis
    proof cases
      case a
      have "\<not> sol1 \<rho> \<sigma> env s t" for \<rho> \<sigma>
      proof
        assume "sol1 \<rho> \<sigma> env s t"
        from cp(1)[OF this] Err a show False by (simp add: xok_def)
      qed
      with u a show ?thesis by (intro No_Unifier) simp_all
    next
      case b
      with u show ?thesis by (intro Not_Pattern) simp
    next
      case c
      have "\<not> ncons env (vars s \<union> vars t)" using nc[OF _ Err] c by auto
      with u c show ?thesis by (intro Clash) simp_all
    next
      case d
      have "\<not> ncons env (vars s \<union> vars t)" using nc[OF _ Err] d by auto
      with u d show ?thesis by (intro Fail) simp_all
    qed
  qed
qed

end


subsection \<open>Higher-order unification\<close>

text \<open>
  The enumeration of a sequence of unifiers: the elements that are pulled, and the exception
  that ends the enumeration, if there is one.
\<close>

inductive pulls :: "cfg \<Rightarrow> seq \<Rightarrow> elem list \<Rightarrow> uexn option \<Rightarrow> bool" for cfg where
  Nil: "pull cfg s = Some (evs, Ok None) \<Longrightarrow> pulls cfg s [] None"
| Exn: "pull cfg s = Some (evs, Err e) \<Longrightarrow> pulls cfg s [] (Some e)"
| Cons: "pull cfg s = Some (evs, Ok (Some (x, s'))) \<Longrightarrow> pulls cfg s' xs r \<Longrightarrow> pulls cfg s (x # xs) r"

lemma evals_pulls: "evals cfg s xs \<Longrightarrow> pulls cfg s xs None"
  by (induction rule: evals.induct) (auto intro: pulls.intros)

lemma pulls_det: "pulls cfg s xs r \<Longrightarrow> pulls cfg s ys r' \<Longrightarrow> xs = ys \<and> r = r'"
proof (induction arbitrary: ys r' rule: pulls.induct)
  case (Nil s evs)
  from Nil.prems show ?case by (cases rule: pulls.cases) (use Nil.hyps in simp_all)
next
  case (Exn s evs e)
  from Exn.prems show ?case by (cases rule: pulls.cases) (use Exn.hyps in simp_all)
next
  case (Cons s evs x s' xs r)
  note IH = Cons.IH and h = Cons.hyps(1)
  from Cons.prems show ?case
  proof (cases rule: pulls.cases)
    case (Cons evs' y s'' ys')
    from Cons(2) h have eq: "y = x" "s'' = s'" by simp_all
    from IH[OF Cons(3)[unfolded eq]] Cons(1) eq show ?thesis by simp
  qed (use h in simp_all)
qed

text \<open>The exceptions that can end an enumeration:\<close>

definition nexn :: "uexn \<Rightarrow> bool" where
  "nexn e \<longleftrightarrow> (\<exists>ts. e = PExn (Type_Error (STR ''Variable has two distinct types'') [] ts)) \<or>
    (\<exists>ts. e = PExn (Term_Error (STR ''add_ffpair: Var name confusion'') ts)) \<or>
    (\<exists>ts. e = PExn (Term_Error (STR ''add_ffpair: Vars expected'') ts))"

context pure_sig_gen
begin

lemma evalx_pulls: "evalx cfg s xs \<Longrightarrow> \<exists>r. pulls cfg s xs r \<and> (\<forall>e. r = Some e \<longrightarrow> gexn e)"
  by (induction rule: evalx.induct) (auto intro: pulls.intros)

lemma gexn_nexn: "gexn e \<Longrightarrow> nexn e"
  by (auto simp: gexn_def clashW_def clashx_def ffexn_def confW_def nexn_def)

end

context pure_sig
begin

text \<open>
  A well-formed problem of higher-order unification: the invariant of the environment, which
  is well-typed under every certified solution of its type environment, and pairs of closed
  terms of one type over the variables \<open>X\<close> and the type variables \<open>A\<close>. Nothing is asked of the
  types of the names.
\<close>

definition wfprobs :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "wfprobs A K X env tus \<longleftrightarrow> einv A K env \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> wt_env \<rho> env) \<and>
    below (maxidx env) (X \<union> evars env) \<and> (\<forall>(t, u)\<in>set tus. upok A env [] X t u)"

text \<open>
  The unifiers identify the variables by their names, so a binding \<open>?x \<mapsto> u\<close> is also used for
  the occurrences of \<open>?x\<close> at other types. A typed solution of an environment is a solution
  that satisfies these readings of the bindings as well, where they are well-typed. If no bound
  name occurs at a second type, this is a solution. Typed solutions exist: \<open>gfix_gsolution\<close>
  in theory \<open>Unify_Smash_Typed\<close>.
\<close>

definition readings :: "tinst \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) set" where
  "readings \<rho> env = {(Var x V, abs_list cs b) | x V cs b U u ds.
    vt_lookup (tenv env) x = Some (U, u) \<and> inst \<rho> u = abs_list ds b \<and> length cs = length ds}"

definition rsolution :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> bool" where
  "rsolution \<rho> \<sigma> env \<longleftrightarrow> solution \<rho> \<sigma> env \<and>
    (\<forall>(l, r)\<in>readings \<rho> env. \<forall>e T. e \<turnstile> l : T \<longrightarrow> e \<turnstile> r : T \<longrightarrow> vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r)"

text \<open>
  On a well-formed problem \<open>Unify.unifiers\<close> returns a sequence whose enumeration ends, or it
  raises one of two exceptions. Every unifier of the enumeration is sound: a typed solution of
  its environment that solves its flex-flex pairs solves the problem. An exception, when the
  sequence is made or during the enumeration, occurs only if the names are not consistent. If
  they are consistent, the enumeration is complete within the bounds of the configuration.
\<close>

theorem unifiers_outcome:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and wf: "wfprobs A K X env tus"
  obtains (Seq) sq xs r where "unifiers alg env tus = return sq" "pulls cfg sq xs r"
      "\<And>e. r = Some e \<Longrightarrow> nexn e \<and> \<not> ncons env X"
      "\<And>env' tps \<rho> \<sigma>. El_R env' tps \<in> set xs \<Longrightarrow> rsolution \<rho> \<sigma> env' \<Longrightarrow> cert_inst \<rho> \<Longrightarrow>
        \<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<Longrightarrow> \<forall>(t, u)\<in>set tus. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      "\<And>k \<rho> \<sigma>. ncons env X \<Longrightarrow> k = nat_of_integer (cfg_arity_bound cfg) \<Longrightarrow>
        scinv \<rho> \<sigma> env (tdps tus) X A \<Longrightarrow> mcp_kokK k \<rho> (tyenv env) A K \<Longrightarrow>
        mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg) \<Longrightarrow>
        \<exists>env' tps \<rho>' \<sigma>'. El_R env' tps \<in> set xs \<and> solution \<rho>' \<sigma>' env' \<and> dsolved \<rho>' \<sigma>' (tdps tps) \<and>
          tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
    | (Clash) ts where "unifiers alg env tus = raise (Type_Error (STR ''Variable has two distinct types'') [] ts)"
        "\<not> ncons env X"
    | (Fail) "unifiers alg env tus = raise (Failure (STR ''mk_ff_list''))" "\<not> ncons env X"
proof -
  interpret G: pure_sig_gen alg ar ctab "UNIV :: indexname set"
    by (rule pure_sig_gen_axioms)
  have si: "G.sinv A K X env (tdps tus)"
    using wf unfolding wfprobs_def G.sinv_def G.winv_def G.vinv_def G.vcons_def by auto
  have si1: "sinv A K X env (tdps tus)" if "ncons env X"
    using wf that unfolding wfprobs_def sinv_def winv_def vinv_def ncons_def by auto
  have gh: "G.gsolution \<rho> \<sigma> e \<longleftrightarrow> rsolution \<rho> \<sigma> e" for \<rho> \<sigma> e
    unfolding G.gsolution_def rsolution_def G.ghosts_def readings_def by simp
  from G.unifiers_cfin[OF cfg fin si] show thesis
  proof (elim disjE exE conjE)
    fix sq assume u: "unifiers alg env tus = return sq"
    have u': "unifiers alg env tus = Some (Ok sq)" using u by (simp add: return_def)
    from G.unifiers_cfin_uresult[OF cfg fin si u'] obtain xs where ex: "G.evalx cfg sq xs"
      and ur: "\<And>x. x \<in> set xs \<Longrightarrow> G.uresult A env tus x"
      unfolding G.cfin_def by blast
    from G.evalx_pulls[OF ex] obtain r where p: "pulls cfg sq xs r"
      and ge: "\<And>e. r = Some e \<Longrightarrow> G.gexn e" by blast
    have cons: "evals cfg sq xs \<and> r = None" if c: "ncons env X"
    proof -
      from unifiers_fin[OF cfg fin si1[OF c]] obtain s where s: "unifiers alg env tus = Some (Ok s)"
        and f: "fin cfg s (fresult A env tus)" by blast
      have ss: "s = sq" using s u' by simp
      from f obtain ys where ys: "evals cfg sq ys" unfolding fin_def ss by blast
      from pulls_det[OF p evals_pulls[OF ys]] ys show ?thesis by simp
    qed
    have e1: "nexn e \<and> \<not> ncons env X" if re: "r = Some e" for e
    proof (intro conjI notI)
      show "nexn e" by (rule G.gexn_nexn[OF ge[OF re]])
      assume "ncons env X"
      from cons[OF this] re show False by simp
    qed
    have snd: "\<forall>(t, u)\<in>set tus. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      if x: "El_R env' tps \<in> set xs" and rs: "rsolution \<rho> \<sigma> env'" and ci: "cert_inst \<rho>"
        and ts: "\<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" for env' tps \<rho> \<sigma>
      by (rule G.uresult_solves[OF ur[OF x] si rs[folded gh] ci ts])
    have cp: "\<exists>env' tps \<rho>' \<sigma>'. El_R env' tps \<in> set xs \<and> solution \<rho>' \<sigma>' env' \<and> dsolved \<rho>' \<sigma>' (tdps tps) \<and>
        tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
      if c: "ncons env X" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
        and inv: "scinv \<rho> \<sigma> env (tdps tus) X A" and kk: "mcp_kokK k \<rho> (tyenv env) A K"
        and bound: "mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg)" for k \<rho> \<sigma>
      using unifiers_most_general[OF cfg k fin si1[OF c] inv kk bound u' conjunct1[OF cons[OF c]]]
      by blast
    show thesis by (rule Seq[OF u p e1 snd cp])
  next
    fix e assume u: "unifiers alg env tus = raise e" and "G.clashx e"
    then obtain ts where e: "e = Type_Error (STR ''Variable has two distinct types'') [] ts"
      by (auto simp: G.clashx_def)
    have "\<not> ncons env X"
    proof
      assume "ncons env X"
      from unifiers_fin[OF cfg fin si1[OF this]] u show False by (auto simp: raise_def)
    qed
    with u e show thesis by (intro Clash) simp_all
  next
    fix e assume u: "unifiers alg env tus = raise e" and e: "e = Failure (STR ''mk_ff_list'')"
    have "\<not> ncons env X"
    proof
      assume "ncons env X"
      from unifiers_fin[OF cfg fin si1[OF this]] u show False by (auto simp: raise_def)
    qed
    with u e show thesis by (intro Fail) simp_all
  qed
qed

end


subsection \<open>The exceptions on solvable problems\<close>

text \<open>
  Two problems over the signature of theory \<open>Unify_Complete_Two_Types\<close>, on which pattern
  unification raises the two exceptions, although the problems have solutions.

  The first is \<open>f (?x::'a) (?x::'b) =?= f (c::'a) (c::'b)\<close>. The solution \<open>'a, 'b \<mapsto> prop\<close>,
  \<open>?x::prop \<mapsto> c\<close> gives the name \<open>?x\<close> one type. The unifier binds \<open>?x::'a\<close>, and the lookup of
  \<open>?x::'b\<close> raises \<open>TYPE\<close>: the type environment does not identify \<open>'a\<close> and \<open>'b\<close>.
\<close>

definition aW :: ptyp where "aW = TVar (STR ''a'', 0) []"
definition bW :: ptyp where "bW = TVar (STR ''b'', 0) []"

definition sW :: pterm where
  "sW = Free STR ''f'' (aW \<rightarrow>\<^sub>T bW \<rightarrow>\<^sub>T pT) $ Var xL aW $ Var xL bW"
definition tW :: pterm where
  "tW = Free STR ''f'' (aW \<rightarrow>\<^sub>T bW \<rightarrow>\<^sub>T pT) $ Free STR ''c'' aW $ Free STR ''c'' bW"

definition AW :: "(indexname \<times> psort) set" where
  "AW = {((STR ''a'', 0), []), ((STR ''b'', 0), [])}"

definition \<rho>W :: tinst where "\<rho>W v S = (if S = [] then pT else TVar v S)"

definition \<sigma>W :: vsubst where
  "\<sigma>W y T = (if y = xL \<and> T = pT then Free STR ''c'' pT else Var y T)"

lemma vt_defined_empty [simp]: "\<not> vt_defined vt_empty k"
  by transfer simp

lemma unify_W: "\<exists>ts. unify algL sW tW envL = raise (Type_Error (STR ''Variable has two distinct types'') [] ts)"
  apply (simp add: unify_def unif.simps sW_def tW_def aW_def bW_def head_norm.simps flexrigid_def occurs.simps
      lookup_def envL_def strip_comb_def ints_of'_def rigid_occurs.simps unify_types_def unified_def
      var_clash_def update_def update_new_def xL_def proj_def handle_def)
  apply (simp add: return_def raise_def bindM_def update_new_def unif.simps head_norm.simps lookup_def
      unified_def var_clash_def vt_is_empty.rep_eq vt_empty.rep_eq)
  done

text \<open>
  The second is \<open>\<lambda>a b. ?x a =?= \<lambda>a b. ?x a b\<close> with \<open>?x\<close> at the types \<open>prop \<Rightarrow> prop\<close> and
  \<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close>. Its solutions keep the name at two types, for instance
  \<open>?x \<mapsto> \<lambda>z. ?y\<close> and \<open>?x \<mapsto> \<lambda>z w. ?y\<close>. The unifier treats the pair as a flex-flex pair with one
  head, and \<open>mk_ff_list\<close> fails on the argument lists of different lengths.
\<close>

definition sF :: pterm where
  "sF = Abs STR ''a'' pT (Abs STR ''b'' pT (Var xL (pT \<rightarrow>\<^sub>T pT) $ Bound 1))"
definition tF :: pterm where
  "tF = Abs STR ''a'' pT (Abs STR ''b'' pT (Var xL (pT \<rightarrow>\<^sub>T pT \<rightarrow>\<^sub>T pT) $ Bound 1 $ Bound 0))"

definition yF :: pterm where "yF = Var (STR ''y'', 0) pT"

definition \<sigma>F :: vsubst where
  "\<sigma>F y T = (if y = xL \<and> T = pT \<rightarrow>\<^sub>T pT then Abs STR ''z'' pT yF
    else if y = xL \<and> T = pT \<rightarrow>\<^sub>T pT \<rightarrow>\<^sub>T pT then Abs STR ''z'' pT (Abs STR ''w'' pT yF)
    else Var y T)"

lemma unify_F: "unify algL sF tF envL = raise (Failure (STR ''mk_ff_list''))"
  apply (simp add: unify_def unif.simps sF_def tF_def head_norm.simps flexrigid_def occurs.simps
      lookup_def envL_def strip_comb_def ints_of'_def rigid_occurs.simps unify_types_def unified_def
      flexflex1_def mk_ff_list_def xL_def)
  done

context
begin

interpretation P: pure_sig algL "\<lambda>_. 0" "\<lambda>_. None"
  using pure_sig_gen_L by (simp add: pure_sig_def)

lemma envL_inv:
  "scert algL (tyenv envL)" "tsorted algL (tyenv envL)" "P.acyc envL" "P.wt_env \<rho> envL"
  "tsol (tyenv envL) \<rho>" "evars envL = {}" "maxidx envL = 0" "tvars_env (tyenv envL) = {}"
  "vt_lookup (tenv envL) x = None"
  by (simp_all add: scert_def tsorted_def bsorted_def P.acyc_def P.dep_def acyclic_def P.wt_env_def tsol_def evars_def bnds_def
      tvars_env_def envL_def)

lemma wfprob_W: "P.wfprob AW envL sW tW"
  unfolding P.wfprob_def
proof (intro conjI allI impI)
  show "finite AW" by (simp add: AW_def)
  show "P.tvinv AW envL"
    by (auto simp: P.tvinv_def tinv_def envL_def tacyc_def tdep_def tvars_env_def scons_def acyclic_def AW_def)
  show "tcert algL (tvars_env (tyenv envL) \<union> AW)" by (simp add: envL_inv AW_def sort_ok_def)
  show "below (maxidx envL) (vars sW \<union> vars tW \<union> evars envL)"
    by (auto simp: below_def envL_inv sW_def tW_def xL_def)
  show "ttvars sW \<union> ttvars tW \<subseteq> tvars_env (tyenv envL) \<union> AW"
    by (auto simp: sW_def tW_def aW_def bW_def AW_def)
  show "closed sW" "closed tW" by (simp_all add: closed_def sW_def tW_def)
next
  fix \<rho> assume "tsol (tyenv envL) \<rho>" and ci: "P.cert_inst \<rho>"
  have so: "sort_ok algL []" by (simp add: sort_ok_def)
  from ci so have c: "cert_typ algL (\<lambda>_. 0) (\<rho> (STR ''a'', 0) [])" "cert_typ algL (\<lambda>_. 0) (\<rho> (STR ''b'', 0) [])"
    by (simp_all add: P.cert_inst_def)
  then have f: "cert_typ algL (\<lambda>_. 0) (\<rho> (STR ''a'', 0) [] \<rightarrow>\<^sub>T \<rho> (STR ''b'', 0) [] \<rightarrow>\<^sub>T pT)"
    by (simp add: cert_typ_def tarity_def)
  have "P.typing e (inst \<rho> sW) pT" "P.typing e (inst \<rho> tW) pT" for e
    using c f by (auto simp: sW_def tW_def aW_def bW_def)
  then show "\<exists>e T. P.typing e (inst \<rho> sW) T \<and> P.typing e (inst \<rho> tW) T" by blast
qed (simp_all add: envL_inv)

text \<open>A solution of the first problem that gives \<open>?x\<close> one type:\<close>

lemma sol1_W: "P.sol1 \<rho>W \<sigma>W envL sW tW"
  unfolding P.sol1_def
proof (intro conjI)
  have "has_sort algL (\<rho>W v S) S" for v S
  proof (cases "S = []")
    case True
    then show ?thesis by simp
  next
    case False
    then have "\<rho>W v S = TVar v S" by (simp add: \<rho>W_def)
    then show ?thesis by (simp only: P.has_sort_TVar_refl)
  qed
  then have "wsinst algL \<rho>W" by (simp only: wsinst_def simp_thms)
  moreover have "P.wt_subst \<sigma>W"
    by (auto simp: P.wt_subst_def closed_subst_def closed_def \<sigma>W_def)
  ultimately show "P.solution \<rho>W \<sigma>W envL" by (simp add: P.solution_def envL_inv)
  show "P.wt_env \<rho>W envL" by (rule envL_inv)
  show "P.vcons \<rho>W (vars sW \<union> vars tW \<union> evars envL)"
    by (auto simp: P.vcons_def envL_inv sW_def tW_def aW_def bW_def \<rho>W_def)
  have "P.typing e (inst \<rho>W sW) pT" "P.typing e (inst \<rho>W tW) pT" for e
    by (auto simp: sW_def tW_def aW_def bW_def \<rho>W_def cert_typ_def tarity_def)
  then show "\<exists>e T. P.typing e (inst \<rho>W sW) T \<and> P.typing e (inst \<rho>W tW) T" by blast
  show "P.conv (P.ap \<rho>W \<sigma>W sW) (P.ap \<rho>W \<sigma>W tW)"
    by (simp add: P.ap_def sW_def tW_def aW_def bW_def \<rho>W_def \<sigma>W_def xL_def)
qed

text \<open>
  So a well-formed problem with a solution that gives every name one type can raise \<open>TYPE\<close>;
  the completeness statement of \<open>unify_outcome\<close> for such solutions excludes \<open>Unif\<close> only.
\<close>

theorem unify_clash_solvable:
  "P.wfprob AW envL sW tW" "P.sol1 \<rho>W \<sigma>W envL sW tW"
  "\<exists>ts. unify algL sW tW envL = raise (Type_Error (STR ''Variable has two distinct types'') [] ts)"
  by (rule wfprob_W sol1_W unify_W)+

lemma wfprob_F: "P.wfprob {} envL sF tF"
  unfolding P.wfprob_def
proof (intro conjI allI impI)
  show "P.tvinv {} envL"
    by (simp add: P.tvinv_def tinv_def envL_def tacyc_def tdep_def tvars_env_def scons_def acyclic_def)
  show "below (maxidx envL) (vars sF \<union> vars tF \<union> evars envL)"
    by (auto simp: below_def envL_inv sF_def tF_def xL_def)
  show "ttvars sF \<union> ttvars tF \<subseteq> tvars_env (tyenv envL) \<union> {}"
    by (auto simp: sF_def tF_def)
  show "closed sF" "closed tF" by (simp_all add: closed_def sF_def tF_def)
next
  fix \<rho> :: tinst
  have "P.typing e (inst \<rho> sF) (pT \<rightarrow>\<^sub>T pT \<rightarrow>\<^sub>T pT)" "P.typing e (inst \<rho> tF) (pT \<rightarrow>\<^sub>T pT \<rightarrow>\<^sub>T pT)" for e
    by (auto simp: sF_def tF_def cert_typ_def tarity_def)
  then show "\<exists>e T. P.typing e (inst \<rho> sF) T \<and> P.typing e (inst \<rho> tF) T" by blast
qed (simp_all add: envL_inv)

text \<open>A solution of the second problem; it keeps \<open>?x\<close> at two types.\<close>

lemma solution_F: "P.solution \<rho>L \<sigma>F envL"
proof -
  have "wsinst algL \<rho>L" unfolding wsinst_def \<rho>L_def by (intro allI) (rule P.has_sort_TVar_refl)
  moreover have "P.wt_subst \<sigma>F"
    by (auto simp: P.wt_subst_def closed_subst_def closed_def \<sigma>F_def yF_def cert_typ_def tarity_def)
  ultimately show ?thesis by (simp add: P.solution_def envL_inv)
qed

lemma solves_F: "P.conv (P.ap \<rho>L \<sigma>F sF) (P.ap \<rho>L \<sigma>F tF)"
proof -
  let ?n = "Abs STR ''a'' pT (Abs STR ''b'' pT yF)"
  let ?m = "Abs STR ''a'' pT (Abs STR ''b'' pT (Abs STR ''w'' pT yF $ Bound 0))"
  have s: "P.ap \<rho>L \<sigma>F sF = Abs STR ''a'' pT (Abs STR ''b'' pT (Abs STR ''z'' pT yF $ Bound 1))"
    and t: "P.ap \<rho>L \<sigma>F tF =
      Abs STR ''a'' pT (Abs STR ''b'' pT (Abs STR ''z'' pT (Abs STR ''w'' pT yF) $ Bound 1 $ Bound 0))"
    by (simp_all add: P.ap_def sF_def tF_def \<sigma>F_def \<rho>L_def yF_def)
  have b1: "Abs a pT yF $ u \<rightarrow>\<^sub>\<beta> yF" for a u
    using beta.beta[of a pT yF u] by (simp add: yF_def)
  have b2: "Abs a pT (Abs STR ''w'' pT yF) $ u \<rightarrow>\<^sub>\<beta> Abs STR ''w'' pT yF" for a u
    using beta.beta[of a pT "Abs STR ''w'' pT yF" u] by (simp add: yF_def)
  have "P.ap \<rho>L \<sigma>F sF \<rightarrow>\<^sub>\<beta> ?n" unfolding s by (intro beta.abs b1)
  then have 1: "(sup beta eta)\<^sup>*\<^sup>* (P.ap \<rho>L \<sigma>F sF) ?n" by blast
  have "P.ap \<rho>L \<sigma>F tF \<rightarrow>\<^sub>\<beta> ?m" unfolding t by (intro beta.abs beta.appL b2)
  moreover have "?m \<rightarrow>\<^sub>\<beta> ?n" by (intro beta.abs b1)
  ultimately have 2: "(sup beta eta)\<^sup>*\<^sup>* (P.ap \<rho>L \<sigma>F tF) ?n"
    by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl sup2I1)
  have "P.typing e (P.ap \<rho>L \<sigma>F sF) (pT \<rightarrow>\<^sub>T pT \<rightarrow>\<^sub>T pT)" "P.typing e (P.ap \<rho>L \<sigma>F tF) (pT \<rightarrow>\<^sub>T pT \<rightarrow>\<^sub>T pT)" for e
    unfolding s t by (auto simp: yF_def cert_typ_def tarity_def)
  then have w: "P.wt (P.ap \<rho>L \<sigma>F sF)" "P.wt (P.ap \<rho>L \<sigma>F tF)"
    unfolding P.wt_def by blast+
  show ?thesis
    by (rule P.conv_trans[OF P.beta_eta_conv[OF 1 w(1)] P.conv_sym[OF P.beta_eta_conv[OF 2 w(2)]]])
qed

text \<open>
  So a well-formed problem with a solution can raise \<open>Fail\<close>. No solution of this problem gives
  \<open>?x\<close> one type: the two types have no common instance.
\<close>

theorem unify_fail_solvable:
  "P.wfprob {} envL sF tF" "P.solution \<rho>L \<sigma>F envL" "P.conv (P.ap \<rho>L \<sigma>F sF) (P.ap \<rho>L \<sigma>F tF)"
  "unify algL sF tF envL = raise (Failure (STR ''mk_ff_list''))"
  by (rule wfprob_F solution_F solves_F unify_F)+

end

end
