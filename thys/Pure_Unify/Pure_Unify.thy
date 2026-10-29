section \<open>Higher-Order Unification\<close>

theory Pure_Unify
  imports Unify_Base
begin

text \<open>
  A literal model of \<^file>\<open>~~/src/Pure/unify.ML\<close> (Paulson): Huet's procedure for higher-order
  unification, with the simplification of disagreement pairs (\<open>SIMPL\<close>), the copying of
  rigid terms by projections and imitation (\<open>MATCH\<close>), the treatment of flex-flex pairs, and
  the trivial unifiers of flex-flex pairs (\<open>smash_unifiers\<close>).

  Function names follow the ML code, and so does the order of evaluation, which determines the
  exception that is raised and the order of the tracing messages. The search produces a lazy
  sequence of unifiers; its representation is explained in the subsection on sequences below.
\<close>


subsection \<open>Configuration\<close>

text \<open>
  The class algebra of the theory and the options \<open>unify_search_bound\<close>,
  \<open>unify_trace_bound\<close>, \<open>unify_trace_simp\<close>, \<open>unify_trace_types\<close> and \<open>unify_arity_bound\<close> of
  the context. The last one is new: the number of arguments that \<open>MATCH\<close> may guess for a type
  variable (see below).
\<close>

datatype cfg = Cfg
  (cfg_alg: algebra) (cfg_search_bound: integer) (cfg_trace_bound: integer)
  (cfg_trace_simp: bool) (cfg_trace_types: bool) (cfg_arity_bound: integer)

text \<open>\<open>fastype env (Ts, t) = Envir.fastype env (map snd Ts) t\<close>\<close>

definition fastype :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> ptyp M" where
  "fastype env Ts t = env_fastype env (map snd Ts) t"


subsection \<open>\<open>\<eta>\<close>-normal form\<close>

partial_function (option) etif :: "tyenv \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "etif tye T t =
    (case T of
      Type a Ts \<Rightarrow>
        (case Ts of
          [T1, U] \<Rightarrow>
            if a = STR ''fun'' then do {
              u \<leftarrow> etif tye U (incr_boundvars 1 t $ Bound 0);
              return (Abs STR '''' T1 u)}
            else return t
        | _ \<Rightarrow> return t)
    | TVar v S \<Rightarrow> do {
        r \<leftarrow> type_lookup tye v S;
        case r of None \<Rightarrow> return t | Some T' \<Rightarrow> etif tye T' t}
    | _ \<Rightarrow> return t)"

fun eta_norm :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "eta_norm env rbinder (Abs a T body) =
    do {body' \<leftarrow> eta_norm env ((a, T) # rbinder) body; return (Abs a T body')}"
| "eta_norm env rbinder t = do {T \<leftarrow> fastype env rbinder t; etif (tyenv env) T t}"


subsection \<open>Occurs check\<close>

text \<open>
  \<open>occurs_terms\<close>: does the variable \<open>v\<close> occur in the terms, modulo the environment? The list
  \<open>seen\<close> of the variables passed through (a reference in the ML code) is threaded through the
  computation; it is shared with the rigid occurs check below. Types of variables are ignored.
\<close>

text \<open>The term is the first argument: \<^theory_text>\<open>partial_function\<close> fails to prove monotonicity of a
  \<open>case\<close> distinction on the last of four or more arguments.\<close>

partial_function (option) occur :: "pterm \<Rightarrow> env \<Rightarrow> indexname \<Rightarrow> indexname list \<Rightarrow>
    (bool \<times> indexname list) M" where
  "occur t env v seen =
    (case t of
      Var w T \<Rightarrow>
        if w \<in> set seen then return (False, seen)
        else if v = w then return (True, seen)
        else do {
          r \<leftarrow> lookup env w T;
          case r of None \<Rightarrow> return (False, w # seen) | Some u \<Rightarrow> occur u env v (w # seen)}
    | Abs _ _ body \<Rightarrow> occur body env v seen
    | f $ u \<Rightarrow> do {
        r \<leftarrow> occur u env v seen;
        if fst r then return (True, snd r) else occur f env v (snd r)}
    | _ \<Rightarrow> return (False, seen))"

fun occurs_list :: "env \<Rightarrow> indexname \<Rightarrow> indexname list \<Rightarrow> pterm list \<Rightarrow> (bool \<times> indexname list) M" where
  "occurs_list env v seen [] = return (False, seen)"
| "occurs_list env v seen (t # ts) =
    do {r \<leftarrow> occur t env v seen; if fst r then return (True, snd r) else occurs_list env v (snd r) ts}"

text \<open>\<open>head_of_in env t\<close>: the head of \<open>t\<close>, following the assignments of head variables.\<close>

partial_function (option) head_of_in :: "env \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "head_of_in env t =
    (case t of
      f $ _ \<Rightarrow> head_of_in env f
    | Var x T \<Rightarrow> do {r \<leftarrow> lookup env x T; case r of Some u \<Rightarrow> head_of_in env u | None \<Rightarrow> return t}
    | _ \<Rightarrow> return t)"

datatype occ = NoOcc | Nonrigid | Rigid

text \<open>
  The rigid occurs check \<open>rigid_occurs_term\<close>: \<^const>\<open>Rigid\<close> if it finds a rigid path to the
  variable, \<^const>\<open>Nonrigid\<close> if it finds a non-rigid path, \<^const>\<open>NoOcc\<close> otherwise. In the ML
  code, \<open>occomb\<close> is mutually recursive with \<open>occur\<close>; here it is parameterised by it.

  \<^bold>\<open>Deviation from \<open>unify.ML\<close>:\<close> an occurrence of the variable that is applied to arguments is
  rigid only if all arguments are bound variables (\<open>pattern_occ\<close>), as in \<open>Pattern.unify\<close>.
  Otherwise the arguments may let a unifier discard the occurrence:
  \<open>\<lambda>y. ?v y =?= \<lambda>y. y (?v (\<lambda>z. d))\<close> has the unifier \<open>?v := \<lambda>y. y d\<close>, but \<open>unify.ML\<close> finds a
  rigid occurrence and fails. (Its comment says that completeness is sacrificed here.)
\<close>

definition pattern_occ :: "indexname \<Rightarrow> pterm \<Rightarrow> bool" where
  "pattern_occ v t \<longleftrightarrow>
    (case strip_comb t of (Var w _, ts) \<Rightarrow> w = v \<and> list_all is_Bound ts | _ \<Rightarrow> False)"

fun occomb :: "(indexname list \<Rightarrow> pterm \<Rightarrow> (occ \<times> indexname list) M) \<Rightarrow> indexname list \<Rightarrow> pterm \<Rightarrow>
    (occ \<times> indexname list) M" where
  "occomb oc seen (f $ t) =
    do {
      r \<leftarrow> oc seen t;
      if fst r = Rigid then return (Rigid, snd r)
      else do {r2 \<leftarrow> occomb oc (snd r) f; return (if fst r2 = NoOcc then fst r else fst r2, snd r2)}
    }"
| "occomb oc seen t = oc seen t"

lemma occomb_mono[partial_function_mono]:
  assumes "\<And>seen t. mono_option (\<lambda>f. C seen t f)"
  shows "mono_option (\<lambda>f. occomb (\<lambda>seen t. C seen t f) seen t)"
  using assms
  using assms
  by (induction t arbitrary: seen) (auto intro!: bindM_mono if_mono_option simp: return_def option.const_mono)

definition nonrigid :: "env \<Rightarrow> indexname \<Rightarrow> indexname list \<Rightarrow> pterm \<Rightarrow> (occ \<times> indexname list) M" where
  "nonrigid env v seen t =
    do {(b, seen') \<leftarrow> occurs_list env v seen [t]; return (if b then Nonrigid else NoOcc, seen')}"

partial_function (option) rocc :: "pterm \<Rightarrow> env \<Rightarrow> indexname \<Rightarrow> indexname list \<Rightarrow>
    (occ \<times> indexname list) M" where
  "rocc t env v seen =
    (case t of
      Var w T \<Rightarrow>
        if w \<in> set seen then return (NoOcc, seen)
        else if v = w then return (Rigid, seen)
        else do {
          r \<leftarrow> lookup env w T;
          case r of None \<Rightarrow> return (NoOcc, w # seen) | Some u \<Rightarrow> rocc u env v (w # seen)}
    | Abs _ _ body \<Rightarrow> rocc body env v seen
    | f $ _ \<Rightarrow> do {
        h \<leftarrow> head_of_in env f;
        case h of
          Var w _ \<Rightarrow> if v = w \<and> pattern_occ v t then return (Rigid, seen) else nonrigid env v seen t
        | Abs _ _ _ \<Rightarrow> nonrigid env v seen t
        | _ \<Rightarrow> occomb (\<lambda>seen t. rocc t env v seen) seen t}
    | _ \<Rightarrow> return (NoOcc, seen))"

definition rigid_occurs_term :: "env \<Rightarrow> indexname \<Rightarrow> pterm \<Rightarrow> occ M" where
  "rigid_occurs_term env v t = do {r \<leftarrow> rocc t env v []; return (fst r)}"

definition occurs_terms :: "env \<Rightarrow> indexname \<Rightarrow> pterm list \<Rightarrow> bool M" where
  "occurs_terms env v ts = do {r \<leftarrow> occurs_list env v [] ts; return (fst r)}"


subsection \<open>Assignments\<close>

text \<open>
  \<open>unify_types\<close> of \<open>unify.ML\<close>: \<open>Pattern.unify_types\<close>, with \<open>Pattern.Unif\<close> turned into
  \<open>CANTUNIFY\<close>; the failure is traced (option \<open>unify_trace_failure\<close>).
\<close>

definition cunify_types :: "algebra \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> env \<Rightarrow> env W" where
  "cunify_types alg T U env =
    (case unify_types alg T U env of
      None \<Rightarrow> None
    | Some (Ok env') \<Rightarrow> returnW env'
    | Some (Err (Unif tr)) \<Rightarrow> do {emit (Ev_Unif tr); raiseW CANTUNIFY}
    | Some (Err e) \<Rightarrow> raiseW (PExn e))"

definition test_unify_types :: "algebra \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> env \<Rightarrow> env W" where
  "test_unify_types alg T U env =
    do {
      env' \<leftarrow> cunify_types alg T U env;
      whenW (is_TVar T \<or> is_TVar U) (emit (Ev_Loss T U));
      returnW env'
    }"

text \<open>\<open>get_eta_var\<close>: is the term \<open>\<eta>\<close>-convertible to a single variable with the given binder?\<close>

fun get_eta_var :: "binders \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> (indexname \<times> ptyp) W" where
  "get_eta_var [] _ (Var v T) = returnW (v, T)"
| "get_eta_var (_ # rbinder) n (f $ Bound i) =
    (if n = i then get_eta_var rbinder (n + 1) f else raiseW ASSIGN)"
| "get_eta_var _ _ _ = raiseW ASSIGN"

text \<open>\<open>assignment\<close>: solve \<open>v =?= u\<close> by assignment if \<open>v\<close> does not occur in \<open>u\<close>.\<close>

definition assignment :: "algebra \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> env W" where
  "assignment alg rbinder t u env =
    do {
      (v, T) \<leftarrow> get_eta_var rbinder 0 t;
      oc \<leftarrow> liftM (rigid_occurs_term env v u);
      case oc of
        NoOcc \<Rightarrow> do {
          T1 \<leftarrow> liftM (body_type env T);
          T2 \<leftarrow> liftM (fastype env rbinder u);
          env' \<leftarrow> cunify_types alg T1 T2 env;
          liftM (update (v, T) (rlist_abs rbinder u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN
      | Rigid \<Rightarrow> raiseW CANTUNIFY
    }"

text \<open>\<open>new_dpair\<close>: strip common abstractions, unifying the types of the bound variables.\<close>

fun new_dpair :: "algebra \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> (dpair \<times> env) W" where
  "new_dpair alg rbinder (Abs a T body1) (Abs b U body2) env =
    do {
      env' \<leftarrow> cunify_types alg T U env;
      let c = (if a = STR '''' then b else a);
      new_dpair alg ((c, T) # rbinder) body1 body2 env'
    }"
| "new_dpair alg rbinder (Abs _ _ _) _ env = raiseW (PExn (Term_Error (STR ''new_dpair'') []))"
| "new_dpair alg rbinder _ (Abs _ _ _) env = raiseW (PExn (Term_Error (STR ''new_dpair'') []))"
| "new_dpair alg rbinder t1 t2 env = returnW ((rbinder, t1, t2), env)"

definition head_norm_dpair :: "algebra \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> (dpair \<times> env) W" where
  "head_norm_dpair alg env dp =
    (case dp of (rbinder, t, u) \<Rightarrow> do {
      t1 \<leftarrow> liftM (head_norm env t);
      t2 \<leftarrow> liftM (eta_norm env rbinder t1);
      u1 \<leftarrow> liftM (head_norm env u);
      u2 \<leftarrow> liftM (eta_norm env rbinder u1);
      new_dpair alg rbinder t2 u2 env})"


subsection \<open>Simplification of disagreement pairs\<close>

type_synonym sstate = "env \<times> dpair list \<times> dpair list"

text \<open>
  \<open>SIMRANDS\<close> of \<open>SIMPL0\<close>: simplify the pairs of arguments, from left to right. It is
  parameterised by the recursive call to \<open>SIMPL0\<close>; \<open>u0\<close> is the right-hand side of the
  disagreement pair, which appears in an error message.
\<close>

fun simrands :: "(dpair \<Rightarrow> sstate \<Rightarrow> sstate W) \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> sstate \<Rightarrow>
    sstate W" where
  "simrands f rbinder u0 (f1 $ t) (g1 $ u) st =
    do {st' \<leftarrow> simrands f rbinder u0 f1 g1 st; f (rbinder, t, u) st'}"
| "simrands f rbinder u0 (t1 $ t2) _ st =
    raiseW (PExn (Term_Error (STR ''SIMPL: operands mismatch'') [t1 $ t2, u0]))"
| "simrands f rbinder u0 t (u1 $ u2) st =
    raiseW (PExn (Term_Error (STR ''SIMPL: operands mismatch'') [t, u1 $ u2]))"
| "simrands f rbinder u0 _ _ st = returnW st"

lemma simrands_mono[partial_function_mono]:
  assumes "\<And>dp st. mono_option (\<lambda>f. C dp st f)"
  shows "mono_option (\<lambda>f. simrands (\<lambda>dp st. C dp st f) rbinder u0 t u st)"
  using assms
  by (induction "\<lambda>dp st. C dp st undefined" rbinder u0 t u st rule: simrands.induct)
    (auto intro!: bindW_mono simp: raiseW_def returnW_def option.const_mono)

text \<open>
  \<open>SIMPL0\<close>: head-normalise a disagreement pair, solve it by assignment if possible, decompose
  it if it is rigid-rigid, and collect it otherwise. Flex-flex pairs are not solved.
\<close>

partial_function (option) SIMPL0 :: "algebra \<Rightarrow> dpair \<Rightarrow> sstate \<Rightarrow> sstate W" where
  "SIMPL0 alg dp0 st =
    (case st of (env, ffs, frs) \<Rightarrow> do {
      (dp, env) \<leftarrow> head_norm_dpair alg env dp0;
      case dp of (rbinder, t, u) \<Rightarrow>
        (case (head_of t, head_of u) of
          (Var _ T, Var _ U) \<Rightarrow> do {
            T' \<leftarrow> liftM (body_type env T);
            U' \<leftarrow> liftM (body_type env U);
            env \<leftarrow> cunify_types alg T' U' env;
            returnW (env, dp # ffs, frs)}
        | (Var _ _, _) \<Rightarrow>
            handleW (do {env' \<leftarrow> assignment alg rbinder t u env; returnW (env', ffs, frs)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, dp # frs) | _ \<Rightarrow> raiseW e)
        | (_, Var _ _) \<Rightarrow>
            handleW (do {env' \<leftarrow> assignment alg rbinder u t env; returnW (env', ffs, frs)})
              (\<lambda>e. case e of
                ASSIGN \<Rightarrow> returnW (env, ffs, (rbinder, u, t) # frs)
              | _ \<Rightarrow> raiseW e)
        | (Const a T, Const b U) \<Rightarrow>
            if a = b then do {
              env' \<leftarrow> cunify_types alg T U env;
              simrands (SIMPL0 alg) rbinder u t u (env', ffs, frs)}
            else raiseW CANTUNIFY
        | (Bound i, Bound j) \<Rightarrow>
            if i = j then simrands (SIMPL0 alg) rbinder u t u (env, ffs, frs)
            else raiseW CANTUNIFY
        | (Free a T, Free b U) \<Rightarrow>
            if a = b then do {
              env' \<leftarrow> cunify_types alg T U env;
              simrands (SIMPL0 alg) rbinder u t u (env', ffs, frs)}
            else raiseW CANTUNIFY
        | _ \<Rightarrow> raiseW CANTUNIFY)})"

text \<open>\<open>changed env t\<close>: is the head of \<open>t\<close> a variable assigned in \<open>env\<close>?\<close>

fun changed :: "env \<Rightarrow> pterm \<Rightarrow> bool M" where
  "changed env (f $ _) = changed env f"
| "changed env (Var v T) = do {r \<leftarrow> lookup env v T; return (\<not> Option.is_none r)}"
| "changed env _ = return False"

text \<open>\<open>SIMPL\<close>: repeat \<open>SIMPL0\<close> as long as the head variables of disagreement pairs get assigned.\<close>

partial_function (option) SIMPL :: "algebra \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> sstate W" where
  "SIMPL alg env dpairs =
    do {
      st \<leftarrow> foldrW (SIMPL0 alg) dpairs (env, [], []);
      case st of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then SIMPL alg env' dps else returnW st}
    }"


subsection \<open>Flex-flex pairs\<close>

text \<open>\<open>ff_assign\<close>: at the end of unification, do flex-flex assignments like \<open>?a \<mapsto> ?f(?b)\<close>.\<close>

definition ff_assign :: "algebra \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env W" where
  "ff_assign alg env rbinder t u =
    do {
      (v, T) \<leftarrow> get_eta_var rbinder 0 t;
      b \<leftarrow> liftM (occurs_terms env v [u]);
      if b then raiseW ASSIGN
      else do {
        T1 \<leftarrow> liftM (body_type env T);
        T2 \<leftarrow> liftM (fastype env rbinder u);
        env' \<leftarrow> cunify_types alg T1 T2 env;
        liftM (vupdate (v, T) (rlist_abs rbinder u) env')}
    }"

text \<open>Flex arguments: a term, its type, and the index that refers to it (\<open>flarg\<close>).\<close>

datatype flarg = Flarg (fl_j: integer) (fl_t: pterm) (fl_T: ptyp)

fun flexargs :: "integer list \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> flarg list W" where
  "flexargs [] [] [] = returnW []"
| "flexargs (j # js) (t # ts) (T # Ts) = do {args \<leftarrow> flexargs js ts Ts; returnW (Flarg j t T # args)}"
| "flexargs _ _ _ = raiseW CHANGE_FAIL"

text \<open>
  \<open>rigid_bound (lev, banned) t\<close>: do the banned bound variables occur rigidly in \<open>t\<close>?

  \<^bold>\<open>Deviation from \<open>unify.ML\<close>:\<close> an occurrence in the arguments of a \<open>\<beta>\<close>-redex is not rigid, since
  the redex may discard them; \<open>unify.ML\<close> treats it as rigid. For the \<open>\<beta>\<close>-normal terms that
  \<open>clean_term\<close> receives the two agree.
\<close>

lemma strip_comb_acc_head_size:
  "strip_comb_acc t ts = (h, us) \<Longrightarrow> size h \<le> size t"
  by (induction t ts rule: strip_comb_acc.induct) fastforce+

lemma strip_comb_head_size': "strip_comb t = (h, us) \<Longrightarrow> size h \<le> size t"
  by (simp add: strip_comb_def strip_comb_acc_head_size)

lemma strip_comb_arg_size: "strip_comb t = (h, us) \<Longrightarrow> u \<in> set us \<Longrightarrow> size u < size t"
  using strip_comb_acc_size[of t "[]" h us u] by (simp add: strip_comb_def)

function rigid_bound :: "integer \<Rightarrow> integer list \<Rightarrow> pterm \<Rightarrow> bool" where
  "rigid_bound lev banned t =
    (let (head, args) = strip_comb t in
      case head of
        Bound i \<Rightarrow> (i - lev) \<in> set banned \<or> (\<exists>a\<in>set args. rigid_bound lev banned a)
      | Var _ _ \<Rightarrow> False
      | Abs _ _ u \<Rightarrow> List.null args \<and> rigid_bound (lev + 1) banned u
      | _ \<Rightarrow> (\<exists>a\<in>set args. rigid_bound lev banned a))"
  by auto
termination
  by (relation "measure (\<lambda>(lev, banned, t). size t)")
    (auto dest: strip_comb_arg_size[OF sym] strip_comb_head_size'[OF sym])

declare rigid_bound.simps[simp del]

text \<open>\<open>change_bnos banned\<close>: squash down indices at level \<open>\<ge> lev\<close> to delete the banned ones.\<close>

fun change_bnos :: "integer list \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm W" where
  "change_bnos banned lev (Bound i) =
    (if i < lev then returnW (Bound i)
     else if (i - lev) \<in> set banned then raiseW CHANGE_FAIL
     else returnW (Bound (i - ilength (filter (\<lambda>j. j < i - lev) banned))))"
| "change_bnos banned lev (Abs a T t) =
    do {t' \<leftarrow> change_bnos banned (lev + 1) t; returnW (Abs a T t')}"
| "change_bnos banned lev (t $ u) =
    do {t' \<leftarrow> change_bnos banned lev t; u' \<leftarrow> change_bnos banned lev u; returnW (t' $ u')}"
| "change_bnos banned lev t = returnW t"

text \<open>
  \<open>change_arg del banned\<close>: change indices; if \<open>del\<close>, delete the argument if a banned bound
  variable occurs rigidly in it.
\<close>

definition change_arg :: "bool \<Rightarrow> integer list \<Rightarrow> flarg \<Rightarrow> flarg list \<Rightarrow> flarg list W" where
  "change_arg del banned a args =
    (case a of Flarg j t T \<Rightarrow>
      if del \<and> rigid_bound 0 banned t then returnW args
      else do {t' \<leftarrow> change_bnos banned 0 t; returnW (Flarg j t' T # args)})"

text \<open>\<open>sort_args\<close>: insertion sort, creating \<open>\<eta>\<close>-terms like \<open>?g B.1 B.0\<close>.\<close>

fun less_arg :: "flarg \<Rightarrow> flarg \<Rightarrow> bool" where
  "less_arg (Flarg _ (Bound i1) _) (Flarg _ (Bound i2) _) = (i2 < i1)"
| "less_arg _ _ = False"

fun ins_arg :: "flarg \<Rightarrow> flarg list \<Rightarrow> flarg list" where
  "ins_arg x [] = [x]"
| "ins_arg x (y # ys) = (if less_arg y x then y # ins_arg x ys else x # y # ys)"

fun sort_args :: "flarg list \<Rightarrow> flarg list" where
  "sort_args [] = []"
| "sort_args (x # xs) = ins_arg x (sort_args xs)"

text \<open>\<open>decreasing n args\<close>: would the new term be \<open>\<eta>\<close>-equivalent to a variable?\<close>

fun decreasing :: "integer \<Rightarrow> flarg list \<Rightarrow> bool" where
  "decreasing n [] = (n = 0)"
| "decreasing n (a # args) = (fl_j a = n - 1 \<and> decreasing (n - 1) args)"

text \<open>
  \<open>rigid_headed t\<close>: the head of \<open>t\<close> is a constant, a free variable or a bound variable. Such a term
  cannot discard the arguments it is applied to, whatever is substituted for the schematic
  variables.
\<close>

definition rigid_headed :: "pterm \<Rightarrow> bool" where
  "rigid_headed t \<longleftrightarrow> (case head_of t of Const _ _ \<Rightarrow> True | Free _ _ \<Rightarrow> True | Bound _ \<Rightarrow> True | _ \<Rightarrow> False)"

text \<open>
  \<open>clean_term\<close>: delete banned indices in the term, simplifying it.

  \<^bold>\<open>Deviation from \<open>unify.ML\<close>:\<close> an argument with a rigid banned bound variable is deleted only
  if all arguments have rigid heads. Otherwise a unifier may use the argument and still
  discard the banned variable, by passing the argument to another argument that ignores it,
  and \<open>unify.ML\<close> loses such unifiers: for \<open>\<lambda>j. ?F (\<lambda>z. z j) =?= \<lambda>j. ?G\<close> it only returns
  \<open>?F := \<lambda>x. ?G\<close>, not \<open>?F := \<lambda>x. x (\<lambda>w. c), ?G := c\<close>.
\<close>

definition clean_term :: "integer list \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> (env \<times> pterm) W" where
  "clean_term banned env t =
    (case strip_comb t of
      (Var v T, ts) \<Rightarrow> do {
        (Ts, U) \<leftarrow> liftM (strip_type env T);
        let js = downto0_list (length ts);
        fas \<leftarrow> flexargs js ts Ts;
        cas \<leftarrow> foldrW (change_arg (list_all rigid_headed ts) banned) fas [];
        let args = sort_args cas;
        let ts' = map fl_t args;
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T) ts')
        else do {
          let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
          let body = list_comb v' (map (Bound \<circ> fl_j) args);
          env2 \<leftarrow> liftM (vupdate (v, T) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')}}
    | _ \<Rightarrow> raiseW Bind)"

text \<open>\<open>add_tpair\<close>: add a pair if it is not trivial and not already there.\<close>

definition add_tpair :: "binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list" where
  "add_tpair rbinder t0 u0 tpairs =
    (if aconv_term t0 u0 then tpairs
     else
      (let t = rlist_abs rbinder t0; u = rlist_abs rbinder u0 in
        if (\<exists>(t', u')\<in>set tpairs. aconv_term t t' \<and> aconv_term u u') then tpairs
        else (t, u) # tpairs))"

text \<open>\<open>clean_ffpair\<close>: simplify both terms and check for assignments. Bound variables of the
  binder are banned unless used in both terms.\<close>

definition add_index :: "integer list \<Rightarrow> integer list \<Rightarrow> integer \<times> (name \<times> ptyp) \<Rightarrow>
    integer list \<times> binders \<Rightarrow> integer list \<times> binders" where
  "add_index loot loou jxT st =
    (case (jxT, st) of ((j, xT), (bnos, newbinder)) \<Rightarrow>
      if j \<in> set loot \<and> j \<in> set loou then (bnos, xT # newbinder) else (j # bnos, newbinder))"

definition clean_ffpair :: "algebra \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow>
    (env \<times> (pterm \<times> pterm) list) W" where
  "clean_ffpair alg rbinder t u env tpairs =
    handleW
      (do {
        let loot = loose_bnos t;
        let loou = loose_bnos u;
        let (banned, rbin') =
          foldr (add_index loot loou) (zip (upto_list (length rbinder)) rbinder) ([], []);
        (env', t') \<leftarrow> clean_term banned env t;
        (env'', u') \<leftarrow> clean_term banned env' u;
        handleW (do {env3 \<leftarrow> ff_assign alg env'' rbin' t' u'; returnW (env3, tpairs)})
          (\<lambda>e. case e of
            ASSIGN \<Rightarrow>
              handleW (do {env3 \<leftarrow> ff_assign alg env'' rbin' u' t'; returnW (env3, tpairs)})
                (\<lambda>e. case e of
                  ASSIGN \<Rightarrow> returnW (env'', add_tpair rbin' t' u' tpairs)
                | _ \<Rightarrow> raiseW e)
          | _ \<Rightarrow> raiseW e)})
      (\<lambda>e. case e of CHANGE_FAIL \<Rightarrow> returnW (env, add_tpair rbinder t u tpairs) | _ \<Rightarrow> raiseW e)"

text \<open>\<open>add_ffpair\<close>: if the flex-flex pair is an assignment then do it, else put it into the
  list of remaining pairs. The larger variable is updated.\<close>

definition add_ffpair :: "algebra \<Rightarrow> dpair \<Rightarrow> env \<times> (pterm \<times> pterm) list \<Rightarrow>
    (env \<times> (pterm \<times> pterm) list) W" where
  "add_ffpair alg dp st =
    (case (dp, st) of ((rbinder, t0, u0), (env, tpairs)) \<Rightarrow> do {
      t \<leftarrow> liftM (norm_term env t0);
      u \<leftarrow> liftM (norm_term env u0);
      case (head_of t, head_of u) of
        (Var v T, Var w U) \<Rightarrow>
          if v = w then
            (if T = U then returnW (env, add_tpair rbinder t u tpairs)
             else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
          else if indexname_less v w then clean_ffpair alg rbinder u t env tpairs
          else clean_ffpair alg rbinder t u env tpairs
      | _ \<Rightarrow> raiseW (PExn (Term_Error (STR ''add_ffpair: Vars expected'') [t, u]))})"


subsection \<open>Lazy sequences\<close>

text \<open>
  \<open>unify.ML\<close> enumerates unifiers by lazy sequences (\<open>Seq.seq\<close>), built from closures that are
  evaluated when the sequence is pulled. We represent each closure that occurs by its data
  (defunctionalisation): a constructor of \<open>seq\<close> per closure, holding its free variables.
  The function \<open>pull\<close> evaluates them, exactly as \<open>Seq.pull\<close> evaluates the closure; it may
  raise exceptions, produce tracing messages, and diverge. The ML wrapper turns a \<open>seq\<close>
  into a \<open>Seq.seq\<close> that pulls it.

  Sequences of different element types occur: unifiers with flex-flex pairs (\<open>El_R\<close>),
  environments with disagreement pairs from \<open>MATCH\<close> (\<open>El_E\<close>), and the copies of terms
  (\<open>El_C\<close>) and of argument lists (\<open>El_D\<close>) of \<open>matchcopy\<close>, together with their
  environment and disagreement pairs. They share one type of elements.
\<close>

datatype elem =
  El_R env "(pterm \<times> pterm) list"
| El_E env "dpair list"
| El_C pterm env "dpair list"
| El_D "pterm list" env "dpair list"

datatype seq =
  S_Empty  \<comment> \<open>\<open>Seq.empty\<close>\<close>
| S_Single elem  \<comment> \<open>\<open>Seq.single\<close>\<close>
| S_AddUnify integer env "dpair list" seq
    \<comment> \<open>\<open>add_unify tdepth ((env, dpairs), reseq)\<close> in \<open>hounifiers\<close>\<close>
| S_ItRight integer seq seq  \<comment> \<open>\<open>Seq.it_right (add_unify tdepth) (xq, yq)\<close>\<close>
| S_MapNewDset "indexname \<times> ptyp" "ptyp list" seq  \<comment> \<open>\<open>Seq.map new_dset\<close> in \<open>MATCH\<close>\<close>
| S_MapAbs name ptyp seq  \<comment> \<open>abstraction of copies in \<open>matchcopy\<close>\<close>
| S_Proj name env "ptyp list" "ptyp list" "pterm list" binders pterm "dpair list" pterm pterm seq
    \<comment> \<open>projection in \<open>projenv\<close>: \<open>vname env Ts Us targs rbinder u dpairs head targ tail\<close>\<close>
| S_MapJoin pterm seq  \<comment> \<open>\<open>Seq.map joinargs\<close>: imitation\<close>
| S_Maps name binders "pterm list" pterm seq
    \<comment> \<open>\<open>Seq.maps (copycons uarg)\<close> in \<open>copyargs\<close>: \<open>vname rbinder targs uarg\<close>\<close>
| S_Append seq seq  \<comment> \<open>\<open>Seq.append\<close>\<close>
| S_MapCons "pterm list" seq  \<comment> \<open>\<open>Seq.map (fn (uarg', ed') => (uarg' :: uargs, ed'))\<close>\<close>


subsection \<open>Copying rigid terms\<close>

text \<open>\<open>make_args\<close>: the terms \<open>?G\<^sub>i(B.(n-1), ..., B.0)\<close> of types \<open>Us\<close>.\<close>

definition make_args :: "name \<Rightarrow> ptyp list \<Rightarrow> env \<Rightarrow> ptyp list \<Rightarrow> env \<times> pterm list" where
  "make_args name Ts env Us =
    (if List.null Us then (env, [])
     else
      (let (env', vars) = genvars name env (map (\<lambda>T. foldr fun_type Ts T) Us) in
        (env', map (\<lambda>var. combound var 0 (length Ts)) vars)))"

text \<open>The projections in \<open>matchcopy\<close> (\<open>make_projs\<close>); \<open>u\<close> and \<open>targs\<close> appear in the error.\<close>

fun make_projs :: "pterm \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> ptyp \<times> pterm) list W" where
  "make_projs u targs0 (T # Ts) (targ # targs) =
    do {ps \<leftarrow> make_projs u targs0 Ts targs; returnW ((Bound (ilength Ts), T, targ) # ps)}"
| "make_projs u targs0 [] [] = returnW []"
| "make_projs u targs0 _ _ = raiseW (PExn (Term_Error (STR ''make_projs'') (u # targs0)))"

text \<open>\<open>copyargs\<close>: the sequence of all ways of copying the argument list.\<close>

fun copyargs :: "name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> pterm list \<Rightarrow> seq" where
  "copyargs vname rbinder targs env dpairs [] = S_Single (El_D [] env dpairs)"
| "copyargs vname rbinder targs env dpairs (uarg # uargs) =
    S_Maps vname rbinder targs uarg (copyargs vname rbinder targs env dpairs uargs)"

text \<open>
  \<^bold>\<open>Extension of \<open>unify.ML\<close>: guessing arities.\<close> \<open>unify.ML\<close> treats an unbound type variable like
  a base type: it fixes the number of arguments of a term whose type ends in it. A unifier may
  instantiate the type variable with a function type, so \<open>unify.ML\<close> loses unifiers of
  polymorphic problems: for \<open>?F ?G =?= c\<close> with \<open>?F :: ?'a \<Rightarrow> 'b\<close>, it misses
  \<open>?'a := 'd \<Rightarrow> 'b, ?F := \<lambda>x. x e, ?G := \<lambda>y. c\<close>. (With option \<open>unify_trace_types\<close>, it warns about a
  potential loss of completeness.) The model guesses the missing arguments, up to the arity bound
  \<^const>\<open>cfg_arity_bound\<close>, at three places:
  \<^item> the type of a flex-rigid pair in \<open>MATCH\<close>, if it is an unbound type variable \<open>?'b\<close>: for
    \<open>j > 0\<close>, \<open>?'b := ?'e\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> ?'e\<^sub>j \<Rightarrow> ?'r\<close>, and the pair is \<open>\<eta>\<close>-expanded by \<open>j\<close> bound variables;
  \<^item> the result type of the argument of a projection, if it is an unbound type variable \<open>?'a\<close>:
    for \<open>p > 0\<close>, \<open>?'a := ?'c\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> ?'c\<^sub>p \<Rightarrow> base\<close>, and the projection takes \<open>p\<close> more arguments;
  \<^item> an argument of the rigid side whose type ends in an unbound type variable is not copied, but
    becomes a new flex-rigid pair, as a flexible argument is (\<open>copycons\<close>); the first guess
    applies to it.
  The guesses \<open>j = 0\<close> and \<open>p = 0\<close> are the steps of \<open>unify.ML\<close>, and come first. With arity bound
  \<open>0\<close> (the default), nothing is guessed or deferred, and the search is that of \<open>unify.ML\<close>. On
  problems without type variables, the search is that of \<open>unify.ML\<close> for every arity bound.

  In a build of session \<open>HOL\<close> (Isabelle2026), \<open>unify.ML\<close> calls \<open>MATCH\<close> 107241 times, 184 times
  on a pair whose type is an unbound type variable; of 576562 projections, 41341 have an argument
  with an unbound type variable as result type; of 453474 copied arguments, 86452 have a type that
  ends in an unbound type variable.
\<close>

text \<open>New type variables, with index \<open>maxidx + 1\<close>.\<close>

definition gentvars :: "nat \<Rightarrow> env \<Rightarrow> env \<times> ptyp list" where
  "gentvars p env =
    (if p = 0 then (env, [])
     else
      (case env of Envir i te tye \<Rightarrow>
        (Envir (i + 1) te tye, map (\<lambda>n. TVar (aT + radixstring (integer_of_nat n), i + 1) []) [0..<p])))"

text \<open>The guesses for the number of arguments of type \<open>T\<close>.\<close>

definition arity_guesses :: "cfg \<Rightarrow> ptyp \<Rightarrow> nat list" where
  "arity_guesses cfg T = (if is_TVar T then [0..<Suc (nat_of_integer (cfg_arity_bound cfg))] else [0])"

text \<open>
  The type unification of a projection with the new argument types \<open>Cs\<close>: the result type
  \<open>bary\<close> of the argument becomes \<open>Cs \<Rightarrow> base\<close>.
\<close>

definition proj_unify :: "cfg \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> ptyp list \<Rightarrow> env \<Rightarrow> env W" where
  "proj_unify cfg base bary Cs env =
    (if List.null Cs then
      (if cfg_trace_types cfg then test_unify_types (cfg_alg cfg) base bary env
       else cunify_types (cfg_alg cfg) base bary env)
     else cunify_types (cfg_alg cfg) bary (foldr fun_type Cs base) env)"

text \<open>
  \<open>projenv\<close>: attempt a projection on an argument, with \<open>p\<close> more arguments; the type unification
  is eager.
\<close>

definition projenv :: "cfg \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow>
    ptyp \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp list \<times> ptyp \<Rightarrow> pterm \<Rightarrow> nat \<Rightarrow> seq \<Rightarrow> seq W" where
  "projenv cfg vname rbinder targs u env dpairs base Ts head Usb targ p tail =
    (case (Usb, gentvars p env) of ((Us, bary), (env0, Cs)) \<Rightarrow>
      handleW
        (do {
          env' \<leftarrow> proj_unify cfg base bary Cs env0;
          returnW (S_Proj vname env' Ts (Us @ Cs) targs rbinder u dpairs head targ tail)})
        (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e))"

text \<open>\<open>matchfun\<close>: try the projections, and imitation last of all.\<close>

fun matchfun :: "cfg \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> pterm \<Rightarrow>
    pterm list \<Rightarrow> ptyp \<Rightarrow> ptyp list \<Rightarrow> (pterm \<times> ptyp \<times> pterm) list \<Rightarrow> seq W" where
  "matchfun cfg vname rbinder targs u env dpairs uhead uargs base Ts ((bvar, T, targ) # projs) =
    do {
      Usb \<leftarrow> liftM (strip_type env T);
      tail \<leftarrow> matchfun cfg vname rbinder targs u env dpairs uhead uargs base Ts projs;
      foldrW (projenv cfg vname rbinder targs u env dpairs base Ts bvar Usb targ) (arity_guesses cfg (snd Usb)) tail
    }"
| "matchfun cfg vname rbinder targs u env dpairs uhead uargs base Ts [] =
    returnW
      (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rbinder targs env dpairs uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rbinder targs env dpairs uargs)
      | _ \<Rightarrow> S_Empty)"

text \<open>
  \<open>mc\<close> of \<open>matchcopy\<close>: copy \<open>u\<close> into the variable, by projection on \<open>targs\<close> or imitation. Only
  the outer abstractions are copied eagerly; the arguments are copied when the sequence is
  pulled (\<^const>\<open>S_Maps\<close>).
\<close>

lemma strip_comb_head_size: "size (fst (strip_comb u)) \<le> size u"
  using strip_comb_head_size'[of u "fst (strip_comb u)" "snd (strip_comb u)"] by simp

lemma strip_comb_Abs_size: "fst (strip_comb u) = Abs a T body \<Longrightarrow> size body < size u"
  using strip_comb_head_size[of u] by simp

function mc :: "cfg \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> seq W" where
  "mc cfg vname rbinder targs u env dpairs =
    (let uhead = fst (strip_comb u); uargs = snd (strip_comb u) in
    do {
      T0 \<leftarrow> liftM (fastype env rbinder uhead);
      base \<leftarrow> liftM (body_type env T0);
      Ts \<leftarrow> liftM (mapM (fastype env rbinder) targs);
      case uhead of
        Abs a T body \<Rightarrow> do {
          s \<leftarrow> mc cfg vname ((a, T) # rbinder) (map (incr_boundvars 1) targs @ [Bound 0]) body env dpairs;
          returnW (S_MapAbs a T s)}
      | Var w _ \<Rightarrow>
          (let (env', newhd) = genvar (fst w) env (foldr fun_type Ts base) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rbinder, list_comb newhd targs, u) # dpairs))))
      | _ \<Rightarrow> do {
          projs \<leftarrow> make_projs u targs Ts targs;
          matchfun cfg vname rbinder targs u env dpairs uhead uargs base Ts (rev projs)}
    })"
  by auto
termination
  by (relation "measure (\<lambda>(cfg, vname, rbinder, targs, u, env, dpairs). size u)")
    (auto dest: strip_comb_Abs_size[OF sym])

declare mc.simps[simp del]

text \<open>
  \<open>copycons\<close>: produce copies of an argument and cons them in front of the other arguments.
  If the arity bound is positive and the type of the argument ends in an unbound type
  variable, the argument is deferred: its copy is a new variable applied to \<open>targs\<close>, with a new
  flex-rigid pair, as in the case of a flexible argument in \<^const>\<open>mc\<close>.
\<close>

definition defer_arg :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool M" where
  "defer_arg env rbinder u = do {A \<leftarrow> fastype env rbinder u; B \<leftarrow> body_type env A; return (is_TVar B)}"

definition copycons :: "cfg \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> seq W" where
  "copycons cfg vname rbinder targs uarg uargs env dpairs =
    do {
      u1 \<leftarrow> liftM (head_norm env uarg);
      u2 \<leftarrow> liftM (eta_norm env rbinder u1);
      d \<leftarrow> (if 0 < cfg_arity_bound cfg then liftM (defer_arg env rbinder u2) else returnW False);
      s \<leftarrow>
        (if d then do {
          A \<leftarrow> liftM (fastype env rbinder u2);
          Ts \<leftarrow> liftM (mapM (fastype env rbinder) targs);
          (let (env', newhd) = genvar vname env (foldr fun_type Ts A) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rbinder, list_comb newhd targs, u2) # dpairs))))}
         else mc cfg vname rbinder targs u2 env dpairs);
      returnW (S_MapCons uargs s)
    }"

text \<open>
  \<open>match1\<close>: a single step of matching, the projections and the imitation with new variables for
  the arguments; the pairs \<open>dpairs\<close> are kept.
\<close>

definition match1_proj :: "cfg \<Rightarrow> name \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> ptyp \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow>
    ptyp list \<times> ptyp \<Rightarrow> nat \<Rightarrow> seq \<Rightarrow> seq W" where
  "match1_proj cfg vname env dpairs base Ts bvar Usb p tail =
    (case (Usb, gentvars p env) of ((Us, bary), (env0, Cs)) \<Rightarrow>
      handleW
        (do {
          env' \<leftarrow> proj_unify cfg base bary Cs env0;
          (case make_args vname Ts env' (Us @ Cs) of (env'', args) \<Rightarrow>
            returnW (S_Append (S_Single (El_C (list_comb bvar args) env'' dpairs)) tail))})
        (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e))"

fun match1_projs :: "cfg \<Rightarrow> name \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> ptyp \<Rightarrow> ptyp list \<Rightarrow>
    (pterm \<times> ptyp \<times> pterm) list \<Rightarrow> seq \<Rightarrow> seq W" where
  "match1_projs cfg vname env dpairs base Ts ((bvar, T, targ) # projs) tail =
    do {
      Usb \<leftarrow> liftM (strip_type env T);
      tl \<leftarrow> match1_projs cfg vname env dpairs base Ts projs tail;
      foldrW (match1_proj cfg vname env dpairs base Ts bvar Usb) (arity_guesses cfg (snd Usb)) tl
    }"
| "match1_projs cfg vname env dpairs base Ts [] tail = returnW tail"

definition match1 :: "cfg \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> seq W" where
  "match1 cfg vname rbinder targs u env dpairs =
    (let uhead = fst (strip_comb u) in
    do {
      T0 \<leftarrow> liftM (fastype env rbinder uhead);
      base \<leftarrow> liftM (body_type env T0);
      Ts \<leftarrow> liftM (mapM (fastype env rbinder) targs);
      projs \<leftarrow> make_projs u targs Ts targs;
      imit \<leftarrow>
        (case uhead of
          Const _ _ \<Rightarrow> do {
            Us \<leftarrow> liftM (binder_types env T0);
            (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb uhead args) env' dpairs)))}
        | Free _ _ \<Rightarrow> do {
            Us \<leftarrow> liftM (binder_types env T0);
            (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (S_Single (El_C (list_comb uhead args) env' dpairs)))}
        | _ \<Rightarrow> returnW S_Empty);
      match1_projs cfg vname env dpairs base Ts (rev projs) imit
    })"

text \<open>
  \<open>match_pair\<close>: the assignments to the variable of a flex-rigid pair (\<open>MATCH\<close> of \<open>unify.ML\<close>).

  \<^bold>\<open>Deviation from \<open>unify.ML\<close>:\<close> if the variable \<open>v\<close> occurs in \<open>u\<close>, in its arguments \<open>targs\<close>
  or in the other pairs, we only take a single step (\<^const>\<open>match1\<close>) and keep the pair.
  Copying \<open>u\<close> (\<^const>\<open>mc\<close>) may then assign the new variables of a projection to terms that
  contain \<open>v\<close>, and the update of \<open>v\<close> in \<open>new_dset\<close> closes a cycle in the environment, on which
  normalization diverges: for \<open>\<lambda>x. ?v x =?= \<lambda>x. x (c (?F ?v))\<close>, the projection
  \<open>?v := \<lambda>x. x (?G x)\<close> assigns \<open>?G := \<lambda>x. c (?F ?v)\<close>.
\<close>

definition match_pair :: "cfg \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> dpair list \<Rightarrow> seq W" where
  "match_pair cfg env dp dpairs =
    (case dp of (rbinder, t, u) \<Rightarrow>
      (case strip_comb t of
        (Var v T, targs) \<Rightarrow> do {
          Ts \<leftarrow> liftM (binder_types env T);
          occ \<leftarrow> liftM (occurs_terms env v (u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dpairs)));
          s \<leftarrow>
            (if occ then match1 cfg (fst v) rbinder targs u env (dp # dpairs)
             else mc cfg (fst v) rbinder targs u env dpairs);
          returnW (S_MapNewDset (v, T) Ts s)}
      | _ \<Rightarrow> raiseW Bind))"

text \<open>
  The \<open>\<eta>\<close>-expansion of a pair by new bound variables of types \<open>Es\<close>, the innermost last, and the
  guess of \<open>j\<close> arguments for the type \<open>B\<close> of a pair.
\<close>

definition eta_expand_dpair :: "ptyp list \<Rightarrow> dpair \<Rightarrow> dpair" where
  "eta_expand_dpair Es dp =
    (case dp of (rbinder, t, u) \<Rightarrow>
      (let j = length Es; bs = map (\<lambda>i. Bound (integer_of_nat i)) (rev [0..<j]) in
        (rev (map (\<lambda>T. (STR '''', T)) Es) @ rbinder,
         list_comb (incr_boundvars (integer_of_nat j) t) bs,
         list_comb (incr_boundvars (integer_of_nat j) u) bs)))"

definition match_eta :: "cfg \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> dpair list \<Rightarrow> ptyp \<Rightarrow> nat \<Rightarrow> seq \<Rightarrow> seq W" where
  "match_eta cfg env dp dpairs B j tail =
    (if j = 0 then do {s \<leftarrow> match_pair cfg env dp dpairs; returnW (S_Append s tail)}
     else
      (case gentvars (Suc j) env of (env1, Rs) \<Rightarrow>
        handleW
          (do {
            env2 \<leftarrow> cunify_types (cfg_alg cfg) B (foldr fun_type (tl Rs) (hd Rs)) env1;
            s \<leftarrow> match_pair cfg env2 (eta_expand_dpair (tl Rs) dp) dpairs;
            returnW (S_Append s tail)})
          (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)))"

text \<open>
  \<open>MATCH\<close>: if the type of the pair is an unbound type variable, guess its number of arguments.
\<close>

definition MATCH :: "cfg \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> dpair list \<Rightarrow> seq W" where
  "MATCH cfg env dp dpairs =
    (case dp of (rbinder, t, u) \<Rightarrow>
      (case strip_comb t of
        (Var v T, targs) \<Rightarrow> do {
          B \<leftarrow> liftM (body_type env T);
          if is_TVar B then foldrW (match_eta cfg env dp dpairs B) (arity_guesses cfg B) S_Empty
          else match_pair cfg env dp dpairs}
      | _ \<Rightarrow> raiseW Bind))"

text \<open>\<open>new_dset\<close> of \<open>MATCH\<close>: if \<open>v\<close> was updated to \<open>s\<close>, unify \<open>s\<close> with the copy.\<close>

definition new_dset :: "indexname \<times> ptyp \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> elem W" where
  "new_dset vT Ts u' env' dpairs' =
    do {
      r \<leftarrow> liftM (lookup env' (fst vT) (snd vT));
      case r of
        None \<Rightarrow> do {env'' \<leftarrow> liftM (update vT (types_abs Ts u') env'); returnW (El_E env'' dpairs')}
      | Some s \<Rightarrow> returnW (El_E env' (([], s, types_abs Ts u') # dpairs'))
    }"


subsection \<open>Pulling sequences\<close>

text \<open>
  \<open>pull cfg s\<close> evaluates the closure represented by \<open>s\<close>: \<^const>\<open>None\<close> if the sequence is
  empty, \<open>Some (x, s')\<close> for its first element and the rest. The clauses follow the closures:
  \<^item> \<^const>\<open>S_AddUnify\<close>: the closure of \<open>add_unify\<close> in \<open>hounifiers\<close>, which simplifies the
    disagreement pairs, returns a unifier if there are no flex-rigid pairs, and otherwise
    continues the search with the assignments of \<open>MATCH\<close> to the first one; \<open>CANTUNIFY\<close>
    continues with the rest of the search (\<open>reseq\<close>).
  \<^item> \<^const>\<open>S_Proj\<close>: the closure of \<open>projenv\<close> in \<open>matchcopy\<close>.
  \<^item> \<^const>\<open>S_Maps\<close>: the closure of \<open>Seq.maps (copycons uarg)\<close>.
  \<^item> the other constructors: the closures of \<open>Seq.it_right\<close>, \<open>Seq.map\<close> and \<open>Seq.append\<close>.
\<close>

definition pull_fail :: "(elem \<times> seq) option W" where
  "pull_fail = raiseW (PExn (Failure (STR ''pull'')))"

partial_function (option) pull :: "cfg \<Rightarrow> seq \<Rightarrow> (elem \<times> seq) option W" where
  "pull cfg s =
    (case s of
      S_Empty \<Rightarrow> returnW None
    | S_Single x \<Rightarrow> returnW (Some (x, S_Empty))
    | S_AddUnify tdepth env dpairs reseq \<Rightarrow>
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
          | _ \<Rightarrow> raiseW e)
    | S_ItRight tdepth xq yq \<Rightarrow> do {
        r \<leftarrow> pull cfg xq;
        case r of
          None \<Rightarrow> pull cfg yq
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_E env dpairs \<Rightarrow> pull cfg (S_AddUnify tdepth env dpairs (S_ItRight tdepth xq' yq))
            | _ \<Rightarrow> pull_fail)}
    | S_MapNewDset vT Ts xq \<Rightarrow> do {
        r \<leftarrow> pull cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_C u' env' dpairs' \<Rightarrow> do {
                y \<leftarrow> new_dset vT Ts u' env' dpairs';
                returnW (Some (y, S_MapNewDset vT Ts xq'))}
            | _ \<Rightarrow> pull_fail)}
    | S_MapAbs a T xq \<Rightarrow> do {
        r \<leftarrow> pull cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_C body' env' dpairs' \<Rightarrow> returnW (Some (El_C (Abs a T body') env' dpairs', S_MapAbs a T xq'))
            | _ \<Rightarrow> pull_fail)}
    | S_Proj vname env Ts Us targs rbinder u dpairs head targ tail \<Rightarrow>
        handleW
          (do {
            let (env', args) = make_args vname Ts env Us;
            let dp = (rbinder, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u);
            st \<leftarrow> SIMPL (cfg_alg cfg) env' (dp # dpairs);
            case st of (env2, frigid, fflex) \<Rightarrow>
              returnW (Some (El_C (list_comb head args) env2 (frigid @ fflex), tail))})
          (\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg tail | _ \<Rightarrow> raiseW e)
    | S_MapJoin uhead xq \<Rightarrow> do {
        r \<leftarrow> pull cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_D uargs' env' dpairs' \<Rightarrow>
                returnW (Some (El_C (list_comb uhead uargs') env' dpairs', S_MapJoin uhead xq'))
            | _ \<Rightarrow> pull_fail)}
    | S_Maps vname rbinder targs uarg xq \<Rightarrow> do {
        r \<leftarrow> pull cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_D uargs env dpairs \<Rightarrow> do {
                cs \<leftarrow> copycons cfg vname rbinder targs uarg uargs env dpairs;
                pull cfg (S_Append cs (S_Maps vname rbinder targs uarg xq'))}
            | _ \<Rightarrow> pull_fail)}
    | S_Append xq yq \<Rightarrow> do {
        r \<leftarrow> pull cfg xq;
        case r of
          None \<Rightarrow> pull cfg yq
        | Some (x, xq') \<Rightarrow> returnW (Some (x, S_Append xq' yq))}
    | S_MapCons uargs xq \<Rightarrow> do {
        r \<leftarrow> pull cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_C uarg' env' dpairs' \<Rightarrow> returnW (Some (El_D (uarg' # uargs) env' dpairs', S_MapCons uargs xq'))
            | _ \<Rightarrow> pull_fail)})"


subsection \<open>Unification\<close>

text \<open>
  \<open>hounifiers\<close>: unify the pairs of terms in the environment, with Huet's procedure. The
  unifiers come with flex-flex pairs, which need not be in normal form.
\<close>

definition hounifiers :: "binders \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> seq" where
  "hounifiers binders env tus = S_AddUnify 1 env (map (\<lambda>(t, u). (binders, t, u)) tus) S_Empty"

text \<open>
  \<open>unifiers\<close>: try pattern unification first; fall back to \<open>hounifiers\<close> if a term is not a
  pattern. The pattern unification is the model of session \<open>Pure_Pattern\<close>; in the generated
  code, the wrapper calls Pure's \<open>Pattern.unify\<close> instead.
\<close>

definition unifiers :: "algebra \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> seq M" where
  "unifiers alg env tus =
    handle (do {env' \<leftarrow> foldM (\<lambda>(t, u) env. unify alg t u env) tus env; return (S_Single (El_R env' []))})
      (\<lambda>e. case e of
        Unif _ \<Rightarrow> return S_Empty
      | Pattern \<Rightarrow> return (hounifiers [] env tus)
      | _ \<Rightarrow> raise e)"

text \<open>Trivial unifiers of flex-flex pairs (\<open>smash_flexflex\<close>).\<close>

definition var_head_of :: "env \<Rightarrow> pterm \<Rightarrow> (indexname \<times> ptyp) W" where
  "var_head_of env t =
    do {
      t' \<leftarrow> liftM (norm_term env t);
      case head_of (strip_abs_body t') of Var v T \<Rightarrow> returnW (v, T) | _ \<Rightarrow> raiseW CANTUNIFY
    }"

definition type_abs :: "env \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "type_abs env T t = do {Ts \<leftarrow> binder_types env T; return (types_abs Ts t)}"

definition smash_flexflex1 :: "pterm \<times> pterm \<Rightarrow> env \<Rightarrow> env W" where
  "smash_flexflex1 tu env =
    (case tu of (t, u) \<Rightarrow> do {
      (v, T) \<leftarrow> var_head_of env t;
      (w, U) \<leftarrow> var_head_of env u;
      B \<leftarrow> liftM (body_type env T);
      let (env', var) = genvar (fst v) env B;
      tU \<leftarrow> liftM (type_abs env' U var);
      env'' \<leftarrow> liftM (vupdate (w, U) tU env');
      if v = w \<and> T = U then returnW env''
      else do {tT \<leftarrow> liftM (type_abs env' T var); liftM (vupdate (v, T) tT env'')}})"

definition smash_flexflex :: "env \<times> (pterm \<times> pterm) list \<Rightarrow> env W" where
  "smash_flexflex et = (case et of (env, tpairs) \<Rightarrow> foldrW smash_flexflex1 tpairs env)"

end
