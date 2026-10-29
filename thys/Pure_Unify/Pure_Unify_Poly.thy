section \<open>Prototype: Complete Matching for Polymorphic Problems\<close>

theory Pure_Unify_Poly
  imports Pure_Unify
begin

text \<open>
  \<^const>\<open>MATCH\<close> fixes the number of arguments of terms whose type is an unbound type variable:
  it treats the type variable as a base type. A solution may instantiate it with a function
  type, so \<^const>\<open>hounifiers\<close> loses unifiers of polymorphic problems. For example, for
  \<open>?F ?G =?= c\<close> with \<open>?F :: ?'a \<Rightarrow> 'b\<close> it misses \<open>?'a := 'd \<Rightarrow> 'b, ?F := \<lambda>x. x e, ?G := \<lambda>y. c\<close>.

  This prototype guesses the missing arities where they matter, up to the remaining search
  budget (each guessed argument costs at least one unit of the size of a solution):
  \<^item> the type of a flex-rigid pair, if it is an unbound type variable \<open>?'b\<close>: for \<open>j > 0\<close>,
    \<open>?'b := ?'e\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> ?'e\<^sub>j \<Rightarrow> ?'r\<close>, and the pair is \<open>\<eta>\<close>-expanded by \<open>j\<close> bound variables;
  \<^item> the result type of a projected argument, if it is an unbound type variable \<open>?'a\<close>: for
    \<open>p > 0\<close>, \<open>?'a := ?'c\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> ?'c\<^sub>p \<Rightarrow> ?'a'\<close>, and the projection takes \<open>p\<close> more arguments;
  \<^item> an argument of the rigid side whose type ends in an unbound type variable is not copied,
    but becomes a new flex-rigid pair, where the first guess applies.
  With \<open>j = 0\<close> and \<open>p = 0\<close> the steps are those of \<^const>\<open>MATCH\<close>. If no unbound type variable
  occurs in these positions, in particular on monomorphic problems, the search is the one of
  \<^const>\<open>hounifiers\<close>.
\<close>

subsection \<open>New type variables\<close>

definition gentvars :: "nat \<Rightarrow> env \<Rightarrow> env \<times> ptyp list" where
  "gentvars k env =
    (case env of Envir i te tye \<Rightarrow>
      (Envir (i + 1) te tye, map (\<lambda>n. TVar (aT + radixstring (integer_of_nat n), i + 1) []) [0..<k]))"

text \<open>Guesses up to the budget: the list \<open>[0, \<dots>, b]\<close>.\<close>

definition guesses :: "integer \<Rightarrow> nat list" where
  "guesses b = [0..<Suc (nat_of_integer b)]"


subsection \<open>Sequences\<close>

text \<open>As \<^typ>\<open>seq\<close>, but the closure of \<open>Seq.maps (copycons uarg)\<close> carries the budget.\<close>

datatype cseq =
  C_Empty
| C_Single elem
| C_AddUnify integer env "dpair list" cseq
| C_ItRight integer cseq cseq
| C_MapNewDset "indexname \<times> ptyp" "ptyp list" cseq
| C_MapAbs name ptyp cseq
| C_Proj name env "ptyp list" "ptyp list" "pterm list" binders pterm "dpair list" pterm pterm cseq
| C_MapJoin pterm cseq
| C_Maps integer name binders "pterm list" pterm cseq
| C_Append cseq cseq
| C_MapCons "pterm list" cseq


subsection \<open>Copying rigid terms\<close>

fun copyargsc :: "integer \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> pterm list \<Rightarrow> cseq" where
  "copyargsc bud vname rbinder targs env dpairs [] = C_Single (El_D [] env dpairs)"
| "copyargsc bud vname rbinder targs env dpairs (uarg # uargs) =
    C_Maps bud vname rbinder targs uarg (copyargsc bud vname rbinder targs env dpairs uargs)"

text \<open>
  The type unifications of a projection with \<open>p\<close> more arguments: the result type \<open>bary\<close> of the
  argument becomes \<open>?'c\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> ?'c\<^sub>p \<Rightarrow> ?'a'\<close>, and \<open>?'a'\<close> is unified with the base type.
\<close>

definition proj_types :: "cfg \<Rightarrow> ptyp \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> (ptyp list \<times> env) W" where
  "proj_types cfg base Us bary p env =
    (if p = 0 then do {
      env' \<leftarrow>
        (if cfg_trace_types cfg then test_unify_types (cfg_alg cfg) base bary env
         else cunify_types (cfg_alg cfg) base bary env);
      returnW (Us, env')}
     else
      (case gentvars (Suc p) env of (env1, tvs) \<Rightarrow> do {
        env2 \<leftarrow> cunify_types (cfg_alg cfg) bary (foldr fun_type (butlast tvs) (last tvs)) env1;
        env3 \<leftarrow> cunify_types (cfg_alg cfg) base (last tvs) env2;
        returnW (Us @ butlast tvs, env3)}))"

text \<open>The arities of the projection on an argument with result type \<open>bary\<close>:\<close>

definition proj_arities :: "integer \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> nat list" where
  "proj_arities bud Us bary = (if is_TVar bary then guesses (bud - ilength Us) else [0])"

fun projenvsc :: "cfg \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow>
    ptyp \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> nat list \<Rightarrow> cseq \<Rightarrow> cseq W" where
  "projenvsc cfg vname rbinder targs u env dpairs base Ts head Us bary targ [] tail = returnW tail"
| "projenvsc cfg vname rbinder targs u env dpairs base Ts head Us bary targ (p # ps) tail =
    do {
      tl \<leftarrow> projenvsc cfg vname rbinder targs u env dpairs base Ts head Us bary targ ps tail;
      handleW
        (do {
          (Us', env') \<leftarrow> proj_types cfg base Us bary p env;
          returnW (C_Proj vname env' Ts Us' targs rbinder u dpairs head targ tl)})
        (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tl | _ \<Rightarrow> raiseW e)
    }"

fun matchfunc :: "cfg \<Rightarrow> integer \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> pterm \<Rightarrow>
    pterm list \<Rightarrow> ptyp \<Rightarrow> ptyp list \<Rightarrow> (pterm \<times> ptyp \<times> pterm) list \<Rightarrow> cseq W" where
  "matchfunc cfg bud vname rbinder targs u env dpairs uhead uargs base Ts ((bvar, T, targ) # projs) =
    do {
      Usb \<leftarrow> liftM (strip_type env T);
      tail \<leftarrow> matchfunc cfg bud vname rbinder targs u env dpairs uhead uargs base Ts projs;
      (case Usb of (Us, bary) \<Rightarrow>
        projenvsc cfg vname rbinder targs u env dpairs base Ts bvar Us bary targ (proj_arities bud Us bary) tail)
    }"
| "matchfunc cfg bud vname rbinder targs u env dpairs uhead uargs base Ts [] =
    returnW
      (case uhead of
        Const _ _ \<Rightarrow> C_MapJoin uhead (copyargsc bud vname rbinder targs env dpairs uargs)
      | Free _ _ \<Rightarrow> C_MapJoin uhead (copyargsc bud vname rbinder targs env dpairs uargs)
      | _ \<Rightarrow> C_Empty)"

function mcc :: "cfg \<Rightarrow> integer \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> cseq W" where
  "mcc cfg bud vname rbinder targs u env dpairs =
    (let uhead = fst (strip_comb u); uargs = snd (strip_comb u) in
    do {
      T0 \<leftarrow> liftM (fastype env rbinder uhead);
      base \<leftarrow> liftM (body_type env T0);
      Ts \<leftarrow> liftM (mapM (fastype env rbinder) targs);
      case uhead of
        Abs a T body \<Rightarrow> do {
          s \<leftarrow> mcc cfg bud vname ((a, T) # rbinder) (map (incr_boundvars 1) targs @ [Bound 0]) body env dpairs;
          returnW (C_MapAbs a T s)}
      | Var w _ \<Rightarrow>
          (let (env', newhd) = genvar (fst w) env (foldr fun_type Ts base) in
            returnW (C_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rbinder, list_comb newhd targs, u) # dpairs))))
      | _ \<Rightarrow> do {
          projs \<leftarrow> make_projs u targs Ts targs;
          matchfunc cfg bud vname rbinder targs u env dpairs uhead uargs base Ts (rev projs)}
    })"
  by auto
termination
  by (relation "measure (\<lambda>(cfg, bud, vname, rbinder, targs, u, env, dpairs). size u)")
    (auto dest: strip_comb_Abs_size[OF sym])

declare mcc.simps[simp del]

text \<open>
  An argument whose type ends in an unbound type variable is deferred: its copy is a new
  variable applied to the arguments \<open>targs\<close>, with a new flex-rigid pair.
\<close>

definition copyconsc :: "cfg \<Rightarrow> integer \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> cseq W" where
  "copyconsc cfg bud vname rbinder targs uarg uargs env dpairs =
    do {
      u1 \<leftarrow> liftM (head_norm env uarg);
      u2 \<leftarrow> liftM (eta_norm env rbinder u1);
      A \<leftarrow> liftM (fastype env rbinder u2);
      B \<leftarrow> liftM (body_type env A);
      s \<leftarrow>
        (if is_TVar B then do {
          Ts \<leftarrow> liftM (mapM (fastype env rbinder) targs);
          (let (env', newhd) = genvar vname env (foldr fun_type Ts A) in
            returnW (C_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rbinder, list_comb newhd targs, u2) # dpairs))))}
         else mcc cfg bud vname rbinder targs u2 env dpairs);
      returnW (C_MapCons uargs s)
    }"

fun match1_projsc :: "cfg \<Rightarrow> integer \<Rightarrow> name \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> ptyp \<Rightarrow> ptyp list \<Rightarrow>
    (pterm \<times> ptyp \<times> pterm) list \<Rightarrow> cseq \<Rightarrow> cseq W" where
  "match1_projsc cfg bud vname env dpairs base Ts ((bvar, T, targ) # projs) tail =
    do {
      Usb \<leftarrow> liftM (strip_type env T);
      tl \<leftarrow> match1_projsc cfg bud vname env dpairs base Ts projs tail;
      (case Usb of (Us, bary) \<Rightarrow>
        foldrW (\<lambda>p tl.
          handleW
            (do {
              (Us', env') \<leftarrow> proj_types cfg base Us bary p env;
              (case make_args vname Ts env' Us' of (env'', args) \<Rightarrow>
                returnW (C_Append (C_Single (El_C (list_comb bvar args) env'' dpairs)) tl))})
            (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tl | _ \<Rightarrow> raiseW e))
          (proj_arities bud Us bary) tl)
    }"
| "match1_projsc cfg bud vname env dpairs base Ts [] tail = returnW tail"

definition match1c :: "cfg \<Rightarrow> integer \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> cseq W" where
  "match1c cfg bud vname rbinder targs u env dpairs =
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
              returnW (C_Single (El_C (list_comb uhead args) env' dpairs)))}
        | Free _ _ \<Rightarrow> do {
            Us \<leftarrow> liftM (binder_types env T0);
            (case make_args vname Ts env Us of (env', args) \<Rightarrow>
              returnW (C_Single (El_C (list_comb uhead args) env' dpairs)))}
        | _ \<Rightarrow> returnW C_Empty);
      match1_projsc cfg bud vname env dpairs base Ts (rev projs) imit
    })"


subsection \<open>Matching\<close>

text \<open>\<^const>\<open>MATCH\<close> on a pair whose type is treated as a base type.\<close>

definition match_core :: "cfg \<Rightarrow> integer \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> dpair list \<Rightarrow> dpair \<Rightarrow> cseq W" where
  "match_core cfg bud env dp dpairs dp0 =
    (case dp of (rbinder, t, u) \<Rightarrow>
      (case strip_comb t of
        (Var v T, targs) \<Rightarrow> do {
          Ts \<leftarrow> liftM (binder_types env T);
          occ \<leftarrow> liftM (occurs_terms env v (u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dpairs)));
          s \<leftarrow>
            (if occ then match1c cfg bud (fst v) rbinder targs u env (dp0 # dpairs)
             else mcc cfg bud (fst v) rbinder targs u env dpairs);
          returnW (C_MapNewDset (v, T) Ts s)}
      | _ \<Rightarrow> raiseW Bind))"

text \<open>
  The \<open>\<eta>\<close>-expansion of a pair by \<open>j\<close> new bound variables of types \<open>es\<close>, the innermost last.
\<close>

definition eta_expand_dpair :: "ptyp list \<Rightarrow> dpair \<Rightarrow> dpair" where
  "eta_expand_dpair es dp =
    (case dp of (rbinder, t, u) \<Rightarrow>
      (let j = length es; bs = map (\<lambda>i. Bound (integer_of_nat i)) (rev [0..<j]) in
        (rev (map (\<lambda>T. (STR '''', T)) es) @ rbinder,
         list_comb (incr_boundvars (integer_of_nat j) t) bs,
         list_comb (incr_boundvars (integer_of_nat j) u) bs)))"

text \<open>
  The guesses of the arity of the type \<open>B\<close> of the pair: \<open>j = 0\<close> treats \<open>B\<close> as a base type, as
  \<^const>\<open>MATCH\<close> does.
\<close>

definition match_eta :: "cfg \<Rightarrow> integer \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> dpair list \<Rightarrow> ptyp \<Rightarrow> nat \<Rightarrow> cseq W" where
  "match_eta cfg bud env dp dpairs B j =
    (if j = 0 then match_core cfg bud env dp dpairs dp
     else
      (case gentvars (Suc j) env of (env1, tvs) \<Rightarrow> do {
        env2 \<leftarrow> cunify_types (cfg_alg cfg) B (foldr fun_type (butlast tvs) (last tvs)) env1;
        match_core cfg bud env2 (eta_expand_dpair (butlast tvs) dp) dpairs dp}))"

definition MATCHc :: "cfg \<Rightarrow> integer \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> dpair list \<Rightarrow> cseq W" where
  "MATCHc cfg bud env dp dpairs =
    (case dp of (rbinder, t, u) \<Rightarrow>
      (case strip_comb t of
        (Var v T, targs) \<Rightarrow> do {
          B \<leftarrow> liftM (body_type env T);
          foldrW (\<lambda>j s.
            handleW (do {s' \<leftarrow> match_eta cfg bud env dp dpairs B j; returnW (C_Append s' s)})
              (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW s | _ \<Rightarrow> raiseW e))
            (if is_TVar B then guesses bud else [0]) C_Empty}
      | _ \<Rightarrow> raiseW Bind))"


subsection \<open>Pulling sequences\<close>

definition pullc_fail :: "(elem \<times> cseq) option W" where
  "pullc_fail = raiseW (PExn (Failure (STR ''pull'')))"

partial_function (option) pullc :: "cfg \<Rightarrow> cseq \<Rightarrow> (elem \<times> cseq) option W" where
  "pullc cfg s =
    (case s of
      C_Empty \<Rightarrow> returnW None
    | C_Single x \<Rightarrow> returnW (Some (x, C_Empty))
    | C_AddUnify tdepth env dpairs reseq \<Rightarrow>
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
                    pullc cfg reseq}
                  else do {
                    whenW (tdepth > cfg_trace_bound cfg)
                      (emit (Ev_Dpairs (STR ''Enter MATCH'') env' (frs @ ffs)));
                    ms \<leftarrow> MATCHc cfg (cfg_search_bound cfg - tdepth) env' dp (frigid' @ ffs);
                    pullc cfg (C_ItRight (tdepth + 1) ms reseq)})})
          (\<lambda>e. case e of
            CANTUNIFY \<Rightarrow> do {
              whenW (tdepth > cfg_trace_bound cfg) (emit Ev_Failure_Node);
              pullc cfg reseq}
          | _ \<Rightarrow> raiseW e)
    | C_ItRight tdepth xq yq \<Rightarrow> do {
        r \<leftarrow> pullc cfg xq;
        case r of
          None \<Rightarrow> pullc cfg yq
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_E env dpairs \<Rightarrow> pullc cfg (C_AddUnify tdepth env dpairs (C_ItRight tdepth xq' yq))
            | _ \<Rightarrow> pullc_fail)}
    | C_MapNewDset vT Ts xq \<Rightarrow> do {
        r \<leftarrow> pullc cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_C u' env' dpairs' \<Rightarrow> do {
                y \<leftarrow> new_dset vT Ts u' env' dpairs';
                returnW (Some (y, C_MapNewDset vT Ts xq'))}
            | _ \<Rightarrow> pullc_fail)}
    | C_MapAbs a T xq \<Rightarrow> do {
        r \<leftarrow> pullc cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_C body' env' dpairs' \<Rightarrow> returnW (Some (El_C (Abs a T body') env' dpairs', C_MapAbs a T xq'))
            | _ \<Rightarrow> pullc_fail)}
    | C_Proj vname env Ts Us targs rbinder u dpairs head targ tail \<Rightarrow>
        handleW
          (do {
            let (env', args) = make_args vname Ts env Us;
            let dp = (rbinder, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u);
            st \<leftarrow> SIMPL (cfg_alg cfg) env' (dp # dpairs);
            case st of (env2, frigid, fflex) \<Rightarrow>
              returnW (Some (El_C (list_comb head args) env2 (frigid @ fflex), tail))})
          (\<lambda>e. case e of CANTUNIFY \<Rightarrow> pullc cfg tail | _ \<Rightarrow> raiseW e)
    | C_MapJoin uhead xq \<Rightarrow> do {
        r \<leftarrow> pullc cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_D uargs' env' dpairs' \<Rightarrow>
                returnW (Some (El_C (list_comb uhead uargs') env' dpairs', C_MapJoin uhead xq'))
            | _ \<Rightarrow> pullc_fail)}
    | C_Maps bud vname rbinder targs uarg xq \<Rightarrow> do {
        r \<leftarrow> pullc cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_D uargs env dpairs \<Rightarrow> do {
                cs \<leftarrow> copyconsc cfg bud vname rbinder targs uarg uargs env dpairs;
                pullc cfg (C_Append cs (C_Maps bud vname rbinder targs uarg xq'))}
            | _ \<Rightarrow> pullc_fail)}
    | C_Append xq yq \<Rightarrow> do {
        r \<leftarrow> pullc cfg xq;
        case r of
          None \<Rightarrow> pullc cfg yq
        | Some (x, xq') \<Rightarrow> returnW (Some (x, C_Append xq' yq))}
    | C_MapCons uargs xq \<Rightarrow> do {
        r \<leftarrow> pullc cfg xq;
        case r of
          None \<Rightarrow> returnW None
        | Some (x, xq') \<Rightarrow>
            (case x of
              El_C uarg' env' dpairs' \<Rightarrow> returnW (Some (El_D (uarg' # uargs) env' dpairs', C_MapCons uargs xq'))
            | _ \<Rightarrow> pullc_fail)})"

definition hounifiersc :: "binders \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> cseq" where
  "hounifiersc binders env tus = C_AddUnify 1 env (map (\<lambda>(t, u). (binders, t, u)) tus) C_Empty"

declare pullc.simps[code]

end
