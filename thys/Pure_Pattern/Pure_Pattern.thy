section \<open>Unification and Matching of Higher-Order Patterns\<close>

theory Pure_Pattern
  imports Pure_Envir
begin

text \<open>
  A literal model of \<^file>\<open>~~/src/Pure/pattern.ML\<close> (Nipkow, Heinzelmann, Berghofer):
  unification of higher-order patterns (\<open>Pattern.unify\<close>), including the shortcuts of the ML
  implementation (avoiding projections for \<open>F(x\<^sub>n, \<dots>, x\<^sub>1)\<close>, the two flex-flex cases,
  on-the-fly \<open>\<eta>\<close>-expansion, unification of types with sorts), matching of higher-order patterns
  (\<open>Pattern.match\<close>) with fallback to first-order matching (\<open>Pattern.first_order_match\<close>), and
  the test \<open>Pattern.pattern\<close>.

  The function names follow the ML code; the order of evaluation (and hence which exception
  is raised first) is preserved. Failures of unification carry tracing information
  (see \<^typ>\<open>unif_trace\<close>). One deviation from Isabelle2026 is a fix: a failed occurs check
  raises \<open>Unif\<close> only for a rigid occurrence (see \<open>flexrigid\<close>).
\<close>


subsection \<open>Auxiliary functions\<close>

text \<open>Occurs check of term variables (\<open>occurs\<close>); may diverge on cyclic environments.\<close>

partial_function (option) occurs :: "indexname \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool M" where
  "occurs F t env =
    (case t of
      Var G T \<Rightarrow> do {r \<leftarrow> lookup env G T; case r of Some u \<Rightarrow> occurs F u env | None \<Rightarrow> return (F = G)}
    | t1 $ t2 \<Rightarrow> do {b \<leftarrow> occurs F t1 env; if b then return True else occurs F t2 env}
    | Abs _ _ u \<Rightarrow> occurs F u env
    | _ \<Rightarrow> return False)"

text \<open>\<open>mapbnd f\<close>: apply \<open>f\<close> to the loose bound variables (\<open>f\<close> may raise exceptions).\<close>

fun mapbnd :: "(integer \<Rightarrow> integer M) \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "mapbnd f d (Bound i) = (if i < d then return (Bound i) else do {j \<leftarrow> f (i - d); return (Bound (j + d))})"
| "mapbnd f d (Abs s T t) = do {t' \<leftarrow> mapbnd f (d + 1) t; return (Abs s T t')}"
| "mapbnd f d (u1 $ u2) = do {u1' \<leftarrow> mapbnd f d u1; u2' \<leftarrow> mapbnd f d u2; return (u1' $ u2')}"
| "mapbnd f d atom = return atom"

fun incr_aux :: "integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "incr_aux d (Bound i) = (if i < d then Bound i else Bound (i + 1))"
| "incr_aux d (Abs s T t) = Abs s T (incr_aux (d + 1) t)"
| "incr_aux d (u1 $ u2) = incr_aux d u1 $ incr_aux d u2"
| "incr_aux d atom = atom"

text \<open>\<open>incr = mapbnd (fn i => i + 1)\<close>\<close>

definition incr :: "pterm \<Rightarrow> pterm" where
  "incr t = incr_aux 0 t"

lemma mapbnd_incr: "mapbnd (\<lambda>i. return (i + 1)) d t = return (incr_aux d t)"
  by (induction t arbitrary: d) simp_all

fun idx :: "integer list \<Rightarrow> integer \<Rightarrow> integer M" where
  "idx [] j = raise (Unif No_Trace)"
| "idx (i # is) j = (if i = j then return (ilength is) else idx is j)"

fun mkabs :: "binders \<Rightarrow> integer list \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "mkabs binders [] t = return t"
| "mkabs binders (i # is) t = do {(x, T) \<leftarrow> nth binders i; u \<leftarrow> mkabs binders is t; return (Abs x T u)}"

fun ints_of :: "pterm list \<Rightarrow> integer list M" where
  "ints_of [] = return []"
| "ints_of (Bound i # bs) = do {is \<leftarrow> ints_of bs; if i \<in> set is then raise Pattern else return (i # is)}"
| "ints_of _ = raise Pattern"

definition ints_of' :: "env \<Rightarrow> pterm list \<Rightarrow> integer list M" where
  "ints_of' env ts = do {ts' \<leftarrow> mapM (head_norm env) ts; ints_of ts'}"

text \<open>
  Rigid occurrence check (not in the ML code of Isabelle2026, see \<open>flexrigid\<close>):
  \<open>F\<close> occurs as the head of a pattern \<open>F x\<^sub>1 \<dots> x\<^sub>n\<close> (distinct bound variables) that is
  reached, modulo head normalisation, through abstractions and arguments of rigid heads only.
  Such an occurrence survives in every well-typed instance, so the unification problem
  \<open>F y\<^sub>1 \<dots> y\<^sub>m =?= t\<close> has no solution. Other occurrences may vanish in instances.
\<close>

context
begin

text \<open>The default bound is too small to derive the fixed-point induction rule.\<close>

declare [[unify_search_bound = 100]]

partial_function (option) rigid_occurs :: "indexname \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool M" where
  "rigid_occurs F t env =
    do {
      t' \<leftarrow> head_norm env t;
      (case t' of
        Abs _ _ u \<Rightarrow> rigid_occurs F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              Var G _ \<Rightarrow>
                if G = F then
                  handle (do {_ \<leftarrow> ints_of' env ts; return True})
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u env) ts)))
    }"

end

definition app :: "pterm \<Rightarrow> integer list \<Rightarrow> pterm" where
  "app s is = foldl (\<lambda>s i. s $ Bound i) s is"

fun red :: "pterm \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> pterm M" where
  "red (Abs _ _ s) (i # is) js = red s is (i # js)"
| "red t [] [] = return t"
| "red t is jn = do {t' \<leftarrow> mapbnd (nth jn) 0 t; return (app t' is)}"

text \<open>\<open>split_type ([T1,....,Tn]---> T,n,[]) = ([Tn,...,T1],T)\<close>\<close>

function (sequential) split_type :: "ptyp \<Rightarrow> integer \<Rightarrow> ptyp list \<Rightarrow> (ptyp list \<times> ptyp) M" where
  "split_type T n Ts =
    (if n = 0 then return (Ts, T) else
      case T of
        Type a [T1, T2] \<Rightarrow> if a = STR ''fun'' then split_type T2 (n - 1) (T1 # Ts)
          else raise (Failure (STR ''split_type''))
      | _ \<Rightarrow> raise (Failure (STR ''split_type'')))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(T, n, Ts). size T)") auto

definition type_of_G :: "env \<Rightarrow> ptyp \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> ptyp M" where
  "type_of_G env T n is =
    do {
      T' \<leftarrow> norm_type (tyenv env) T;
      (Ts, U) \<leftarrow> split_type T' n [];
      Us \<leftarrow> mapM (nth Ts) is;
      return (foldr fun_type Us U)
    }"

definition mk_hnf :: "binders \<Rightarrow> integer list \<Rightarrow> pterm \<Rightarrow> integer list \<Rightarrow> pterm M" where
  "mk_hnf binders is G js = mkabs binders is (app G js)"

definition mk_new_hnf :: "env \<Rightarrow> binders \<Rightarrow> integer list \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> integer list \<Rightarrow> env M" where
  "mk_new_hnf env binders is F T js =
    do {
      Gty \<leftarrow> type_of_G env T (ilength is) js;
      let (env', G) = genvar (fst F) env Gty;
      t \<leftarrow> mk_hnf binders is G js;
      update (F, T) t env'
    }"

text \<open>\<open>downto0 (is, n) \<longleftrightarrow> is = [n, n - 1, ..., 0]\<close>\<close>

fun downto0 :: "integer list \<Rightarrow> integer \<Rightarrow> bool" where
  "downto0 (i # is) n = (i = n \<and> downto0 is (n - 1))"
| "downto0 [] n = (n = -1)"

text \<open>\<open>mk_proj_list is = [ |is| - k | 1 <= k <= |is| and is[k] >= 0 ]\<close>\<close>

fun mk_proj_list_aux :: "integer option list \<Rightarrow> integer \<Rightarrow> integer list" where
  "mk_proj_list_aux (i # is) j = (if i \<noteq> None then j # mk_proj_list_aux is (j - 1) else mk_proj_list_aux is (j - 1))"
| "mk_proj_list_aux [] _ = []"

definition mk_proj_list :: "integer option list \<Rightarrow> integer list" where
  "mk_proj_list is = mk_proj_list_aux is (ilength is - 1)"

text \<open>Iteration that threads a state (\<open>prs\<close> in \<open>proj\<close>).\<close>

fun mapAccM :: "('a \<Rightarrow> 's \<Rightarrow> ('b \<times> 's) M) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> ('b list \<times> 's) M" where
  "mapAccM f [] s = return ([], s)"
| "mapAccM f (x # xs) s = do {(y, s1) \<leftarrow> f x s; (ys, s2) \<leftarrow> mapAccM f xs s1; return (y # ys, s2)}"

lemma mapAccM_mono[partial_function_mono]:
  assumes "\<And>x s. mono_option (\<lambda>f. C x s f)"
  shows "mono_option (\<lambda>f. mapAccM (\<lambda>x s. C x s f) xs s)"
  using assms
  by (induction xs arbitrary: s)
    (auto intro!: bindM_mono simp: return_def option.const_mono split_def)

definition try_trans :: "integer list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer option M" where
  "try_trans is d i =
    handle (if i < d then return (Some i) else do {j \<leftarrow> idx is (i - d); return (Some (j + d))})
      (\<lambda>_. return None)"

definition trans :: "integer list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer M" where
  "trans is d i = (if i < d then return i else do {j \<leftarrow> idx is (i - d); return (j + d)})"

text \<open>Projection (\<open>pr\<close> in \<open>proj\<close>).\<close>

partial_function (option) pr ::
  "integer list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> binders \<Rightarrow> (pterm \<times> env) M" where
  "pr xs s env d binders =
    do {
      s' \<leftarrow> head_norm env s;
      if is_Abs s' then
        (case s' of
          Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> pr xs t env (d + 1) ((a, T) # binders); return (Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s' in
          if is_Var h then
            (case h of
              Var F Fty \<Rightarrow> do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}
            | _ \<Rightarrow> raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. pr xs s env d binders) ts env;
            return (list_comb h' ts', env')})
    }"

definition proj :: "pterm \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> integer list \<Rightarrow> (pterm \<times> env) M" where
  "proj s env binders is =
    (if downto0 is (ilength binders - 1) then return (s, env) else pr is s env 0 binders)"

text \<open>\<open>mk_ff_list (is, js) = [ length(is) - k | 1 <= k <= |is| and is[k] = js[k] ]\<close>\<close>

fun mk_ff_list_aux :: "integer list \<Rightarrow> integer list \<Rightarrow> integer \<Rightarrow> integer list M" where
  "mk_ff_list_aux [] [] _ = return []"
| "mk_ff_list_aux (i # is) (j # js) k =
    (if i = j then do {ks \<leftarrow> mk_ff_list_aux is js (k - 1); return (k # ks)}
     else mk_ff_list_aux is js (k - 1))"
| "mk_ff_list_aux _ _ _ = raise (Failure (STR ''mk_ff_list''))"

definition mk_ff_list :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list M" where
  "mk_ff_list is js = mk_ff_list_aux is js (ilength is - 1)"

definition flexflex1 :: "env \<Rightarrow> binders \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> env M" where
  "flexflex1 env binders F Fty is js =
    (if is = js then return env
     else do {ks \<leftarrow> mk_ff_list is js; mk_new_hnf env binders is F Fty ks})"

text \<open>\<open>Term_Ord.indexname_ord (G, F) = LESS\<close>\<close>

definition indexname_less :: "indexname \<Rightarrow> indexname \<Rightarrow> bool" where
  "indexname_less G F \<longleftrightarrow> snd G < snd F \<or> (snd G = snd F \<and> fst G < fst F)"

definition ff :: "env \<Rightarrow> binders \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> integer list \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow>
    integer list \<Rightarrow> env M" where
  "ff env binders F Fty is G Gty js =
    (if subset js is then do {
       ks \<leftarrow> mapM (idx is) js;
       t \<leftarrow> mkabs binders is (app (Var G Gty) ks);
       update (F, Fty) t env}
     else do {
       let ks = inter js is;
       ks' \<leftarrow> mapM (idx is) ks;
       Hty \<leftarrow> type_of_G env Fty (ilength is) ks';
       let (env', H) = genvar (fst G) env Hty;
       let lam = (\<lambda>is. do {ks' \<leftarrow> mapM (idx is) ks; mkabs binders is (app H ks')});
       tG \<leftarrow> lam js;
       tF \<leftarrow> lam is;
       env'' \<leftarrow> update (F, Fty) tF env';
       update (G, Gty) tG env''})"

definition flexflex2 :: "env \<Rightarrow> binders \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> integer list \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow>
    integer list \<Rightarrow> env M" where
  "flexflex2 env binders F Fty is G Gty js =
    (if indexname_less G F then ff env binders F Fty is G Gty js
     else ff env binders G Gty js F Fty is)"


subsection \<open>Unification\<close>

text \<open>\<open>Pattern.unify_types\<close>: type unification via \<open>Sign.typ_unify\<close> (arguments swapped).\<close>

definition unify_types :: "algebra \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> env \<Rightarrow> env M" where
  "unify_types alg T U env =
    (if T = U then return env
     else handle
      (do {(tye', maxidx') \<leftarrow> type_unify alg U T (tyenv env, maxidx env);
           return (Envir maxidx' (tenv env) tye')})
      (\<lambda>e. case e of TUnify \<Rightarrow> raise (Unif (Typ_Clash (tyenv env) T U)) | _ \<Rightarrow> raise e))"

text \<open>
  Unlike Isabelle2026, a failed occurs check raises \<open>Unif\<close> (no unifier) only for a rigid
  occurrence (\<^const>\<open>rigid_occurs\<close>), and \<open>Pattern\<close> (give up) otherwise: e.g.
  \<open>?p =?= \<not> (?f ?p)\<close> has the unifier \<open>?p \<mapsto> \<not> False\<close>, \<open>?f \<mapsto> \<lambda>_. False\<close>. The occurs check
  itself remains: it prevents cyclic bindings.
\<close>

definition flexrigid :: "env \<Rightarrow> binders \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> integer list \<Rightarrow> pterm \<Rightarrow> env M" where
  "flexrigid env binders F Fty is t =
    do {
      b \<leftarrow> occurs F t env;
      if b then do {
        b' \<leftarrow> rigid_occurs F t env;
        if b' then raise (Unif (Ocheck_Fail F t binders env)) else raise Pattern}
      else handle
        (do {(u, env') \<leftarrow> proj t env binders is; u' \<leftarrow> mkabs binders is u; update (F, Fty) u' env'})
        (\<lambda>e. case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env binders F is t)) | _ \<Rightarrow> raise e)
    }"

text \<open>
  \<open>unif\<close> together with the functions \<open>cases\<close>, \<open>rigidrigid\<close> and \<open>rigidrigidB\<close>, which are
  mutually recursive with it in the ML code and inlined here.
\<close>

definition rigid_name :: "pterm \<Rightarrow> name" where
  "rigid_name h = (case h of Const c _ \<Rightarrow> c | Free f _ \<Rightarrow> f | _ \<Rightarrow> STR '''')"

text \<open>The clash cases of \<open>cases\<close> (heads are distinct or of different kinds).\<close>

definition rigid_clash :: "binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env M" where
  "rigid_clash binders h1 h2 =
    (case (h1, h2) of
      (Bound i, Bound j) \<Rightarrow> raise (Unif (Clash_BB binders i j))
    | (Bound i, _) \<Rightarrow> raise (Unif (Clash_B binders i (rigid_name h2)))
    | (_, Bound i) \<Rightarrow> raise (Unif (Clash_B binders i (rigid_name h1)))
    | _ \<Rightarrow> raise (Unif (Clash (rigid_name h1) (rigid_name h2))))"

partial_function (option) unif :: "algebra \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> env M" where
  "unif alg binders s t env =
    do {
      s' \<leftarrow> head_norm env s;
      t' \<leftarrow> head_norm env t;
      if is_Abs s' \<and> is_Abs t' then
        (case (s', t') of
          (Abs ns Ts ts, Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            unif alg ((name, Ts) # binders) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s' then
        (case s' of
          Abs ns Ts ts \<Rightarrow> unif alg ((ns, Ts) # binders) ts (incr t' $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t' then
        (case t' of
          Abs nt Tt tt \<Rightarrow> unif alg ((nt, Tt) # binders) (incr s' $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s'; (ht, ts) = strip_comb t' in
          if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (Var F Fty, Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env binders F Fty is js
                else flexflex2 env binders F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env binders F Fty is t'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env binders F Fty is s'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg binders s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg binders s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB binders i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg binders s t env) ps env}
            | _ \<Rightarrow> rigid_clash binders hs ht))
    }"

definition unify :: "algebra \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> env M" where
  "unify alg s t env = unif alg [] s t env"


subsection \<open>Matching\<close>

type_synonym match_env = "tyenv \<times> tenv"

definition typ_match_m :: "algebra \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> tyenv \<Rightarrow> tyenv M" where
  "typ_match_m alg T U tye =
    handle (typ_match alg T U tye) (\<lambda>e. case e of Type_Match \<Rightarrow> raise Match | _ \<Rightarrow> raise e)"

text \<open>
  First-order matching (\<open>Pattern.first_order_match\<close>): the object is \<open>\<eta>\<close>-contracted on the
  fly by \<open>\<eta>\<close>-expanding the pattern; outside abstractions, \<open>?x\<close> may match terms with loose
  bound variables.
\<close>

partial_function (option) fo_mtch :: "algebra \<Rightarrow> bool \<Rightarrow> match_env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> match_env M" where
  "fo_mtch alg inAbs instsp pat obj =
    (let (tyinsts, insts) = instsp in
    if is_Var pat then
      (case pat of
        Var ixn T \<Rightarrow>
          if inAbs \<and> is_open obj then raise Match
          else do {
            r \<leftarrow> lookup1 insts ixn T;
            case r of
              None \<Rightarrow> do {
                tT \<leftarrow> fastype_of obj;
                tyinsts' \<leftarrow> typ_match_m alg T tT tyinsts;
                insts' \<leftarrow> update_new (ixn, (T, obj)) insts;
                return (tyinsts', insts')}
            | Some u \<Rightarrow> if aeconv obj u then return instsp else raise Match}
      | _ \<Rightarrow> raise (Failure (STR ''fo_mtch'')))
    else
      (case (pat, obj) of
        (Free a T, Free b U) \<Rightarrow>
          if a = b then do {tyinsts' \<leftarrow> typ_match_m alg T U tyinsts; return (tyinsts', insts)}
          else raise Match
      | (Const a T, Const b U) \<Rightarrow>
          if a = b then do {tyinsts' \<leftarrow> typ_match_m alg T U tyinsts; return (tyinsts', insts)}
          else raise Match
      | (Bound i, Bound j) \<Rightarrow> if i = j then return instsp else raise Match
      | (Abs _ T t, Abs _ U u) \<Rightarrow> do {
          tyinsts' \<leftarrow> typ_match_m alg T U tyinsts;
          fo_mtch alg True (tyinsts', insts) t u}
      | (f $ t, g $ u) \<Rightarrow> do {instsp' \<leftarrow> fo_mtch alg inAbs instsp f g; fo_mtch alg inAbs instsp' t u}
      | (_, Abs _ U u) \<Rightarrow> fo_mtch alg True instsp (incr pat $ Bound 0) u
      | _ \<Rightarrow> raise Match))"

definition first_order_match :: "algebra \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> match_env \<Rightarrow> match_env M" where
  "first_order_match alg pat obj env = fo_mtch alg False env pat obj"

text \<open>Matching of higher-order patterns.\<close>

definition match_bind ::
  "tenv \<Rightarrow> binders \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> integer list \<Rightarrow> pterm \<Rightarrow> tenv M" where
  "match_bind itms binders ixn T is t =
    (let js = loose_bnos t in
      if is = [] then
        (if js = [] then update_new (ixn, (T, t)) itms else raise Match)
      else if subset js is then do {
        t' \<leftarrow> (if downto0 is (ilength binders - 1) then return t else mapbnd (idx is) 0 t);
        u \<leftarrow> mkabs binders is t';
        update_new (ixn, (T, u)) itms}
      else raise Match)"

text \<open>\<open>mtch\<close> together with \<open>cases\<close> (mutually recursive in the ML code).\<close>

partial_function (option) mtch :: "algebra \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> match_env \<Rightarrow> match_env M" where
  "mtch alg binders pat obj env =
    (let (iTs, itms) = env in
    if is_Abs pat then
      (case pat of
        Abs ns Ts ts \<Rightarrow>
          if is_Abs obj then
            (case obj of
              Abs nt Tt tt \<Rightarrow> mtch alg ((nt, Tt) # binders) ts tt env
            | _ \<Rightarrow> raise (Failure (STR ''mtch'')))
          else do {Tt \<leftarrow> subst_type iTs Ts; mtch alg ((ns, Tt) # binders) ts (incr obj $ Bound 0) env}
      | _ \<Rightarrow> raise (Failure (STR ''mtch'')))
    else if is_Abs obj then
      (case obj of
        Abs nt Tt tt \<Rightarrow> mtch alg ((nt, Tt) # binders) (incr pat $ Bound 0) tt env
      | _ \<Rightarrow> raise (Failure (STR ''mtch'')))
    else
      (let (ph, pargs) = strip_comb pat in
        if is_Var ph then
          (case ph of
            Var ixn T \<Rightarrow> do {
              is \<leftarrow> ints_of pargs;
              r \<leftarrow> lookup1 itms ixn T;
              case r of
                None \<Rightarrow> do {itms' \<leftarrow> match_bind itms binders ixn T is obj; return (iTs, itms')}
              | Some u \<Rightarrow> do {u' \<leftarrow> red u is []; if aeconv obj u' then return env else raise Match}}
          | _ \<Rightarrow> raise (Failure (STR ''mtch'')))
        else
          (let (oh, oargs) = strip_comb obj in
            case (ph, oh) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise Match
                else do {iTs' \<leftarrow> typ_match_m alg Ta Tb iTs;
                  handle
                    (do {ps \<leftarrow> zip_eq pargs oargs;
                         foldM (\<lambda>(p, q) e. mtch alg binders p q e) ps (iTs', itms)})
                    (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise Match
                else do {iTs' \<leftarrow> typ_match_m alg Ta Tb iTs;
                  handle
                    (do {ps \<leftarrow> zip_eq pargs oargs;
                         foldM (\<lambda>(p, q) e. mtch alg binders p q e) ps (iTs', itms)})
                    (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)}
            | (Bound i, Bound j) \<Rightarrow> if i \<noteq> j then raise Match else
                  handle
                    (do {ps \<leftarrow> zip_eq pargs oargs;
                         foldM (\<lambda>(p, q) e. mtch alg binders p q e) ps (iTs, itms)})
                    (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)
            | (Abs _ _ _, _) \<Rightarrow> raise Pattern
            | (_, Abs _ _ _) \<Rightarrow> raise Pattern
            | _ \<Rightarrow> raise Match)))"

definition match :: "algebra \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> match_env \<Rightarrow> match_env M" where
  "match alg pat obj envir =
    do {
      pT \<leftarrow> fastype_of pat;
      oT \<leftarrow> fastype_of obj;
      iTs \<leftarrow> typ_match_m alg pT oT (fst envir);
      let envir' = (iTs, snd envir);
      handle (mtch alg [] pat obj envir')
        (\<lambda>e. case e of Pattern \<Rightarrow> first_order_match alg pat obj envir' | _ \<Rightarrow> raise e)
    }"


subsection \<open>Patterns\<close>

fun has_duplicates_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "has_duplicates_by eq [] = False"
| "has_duplicates_by eq (x # xs) = (list_ex (\<lambda>y. eq x y) xs \<or> has_duplicates_by eq xs)"

lemma strip_comb_acc_size:
  "strip_comb_acc t ts = (h, us) \<Longrightarrow> u \<in> set us \<Longrightarrow> u \<in> set ts \<or> size u < size t"
  by (induction t ts rule: strip_comb_acc.induct) fastforce+

function pattern :: "pterm \<Rightarrow> bool" where
  "pattern t =
    (case t of
      Abs _ _ u \<Rightarrow> pattern u
    | _ \<Rightarrow>
        (let (head, args) = strip_comb t in
          if is_Var head then list_all is_Bound args \<and> \<not> has_duplicates_by aconv_term args
          else list_all (\<lambda>u. pattern u) args))"
  by auto
termination
  by (relation "measure size") (auto simp: strip_comb_def dest!: strip_comb_acc_size[OF sym])

end
