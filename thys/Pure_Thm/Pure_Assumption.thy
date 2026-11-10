section \<open>Proof by assumption and flex-flex pairs: \<open>assumption\<close>, \<open>eq_assumption\<close>, \<open>flexflex_rule\<close>\<close>

theory Pure_Assumption
  imports Pure_ZTerm
begin

text \<open>
  Literal models of \<open>Thm.assumption\<close>, \<open>Thm.eq_assumption\<close> and \<open>Thm.flexflex_rule\<close> of
  \<^file>\<open>~~/src/Pure/thm.ML\<close>. As for \<^const>\<open>bicompose_aux\<close>, the models cover the logical part of a
  theorem (\<^typ>\<open>thm_rep\<close>); its derivation, hypotheses, sort hypotheses, constraints and
  certificate are left to the ML wrapper. The proofs of the new theorems are built by the
  models of \<open>Proofterm.assumption_proof\<close>, \<open>ZTerm.assumption_proof\<close> and the normalisation of
  proofs.
\<close>


subsection \<open>Maximal indices\<close>

text \<open>\<open>Term.maxidx_typ\<close>, \<open>Term.maxidx_term\<close>, \<open>Term.maxidx_of_term\<close> and \<open>Thm.maxidx_tpairs\<close>.\<close>

fun maxidx_typ :: "ptyp \<Rightarrow> integer \<Rightarrow> integer" where
  "maxidx_typ (TVar (_, j) _) i = max i j"
| "maxidx_typ (Type _ Ts) i = fold maxidx_typ Ts i"
| "maxidx_typ (TFree _ _) i = i"

fun maxidx_term :: "pterm \<Rightarrow> integer \<Rightarrow> integer" where
  "maxidx_term (Var (_, j) T) i = maxidx_typ T (max i j)"
| "maxidx_term (Const _ T) i = maxidx_typ T i"
| "maxidx_term (Free _ T) i = maxidx_typ T i"
| "maxidx_term (Bound _) i = i"
| "maxidx_term (Abs _ T t) i = maxidx_term t (maxidx_typ T i)"
| "maxidx_term (t $ u) i = maxidx_term u (maxidx_term t i)"

definition maxidx_of_term :: "pterm \<Rightarrow> integer" where
  "maxidx_of_term t = maxidx_term t (-1)"

definition maxidx_tpairs :: "(pterm \<times> pterm) list \<Rightarrow> integer \<Rightarrow> integer" where
  "maxidx_tpairs tpairs = fold (\<lambda>(t, u) i. maxidx_term u (maxidx_term t i)) tpairs"


subsection \<open>Proof by assumption\<close>

text \<open>
  The data of a call of \<open>assumption i state\<close> that the closures of its result sequence refer
  to: the maximal index of the proof state, its flex-flex pairs, the subgoals \<open>Bs\<close> before
  subgoal \<open>i\<close>, the subgoal \<open>Bi\<close>, the rest \<open>C\<close> (\<open>dest_state\<close>), and the parameters and the
  conclusion of \<open>Bi\<close> (\<open>Logic.assum_problems (~1, Bi)\<close>).
\<close>

datatype actx = ACtx
  (ac_maxidx: integer) (ac_tpairs: "(pterm \<times> pterm) list") (ac_Bs: "pterm list") (ac_Bi: pterm)
  (ac_C: pterm) (ac_params: binders) (ac_concl: pterm)

text \<open>
  A result: the environment, the number \<open>n\<close> of the assumption (for the proof term), and the
  new theorem.
\<close>

datatype ares = ARes (ar_env: env) (ar_n: integer) (ar_thm: thm_rep)

text \<open>
  The closures of the result sequence: \<open>AQ_Try\<close> is \<open>addprfs asms n\<close>; \<open>AQ_Map\<close> is
  \<open>Seq.mapp (newth n) us (addprfs asms m)\<close>, the unifiers \<open>us\<close> for assumption \<open>n\<close> followed by
  the remaining assumptions.
\<close>

datatype 'u aseq =
  AQ_Try actx "pterm list" integer
| AQ_Map actx integer 'u "pterm list" integer

text \<open>The data of the call, which the proofs of the results refer to.\<close>

fun aseq_ctx :: "'u aseq \<Rightarrow> actx" where
  "aseq_ctx (AQ_Try ctx _ _) = ctx"
| "aseq_ctx (AQ_Map ctx _ _ _ _) = ctx"

text \<open>
  \<open>newth n (env, tpairs)\<close>: the proof state without subgoal \<open>i\<close>, instantiated by the unifier,
  with its flex-flex pairs.
\<close>

definition newth :: "actx \<Rightarrow> integer \<Rightarrow> env \<times> (pterm \<times> pterm) list \<Rightarrow> ares T" where
  "newth ctx n et =
    (case et of (env, tpairs) \<Rightarrow>
      if env_is_empty env then
        returnW (ARes env n \<lparr>th_maxidx = maxidx env, th_tpairs = tpairs,
          th_prop = list_implies (ac_Bs ctx) (ac_C ctx)\<rparr>)
      else liftMT (do {
        tps \<leftarrow> mapM (norm_tpair env) tpairs;
        P \<leftarrow> norm_term env (list_implies (ac_Bs ctx) (ac_C ctx));
        return (ARes env n \<lparr>th_maxidx = maxidx env, th_tpairs = tps, th_prop = P\<rparr>)}))"

text \<open>
  \<open>apull\<close> evaluates the closures of the result sequence, as \<open>Seq.pull\<close>: for each
  assumption that passes the quick test, the unifiers of the closed assumption and the closed
  conclusion, together with the flex-flex pairs of the proof state.
\<close>

partial_function (option) apull :: "'u bops \<Rightarrow> 'u aseq \<Rightarrow> (ares \<times> 'u aseq) option T" where
  "apull ops s =
    (case s of
      AQ_Try ctx [] n \<Rightarrow> returnW None
    | AQ_Try ctx (asm # rest) n \<Rightarrow>
        if could_unify asm (ac_concl ctx) then do {
          us \<leftarrow> bo_unifiers ops (empty_env (ac_maxidx ctx))
            ((rlist_abs (ac_params ctx) asm, rlist_abs (ac_params ctx) (ac_concl ctx)) # ac_tpairs ctx);
          apull ops (AQ_Map ctx n us rest (n + 1))}
        else apull ops (AQ_Try ctx rest (n + 1))
    | AQ_Map ctx n us rest m \<Rightarrow> do {
        r \<leftarrow> bo_pull ops us;
        case r of
          None \<Rightarrow> apull ops (AQ_Try ctx rest m)
        | Some (et, us') \<Rightarrow> do {th \<leftarrow> newth ctx n et; returnW (Some (th, AQ_Map ctx n us' rest m))}})"

text \<open>
  \<open>assumption i state\<close>: solve subgoal \<open>i\<close> of the proof state by each of its assumptions in
  turn. Subgoal \<open>i\<close> is destructed at once; everything else is delayed until the sequence is
  pulled.
\<close>

definition assumption :: "integer \<Rightarrow> thm_rep \<Rightarrow> 'u aseq T" where
  "assumption i state = do {
    (tpairs, Bs, Bi, C) \<leftarrow> dest_state state i;
    (case assum_problems (-1) Bi of (params, asms, concl) \<Rightarrow>
      returnW (AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1))}"


subsection \<open>Proof by an assumption that is equivalent to the conclusion\<close>

text \<open>\<open>find_index\<close>, from \<open>0\<close>, with \<^const>\<open>None\<close> for \<open>~1\<close>.\<close>

fun find_index_from :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> integer \<Rightarrow> integer option" where
  "find_index_from P [] k = None"
| "find_index_from P (x # xs) k = (if P x then Some k else find_index_from P xs (k + 1))"

text \<open>
  \<open>eq_assumption i state\<close>: solve subgoal \<open>i\<close> by the first assumption that is
  \<open>\<alpha>\<close>/\<open>\<eta>\<close>-equivalent to its conclusion (\<^const>\<open>aeconv\<close>), without unification; also the
  number of the assumption (for the proof term).
\<close>

definition eq_assumption :: "integer \<Rightarrow> thm_rep \<Rightarrow> (integer \<times> thm_rep) T" where
  "eq_assumption i state = do {
    (tpairs, Bs, Bi, C) \<leftarrow> dest_state state i;
    (case assum_problems (-1) Bi of (_, asms, concl) \<Rightarrow>
      (case find_index_from (\<lambda>asm. aeconv asm concl) asms 0 of
        None \<Rightarrow> raiseW (THM (STR ''eq_assumption'') 0 State)
      | Some n \<Rightarrow> returnW (n + 1,
          \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>)))}"


subsection \<open>Flex-flex pairs\<close>

text \<open>
  The result sequence of \<open>flexflex_rule\<close>: the unifiers of the flex-flex pairs, mapped to the new
  theorems. The model is parameterised by the smashing of the flex-flex pairs of a unifier
  (\<open>Unify.smash_flexflex\<close>, which \<open>Unify.smash_unifiers\<close> applies).
\<close>

datatype 'u fseq = FQ 'u

text \<open>
  The new theorem of an environment: the theorem itself if the environment is empty and it has
  no trivial flex-flex pairs (\<open>t \<equiv> t\<close> up to \<open>\<alpha>\<close>); otherwise its normalized flex-flex pairs,
  without the trivial ones, and its normalized proposition. With the fix of
  \<open>patches/11-thm-flexflex-trivial.patch\<close>: \<open>Thm.flexflex_rule\<close> keeps the trivial pairs of the
  theorem if the environment is empty.
\<close>

definition fnewth :: "thm_rep \<Rightarrow> env \<Rightarrow> thm_rep M" where
  "fnewth th env =
    (if env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th). aconv_term t u) then return th
     else do {
       tps \<leftarrow> mapM (norm_tpair env) (th_tpairs th);
       let tps' = filter (\<lambda>(t, u). \<not> aconv_term t u) tps;
       P \<leftarrow> norm_term env (th_prop th);
       return \<lparr>th_maxidx = maxidx_tpairs tps' (maxidx_of_term P), th_tpairs = tps', th_prop = P\<rparr>})"

text \<open>\<open>fpull\<close>: \<open>Seq.pull\<close> on the result sequence.\<close>

definition fpull :: "'u bops \<Rightarrow> (env \<times> (pterm \<times> pterm) list \<Rightarrow> env T) \<Rightarrow> thm_rep \<Rightarrow>
    'u fseq \<Rightarrow> ((env \<times> thm_rep) \<times> 'u fseq) option T" where
  "fpull ops smash th s =
    (case s of FQ us \<Rightarrow> do {
      r \<leftarrow> bo_pull ops us;
      case r of
        None \<Rightarrow> returnW None
      | Some (et, us') \<Rightarrow> do {
          env \<leftarrow> smash et;
          th' \<leftarrow> liftMT (fnewth th env);
          returnW (Some ((env, th'), FQ us'))}})"

text \<open>
  \<open>flexflex_rule th\<close>: the instances of the theorem by the unifiers of its flex-flex pairs
  without flex-flex pairs left (\<open>Unify.smash_unifiers\<close>); the unifiers are computed lazily,
  but the first step of \<open>Unify.unifiers\<close> (pattern unification) is not.
\<close>

definition flexflex_rule :: "'u bops \<Rightarrow> thm_rep \<Rightarrow> 'u fseq T" where
  "flexflex_rule ops th = do {
    us \<leftarrow> bo_unifiers ops (empty_env (th_maxidx th)) (th_tpairs th);
    returnW (FQ us)}"


subsection \<open>Proofs\<close>

text \<open>
  \<open>Proofterm.assumption_proof Bs Bi n prf\<close>: the proof of \<open>\<lbrakk>Bs; C\<rbrakk>\<close> from the proof \<open>prf\<close> of the
  proof state, whose subgoal \<open>Bi\<close> is proved by its assumption \<open>n\<close>.
\<close>

definition assumption_proof :: "pterm list \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf" where
  "assumption_proof Bs Bi n prf =
    mk_AbsP Bs (proof_combP prf
      (map PBound (downto (integer_of_nat (length Bs) - 1) 0) @ [mk_asm_prf Bi n (-1)]))"

text \<open>
  \<open>ZTerm.assumption_proof thy envir Bs Bi n visible prf\<close>: the tight proof, with the terms
  normalised in the environment and the proof normalised for the visible propositions. With the
  fix of \<open>patches/19-zterm-assumption.patch\<close>, the proof of the subgoal strips as many
  assumptions from the normalised subgoal as \<^const>\<open>assum_problems\<close> from the subgoal before
  normalisation.
\<close>

definition zassumption_proof :: "ztypargs \<Rightarrow> env \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow>
    zproof \<Rightarrow> zproof Z" where
  "zassumption_proof ta env Bs Bi n visible prf = do {
    let normt = (\<lambda>t. do {t' \<leftarrow> zterm_of ta t; znorm_term ta env t'});
    Ns \<leftarrow> mapM normt Bs;
    N \<leftarrow> normt Bi;
    znorm_proof ta env visible
      (ZAbsps Ns (ZAppps prf
        (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @ [zmk_asm_prf N n (zasm_count (-1) Bi)])))}"

text \<open>
  The classic and the tight proofs of a result of \<^const>\<open>assumption\<close>. With the fix of
  \<open>patches/10-thm-assumption.patch\<close>, the classic proof of the subgoal follows the subgoal
  before normalisation, whose assumptions the unifier considered.
\<close>

definition ares_proof :: "actx \<Rightarrow> ares \<Rightarrow> prf \<Rightarrow> prf P" where
  "ares_proof ctx x prf =
    (case x of ARes env n _ \<Rightarrow> do {
      Ns \<leftarrow> liftMP (mapM (norm_term env) (ac_Bs ctx));
      let p = assumption_proof Ns (ac_Bi ctx) n prf;
      if env_is_empty env then returnW p else norm_proof_remove_types env p})"

definition ares_zproof :: "ztypargs \<Rightarrow> thm_rep \<Rightarrow> actx \<Rightarrow> ares \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "ares_zproof ta state ctx x prf =
    (case x of ARes env n _ \<Rightarrow> do {
      P \<leftarrow> liftMZ (full_prop_of (th_tpairs state) (th_prop state));
      zassumption_proof ta env (ac_Bs ctx) (ac_Bi ctx) n [P] prf})"

text \<open>
  The proofs of the result of \<^const>\<open>eq_assumption\<close>: subgoal \<open>i\<close>, with the other subgoals
  \<open>Bs\<close>, is proved by assumption \<open>n\<close>, without an environment.
\<close>

definition eq_assumption_zproof :: "ztypargs \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "eq_assumption_zproof ta Bs Bi n prf = zassumption_proof ta (empty_env (-1)) Bs Bi n [] prf"

text \<open>The proofs of a result of \<^const>\<open>flexflex_rule\<close> with a non-empty environment.\<close>

definition flexflex_zproof :: "ztypargs \<Rightarrow> thm_rep \<Rightarrow> env \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "flexflex_zproof ta th env prf = do {
    P \<leftarrow> liftMZ (full_prop_of (th_tpairs th) (th_prop th));
    znorm_proof ta env [P] prf}"

end
