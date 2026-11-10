section \<open>Unconstraining the Type Variables of a Theorem\<close>

theory Pure_Unconstrain
  imports Pure_Cterm
begin

text \<open>
  A literal model of \<open>Thm.unconstrainT\<close> after \<open>Thm.strip_shyps\<close>: the logical part, the
  classic proof \<open>Proofterm.unconstrain_thm_proof\<close> (a proof box, whose header and body are
  supplied by the parameter \<open>box\<close>) and the tight proof of \<open>ZTerm.add_box_proof
  {unconstrain = true}\<close> with patch \<open>zterm-unconstrain\<close> (a proof box with the name \<open>zn\<close>). The
  contents of the boxes are not part of the theorem; their computation raises no exception for
  the proofs of theorems (after \<open>Thm.strip_shyps\<close>, the type variables of the proofs occur in the
  proposition, the theorem has no hypotheses) and is not modelled. The names of the type
  variables that \<open>Logic.unconstrainT\<close> invents are a parameter \<open>invent\<close>.
\<close>

subsection \<open>Unconstraining a proposition\<close>

text \<open>
  \<open>Logic.unconstrain_context shyps\<close> for the atomic types of a proposition (\<open>Logic.unconstrainT\<close>):
  the present type variables and the extra sorts, which are not the sort of a present type
  variable, get type variables with the invented names, index \<open>0\<close> and their sorts.
\<close>

definition unconstrain_ctx :: "(integer \<Rightarrow> name list) \<Rightarrow> psort list \<Rightarrow> pterm \<Rightarrow>
    ((ptyp \<times> ptyp) list \<times> (psort \<times> ptyp) list) M" where
  "unconstrain_ctx invent shyps prop = do {
    present \<leftarrow> mapM (\<lambda>T. do {S \<leftarrow> sort_of_atyp T; return (T, S)}) (term_atyps prop);
    let extra = fold (ord_remove sort_ord \<circ> snd) present shyps;
    let names = invent (integer_of_nat (length present + length extra));
    let present_map = map2 (\<lambda>(T, S) a. (T, TVar (a, 0) S)) present (take (length present) names);
    let constraints_map = map (\<lambda>(_, V). ((case V of TVar _ S \<Rightarrow> S | _ \<Rightarrow> []), V)) present_map @
      map2 (\<lambda>S a. (S, TVar (a, 0) S)) extra (drop (length present) names);
    return (present_map, constraints_map)}"

text \<open>The premises \<open>OFCLASS\<close> of the type variables (\<open>#constraints\<close>):\<close>

definition ctx_constraints :: "(psort \<times> ptyp) list \<Rightarrow> pterm list" where
  "ctx_constraints constraints_map =
    concat (map (\<lambda>(_, V). case V of TVar ai S \<Rightarrow> map (\<lambda>c. mk_of_class (TVar ai []) c) S | _ \<Rightarrow> []) constraints_map)"

text \<open>\<open>#typ_operation ucontext {strip_sorts = true}\<close> on terms:\<close>

definition unconstrain_term :: "(ptyp \<times> ptyp) list \<Rightarrow> (psort \<times> ptyp) list \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "unconstrain_term present_map constraints_map = map_typesM (map_atypsM (unconstrain_atyp present_map constraints_map))"

text \<open>\<open>Logic.unconstrainT shyps prop\<close>: the context and the new proposition.\<close>

definition unconstrain_prop :: "(integer \<Rightarrow> name list) \<Rightarrow> psort list \<Rightarrow> pterm \<Rightarrow>
    (((ptyp \<times> ptyp) list \<times> (psort \<times> ptyp) list) \<times> pterm) M" where
  "unconstrain_prop invent shyps prop = do {
    (pm, cm) \<leftarrow> unconstrain_ctx invent shyps prop;
    prop' \<leftarrow> unconstrain_term pm cm prop;
    return ((pm, cm), list_implies (ctx_constraints cm) prop')}"


subsection \<open>The rule\<close>

text \<open>
  \<open>Thm.unconstrainT\<close> after \<open>Thm.strip_shyps\<close>, with the sort hypotheses \<open>shyps\<close> and the
  hypotheses \<open>hyps\<close> of the stripped theorem: no hypotheses, flex-flex pairs and free type
  variables; the sort hypotheses of the result are \<open>[[]]\<close>.
\<close>

definition commas_quote :: "name list \<Rightarrow> String.literal" where
  "commas_quote xs = (case xs of [] \<Rightarrow> STR '''' | x # xs \<Rightarrow> fold (\<lambda>y s. s + STR '', '' + quote_lit y) xs (quote_lit x))"

definition unconstrainT_rep :: "(integer \<Rightarrow> name list) \<Rightarrow> psort list \<Rightarrow> pterm list \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "unconstrainT_rep invent shyps hyps th =
    (if hyps \<noteq> [] then raiseW (THM (STR ''unconstrainT: bad hyps'') 0 State)
     else if th_tpairs th \<noteq> [] then raiseW (THM (STR ''unconstrainT: bad flex-flex constraints'') 0 State)
     else (let tfrees = rev (add_tfree_names (th_prop th) []) in
       if tfrees \<noteq> [] then
         raiseW (THM (STR ''unconstrainT: illegal free type variables '' + commas_quote tfrees) 0 State)
       else liftMT (do {
         args \<leftarrow> prop_args (th_prop th);
         (_, prop') \<leftarrow> unconstrain_prop invent shyps (th_prop th);
         return (mk_rep (maxidx_of_term prop') [] prop')})))"

text \<open>
  The classic proof (\<open>Proofterm.unconstrain_thm_proof\<close>): the box of the new proposition applied
  to the arguments of the proposition (\<open>Proofterm.prop_args\<close>) with unconstrained types.
\<close>

definition unconstrain_thm_proof :: "(pterm \<Rightarrow> thm_header \<times> thm_body) \<Rightarrow> (integer \<Rightarrow> name list) \<Rightarrow>
    psort list \<Rightarrow> pterm \<Rightarrow> prf M" where
  "unconstrain_thm_proof box invent shyps prop = do {
    args \<leftarrow> prop_args prop;
    ((pm, cm), prop1) \<leftarrow> unconstrain_prop invent shyps prop;
    argst \<leftarrow> mapM (\<lambda>a. case a of None \<Rightarrow> return None
      | Some t \<Rightarrow> do {t' \<leftarrow> unconstrain_term pm cm t; return (Some t')}) args;
    return (foldl PAppt (PThm (box prop1)) argst)}"

text \<open>
  The tight proof (\<open>ZTerm.box_proof {unconstrain = true}\<close> with patch \<open>zterm-unconstrain\<close>):
  the box of the new proposition, closed by the premises of the type variables.
\<close>

fun close_zprop :: "zterm list \<Rightarrow> zterm \<Rightarrow> zterm" where
  "close_zprop [] B = B"
| "close_zprop (A # As) B = ZApp (ZApp (ZConst0 STR ''Pure.imp'') A) (close_zprop As B)"

definition zunconstrain_proof :: "ztypargs \<Rightarrow> zthm_name \<Rightarrow> (integer \<Rightarrow> name list) \<Rightarrow> psort list \<Rightarrow>
    pterm \<Rightarrow> zproof Z" where
  "zunconstrain_proof ta zn invent shyps prop = do {
    ((pm, cm), _) \<leftarrow> liftMZ (unconstrain_prop invent shyps prop);
    prems \<leftarrow> mapM (zterm_of ta) (ctx_constraints cm);
    concl' \<leftarrow> liftMZ (unconstrain_term pm cm prop);
    C \<leftarrow> zterm_of ta concl';
    A \<leftarrow> liftOZ (beta_norm_term (close_zprop prems C));
    return (ZConstp (zproof_const (ZThm zn) A))}"

end
