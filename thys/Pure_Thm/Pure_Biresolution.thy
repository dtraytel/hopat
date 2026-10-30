section \<open>Biresolution: \<open>biresolution\<close>\<close>

theory Pure_Biresolution
  imports Pure_Bicompose
begin

text \<open>
  A literal model of \<open>Thm.biresolution\<close> of \<^file>\<open>~~/src/Pure/thm.ML\<close>, with the functions of
  \<^file>\<open>~~/src/Pure/logic.ML\<close> that it uses: it resolves subgoal \<open>i\<close> of a proof state with a list
  of rules, each lifted over the subgoal (\<open>Thm.lift_rule\<close>) and composed with the proof state by
  \<^const>\<open>bicompose_aux\<close>. As for \<^const>\<open>bicompose_aux\<close>, the model covers the logical part of a
  theorem; its derivation, hypotheses, sort hypotheses, constraints and certificate are left to
  the ML wrapper.
\<close>


subsection \<open>Theorems\<close>

text \<open>
  The logical content of a theorem (of the record of the abstract type \<open>thm\<close>): its maximal
  index, its flex-flex pairs and its proposition.
\<close>

record thm_rep =
  th_maxidx :: integer
  th_tpairs :: "(pterm \<times> pterm) list"
  th_prop :: pterm

definition pthm_of :: "thm_rep \<Rightarrow> pthm" where
  "pthm_of th = (th_maxidx th, th_tpairs th, th_prop th)"


subsection \<open>Functions of \<open>logic.ML\<close>\<close>

text \<open>\<open>Logic.strip_imp_prems\<close>, \<open>Logic.strip_imp_concl\<close> and \<open>Logic.nth_prem\<close>.\<close>

function strip_imp_prems :: "pterm \<Rightarrow> pterm list" where
  "strip_imp_prems t = (case dest_imp t of Some (A, B) \<Rightarrow> A # strip_imp_prems B | None \<Rightarrow> [])"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare strip_imp_prems.simps[simp del]

function strip_imp_concl :: "pterm \<Rightarrow> pterm" where
  "strip_imp_concl t = (case dest_imp t of Some (_, B) \<Rightarrow> strip_imp_concl B | None \<Rightarrow> t)"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare strip_imp_concl.simps[simp del]

function nth_prem :: "integer \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "nth_prem i t =
    (case dest_imp t of
      Some (A, B) \<Rightarrow> if i = 1 then return A else nth_prem (i - 1) B
    | None \<Rightarrow> raise (Term_Error (STR ''nth_prem'') [t]))"
  by auto
termination by (relation "measure (\<lambda>(_, t). size t)") (auto dest: dest_size)

declare nth_prem.simps[simp del]

text \<open>\<open>Logic.strip_assums_hyp\<close> and \<open>Logic.strip_assums_concl\<close>: the assumptions and the conclusion
  of a subgoal.\<close>

function strip_assums_hyp_aux :: "pterm list \<Rightarrow> pterm \<Rightarrow> pterm list" where
  "strip_assums_hyp_aux Hs t =
    (case dest_imp t of
      Some (H, B) \<Rightarrow> strip_assums_hyp_aux (H # Hs) B
    | None \<Rightarrow>
      (case dest_all t of
        Some (_, _, b) \<Rightarrow> strip_assums_hyp_aux (map (incr_boundvars 1) Hs) b
      | None \<Rightarrow> rev Hs))"
  by auto
termination by (relation "measure (\<lambda>(_, t). size t)") (auto dest: dest_size)

declare strip_assums_hyp_aux.simps[simp del]

definition strip_assums_hyp :: "pterm \<Rightarrow> pterm list" where
  "strip_assums_hyp B = strip_assums_hyp_aux [] B"

function strip_assums_concl :: "pterm \<Rightarrow> pterm" where
  "strip_assums_concl t =
    (case dest_imp t of
      Some (_, B) \<Rightarrow> strip_assums_concl B
    | None \<Rightarrow> (case dest_all t of Some (_, _, b) \<Rightarrow> strip_assums_concl b | None \<Rightarrow> t))"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare strip_assums_concl.simps[simp del]

text \<open>
  \<open>Logic.incr_tvar\<close> and \<open>Logic.incr_indexes (Ts, inc)\<close>: increment the indices of the schematic
  variables by \<open>inc\<close> and lift them over the types \<open>Ts\<close> of bound variables; at abstraction level
  \<open>lev\<close>, \<open>?x\<close> becomes \<open>?x (Bound (lev + n - 1)) \<dots> (Bound lev)\<close> with \<open>n = length Ts\<close>.
\<close>

fun incr_tvar :: "integer \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "incr_tvar inc (Type a Ts) = Type a (map (incr_tvar inc) Ts)"
| "incr_tvar inc (TFree a S) = TFree a S"
| "incr_tvar inc (TVar (a, i) S) = TVar (a, i + inc) S"

fun incr_idx :: "ptyp list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "incr_idx Ts inc lev (Var (x, i) T) =
    combound (Var (x, i + inc) (foldr fun_type Ts (incr_tvar inc T))) lev (length Ts)"
| "incr_idx Ts inc lev (Free x T) = Free x (incr_tvar inc T)"
| "incr_idx Ts inc lev (Abs x T t) = Abs x (incr_tvar inc T) (incr_idx Ts inc (lev + 1) t)"
| "incr_idx Ts inc lev (t $ u) = incr_idx Ts inc lev t $ incr_idx Ts inc lev u"
| "incr_idx Ts inc lev (Const c T) = Const c (incr_tvar inc T)"
| "incr_idx Ts inc lev (Bound i) = Bound i"

definition incr_indexes :: "ptyp list \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "incr_indexes Ts inc t = (if Ts = [] \<and> inc = 0 then t else incr_idx Ts inc 0 t)"

text \<open>
  \<open>Logic.lift_abs inc gprop t\<close> and \<open>Logic.lift_all inc gprop t\<close>: lift the term \<open>t\<close> over the
  parameters of the subgoal \<open>gprop\<close>, and the proposition \<open>t\<close> over its parameters and
  assumptions.
\<close>

fun lift_abs_aux :: "integer \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "lift_abs_aux inc Ts (Const c U $ H $ B) t =
    (if c = STR ''Pure.imp'' then lift_abs_aux inc Ts B t else incr_indexes (rev Ts) inc t)"
| "lift_abs_aux inc Ts (Const c U $ Abs a T B) t =
    (if c = STR ''Pure.all'' then Abs a T (lift_abs_aux inc (T # Ts) B t) else incr_indexes (rev Ts) inc t)"
| "lift_abs_aux inc Ts _ t = incr_indexes (rev Ts) inc t"

definition lift_abs :: "integer \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "lift_abs inc gprop t = lift_abs_aux inc [] gprop t"

fun lift_all_aux :: "integer \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "lift_all_aux inc Ts (Const c U $ H $ B) t =
    (if c = STR ''Pure.imp'' then Const c U $ H $ lift_all_aux inc Ts B t
     else incr_indexes (rev Ts) inc t)"
| "lift_all_aux inc Ts (Const c U $ Abs a T B) t =
    (if c = STR ''Pure.all'' then Const c U $ Abs a T (lift_all_aux inc (T # Ts) B t)
     else incr_indexes (rev Ts) inc t)"
| "lift_all_aux inc Ts _ t = incr_indexes (rev Ts) inc t"

definition lift_all :: "integer \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "lift_all inc gprop t = lift_all_aux inc [] gprop t"


subsection \<open>Functions of \<open>thm.ML\<close>\<close>

definition prems_of :: "thm_rep \<Rightarrow> pterm list" where
  "prems_of th = strip_imp_prems (th_prop th)"

definition concl_of :: "thm_rep \<Rightarrow> pterm" where
  "concl_of th = strip_imp_concl (th_prop th)"

definition nprems_of :: "thm_rep \<Rightarrow> integer" where
  "nprems_of th = count_prems (th_prop th)"

text \<open>
  \<open>Thm.cprem_of th i\<close>, of which the model takes the term: the maximal index of the certified term
  is that of the theorem.
\<close>

definition cprem_of :: "thm_rep \<Rightarrow> integer \<Rightarrow> pterm T" where
  "cprem_of th i =
    handleT (liftMT (nth_prem i (th_prop th)))
      (\<lambda>e. case e of
        UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''cprem_of'') i State)
      | _ \<Rightarrow> raiseT e)"

text \<open>\<open>Thm.dest_state (state, i)\<close>: the flex-flex pairs, the other subgoals, subgoal \<open>i\<close> and the
  conclusion of the proof state.\<close>

definition dest_state :: "thm_rep \<Rightarrow> integer \<Rightarrow> ((pterm \<times> pterm) list \<times> pterm list \<times> pterm \<times> pterm) T" where
  "dest_state state i =
    handleT
      (do {
        (rBs, C) \<leftarrow> liftMT (strip_prems i [] (th_prop state));
        (case rBs of
          B # rBs' \<Rightarrow> returnT (th_tpairs state, rev rBs', B, C)
        | [] \<Rightarrow> raiseT (THM (STR ''dest_state'') i State))})
      (\<lambda>e. case e of
        UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''dest_state'') i State)
      | _ \<Rightarrow> raiseT e)"

text \<open>
  \<open>Thm.lift_rule goal orule\<close>: lift the rule over the parameters and assumptions of the subgoal
  \<open>goal\<close>, of which the model takes the term and the maximal index \<open>gmax\<close>, and increment the
  indices of its schematic variables above \<open>gmax\<close>. Since the goal is a premise of a theorem
  (\<open>Thm.cprem_of\<close>), its type is \<open>prop\<close>, and the check of \<open>lift_rule\<close> for that never fails.
\<close>

definition lift_rule :: "pterm \<Rightarrow> integer \<Rightarrow> thm_rep \<Rightarrow> thm_rep" where
  "lift_rule gprop gmax orule =
    (let
      inc = gmax + 1;
      As = strip_imp_prems (th_prop orule);
      B = strip_imp_concl (th_prop orule)
    in
      \<lparr>th_maxidx = th_maxidx orule + inc,
       th_tpairs = map (\<lambda>(t, u). (lift_abs inc gprop t, lift_abs inc gprop u)) (th_tpairs orule),
       th_prop = list_implies (map (lift_all inc gprop) As) (lift_all inc gprop B)\<rparr>)"

text \<open>
  \<open>Thm.could_bires (Hs, B, eres_flg, rule)\<close>: a quick test whether the rule is resolvable with the
  subgoal with assumptions \<open>Hs\<close> and conclusion \<open>B\<close>; for elim-resolution, its first premise must
  also be unifiable with an assumption.
\<close>

fun could_reshyp :: "pterm list \<Rightarrow> pterm list \<Rightarrow> bool" where
  "could_reshyp Hs (A1 # _) = list_ex (\<lambda>H. could_unify A1 H) Hs"
| "could_reshyp Hs [] = False"

definition could_bires :: "pterm list \<Rightarrow> pterm \<Rightarrow> bool \<Rightarrow> thm_rep \<Rightarrow> bool" where
  "could_bires Hs B eres_flg rule \<longleftrightarrow>
    could_unify (concl_of rule) B \<and> (\<not> eres_flg \<or> could_reshyp Hs (prems_of rule))"


subsection \<open>Biresolution\<close>

text \<open>
  The data of a call that the closures of its result sequence refer to: the flags
  \<open>Pattern.unify_trace_failure\<close> (which disables the quick test) and \<open>match\<close>, the proof state,
  the result \<open>(stpairs, Bs, Bi, C)\<close> of \<open>dest_state\<close>, the subgoal \<open>goal\<close> (\<open>Thm.cprem_of\<close>), and
  the conclusion \<open>B\<close> and the assumptions \<open>Hs\<close> of the subgoal.
\<close>

datatype brctx = BRCtx
  (brc_trace: bool) (brc_match: bool) (brc_state: thm_rep)
  (brc_dst: "(pterm \<times> pterm) list \<times> pterm list \<times> pterm \<times> pterm") (brc_goal: pterm)
  (brc_B: pterm) (brc_Hs: "pterm list")

text \<open>
  The result sequence \<open>Seq.flat (res brules)\<close> of \<open>biresolution\<close>, for rules of type \<open>'r\<close> with
  logical content \<open>rep\<close>: \<open>RQ_Make\<close> is the closure of \<open>res\<close> for a rule that passed the quick
  test, followed by the remaining rules; \<open>RQ_App\<close> is the sequence \<open>Seq.append xq (Seq.flat xqq)\<close>
  of the results \<open>xq\<close> of a rule followed by those of the remaining rules \<open>xqq\<close>. A result comes
  with the rule that it was obtained with.
\<close>

datatype ('u, 'r) rseq =
  RQ_Empty
| RQ_Make brctx "bool \<times> 'r" "(bool \<times> 'r) list"
| RQ_App "bool \<times> 'r" "'u bseq" "('u, 'r) rseq"

text \<open>\<open>res brules\<close> of \<open>biresolution\<close>: skip the rules that fail the quick test.\<close>

fun res :: "('r \<Rightarrow> thm_rep) \<Rightarrow> brctx \<Rightarrow> (bool \<times> 'r) list \<Rightarrow> ('u, 'r) rseq" where
  "res rep ctx [] = RQ_Empty"
| "res rep ctx ((eres_flg, rule) # brules) =
    (if brc_trace ctx \<or> could_bires (brc_Hs ctx) (brc_B ctx) eres_flg (rep rule)
     then RQ_Make ctx (eres_flg, rule) brules
     else res rep ctx brules)"

text \<open>\<open>compose (eres_flg, lift rule, nprems_of rule)\<close> of \<open>biresolution\<close>.\<close>

definition compose :: "'u bops \<Rightarrow> algebra \<Rightarrow> brctx \<Rightarrow> bool \<Rightarrow> thm_rep \<Rightarrow> 'u bseq T" where
  "compose ops alg ctx eres_flg rule =
    bicompose_aux ops alg True (brc_match ctx) True (pthm_of (brc_state ctx)) (brc_dst ctx) True
      eres_flg (pthm_of (lift_rule (brc_goal ctx) (th_maxidx (brc_state ctx)) rule)) (nprems_of rule)"

text \<open>
  A step of pulling the result sequence (\<open>Seq.pull\<close>): the closure of \<open>res\<close> composes the rule
  with the proof state and then evaluates \<open>res\<close> for the remaining rules (\<open>RS_Skip\<close>); the
  results of a rule are pulled one by one (\<open>RS_Result\<close>), and then those of the remaining rules.
  The rule whose computation a step evaluates is \<open>brrule\<close>; the ML wrapper raises the
  exceptions of a step with it.
\<close>

datatype ('u, 'r) rstep =
  RS_Done
| RS_Skip "('u, 'r) rseq"
| RS_Result "bres \<times> (bool \<times> 'r)" "('u, 'r) rseq"

fun brstep :: "'u bops \<Rightarrow> algebra \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> ('u, 'r) rseq \<Rightarrow> ('u, 'r) rstep T" where
  "brstep ops alg rep RQ_Empty = returnT RS_Done"
| "brstep ops alg rep (RQ_Make ctx (eres_flg, rule) brules) = do {
    xq \<leftarrow> compose ops alg ctx eres_flg (rep rule);
    returnT (RS_Skip (RQ_App (eres_flg, rule) xq (res rep ctx brules)))}"
| "brstep ops alg rep (RQ_App r xq xqq) = do {
    x \<leftarrow> bpull ops xq;
    (case x of
      None \<Rightarrow> returnT (RS_Skip xqq)
    | Some (th, xq') \<Rightarrow> returnT (RS_Result (th, r) (RQ_App r xq' xqq)))}"

fun brrule :: "('u, 'r) rseq \<Rightarrow> (bool \<times> 'r) option" where
  "brrule RQ_Empty = None"
| "brrule (RQ_Make _ r _) = Some r"
| "brrule (RQ_App r _ _) = Some r"

text \<open>\<open>brpull\<close> evaluates the closures of the result sequence up to the next result.\<close>

partial_function (option) brpull :: "'u bops \<Rightarrow> algebra \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> ('u, 'r) rseq \<Rightarrow>
    ((bres \<times> (bool \<times> 'r)) \<times> ('u, 'r) rseq) option T" where
  "brpull ops alg rep s = do {
    st \<leftarrow> brstep ops alg rep s;
    (case st of
      RS_Done \<Rightarrow> returnT None
    | RS_Skip s' \<Rightarrow> brpull ops alg rep s'
    | RS_Result x s' \<Rightarrow> returnT (Some (x, s')))}"

text \<open>
  \<open>biresolution trace match brules i state\<close>: bi-resolution of a proof state with a list of
  (flag, rule) pairs, putting the rule above: rule/state. Subgoal \<open>i\<close> is destructed and the
  quick test is run for the rules up to the first that passes it; everything else is delayed
  until the sequence is pulled.
\<close>

definition biresolution :: "bool \<Rightarrow> bool \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> (bool \<times> 'r) list \<Rightarrow> integer \<Rightarrow>
    thm_rep \<Rightarrow> ('u, 'r) rseq T" where
  "biresolution trace match_flg rep brules i state = do {
    dst \<leftarrow> dest_state state i;
    goal \<leftarrow> cprem_of state i;
    (case dst of (_, _, Bi, _) \<Rightarrow>
      returnT (res rep (BRCtx trace match_flg state dst goal (strip_assums_concl Bi)
        (strip_assums_hyp Bi)) brules))}"

end
