section \<open>The primitive inference rules of \<open>thm.ML\<close>\<close>

theory Pure_Rules
  imports Pure_Assumption
begin

text \<open>
  Literal models of the primitive inference rules of \<^file>\<open>~~/src/Pure/thm.ML\<close>
  (\<open>Thm.assume\<close>, \<open>Thm.implies_intr\<close>, \<open>Thm.implies_elim\<close>, \<open>Thm.forall_intr\<close>,
  \<open>Thm.forall_elim\<close>, \<open>Thm.reflexive\<close>, \<open>Thm.symmetric\<close>, \<open>Thm.transitive\<close>,
  \<open>Thm.beta_conversion\<close>, \<open>Thm.eta_conversion\<close>, \<open>Thm.eta_long_conversion\<close>,
  \<open>Thm.abstract_rule\<close>, \<open>Thm.combination\<close>, \<open>Thm.equal_intr\<close>, \<open>Thm.equal_elim\<close>), of
  \<open>Thm.trivial\<close>, \<open>Thm.weaken\<close>, \<open>Thm.renamed_prop\<close> and \<open>Thm.adjust_maxidx_thm\<close>, and of the
  proofs they build (\<^file>\<open>~~/src/Pure/proofterm.ML\<close>, \<^file>\<open>~~/src/Pure/zterm.ML\<close>). As for
  \<^const>\<open>bicompose_aux\<close>, the models cover the logical part of a theorem (\<^typ>\<open>thm_rep\<close>);
  the hypotheses are an argument where a rule inspects them (the eigenvariable conditions), and
  the hypotheses of the result, the sort hypotheses, the constraints and the certificate are left
  to the ML wrapper. A certified term (\<open>Thm.cterm\<close>) is represented by its term, its type and its
  maximal index.
\<close>


subsection \<open>Certified terms and exceptions\<close>

datatype cterm_rep = CTerm (ct_t: pterm) (ct_T: ptyp) (ct_maxidx: integer)

text \<open>\<open>Thm.adjust_maxidx_cterm\<close>.\<close>

definition adjust_maxidx_cterm :: "integer \<Rightarrow> cterm_rep \<Rightarrow> cterm_rep" where
  "adjust_maxidx_cterm i ct =
    (if ct_maxidx ct = i then ct
     else if ct_maxidx ct < i then CTerm (ct_t ct) (ct_T ct) i
     else CTerm (ct_t ct) (ct_T ct) (max (maxidx_of_term (ct_t ct)) i))"

text \<open>
  The exception \<open>THM (msg, i, ths)\<close> refers to no theorem (\<^const>\<open>No_Thm\<close>), to the theorem
  of a rule with one premise (\<^const>\<open>State\<close>), or to both theorems of a rule with two premises,
  in their order (\<^const>\<open>Orule_State\<close>, with the first premise as the ``rule'').
\<close>

text \<open>The names \<open>'a\<close> and \<open>'b\<close> of type variables.\<close>

definition tvar_a :: String.literal where "tvar_a = String.implode [CHR 0x27, CHR ''a'']"
definition tvar_b :: String.literal where "tvar_b = String.implode [CHR 0x27, CHR ''b'']"

definition quote_lit :: "String.literal \<Rightarrow> String.literal" where
  \<open>quote_lit s = STR ''"'' + s + STR ''"''\<close>


subsection \<open>Functions of \<open>term.ML\<close>, \<open>logic.ML\<close> and \<open>envir.ML\<close>\<close>

text \<open>\<open>Term.exists_subterm\<close> and \<open>Logic.occs\<close>.\<close>

fun exists_subterm :: "(pterm \<Rightarrow> bool) \<Rightarrow> pterm \<Rightarrow> bool" where
  "exists_subterm P (t $ u) = (P (t $ u) \<or> exists_subterm P t \<or> exists_subterm P u)"
| "exists_subterm P (Abs a T t) = (P (Abs a T t) \<or> exists_subterm P t)"
| "exists_subterm P t = P t"

definition occs :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "occs t u = exists_subterm (aconv_term t) u"

text \<open>\<open>occs x ts tpairs\<close> of \<open>thm.ML\<close>: \<open>x\<close> occurs in the hypotheses or the flex-flex pairs.\<close>

definition occs_hyps :: "pterm \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "occs_hyps x ts tpairs \<longleftrightarrow>
    (\<exists>t\<in>set ts. occs x t) \<or> (\<exists>(t, u)\<in>set tpairs. occs x t) \<or> (\<exists>(t, u)\<in>set tpairs. occs x u)"

text \<open>\<open>Term.abstract_over\<close>.\<close>

fun abstract_over_aux :: "pterm \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "abstract_over_aux v lev (Abs a T t) =
    (if aconv_term v (Abs a T t) then Bound lev else Abs a T (abstract_over_aux v (lev + 1) t))"
| "abstract_over_aux v lev (t $ u) =
    (if aconv_term v (t $ u) then Bound lev else abstract_over_aux v lev t $ abstract_over_aux v lev u)"
| "abstract_over_aux v lev t = (if aconv_term v t then Bound lev else t)"

definition abstract_over :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "abstract_over v body = abstract_over_aux v 0 body"

text \<open>\<open>Term.betapply\<close>.\<close>

fun betapply :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "betapply (Abs _ _ t) u = subst_bound u t"
| "betapply f u = f $ u"

text \<open>\<open>Envir.beta_norm\<close>: normalisation in the empty environment \<open>Envir.init\<close>.\<close>

definition beta_norm :: "pterm \<Rightarrow> pterm M" where
  "beta_norm t = norm_term (empty_env (-1)) t"

text \<open>\<open>Term.binder_types\<close>.\<close>

fun binder_types :: "ptyp \<Rightarrow> ptyp list" where
  "binder_types (Type n [T, U]) = (if n = STR ''fun'' then T # binder_types U else [])"
| "binder_types _ = []"

text \<open>
  \<open>Envir.eta_long\<close>: the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal form, with the types \<open>Ts\<close> of the loose bound
  variables. It may raise \<open>TERM\<close> (\<open>fastype_of\<close>) and it diverges on terms whose
  \<open>\<beta>\<close>-normalisation diverges.
\<close>

context
begin

declare [[unify_search_bound = 100]]

fun dest_Abs :: "pterm \<Rightarrow> (name \<times> ptyp \<times> pterm) option" where
  "dest_Abs (Abs s T b) = Some (s, T, b)"
| "dest_Abs _ = None"

partial_function (option) eta_long :: "ptyp list \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "eta_long Ts t =
    (case dest_Abs t of
      Some (s, T, b) \<Rightarrow> do {b' \<leftarrow> eta_long (T # Ts) b; return (Abs s T b')}
    | None \<Rightarrow>
      (case strip_comb t of
        (u, ts) \<Rightarrow>
          if is_Abs u then do {t' \<leftarrow> beta_norm t; eta_long Ts t'}
          else do {
            T \<leftarrow> fastype_of_term Ts t;
            ts' \<leftarrow> mapM (\<lambda>s. eta_long (rev (binder_types T) @ Ts)
              (incr_boundvars (integer_of_nat (length (binder_types T))) s)) ts;
            bs \<leftarrow> mapM (\<lambda>j. eta_long (rev (binder_types T) @ Ts) (Bound j))
              (downto (integer_of_nat (length (binder_types T)) - 1) 0);
            return (foldr (\<lambda>U b. Abs (STR ''x'') U b) (binder_types T)
              (list_comb (incr_boundvars (integer_of_nat (length (binder_types T))) u) (ts' @ bs)))}))"

end

text \<open>\<open>Thm.union_tpairs\<close> (\<open>Library.merge eq_tpairs\<close>).\<close>

definition eq_tpair :: "pterm \<times> pterm \<Rightarrow> pterm \<times> pterm \<Rightarrow> bool" where
  "eq_tpair tu tu' \<longleftrightarrow> aconv_term (fst tu) (fst tu') \<and> aconv_term (snd tu) (snd tu')"

definition insert_tpair :: "pterm \<times> pterm \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list" where
  "insert_tpair x xs = (if (\<exists>y\<in>set xs. eq_tpair x y) then xs else x # xs)"

definition union_tpairs :: "(pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list" where
  "union_tpairs ts us = (if ts = [] then us else foldr insert_tpair us ts)"

text \<open>Destructors of equations whose constant has a function type (as the patterns of \<open>thm.ML\<close>).\<close>

fun dest_eq :: "pterm \<Rightarrow> (ptyp \<times> pterm \<times> pterm) option" where
  "dest_eq (Const c (Type n [T, _]) $ t $ u) =
    (if c = STR ''Pure.eq'' then Some (T, t, u) else None)"
| "dest_eq _ = None"

fun dest_eq_fun :: "pterm \<Rightarrow> (ptyp \<times> pterm \<times> pterm) option" where
  "dest_eq_fun (Const c (Type n [T, U]) $ t $ u) =
    (if c = STR ''Pure.eq'' \<and> n = STR ''fun'' then Some (T, t, u) else None)"
| "dest_eq_fun _ = None"

fun dest_eq_any :: "pterm \<Rightarrow> (pterm \<times> pterm) option" where
  "dest_eq_any (Const c _ $ t $ u) = (if c = STR ''Pure.eq'' then Some (t, u) else None)"
| "dest_eq_any _ = None"

text \<open>The quantifier of \<open>forall_elim\<close>: \<open>Const ("Pure.all", Type ("fun", [Type ("fun", [qary, _]), _])) $ A\<close>.\<close>

fun dest_all_app :: "pterm \<Rightarrow> (ptyp \<times> pterm) option" where
  "dest_all_app (Const c (Type n [Type m [qary, _], _]) $ A) =
    (if c = STR ''Pure.all'' \<and> n = STR ''fun'' \<and> m = STR ''fun'' then Some (qary, A) else None)"
| "dest_all_app _ = None"


subsection \<open>The rules\<close>

definition mk_rep :: "integer \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> thm_rep" where
  "mk_rep m tps P = \<lparr>th_maxidx = m, th_tpairs = tps, th_prop = P\<rparr>"

text \<open>\<open>Thm.assume\<close>: \<open>A \<turnstile> A\<close>.\<close>

definition assume_rule :: "cterm_rep \<Rightarrow> thm_rep T" where
  "assume_rule raw_ct =
    (let ct = adjust_maxidx_cterm (-1) raw_ct in
      if ct_T ct \<noteq> propT then raiseW (THM (STR ''assume: prop'') 0 No_Thm)
      else if ct_maxidx ct \<noteq> -1 then raiseW (THM (STR ''assume: variables'') (ct_maxidx ct) No_Thm)
      else returnW (mk_rep (-1) [] (ct_t ct)))"

text \<open>\<open>Thm.implies_intr\<close>.\<close>

definition implies_intr :: "cterm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "implies_intr ct th =
    (if ct_T ct \<noteq> propT then raiseW (THM (STR ''implies_intr: assumptions must have type prop'') 0 State)
     else returnW (mk_rep (max (ct_maxidx ct) (th_maxidx th)) (th_tpairs th) (mk_implies (ct_t ct) (th_prop th))))"

text \<open>\<open>Thm.implies_elim thAB thA\<close>.\<close>

definition implies_elim :: "thm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "implies_elim thAB thA =
    (case dest_imp (th_prop thAB) of
      Some (A, B) \<Rightarrow>
        if aconv_term A (th_prop thA) then
          returnW (mk_rep (max (th_maxidx thA) (th_maxidx thAB)) (union_tpairs (th_tpairs thA) (th_tpairs thAB)) B)
        else raiseW (THM (STR ''implies_elim: major premise'') 0 Orule_State)
    | None \<Rightarrow> raiseW (THM (STR ''implies_elim: major premise'') 0 Orule_State))"

text \<open>\<open>Thm.forall_intr\<close>, with the hypotheses of the theorem.\<close>

definition forall_intr :: "pterm list \<Rightarrow> cterm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "forall_intr hyps ct th =
    (let x = ct_t ct; T = ct_T ct;
      check = (\<lambda>a ts.
        if occs_hyps x ts (th_tpairs th) then
          raiseW (THM (STR ''forall_intr: variable '' + quote_lit a + STR '' free in assumptions'') 0 State)
        else returnW (mk_rep (max (ct_maxidx ct) (th_maxidx th)) (th_tpairs th)
          (all_const T $ Abs a T (abstract_over x (th_prop th)))))
     in case x of
       Free a _ \<Rightarrow> check a hyps
     | Var (a, _) _ \<Rightarrow> check a []
     | _ \<Rightarrow> raiseW (THM (STR ''forall_intr: not a variable'') 0 State))"

text \<open>\<open>Thm.forall_elim\<close>.\<close>

definition forall_elim :: "cterm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "forall_elim ct th =
    (case dest_all_app (th_prop th) of
      Some (qary, A) \<Rightarrow>
        if ct_T ct \<noteq> qary then raiseW (THM (STR ''forall_elim: type mismatch'') 0 State)
        else returnW (mk_rep (max (ct_maxidx ct) (th_maxidx th)) (th_tpairs th) (betapply A (ct_t ct)))
    | None \<Rightarrow> raiseW (THM (STR ''forall_elim: not quantified'') 0 State))"

text \<open>\<open>Thm.reflexive\<close>.\<close>

definition reflexive :: "cterm_rep \<Rightarrow> thm_rep T" where
  "reflexive ct = liftMT (do {P \<leftarrow> mk_equals (ct_t ct, ct_t ct); return (mk_rep (ct_maxidx ct) [] P)})"

text \<open>\<open>Thm.symmetric\<close>.\<close>

definition symmetric :: "thm_rep \<Rightarrow> thm_rep T" where
  "symmetric th =
    (case th_prop th of
      eq $ t $ u \<Rightarrow>
        (case dest_eq_fun (th_prop th) of
          Some _ \<Rightarrow> returnW (mk_rep (th_maxidx th) (th_tpairs th) (eq $ u $ t))
        | None \<Rightarrow> raiseW (THM (STR ''symmetric'') 0 State))
    | _ \<Rightarrow> raiseW (THM (STR ''symmetric'') 0 State))"

text \<open>\<open>Thm.transitive\<close>.\<close>

definition transitive :: "thm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "transitive th1 th2 =
    (case (th_prop th1, dest_eq (th_prop th1), dest_eq_any (th_prop th2)) of
      (eq $ _ $ _, Some (T, t1, u), Some (u', t2)) \<Rightarrow>
        if \<not> aconv_term u u' then raiseW (THM (STR ''transitive: middle term'') 0 Orule_State)
        else returnW (mk_rep (max (th_maxidx th1) (th_maxidx th2))
          (union_tpairs (th_tpairs th1) (th_tpairs th2)) (eq $ t1 $ t2))
    | _ \<Rightarrow> raiseW (THM (STR ''transitive: premises'') 0 Orule_State))"

text \<open>\<open>Thm.beta_conversion\<close>, \<open>Thm.eta_conversion\<close> and \<open>Thm.eta_long_conversion\<close>.\<close>

definition beta_conversion :: "bool \<Rightarrow> cterm_rep \<Rightarrow> thm_rep T" where
  "beta_conversion full ct =
    (let t = ct_t ct in do {
      t' \<leftarrow> (if full then liftMT (beta_norm t)
             else (case t of
               Abs _ _ bodt $ u \<Rightarrow> returnW (subst_bound u bodt)
             | _ \<Rightarrow> raiseW (THM (STR ''beta_conversion: not a redex'') 0 No_Thm)));
      liftMT (do {P \<leftarrow> mk_equals (t, t'); return (mk_rep (ct_maxidx ct) [] P)})})"

definition eta_conversion :: "cterm_rep \<Rightarrow> thm_rep T" where
  "eta_conversion ct =
    liftMT (do {P \<leftarrow> mk_equals (ct_t ct, eta_contract (ct_t ct)); return (mk_rep (ct_maxidx ct) [] P)})"

definition eta_long_conversion :: "cterm_rep \<Rightarrow> thm_rep T" where
  "eta_long_conversion ct =
    liftMT (do {
      t' \<leftarrow> eta_long [] (ct_t ct);
      P \<leftarrow> mk_equals (ct_t ct, t');
      return (mk_rep (ct_maxidx ct) [] P)})"

text \<open>\<open>Thm.abstract_rule b x th\<close>, with the hypotheses of the theorem; also the abstractions
  \<open>f\<close>, \<open>g\<close> and the type \<open>U\<close> (for the proofs).\<close>

definition abstract_rule_data :: "name \<Rightarrow> pterm list \<Rightarrow> cterm_rep \<Rightarrow> thm_rep \<Rightarrow>
    (ptyp \<times> pterm \<times> pterm) T" where
  "abstract_rule_data b hyps ct th =
    (case dest_eq_fun (th_prop th) of
      None \<Rightarrow> raiseW (THM (STR ''abstract_rule: premise not an equality'') 0 State)
    | Some (U, t, u) \<Rightarrow>
        (let x = ct_t ct; T = ct_T ct;
          check = (\<lambda>a ts.
            if occs_hyps x ts (th_tpairs th) then
              raiseW (THM (STR ''abstract_rule: variable '' + quote_lit a + STR '' free in assumptions'') 0 State)
            else returnW (U, Abs b T (abstract_over x t), Abs b T (abstract_over x u)))
         in case x of
           Free a _ \<Rightarrow> check a hyps
         | Var (a, _) _ \<Rightarrow> check a []
         | _ \<Rightarrow> raiseW (THM (STR ''abstract_rule: not a variable'') 0 State)))"

definition abstract_rule :: "name \<Rightarrow> pterm list \<Rightarrow> cterm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "abstract_rule b hyps ct th = do {
    (_, f, g) \<leftarrow> abstract_rule_data b hyps ct th;
    liftMT (do {P \<leftarrow> mk_equals (f, g); return (mk_rep (maxidx_typ (ct_T ct) (th_maxidx th)) (th_tpairs th) P)})}"

text \<open>The theorem with the data for its proofs (one evaluation for the wrapper).\<close>

definition abstract_rule_res :: "name \<Rightarrow> pterm list \<Rightarrow> cterm_rep \<Rightarrow> thm_rep \<Rightarrow>
    (thm_rep \<times> ptyp \<times> pterm \<times> pterm) T" where
  "abstract_rule_res b hyps ct th = do {
    (U, f, g) \<leftarrow> abstract_rule_data b hyps ct th;
    P \<leftarrow> liftMT (mk_equals (f, g));
    returnW (mk_rep (maxidx_typ (ct_T ct) (th_maxidx th)) (th_tpairs th) P, U, f, g)}"

text \<open>\<open>Thm.combination\<close>; also the types \<open>fT\<close>, \<open>U\<close> and the terms \<open>f\<close>, \<open>g\<close>, \<open>t\<close>, \<open>u\<close>.\<close>

definition combination_data :: "thm_rep \<Rightarrow> thm_rep \<Rightarrow>
    (ptyp \<times> ptyp \<times> pterm \<times> pterm \<times> pterm \<times> pterm) T" where
  "combination_data th1 th2 =
    (case (dest_eq_fun (th_prop th1), dest_eq_fun (th_prop th2)) of
      (Some (fT, f, g), Some (tT, t, u)) \<Rightarrow>
        (case fT of
          Type n [T1, U] \<Rightarrow>
            if n = STR ''fun'' then
              if T1 = tT then returnW (fT, U, f, g, t, u)
              else raiseW (THM (STR ''combination: types'') 0 Orule_State)
            else raiseW (THM (STR ''combination: not function type'') 0 Orule_State)
        | _ \<Rightarrow> raiseW (THM (STR ''combination: not function type'') 0 Orule_State))
    | _ \<Rightarrow> raiseW (THM (STR ''combination: premises'') 0 Orule_State))"

definition combination :: "thm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "combination th1 th2 = do {
    (_, _, f, g, t, u) \<leftarrow> combination_data th1 th2;
    liftMT (do {
      P \<leftarrow> mk_equals (f $ t, g $ u);
      return (mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) P)})}"

definition combination_res :: "thm_rep \<Rightarrow> thm_rep \<Rightarrow>
    (thm_rep \<times> ptyp \<times> ptyp \<times> pterm \<times> pterm \<times> pterm \<times> pterm) T" where
  "combination_res th1 th2 = do {
    (fT, U, f, g, t, u) \<leftarrow> combination_data th1 th2;
    P \<leftarrow> liftMT (mk_equals (f $ t, g $ u));
    returnW (mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) P,
      fT, U, f, g, t, u)}"

text \<open>\<open>Thm.equal_intr\<close> and \<open>Thm.equal_elim\<close>.\<close>

definition equal_intr :: "thm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "equal_intr th1 th2 =
    (case (dest_imp (th_prop th1), dest_imp (th_prop th2)) of
      (Some (A, B), Some (B', A')) \<Rightarrow>
        if aconv_term A A' \<and> aconv_term B B' then
          liftMT (do {
            P \<leftarrow> mk_equals (A, B);
            return (mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) P)})
        else raiseW (THM (STR ''equal_intr: not equal'') 0 Orule_State)
    | _ \<Rightarrow> raiseW (THM (STR ''equal_intr: premises'') 0 Orule_State))"

definition equal_elim :: "thm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "equal_elim th1 th2 =
    (case dest_eq_any (th_prop th1) of
      Some (A, B) \<Rightarrow>
        if aconv_term (th_prop th2) A then
          returnW (mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) B)
        else raiseW (THM (STR ''equal_elim: not equal'') 0 Orule_State)
    | None \<Rightarrow> raiseW (THM (STR ''equal_elim: major premise'') 0 Orule_State))"

text \<open>\<open>Thm.trivial\<close>: \<open>A \<Longrightarrow> A\<close>.\<close>

definition trivial :: "cterm_rep \<Rightarrow> thm_rep T" where
  "trivial ct =
    (if ct_T ct \<noteq> propT then raiseW (THM (STR ''trivial: the term must have type prop'') 0 No_Thm)
     else returnW (mk_rep (ct_maxidx ct) [] (mk_implies (ct_t ct) (ct_t ct))))"

text \<open>\<open>Thm.weaken\<close>: the logical part is unchanged; the wrapper adds the hypothesis.\<close>

definition weaken :: "cterm_rep \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "weaken raw_ct th =
    (let ct = adjust_maxidx_cterm (-1) raw_ct in
      if ct_T ct \<noteq> propT then raiseW (THM (STR ''weaken: assumptions must have type prop'') 0 No_Thm)
      else if ct_maxidx ct \<noteq> -1 then
        raiseW (THM (STR ''weaken: assumptions may not contain schematic variables'') (ct_maxidx ct) No_Thm)
      else returnW th)"

text \<open>\<open>Thm.renamed_prop\<close> and \<open>Thm.adjust_maxidx_thm\<close>.\<close>

definition renamed_prop :: "pterm \<Rightarrow> thm_rep \<Rightarrow> thm_rep T" where
  "renamed_prop P th =
    (if aconv_term (th_prop th) P then returnW (mk_rep (th_maxidx th) (th_tpairs th) P)
     else raiseW (UExn (PExn (Term_Error (STR ''renamed_prop: props disagree'') [th_prop th, P]))))"

definition adjust_maxidx_thm :: "integer \<Rightarrow> thm_rep \<Rightarrow> thm_rep" where
  "adjust_maxidx_thm i th =
    (if th_maxidx th = i then th
     else if th_maxidx th < i then mk_rep i (th_tpairs th) (th_prop th)
     else mk_rep (max (maxidx_tpairs (th_tpairs th) (maxidx_of_term (th_prop th))) i) (th_tpairs th) (th_prop th))"


subsection \<open>Classic proofs\<close>

text \<open>The equality axioms of \<open>Theory.equality_axioms\<close>, as \<open>Proofterm\<close> refers to them
  (\<open>Logic.varify_global\<close>: the free variables become schematic with index \<open>0\<close>).\<close>

definition ax_aT :: ptyp where "ax_aT = TVar (tvar_a, 0) []"
definition ax_bT :: ptyp where "ax_bT = TVar (tvar_b, 0) []"

definition ax_eq :: "ptyp \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "ax_eq T t u = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u"

definition ax_var :: "name \<Rightarrow> ptyp \<Rightarrow> pterm" where
  "ax_var x T = Var (x, 0) T"

definition equality_axiom :: "name \<Rightarrow> pterm" where
  "equality_axiom a =
    (let aT = ax_aT; bT = ax_bT;
      x = ax_var STR ''x'' aT; y = ax_var STR ''y'' aT; z = ax_var STR ''z'' aT;
      A = ax_var STR ''A'' propT; B = ax_var STR ''B'' propT;
      f = ax_var STR ''f'' (aT \<rightarrow>\<^sub>T bT); g = ax_var STR ''g'' (aT \<rightarrow>\<^sub>T bT)
     in if a = STR ''reflexive'' then ax_eq aT x x
     else if a = STR ''symmetric'' then mk_implies (ax_eq aT x y) (ax_eq aT y x)
     else if a = STR ''transitive'' then list_implies [ax_eq aT x y, ax_eq aT y z] (ax_eq aT x z)
     else if a = STR ''equal_intr'' then
       list_implies [mk_implies A B, mk_implies B A] (ax_eq propT A B)
     else if a = STR ''equal_elim'' then list_implies [ax_eq propT A B, A] B
     else if a = STR ''abstract_rule'' then
       mk_implies (all_const aT $ Abs STR ''x'' aT (ax_eq bT (f $ Bound 0) (g $ Bound 0)))
         (ax_eq (aT \<rightarrow>\<^sub>T bT) (Abs STR ''x'' aT (f $ Bound 0)) (Abs STR ''x'' aT (g $ Bound 0)))
     else list_implies [ax_eq (aT \<rightarrow>\<^sub>T bT) f g, ax_eq aT x y] (ax_eq bT (f $ x) (g $ y)))"

definition equality_axm :: "name \<Rightarrow> prf" where
  "equality_axm a = PAxm (STR ''Pure.'' + a) (equality_axiom a) None"

abbreviation PAppt' :: "prf \<Rightarrow> pterm \<Rightarrow> prf" (infixl \<open>%>\<close> 70) where
  "p %> t \<equiv> PAppt p (Some t)"

text \<open>\<open>Proofterm.reflexive_proof\<close>, \<open>Proofterm.is_reflexive_proof\<close>,
  \<open>Proofterm.symmetric_proof\<close>, \<open>Proofterm.transitive_proof\<close>, \<open>Proofterm.equal_intr_proof\<close>,
  \<open>Proofterm.equal_elim_proof\<close>.\<close>

definition reflexive_proof :: "prf" where
  "reflexive_proof = PAppt (equality_axm STR ''reflexive'') None"

fun is_reflexive_proof :: "prf \<Rightarrow> bool" where
  "is_reflexive_proof (PAppt (PAxm a _ _) _) = (a = STR ''Pure.reflexive'')"
| "is_reflexive_proof _ = False"

definition symmetric_proof :: "prf \<Rightarrow> prf" where
  "symmetric_proof prf =
    (if is_reflexive_proof prf then prf
     else PAppp (PAppt (PAppt (equality_axm STR ''symmetric'') None) None) prf)"

definition transitive_proof :: "ptyp \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf" where
  "transitive_proof U u prf1 prf2 =
    (if is_reflexive_proof prf1 then prf2
     else if is_reflexive_proof prf2 then prf1
     else if U = propT then
       PAppp (PAppp (PAppt (PAppt (PAppt (equality_axm STR ''transitive'') None) (Some (remove_types u))) None) prf1) prf2
     else PAppp (PAppp (PAppt (PAppt (PAppt (equality_axm STR ''transitive'') None) None) None) prf1) prf2)"

definition equal_intr_proof :: "pterm \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf" where
  "equal_intr_proof A B prf1 prf2 =
    PAppp (PAppp (equality_axm STR ''equal_intr'' %> remove_types A %> remove_types B) prf1) prf2"

definition equal_elim_proof :: "pterm \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf" where
  "equal_elim_proof A B prf1 prf2 =
    PAppp (PAppp (equality_axm STR ''equal_elim'' %> remove_types A %> remove_types B) prf1) prf2"

text \<open>\<open>Proofterm.abstract_over\<close>: abstraction of a proof over the occurrences of a term in its
  terms (the body of an \<^const>\<open>Abst\<close>).\<close>

fun prf_abstract_term :: "pterm \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "prf_abstract_term v lev (Abs a T t) =
    (if aconv_term v (Abs a T t) then Bound lev else Abs a T (prf_abstract_term v (lev + 1) t))"
| "prf_abstract_term v lev (t $ u) =
    (if aconv_term v (t $ u) then Bound lev else prf_abstract_term v lev t $ prf_abstract_term v lev u)"
| "prf_abstract_term v lev t = (if aconv_term v t then Bound lev else t)"

fun prf_abstract_over_aux :: "pterm \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf" where
  "prf_abstract_over_aux v lev (AbsP a t p) =
    AbsP a (map_option (prf_abstract_term v lev) t) (prf_abstract_over_aux v lev p)"
| "prf_abstract_over_aux v lev (Abst a T p) = Abst a T (prf_abstract_over_aux v (lev + 1) p)"
| "prf_abstract_over_aux v lev (PAppp p q) = PAppp (prf_abstract_over_aux v lev p) (prf_abstract_over_aux v lev q)"
| "prf_abstract_over_aux v lev (PAppt p t) =
    PAppt (prf_abstract_over_aux v lev p) (map_option (prf_abstract_term v lev) t)"
| "prf_abstract_over_aux v lev p = p"

definition prf_abstract_over :: "pterm \<Rightarrow> prf \<Rightarrow> prf" where
  "prf_abstract_over v p = prf_abstract_over_aux v 0 p"

text \<open>\<open>Proofterm.forall_intr_proof (a, v) NONE\<close> and \<open>Proofterm.abstract_rule_proof\<close>.\<close>

definition forall_intr_proof :: "name \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf" where
  "forall_intr_proof a v prf = Abst a None (prf_abstract_over v prf)"

definition abstract_rule_proof :: "name \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf" where
  "abstract_rule_proof a x prf =
    PAppp (PAppt (PAppt (equality_axm STR ''abstract_rule'') None) None) (forall_intr_proof a x prf)"

text \<open>\<open>Proofterm.implies_intr_proof\<close>: the hypotheses \<open>h\<close> become the bound proof variable.\<close>

fun abshyp :: "pterm \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf" where
  "abshyp h i (Hyp t) = (if aconv_term h t then PBound i else Hyp t)"
| "abshyp h i (Abst s T p) = Abst s T (abshyp h i p)"
| "abshyp h i (AbsP s t p) = AbsP s t (abshyp h (i + 1) p)"
| "abshyp h i (PAppt p t) = PAppt (abshyp h i p) t"
| "abshyp h i (PAppp p q) = PAppp (abshyp h i p) (abshyp h i q)"
| "abshyp h i p = p"

definition implies_intr_proof :: "pterm \<Rightarrow> prf \<Rightarrow> prf" where
  "implies_intr_proof h prf = AbsP STR ''H'' None (abshyp h 0 prf)"

text \<open>\<open>Proofterm.combination_proof\<close>.\<close>

fun check_comb :: "prf \<Rightarrow> bool" where
  "check_comb (PAppp (PAppp (PAppt (PAppt (PAppt (PAppt (PAxm a _ _) f) _) _) _) p) _) =
    (a = STR ''Pure.combination'' \<and> (f \<noteq> None \<or> check_comb p))"
| "check_comb (PAppp (PAppp (PAppt (PAppt (PAppt (PAxm a _ _) _) _) _) p) q) =
    (a = STR ''Pure.transitive'' \<and> check_comb p \<and> check_comb q)"
| "check_comb (PAppp (PAppt (PAppt (PAxm a _ _) _) _) p) =
    (a = STR ''Pure.symmetric'' \<and> check_comb p)"
| "check_comb _ = False"

definition comb_arg :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm option" where
  "comb_arg f t = (case head_of f of Abs _ _ _ \<Rightarrow> Some (remove_types t) | Var _ _ \<Rightarrow> Some (remove_types t) | _ \<Rightarrow> None)"

definition combination_proof :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf P" where
  "combination_proof f g t u prf1 prf2 = liftMP (do {
    f' \<leftarrow> beta_norm f;
    g' \<leftarrow> beta_norm g;
    let ax0 = equality_axm STR ''combination'';
    let ax =
      (if check_comb prf1 then PAppt (PAppt ax0 None) None
       else if is_reflexive_proof prf1 then PAppt (ax0 %> remove_types f') None
       else ax0 %> remove_types f' %> remove_types g');
    return (PAppp (PAppp (PAppt (PAppt ax (comb_arg f' t)) (comb_arg g' u)) prf1) prf2)})"

text \<open>\<open>Proofterm.trivial_proof\<close>.\<close>

definition trivial_proof :: "prf" where
  "trivial_proof = AbsP STR ''H'' None (PBound 0)"


subsection \<open>Tight proofs\<close>

text \<open>Tables of type variables (\<open>ZTVars\<close>).\<close>

lift_definition zt_empty :: "'a ztvtab" is Map.empty by simp

lift_definition zt_update :: "(indexname \<times> psort) \<times> 'a \<Rightarrow> 'a ztvtab \<Rightarrow> 'a ztvtab" is
  "\<lambda>(k, x) m. m(k \<mapsto> x)" by (auto split: prod.splits)

text \<open>
  The equality axioms of \<open>zterm.ML\<close> as proof constants (\<open>zproof_axiom\<close> on the theory
  \<open>thy0\<close> with the constants \<open>Pure.all\<close>, \<open>Pure.imp\<close> and \<open>Pure.eq\<close>): their propositions have
  free variables (index \<open>-1\<close>), and their instantiations map each variable to itself.
\<close>

definition zax_aT :: ztyp where "zax_aT = ZTVar (tvar_a, -1) []"
definition zax_bT :: ztyp where "zax_bT = ZTVar (tvar_b, -1) []"

definition zax_eq :: "ztyp \<Rightarrow> zterm \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zax_eq T t u = ZApp (ZApp (ZConst1 STR ''Pure.eq'' T) t) u"

definition zax_imp :: "zterm \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zax_imp A B = ZApp (ZApp (ZConst0 STR ''Pure.imp'') A) B"

definition zax_var :: "name \<Rightarrow> ztyp \<Rightarrow> zterm" where
  "zax_var x T = ZVar (x, -1) T"

definition zequality_axiom :: "name \<Rightarrow> zterm \<times> (indexname \<times> psort) list \<times> (indexname \<times> ztyp) list" where
  "zequality_axiom a =
    (let aT = zax_aT; bT = zax_bT; fT = ZFun aT bT;
      x = zax_var STR ''x'' aT; y = zax_var STR ''y'' aT; z = zax_var STR ''z'' aT;
      A = zax_var STR ''A'' ZProp; B = zax_var STR ''B'' ZProp;
      f = zax_var STR ''f'' fT; g = zax_var STR ''g'' fT;
      va = ((tvar_a, -1), []); vb = ((tvar_b, -1), []);
      vx = ((STR ''x'', -1), aT); vy = ((STR ''y'', -1), aT); vz = ((STR ''z'', -1), aT);
      vA = ((STR ''A'', -1), ZProp); vB = ((STR ''B'', -1), ZProp);
      vf = ((STR ''f'', -1), fT); vg = ((STR ''g'', -1), fT)
     in if a = STR ''reflexive'' then (zax_eq aT x x, [va], [vx])
     else if a = STR ''symmetric'' then (zax_imp (zax_eq aT x y) (zax_eq aT y x), [va], [vx, vy])
     else if a = STR ''transitive'' then
       (zax_imp (zax_eq aT x y) (zax_imp (zax_eq aT y z) (zax_eq aT x z)), [va], [vx, vy, vz])
     else if a = STR ''equal_intr'' then
       (zax_imp (zax_imp A B) (zax_imp (zax_imp B A) (zax_eq ZProp A B)), [], [vA, vB])
     else if a = STR ''equal_elim'' then (zax_imp (zax_eq ZProp A B) (zax_imp A B), [], [vA, vB])
     else if a = STR ''abstract_rule'' then
       (zax_imp (ZApp (ZConst1 STR ''Pure.all'' aT) (ZAbs STR ''x'' aT (zax_eq bT (ZApp f (ZBound 0)) (ZApp g (ZBound 0)))))
         (zax_eq fT (ZAbs STR ''x'' aT (ZApp f (ZBound 0))) (ZAbs STR ''x'' aT (ZApp g (ZBound 0)))),
        [va, vb], [vf, vg])
     else
       (zax_imp (zax_eq fT f g) (zax_imp (zax_eq aT x y) (zax_eq bT (ZApp f x) (ZApp g y))),
        [va, vb], [vf, vg, vx, vy]))"

definition zequality_axm :: "name \<Rightarrow> zproof_const" where
  "zequality_axm a =
    (case zequality_axiom a of (A, tvs, vs) \<Rightarrow>
      ((ZAxiom (STR ''Pure.'' + a), A),
       (fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) tvs zt_empty,
        fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) vs zv_empty)))"

text \<open>\<open>ZTerm.make_const_proof (f, g)\<close>: instantiation of a proof constant by name.\<close>

fun zsubst_tvar_names :: "(name \<Rightarrow> ztyp option) \<Rightarrow> ztyp \<Rightarrow> ztyp" where
  "zsubst_tvar_names f (ZTVar (a, i) S) = (case f a of Some T \<Rightarrow> T | None \<Rightarrow> ZTVar (a, i) S)"
| "zsubst_tvar_names f (ZFun T U) = ZFun (zsubst_tvar_names f T) (zsubst_tvar_names f U)"
| "zsubst_tvar_names f (ZType1 a T) = ZType1 a (zsubst_tvar_names f T)"
| "zsubst_tvar_names f (ZType a Ts) = ZType a (map (zsubst_tvar_names f) Ts)"
| "zsubst_tvar_names f T = T"

definition make_const_proof :: "(name \<Rightarrow> ztyp option) \<Rightarrow> (name \<Rightarrow> zterm option) \<Rightarrow> zproof_const \<Rightarrow> zproof Z" where
  "make_const_proof f g c =
    (case c of (a, insts) \<Rightarrow> do {
      insts' \<leftarrow> map_insts (zsubst_tvar_names f)
        (\<lambda>t. return (case t of ZVar (x, _) _ \<Rightarrow> (case g x of Some u \<Rightarrow> u | None \<Rightarrow> t) | _ \<Rightarrow> t)) insts;
      return (ZConstp (a, insts'))})"

definition zaxiom_proof :: "name \<Rightarrow> (name \<times> ztyp) list \<Rightarrow> (name \<times> zterm) list \<Rightarrow> zproof Z" where
  "zaxiom_proof a Ts ts = make_const_proof (map_of Ts) (map_of ts) (zequality_axm a)"

text \<open>\<open>ZTerm.is_reflexive_proof\<close>.\<close>

fun zis_reflexive_proof :: "zproof \<Rightarrow> bool" where
  "zis_reflexive_proof (ZConstp ((ZAxiom a, _), _)) = (a = STR ''Pure.reflexive'')"
| "zis_reflexive_proof _ = False"

text \<open>\<open>ZTerm.assume_proof\<close>, \<open>ZTerm.trivial_proof\<close>, \<open>ZTerm.implies_intr_proof\<close>.\<close>

definition zassume_proof :: "ztypargs \<Rightarrow> pterm \<Rightarrow> zproof Z" where
  "zassume_proof ta A = do {A' \<leftarrow> zterm_of ta A; return (ZHyp A')}"

definition ztrivial_proof :: "ztypargs \<Rightarrow> pterm \<Rightarrow> zproof Z" where
  "ztrivial_proof ta A = do {A' \<leftarrow> zterm_of ta A; return (ZAbsp STR ''H'' A' (ZBoundp 0))}"

fun zabshyp :: "zterm \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> zproof" where
  "zabshyp h lev (ZHyp t) = (if aconv_zterm h t then ZBoundp lev else ZHyp t)"
| "zabshyp h lev (ZAbst x T p) = ZAbst x T (zabshyp h lev p)"
| "zabshyp h lev (ZAbsp x t p) = ZAbsp x t (zabshyp h (lev + 1) p)"
| "zabshyp h lev (ZAppt p t) = ZAppt (zabshyp h lev p) t"
| "zabshyp h lev (ZAppp p q) = ZAppp (zabshyp h lev p) (zabshyp h lev q)"
| "zabshyp h lev p = p"

definition zimplies_intr_proof :: "ztypargs \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zimplies_intr_proof ta A prf = do {h \<leftarrow> zterm_of ta A; return (ZAbsp STR ''H'' h (zabshyp h 0 prf))}"

text \<open>\<open>ZTerm.forall_intr_proof\<close> and \<open>ZTerm.forall_elim_proof\<close>.\<close>

fun zabstract_term :: "zterm \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zabstract_term z i (ZAbs x T t) =
    (if aconv_zterm (ZAbs x T t) z then ZBound i else ZAbs x T (zabstract_term z (i + 1) t))"
| "zabstract_term z i (ZApp t u) =
    (if aconv_zterm (ZApp t u) z then ZBound i else ZApp (zabstract_term z i t) (zabstract_term z i u))"
| "zabstract_term z i t = (if aconv_zterm t z then ZBound i else t)"

fun zabstract_proof :: "zterm \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> zproof" where
  "zabstract_proof z i (ZAbst x T p) = ZAbst x T (zabstract_proof z (i + 1) p)"
| "zabstract_proof z i (ZAbsp x t p) = ZAbsp x (zabstract_term z i t) (zabstract_proof z i p)"
| "zabstract_proof z i (ZAppt p t) = ZAppt (zabstract_proof z i p) (zabstract_term z i t)"
| "zabstract_proof z i (ZAppp p q) = ZAppp (zabstract_proof z i p) (zabstract_proof z i q)"
| "zabstract_proof z i p = p"

definition zforall_intr_proof :: "ztypargs \<Rightarrow> ptyp \<Rightarrow> name \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zforall_intr_proof ta T a x prf = do {
    z \<leftarrow> zterm_of ta x;
    return (ZAbst a (ztyp_of T) (zabstract_proof z 0 prf))}"

definition zforall_elim_proof :: "ztypargs \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zforall_elim_proof ta t p = do {t' \<leftarrow> zterm_of ta t; return (ZAppt p t')}"

text \<open>The tight proofs of the equality rules.\<close>

definition zreflexive_proof :: "ztypargs \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> zproof Z" where
  "zreflexive_proof ta T t = do {
    x \<leftarrow> zterm_of ta t;
    zaxiom_proof STR ''reflexive'' [(tvar_a, ztyp_of T)] [(STR ''x'', x)]}"

definition zsymmetric_proof :: "ztypargs \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zsymmetric_proof ta T t u prf =
    (if zis_reflexive_proof prf then return prf
     else do {
       x \<leftarrow> zterm_of ta t;
       y \<leftarrow> zterm_of ta u;
       ax \<leftarrow> zaxiom_proof STR ''symmetric'' [(tvar_a, ztyp_of T)] [(STR ''x'', x), (STR ''y'', y)];
       return (ZAppp ax prf)})"

definition ztransitive_proof :: "ztypargs \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "ztransitive_proof ta T t u v prf1 prf2 =
    (if zis_reflexive_proof prf1 then return prf2
     else if zis_reflexive_proof prf2 then return prf1
     else do {
       x \<leftarrow> zterm_of ta t;
       y \<leftarrow> zterm_of ta u;
       z \<leftarrow> zterm_of ta v;
       ax \<leftarrow> zaxiom_proof STR ''transitive'' [(tvar_a, ztyp_of T)] [(STR ''x'', x), (STR ''y'', y), (STR ''z'', z)];
       return (ZAppp (ZAppp ax prf1) prf2)})"

definition zequal_intr_proof :: "ztypargs \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zequal_intr_proof ta t u prf1 prf2 = do {
    A \<leftarrow> zterm_of ta t;
    B \<leftarrow> zterm_of ta u;
    ax \<leftarrow> zaxiom_proof STR ''equal_intr'' [] [(STR ''A'', A), (STR ''B'', B)];
    return (ZAppp (ZAppp ax prf1) prf2)}"

definition zequal_elim_proof :: "ztypargs \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> zproof \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zequal_elim_proof ta t u prf1 prf2 = do {
    A \<leftarrow> zterm_of ta t;
    B \<leftarrow> zterm_of ta u;
    ax \<leftarrow> zaxiom_proof STR ''equal_elim'' [] [(STR ''A'', A), (STR ''B'', B)];
    return (ZAppp (ZAppp ax prf1) prf2)}"

definition zabstract_rule_proof :: "ztypargs \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> name \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow>
    zproof \<Rightarrow> zproof Z" where
  "zabstract_rule_proof ta T U a x t u prf = do {
    f \<leftarrow> zterm_of ta t;
    g \<leftarrow> zterm_of ta u;
    ax \<leftarrow> zaxiom_proof STR ''abstract_rule'' [(tvar_a, ztyp_of T), (tvar_b, ztyp_of U)]
      [(STR ''f'', f), (STR ''g'', g)];
    p \<leftarrow> zforall_intr_proof ta T a x prf;
    return (ZAppp ax p)}"

definition zcombination_proof :: "ztypargs \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow>
    zproof \<Rightarrow> zproof \<Rightarrow> zproof Z" where
  "zcombination_proof ta T U f g t u prf1 prf2 = do {
    f' \<leftarrow> zterm_of ta f;
    g' \<leftarrow> zterm_of ta g;
    x \<leftarrow> zterm_of ta t;
    y \<leftarrow> zterm_of ta u;
    ax \<leftarrow> zaxiom_proof STR ''combination'' [(tvar_a, ztyp_of T), (tvar_b, ztyp_of U)]
      [(STR ''f'', f'), (STR ''g'', g'), (STR ''x'', x), (STR ''y'', y)];
    return (ZAppp (ZAppp ax prf1) prf2)}"

end
