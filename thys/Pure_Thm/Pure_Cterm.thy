section \<open>Operations on Certified Terms\<close>

theory Pure_Cterm
  imports Pure_Sorts
begin

text \<open>
  Literal models of the destructors and constructors of certified terms of \<open>thm.ML\<close>
  (\<open>Thm.dest_comb\<close>, \<open>Thm.dest_fun\<close>, \<open>Thm.dest_arg\<close>, \<open>Thm.dest_fun2\<close>, \<open>Thm.dest_arg1\<close>,
  \<open>Thm.dest_abs_fresh\<close>, \<open>Thm.dest_abs_global\<close>, \<open>Thm.free\<close>, \<open>Thm.var\<close>, \<open>Thm.apply\<close>,
  \<open>Thm.lambda_name\<close>, \<open>Thm.lambda\<close>, \<open>Thm.incr_indexes_cterm\<close>, \<open>Thm.generalize_cterm\<close>,
  \<open>Thm.instantiate_cterm\<close>, \<open>Thm.instantiate_beta_cterm\<close>; \<open>Thm.adjust_maxidx_cterm\<close> is in
  theory \<^theory_text>\<open>Pure_Rules\<close>) on the logical part of certified terms (\<^typ>\<open>cterm_rep\<close>: term,
  type and maximal index). The sorts and certificates are combined by the wrappers.
  \<open>Term.argument_type_of\<close> raises \<open>TYPE\<close> (via \<open>fastype_of\<close> also \<open>TERM\<close>); the exceptions
  \<open>CTERM\<close> and \<open>Term.USED_FREE\<close> are \<^const>\<open>CTERM\<close> and \<^const>\<open>USED_FREE\<close>, whose certified
  terms are supplied by the wrappers.
\<close>

subsection \<open>Argument types\<close>

text \<open>\<open>Term.argument_type_of tm k\<close>: the type of the \<open>k\<close>-th argument of \<open>tm\<close>.\<close>

fun argT :: "integer \<Rightarrow> ptyp \<Rightarrow> ptyp M" where
  "argT i (Type n [T, U]) =
    (if n = STR ''fun'' then (if i = 0 then return T else argT (i - 1) U)
     else raise (Type_Error (STR ''argument_type_of'') [Type n [T, U]] []))"
| "argT i T = raise (Type_Error (STR ''argument_type_of'') [T] [])"

fun arg_type :: "integer \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp M" where
  "arg_type i Ts (Abs _ T t) = (if i = 0 then return T else arg_type (i - 1) (T # Ts) t)"
| "arg_type i Ts (t $ _) = arg_type (i + 1) Ts t"
| "arg_type i Ts a = do {T \<leftarrow> fastype_of_term Ts a; argT i T}"

definition argument_type_of :: "pterm \<Rightarrow> integer \<Rightarrow> ptyp M" where
  "argument_type_of t k = arg_type k [] t"


subsection \<open>Destructors\<close>

definition dest_comb :: "cterm_rep \<Rightarrow> (cterm_rep \<times> cterm_rep) T" where
  "dest_comb ct =
    (case ct_t ct of
      c $ a \<Rightarrow> liftMT (do {
        A \<leftarrow> argument_type_of c 0;
        return (CTerm c (A \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct), CTerm a A (ct_maxidx ct))})
    | _ \<Rightarrow> raiseW (CTERM (STR ''dest_comb'')))"

definition dest_fun :: "cterm_rep \<Rightarrow> cterm_rep T" where
  "dest_fun ct =
    (case ct_t ct of
      c $ _ \<Rightarrow> liftMT (do {A \<leftarrow> argument_type_of c 0; return (CTerm c (A \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct))})
    | _ \<Rightarrow> raiseW (CTERM (STR ''dest_fun'')))"

definition dest_arg :: "cterm_rep \<Rightarrow> cterm_rep T" where
  "dest_arg ct =
    (case ct_t ct of
      c $ a \<Rightarrow> liftMT (do {A \<leftarrow> argument_type_of c 0; return (CTerm a A (ct_maxidx ct))})
    | _ \<Rightarrow> raiseW (CTERM (STR ''dest_arg'')))"

definition dest_fun2 :: "cterm_rep \<Rightarrow> cterm_rep T" where
  "dest_fun2 ct =
    (case ct_t ct of
      c $ _ $ _ \<Rightarrow> liftMT (do {
        A \<leftarrow> argument_type_of c 0;
        B \<leftarrow> argument_type_of c 1;
        return (CTerm c (A \<rightarrow>\<^sub>T B \<rightarrow>\<^sub>T ct_T ct) (ct_maxidx ct))})
    | _ \<Rightarrow> raiseW (CTERM (STR ''dest_fun2'')))"

definition dest_arg1 :: "cterm_rep \<Rightarrow> cterm_rep T" where
  "dest_arg1 ct =
    (case ct_t ct of
      c $ a $ _ \<Rightarrow> liftMT (do {A \<leftarrow> argument_type_of c 0; return (CTerm a A (ct_maxidx ct))})
    | _ \<Rightarrow> raiseW (CTERM (STR ''dest_arg1'')))"

text \<open>\<open>Term.used_free\<close> and the free names of a term (\<open>Term.declare_free_names\<close>).\<close>

fun used_free :: "name \<Rightarrow> pterm \<Rightarrow> bool" where
  "used_free x (Free y _) \<longleftrightarrow> x = y"
| "used_free x (t $ u) \<longleftrightarrow> used_free x t \<or> used_free x u"
| "used_free x (Abs _ _ t) \<longleftrightarrow> used_free x t"
| "used_free x _ \<longleftrightarrow> False"

fun free_names :: "pterm \<Rightarrow> name list" where
  "free_names (Free y _) = [y]"
| "free_names (t $ u) = free_names t @ free_names u"
| "free_names (Abs _ _ t) = free_names t"
| "free_names _ = []"

text \<open>
  \<open>Thm.gen_dest_abs\<close> with \<open>Term.dest_abs_fresh x\<close> and \<open>Term.dest_abs_global\<close>; the fresh
  name of \<open>Name.variant\<close> is that of \<open>Name.variant_list\<close> (the parameter \<open>vl\<close>).
\<close>

definition dest_abs_with :: "(pterm \<Rightarrow> name T) \<Rightarrow> cterm_rep \<Rightarrow> (cterm_rep \<times> cterm_rep) T" where
  "dest_abs_with nm ct =
    (case (ct_t ct, ct_T ct) of
      (Abs a T b, Type n [_, U]) \<Rightarrow>
        if n = STR ''fun'' then
          bindW (nm (Abs a T b)) (\<lambda>x'.
            returnW (CTerm (Free x' T) T (ct_maxidx ct), CTerm (subst_bound (Free x' T) b) U (ct_maxidx ct)))
        else raiseW (CTERM (STR ''dest_abs''))
    | _ \<Rightarrow> raiseW (CTERM (STR ''dest_abs'')))"

definition dest_abs_fresh :: "name \<Rightarrow> cterm_rep \<Rightarrow> (cterm_rep \<times> cterm_rep) T" where
  "dest_abs_fresh x = dest_abs_with (\<lambda>t.
    (case t of Abs _ _ b \<Rightarrow> if used_free x b then raiseW (USED_FREE x t) else returnW x | _ \<Rightarrow> returnW x))"

definition dest_abs_global :: "(name list \<Rightarrow> name list \<Rightarrow> name list) \<Rightarrow> cterm_rep \<Rightarrow> (cterm_rep \<times> cterm_rep) T" where
  "dest_abs_global vl = dest_abs_with (\<lambda>t.
    (case t of Abs a _ b \<Rightarrow> returnW (if used_free a b then hd (vl (free_names b) [a]) else a)
    | _ \<Rightarrow> raiseW (CTERM (STR ''dest_abs''))))"


subsection \<open>Constructors\<close>

text \<open>\<open>Thm.free\<close> and \<open>Thm.var\<close> of a certified type \<open>T\<close> with maximal index \<open>m\<close>.\<close>

definition free_cterm :: "name \<Rightarrow> ptyp \<Rightarrow> integer \<Rightarrow> cterm_rep" where
  "free_cterm x T m = CTerm (Free x T) T m"

definition var_cterm :: "indexname \<Rightarrow> ptyp \<Rightarrow> integer \<Rightarrow> cterm_rep T" where
  "var_cterm xi T m =
    (if snd xi < 0 then liftMT (raise (Term_Error (STR ''var: bad index'') [Var xi T]))
     else returnW (CTerm (Var xi T) T (max (snd xi) m)))"

definition apply_cterm :: "cterm_rep \<Rightarrow> cterm_rep \<Rightarrow> cterm_rep T" where
  "apply_cterm cf cx =
    (case ct_T cf of
      Type n [dty, rty] \<Rightarrow>
        if n = STR ''fun'' then
          (if ct_T cx = dty then returnW (CTerm (ct_t cf $ ct_t cx) rty (max (ct_maxidx cf) (ct_maxidx cx)))
           else raiseW (CTERM (STR ''apply: types don't agree'')))
        else raiseW (CTERM (STR ''apply: first arg is not a function''))
    | _ \<Rightarrow> raiseW (CTERM (STR ''apply: first arg is not a function'')))"

text \<open>\<open>Long_Name.base_name\<close>, \<open>Term.term_name\<close> and \<open>Term.lambda_name\<close>.\<close>

definition base_name :: "name \<Rightarrow> name" where
  "base_name x = String.implode (rev (takeWhile (\<lambda>c. c \<noteq> CHR ''.'') (rev (String.explode x))))"

fun term_name :: "pterm \<Rightarrow> name" where
  "term_name (Const x _) = base_name x"
| "term_name (Free x _) = x"
| "term_name (Var (x, _) _) = x"
| "term_name _ = STR ''uu''"

definition lambda_name_term :: "name \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm M" where
  "lambda_name_term x v t = do {
    T \<leftarrow> fastype_of v;
    return (Abs (if x = STR '''' then term_name v else x) T (abstract_over v t))}"

definition lambda_name :: "name \<Rightarrow> cterm_rep \<Rightarrow> cterm_rep \<Rightarrow> cterm_rep T" where
  "lambda_name x ct1 ct2 = liftMT (do {
    t \<leftarrow> lambda_name_term x (ct_t ct1) (ct_t ct2);
    return (CTerm t (ct_T ct1 \<rightarrow>\<^sub>T ct_T ct2) (max (ct_maxidx ct1) (ct_maxidx ct2)))})"


definition lambda_cterm :: "cterm_rep \<Rightarrow> cterm_rep \<Rightarrow> cterm_rep T" where
  "lambda_cterm t u = lambda_name STR '''' t u"


subsection \<open>Indices\<close>

definition incr_indexes_cterm :: "integer \<Rightarrow> cterm_rep \<Rightarrow> cterm_rep T" where
  "incr_indexes_cterm i ct =
    (if i < 0 then raiseW (CTERM (STR ''negative increment''))
     else if i = 0 then returnW ct
     else returnW (CTerm (incr_indexes [] i (ct_t ct)) (incr_tvar i (ct_T ct)) (ct_maxidx ct + i)))"


subsection \<open>Generalization and instantiation\<close>

text \<open>\<open>Thm.generalize_cterm\<close> (the name sets as lists).\<close>

definition generalize_cterm :: "name list \<Rightarrow> name list \<Rightarrow> integer \<Rightarrow> cterm_rep \<Rightarrow> cterm_rep T" where
  "generalize_cterm tfrees frees gi ct =
    (if tfrees = [] \<and> frees = [] then returnW ct
     else if gi \<le> ct_maxidx ct then raiseW (CTERM (STR ''generalize_cterm: bad index''))
     else
       (let t' = generalize_term tfrees frees gi (ct_t ct)
        in returnW (CTerm t' (generalizeT tfrees gi (ct_T ct)) (maxidx_of_term t'))))"

text \<open>
  \<open>Thm.instantiate_cterm\<close> (\<open>beta = False\<close>) and \<open>Thm.instantiate_beta_cterm\<close> (\<open>beta = True\<close>),
  with the certification of \<^const>\<open>instantiate\<close>: the term, then its type, with the maximal
  index of both (\<open>Term_Subst.instantiateT_maxidx\<close>).
\<close>

definition instantiate_cterm :: "algebra \<Rightarrow> bool \<Rightarrow> instT_m \<Rightarrow> ((indexname \<times> ptyp) \<times> pterm \<times> ptyp \<times> integer) list \<Rightarrow>
    cterm_rep \<Rightarrow> cterm_rep T" where
  "instantiate_cterm alg beta instT insts ct =
    (if instT = [] \<and> insts = [] then returnW ct
     else do {
       check_instT alg instT;
       check_inst insts;
       let inst = map (\<lambda>(v, (u, U, j)). (v, (u, j))) insts;
       let subst = (if beta then inst_beta_m instT inst else inst_m instT inst);
       (case subst (ct_t ct) (-1) of
         (t', m1) \<Rightarrow> (case instT_m instT (ct_T ct) m1 of (T', m) \<Rightarrow> returnW (CTerm t' T' m)))})"

end
