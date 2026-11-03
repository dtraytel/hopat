section \<open>Pattern Unification Does Not Give Up on Patterns\<close>

theory Pattern_Unify_Patterns
  imports Pattern_Patterns Pattern_Term_Proj
begin

text \<open>
  On \<open>\<beta>\<close>-normal patterns (\<^const>\<open>ppat\<close>) in an environment of closed patterns whose bound
  variables are not negative, \<^const>\<open>unify\<close> never raises \<open>Pattern\<close>, and every resulting
  environment binds patterns only.
\<close>

subsection \<open>Computations that do not raise \<open>Pattern\<close>\<close>

definition pok :: "('a \<Rightarrow> bool) \<Rightarrow> 'a M \<Rightarrow> bool" where
  "pok P m \<longleftrightarrow> (case m of Some (Ok x) \<Rightarrow> P x | Some (Err e) \<Rightarrow> e \<noteq> Pattern | None \<Rightarrow> True)"

abbreviation no_pat :: "'a M \<Rightarrow> bool" where
  "no_pat m \<equiv> pok (\<lambda>_. True) m"

lemma pok_simps [simp]:
  "pok P (return x) \<longleftrightarrow> P x" "pok P (raise e) \<longleftrightarrow> e \<noteq> Pattern" "pok P None"
  "pok P (Some (Ok x)) \<longleftrightarrow> P x" "pok P (Some (Err e)) \<longleftrightarrow> e \<noteq> Pattern"
  by (simp_all add: pok_def return_def raise_def)

lemma pok_IH: "(\<And>r. m = Some r \<Longrightarrow> pok P (Some r)) \<Longrightarrow> pok P m"
  by (cases m) auto

lemma pok_bindM: "pok P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x \<Longrightarrow> pok Q (f x)) \<Longrightarrow> pok Q (bindM m f)"
  by (auto simp: pok_def bindM_def split: option.splits res.splits)

lemma pok_handle:
  "pok P m \<Longrightarrow> (\<And>e. m = Some (Err e) \<Longrightarrow> e \<noteq> Pattern \<Longrightarrow> pok P (h e)) \<Longrightarrow> pok P (handle m h)"
  by (auto simp: pok_def handle_def split: option.splits res.splits)

lemma pok_mono: "pok P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> pok Q m"
  by (auto simp: pok_def split: option.splits res.splits)

lemma pok_okI: "no_pat m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x) \<Longrightarrow> pok P m"
  by (auto simp: pok_def split: option.splits res.splits)

lemma pok_okD: "pok P m \<Longrightarrow> ok m x \<Longrightarrow> P x"
  by (simp add: pok_def)

lemma pok_ErrD: "pok P m \<Longrightarrow> m = Some (Err e) \<Longrightarrow> e \<noteq> Pattern"
  by (simp add: pok_def)

lemma pok_mapM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_pat (f x)) \<Longrightarrow> no_pat (mapM f xs)"
  by (induction xs) (auto intro!: pok_bindM)

lemma pok_foldM:
  "P b \<Longrightarrow> (\<And>x b. x \<in> set xs \<Longrightarrow> P b \<Longrightarrow> pok P (f x b)) \<Longrightarrow> pok P (foldM f xs b)"
  by (induction xs arbitrary: b) (auto intro!: pok_bindM)

lemma pok_allM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_pat (f x)) \<Longrightarrow> no_pat (allM f xs)"
  by (induction xs) (auto intro!: pok_bindM)

lemma pok_existsM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_pat (f x)) \<Longrightarrow> no_pat (existsM f xs)"
  by (induction xs) (auto intro!: pok_bindM)

lemma no_pat_nth: "no_pat (nth xs i)"
  by (induction xs arbitrary: i) auto

lemma no_pat_zip_eq: "no_pat (zip_eq xs ys)"
  by (induction xs ys rule: zip_eq.induct) (auto intro!: pok_bindM)

lemma no_pat_mkabs: "no_pat (mkabs bs is t)"
  by (induction "is") (auto intro!: pok_bindM no_pat_nth split: prod.splits)

lemma no_pat_update_new: "no_pat (update_new kx t)"
  by (simp add: update_new_def)

lemma no_pat_update: "no_pat (update xT t env)"
  by (auto simp: update_def no_pat_update_new split: env.splits intro!: pok_bindM)

lemma no_pat_split_type: "no_pat (split_type T n Ts)"
  by (induction T n Ts rule: split_type.induct)
    (subst split_type.simps, auto split: ptyp.splits list.splits)

lemma no_pat_tvar_clash: "no_pat (tvar_clash v S S')"
  by (simp add: tvar_clash_def)

lemma no_pat_type_lookup: "no_pat (type_lookup \<theta> v S)"
  by (auto simp: type_lookup_def tvar_clash_def split: option.splits)

lemma no_pat_devar: "devar \<theta> T = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction \<theta> T r rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  have IH: "no_pat (dv \<theta>' U)" for \<theta>' U by (rule pok_IH) (rule 1(1))
  have "no_pat (case T of TVar ixn S \<Rightarrow> do {r \<leftarrow> type_lookup \<theta> ixn S; case r of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T}
      | _ \<Rightarrow> return T)"
    by (auto split: ptyp.splits option.splits intro!: pok_bindM no_pat_type_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma no_pat_devar': "no_pat (devar \<theta> T)"
  by (rule pok_IH) (rule no_pat_devar)

lemma no_pat_unified_aux: "unified_aux \<theta> T U = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction \<theta> T U r rule: unified_aux.raw_induct[rotated, consumes 1])
  case (1 ua \<theta> T U r)
  have IH: "no_pat (ua \<theta>' T' U')" for \<theta>' T' U' by (rule pok_IH) (rule 1(1))
  have "no_pat (do {
      V \<leftarrow> devar \<theta> T;
      V' \<leftarrow> devar \<theta> U;
      case (V, V') of
        (Type s Ts, Type s' Ts') \<Rightarrow>
          if s = s' then do {
            b \<leftarrow> allM (\<lambda>(T, T'). ua \<theta> T T') (zip Ts Ts');
            return (b \<and> length Ts = length Ts')}
          else return False
      | _ \<Rightarrow> return (V = V')
    })"
    by (auto split: ptyp.splits prod.splits intro!: pok_bindM pok_allM no_pat_devar' IH)
  then show ?case using 1(2) by simp
qed

lemma no_pat_unified: "no_pat (unified \<theta> T U)"
  by (auto simp: unified_def intro: pok_IH no_pat_unified_aux)

lemma no_pat_lookup: "no_pat (lookup env x T)"
  by (auto simp: lookup_def var_clash_def split: option.splits intro!: pok_bindM no_pat_unified)

lemma no_pat_head_norm: "head_norm env t = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction env t r rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have IH: "no_pat (hn env' t')" for env' t' by (rule pok_IH) (rule 1(1))
  have "no_pat (case t of
      Var xi T \<Rightarrow> do {r \<leftarrow> lookup env xi T; case r of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t}
    | Abs a T body \<Rightarrow> do {body' \<leftarrow> hn env body; return (Abs a T body')}
    | f $ u \<Rightarrow>
        (case f of
          Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> do {
            nf \<leftarrow> hn env f;
            case nf of
              Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
            | _ \<Rightarrow> return (nf $ u)})
    | _ \<Rightarrow> return t)"
    by (auto split: pterm.splits option.splits intro!: pok_bindM no_pat_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma no_pat_head_norm': "no_pat (head_norm env t)"
  by (rule pok_IH) (rule no_pat_head_norm)

lemma no_pat_norm_type_aux: "norm_type_aux \<theta> T = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction \<theta> T r rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nt \<theta> T r)
  have IH: "no_pat (nt \<theta>' U)" for \<theta>' U by (rule pok_IH) (rule 1(1))
  have "no_pat (case T of
      Type a Ts \<Rightarrow> do {Ts' \<leftarrow> mapM (nt \<theta>) Ts; return (Type a Ts')}
    | TFree _ _ \<Rightarrow> return T
    | TVar v S \<Rightarrow> do {r \<leftarrow> type_lookup \<theta> v S; case r of Some U \<Rightarrow> nt \<theta> U | None \<Rightarrow> return T})"
    by (auto split: ptyp.splits option.splits intro!: pok_bindM pok_mapM no_pat_type_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma no_pat_norm_type: "no_pat (norm_type \<theta> T)"
  by (auto simp: norm_type_def intro: pok_IH no_pat_norm_type_aux)

lemma no_pat_type_of_G: "no_pat (type_of_G env T n is)"
  unfolding type_of_G_def
proof (rule pok_bindM[OF no_pat_norm_type])
  fix T' show "no_pat (split_type T' n [] \<bind> (\<lambda>(Ts, U). mapM (nth Ts) is \<bind> (\<lambda>Us. return (foldr fun_type Us U))))"
    by (rule pok_bindM[OF no_pat_split_type]) (auto intro!: pok_bindM pok_mapM no_pat_nth)
qed

lemma no_pat_mk_ff_list: "no_pat (mk_ff_list is js)"
proof -
  have "no_pat (mk_ff_list_aux is js k)" for k
    by (induction "is" js k rule: mk_ff_list_aux.induct) (auto intro!: pok_bindM)
  then show ?thesis by (simp add: mk_ff_list_def)
qed

lemma no_pat_idx: "no_pat (idx xs j)"
  by (induction xs) auto

lemma no_pat_trans: "no_pat (trans xs d i)"
  by (auto simp: trans_def intro!: pok_bindM no_pat_idx)

lemma no_pat_try_trans: "no_pat (try_trans xs d i)"
  by (auto simp: try_trans_def intro!: pok_handle pok_bindM no_pat_idx)

lemma no_pat_occurs: "occurs F t env = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 oc F t env r)
  have IH: "no_pat (oc F' t' env')" for F' t' env' by (rule pok_IH) (rule 1(1))
  have "no_pat (case t of
      Var G T \<Rightarrow> do {r \<leftarrow> lookup env G T; case r of Some u \<Rightarrow> oc F u env | None \<Rightarrow> return (F = G)}
    | t1 $ t2 \<Rightarrow> do {b \<leftarrow> oc F t1 env; if b then return True else oc F t2 env}
    | Abs _ _ u \<Rightarrow> oc F u env
    | _ \<Rightarrow> return False)"
    by (auto split: pterm.splits option.splits intro!: pok_bindM no_pat_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma no_pat_occurs': "no_pat (occurs F t env)"
  by (rule pok_IH) (rule no_pat_occurs)

lemma no_pat_rigid_occurs: "rigid_occurs F t env = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction F t env r rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t env r)
  have IH: "no_pat (ro F' t' env')" for F' t' env' by (rule pok_IH) (rule 1(1))
  have hd: "no_pat (handle (do {_ \<leftarrow> ints_of' env ts; return True})
      (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e))" for ts
  proof (cases "ints_of' env ts")
    case (Some r)
    then show ?thesis by (cases r) (auto simp: handle_def bindM_def return_def split: exn.splits)
  qed (simp add: handle_def bindM_def)
  have "no_pat (do {
      t' \<leftarrow> head_norm env t;
      (case t' of
        Abs _ _ u \<Rightarrow> ro F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              Var G _ \<Rightarrow>
                if G = F then
                  handle (do {_ \<leftarrow> ints_of' env ts; return True})
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts)))
    })"
    by (auto split: pterm.splits prod.splits intro!: pok_bindM no_pat_head_norm' pok_existsM IH hd)
  then show ?case using 1(2) by simp
qed

lemma no_pat_rigid_occurs': "no_pat (rigid_occurs F t env)"
  by (rule pok_IH) (rule no_pat_rigid_occurs)

lemma no_pat_mg_domain: "no_pat (mg_domain alg' a S)"
  unfolding mg_domain_def Let_def
  by (auto split: list.splits option.splits intro!: pok_bindM pok_foldM)

lemma no_pat_mg_domain_unif: "no_pat (mg_domain_unif alg' a S)"
  unfolding mg_domain_unif_def
  by (rule pok_handle[OF no_pat_mg_domain]) (auto split: exn.splits)

lemma no_pat_type_occurs: "type_occurs v \<theta> T = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction v \<theta> T r rule: type_occurs.raw_induct[rotated, consumes 1])
  case (1 to v \<theta> T r)
  have IH: "no_pat (to v' \<theta>' U)" for v' \<theta>' U by (rule pok_IH) (rule 1(1))
  have "no_pat (case T of
      Type _ Ts \<Rightarrow> existsM (to v \<theta>) Ts
    | TFree _ _ \<Rightarrow> return False
    | TVar w S \<Rightarrow>
        if v = w then return True
        else do {r \<leftarrow> type_lookup \<theta> w S; case r of None \<Rightarrow> return False | Some U \<Rightarrow> to v \<theta> U})"
    by (auto split: ptyp.splits option.splits intro!: pok_bindM pok_existsM no_pat_type_lookup IH)
  then show ?case using 1(2) by simp
qed

lemma no_pat_type_occurs': "no_pat (type_occurs v \<theta> T)"
  by (rule pok_IH) (rule no_pat_type_occurs)

lemma no_pat_meet: "meet alg' T S st = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction alg' T S st r rule: meet.raw_induct[rotated, consumes 1])
  case (1 mt alg' T S st r)
  have IH: "no_pat (mt alg' T' S' st')" for T' S' st' by (rule pok_IH) (rule 1(1))
  have "no_pat (if S = [] then return st else
      let (tye, cnt) = st in
      case T of
        TVar xi S' \<Rightarrow>
          if sort_le alg' S' S then return st
          else do {
            let (V, cnt') = gen_tyvar (inter_sort alg' S' S) cnt;
            tye' \<leftarrow> update_new (xi, (S', V)) tye;
            return (tye', cnt')}
      | TFree _ S' \<Rightarrow> if sort_le alg' S' S then return st else raise TUnify
      | Type a Ts \<Rightarrow> do {
          Ss \<leftarrow> mg_domain_unif alg' a S;
          foldM (\<lambda>(T, S) st. do {T' \<leftarrow> devar (fst st) T; mt alg' T' S st}) (zip Ts Ss) st})"
    by (auto simp: Let_def split: ptyp.splits prod.splits
        intro!: pok_bindM pok_foldM no_pat_update_new no_pat_mg_domain_unif no_pat_devar' IH)
  then show ?case using 1(2) by simp
qed

lemma no_pat_meet': "no_pat (meet alg' T S st)"
  by (rule pok_IH) (rule no_pat_meet)

lemma no_pat_unify_aux: "unify_aux alg' T U st = Some r \<Longrightarrow> no_pat (Some r)"
proof (induction alg' T U st r rule: unify_aux.raw_induct[rotated, consumes 1])
  case (1 ua alg' ty1 ty2 st r)
  have IH: "no_pat (ua alg' T' U' st')" for T' U' st' by (rule pok_IH) (rule 1(1))
  have "no_pat (let (tye, cnt) = st in do {
      T \<leftarrow> devar tye ty1;
      U \<leftarrow> devar tye ty2;
      case (T, U) of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return st else tvar_clash v S1 S2)
          else if sort_le alg' S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T)) tye; return (tye', cnt)}
          else if sort_le alg' S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U)) tye; return (tye', cnt)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg' S1 S2) cnt;
            tye' \<leftarrow> update_new (w, (S2, S)) tye;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v tye U;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U)) tye; meet alg' U S (tye', cnt)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v tye T;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T)) tye; meet alg' T S (tye', cnt)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. ua alg' T U st) (zip Ts Us) st
      | _ \<Rightarrow> if T = U then return st else raise TUnify
    })"
    by (auto simp: Let_def split: ptyp.splits prod.splits
        intro!: pok_bindM pok_foldM no_pat_update_new no_pat_devar' no_pat_type_occurs' no_pat_meet'
          no_pat_tvar_clash IH)
  then show ?case using 1(2) by simp
qed

context pure_sig
begin

lemma no_pat_unify_types: "pok (\<lambda>env'. tenv env' = tenv env) (unify_types alg' T U env)"
proof (rule pok_okI)
  show "no_pat (unify_types alg' T U env)"
  proof -
    have "no_pat (type_unify alg' U T (tyenv env, maxidx env) \<bind>
        (\<lambda>(tye', maxidx'). return (Envir maxidx' (tenv env) tye')))"
      unfolding type_unify_def
      by (rule pok_bindM[OF pok_IH[OF no_pat_unify_aux]]) (simp_all split: prod.splits)
    then show ?thesis
      unfolding unify_types_def by (auto intro!: pok_handle split: exn.splits)
  qed
qed (rule unify_types_sound(1))


subsection \<open>Patterns\<close>

definition env_nonneg :: "env \<Rightarrow> bool" where
  "env_nonneg env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> bnds_nonneg u)"

text \<open>The invariant of the environment: closed patterns with non-negative bound variables.\<close>

definition env_pinv :: "env \<Rightarrow> bool" where
  "env_pinv env \<longleftrightarrow> env_ppat env \<and> closed_env env \<and> env_nonneg env"

lemma env_pinvD:
  assumes "env_pinv env" "vt_lookup (tenv env) x = Some (U, u)"
  shows "ppat u" "closed u" "bnds_nonneg u"
  using assms unfolding env_pinv_def env_ppat_def closed_env_def env_nonneg_def by blast+

lemma env_pinv_tenv: "tenv env' = tenv env \<Longrightarrow> env_pinv env' \<longleftrightarrow> env_pinv env"
  by (simp add: env_pinv_def env_ppat_def closed_env_def env_nonneg_def)

lemma env_pinv_update:
  assumes "ok (update (F, T) u env) env'" "env_pinv env" "ppat u" "closed u" "bnds_nonneg u"
  shows "env_pinv env'"
  using assms env_pinvD[OF assms(2)] unfolding env_pinv_def env_ppat_def closed_env_def env_nonneg_def
  by (auto simp: ok_update(2)[OF assms(1)] split: if_splits)

lemma rigid_atom: "rigid h \<Longrightarrow> atom h"
  by (simp add: rigid_iff)

lemma strip_comb_atom_apps: "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> strip_comb (h \<degree>\<degree> ts) = (h, ts)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (cases h) (auto simp: strip_comb_def)
next
  case (snoc t ts)
  then show ?case by (simp add: strip_comb_App)
qed

lemma ppat_nonAbsE:
  assumes "ppat t" "\<not> is_Abs t"
  obtains (rigid) h ts where "rigid h" "t = h \<degree>\<degree> ts" "\<forall>u\<in>set ts. ppat u"
  | (flex) x T "is" where "t = app (Var x T) is" "distinct is"
  using assms by (cases rule: ppat.cases) auto

lemma ppat_AppE:
  assumes "ppat (f $ u)"
  obtains (rigid) h ts where "rigid h" "f $ u = h \<degree>\<degree> ts" "\<forall>u\<in>set ts. ppat u"
  | (flex) x T iss i where "f = app (Var x T) iss" "u = Bound i" "distinct (iss @ [i])"
  using assms
proof (cases rule: ppat.cases)
  case (ppat_flex "is" x T)
  then obtain iss i where "is = iss @ [i]" by (cases "is" rule: rev_cases) (auto simp: app_apps)
  with ppat_flex show ?thesis using that(2) by (auto simp: app_apps)
qed (use that(1) in auto)

lemma ppat_redex: "\<not> ppat (Abs a T b $ u)"
proof
  assume "ppat (Abs a T b $ u)"
  then show False
  proof (cases rule: ppat_AppE)
    case (rigid h ts)
    then show False using rigid_atom[of h] by simp
  qed (simp add: app_apps)
qed

lemma ppat_abs_list: "ppat t \<Longrightarrow> ppat (abs_list bs t)"
proof (induction bs)
  case (Cons b bs)
  then show ?case by (cases b) (auto intro: ppat_Abs)
qed simp

lemma bnds_nonneg_abs_list [simp]: "bnds_nonneg (abs_list bs t) \<longleftrightarrow> bnds_nonneg t"
proof (induction bs)
  case (Cons b bs)
  then show ?case by (cases b) simp
qed simp

lemma bnds_nonneg_apps: "bnds_nonneg (s \<degree>\<degree> ts) \<longleftrightarrow> bnds_nonneg s \<and> (\<forall>t\<in>set ts. bnds_nonneg t)"
  by (induction ts arbitrary: s) auto

lemma bnds_nonneg_app: "bnds_nonneg (app (Var x T) is) \<longleftrightarrow> (\<forall>i\<in>set is. 0 \<le> i)"
  by (auto simp: app_apps bnds_nonneg_apps)

lemma loose_bvar1_app: "loose_bvar1 (app (Var x T) is) k \<longleftrightarrow> k \<in> set is"
  by (auto simp: app_apps loose_bvar1_apps)

lemma bnds_nonneg_incr_bv: "bnds_nonneg t \<Longrightarrow> 0 \<le> n \<Longrightarrow> bnds_nonneg (incr_bv n k t)"
  by (induction n k t rule: incr_bv.induct) auto

lemma bnds_nonneg_subst: "bnds_nonneg t \<Longrightarrow> bnds_nonneg s \<Longrightarrow> 0 \<le> k \<Longrightarrow> bnds_nonneg (t[s/k])"
proof (induction t arbitrary: s k)
  case (Abs a T t)
  then show ?case by (simp add: bnds_nonneg_incr_bv)
qed (auto simp: subst_Bound integer_arith)

lemma loose_bvar_loose_bvar1: "loose_bvar t n \<longleftrightarrow> (\<exists>k. n \<le> k \<and> loose_bvar1 t k)"
proof (induction t arbitrary: n)
  case (Abs a T t)
  have "(\<exists>k. n + 1 \<le> k \<and> loose_bvar1 t k) \<longleftrightarrow> (\<exists>k. n \<le> k \<and> loose_bvar1 t (k + 1))"
    by (metis add.commute add_le_cancel_left diff_add_cancel le_diff_eq)
  with Abs show ?case by simp
qed auto

text \<open>Lifting:\<close>

lemma lift_app: "lift (app (Var x T) is) d = app (Var x T) (map (\<lambda>i. if d \<le> i then i + 1 else i) is)"
  by (simp add: app_apps incr_bv_apps comp_def if_distrib)

lemma ppat_lift: "ppat t \<Longrightarrow> ppat (lift t d)"
proof (induction arbitrary: d rule: ppat.induct)
  case (ppat_Abs t a T)
  then show ?case by (auto intro: ppat.ppat_Abs)
next
  case (ppat_rigid h ts)
  have "rigid (lift h d)" using ppat_rigid.hyps(1) by (cases h) auto
  with ppat_rigid show ?case by (auto simp: incr_bv_apps intro!: ppat.ppat_rigid)
next
  case (ppat_flex "is" x T)
  have "inj_on (\<lambda>i. if d \<le> i then i + 1 else i) (set is)" by (auto simp: inj_on_def split: if_splits)
  with ppat_flex show ?case by (auto simp: lift_app distinct_map intro!: ppat.ppat_flex)
qed

lemma ppat_lift_Bound0:
  assumes "ppat t" "\<not> is_Abs t"
  shows "ppat (lift t 0 $ Bound 0)"
  using assms
proof (cases rule: ppat_nonAbsE)
  case (rigid h ts)
  have "rigid (lift h 0)" using rigid(1) by (cases h) auto
  then have "ppat (lift h 0 \<degree>\<degree> (map (\<lambda>t. lift t 0) ts @ [Bound 0]))"
    using rigid(3) ppat_lift ppat_atom[of "Bound 0"] by (intro ppat.ppat_rigid) auto
  moreover have "lift t 0 $ Bound 0 = lift h 0 \<degree>\<degree> (map (\<lambda>t. lift t 0) ts @ [Bound 0])"
    by (simp add: rigid(2) incr_bv_apps)
  ultimately show ?thesis by simp
next
  case (flex x T "is")
  let ?g = "\<lambda>i::integer. if 0 \<le> i then i + 1 else i"
  have "inj_on ?g (set is)" by (auto simp: inj_on_def split: if_splits)
  moreover have "0 \<notin> ?g ` set is" by auto
  ultimately have "distinct (map ?g is @ [0])" using flex(2) by (auto simp: distinct_map)
  then have "ppat (app (Var x T) (map ?g is @ [0]))" by (rule ppat_flex)
  moreover have "lift t 0 $ Bound 0 = app (Var x T) (map ?g is @ [0])"
    by (simp only: flex(1) lift_app) (simp add: app_def)
  ultimately show ?thesis by simp
qed

text \<open>Substitution of a bound variable:\<close>

lemma subst_apps: "(s \<degree>\<degree> ts)[u/k] = s[u/k] \<degree>\<degree> map (\<lambda>t. t[u/k]) ts"
  by (induction ts arbitrary: s) auto

lemma subst_app:
  "(app (Var x T) is)[Bound j/k] = app (Var x T) (map (\<lambda>i. if k < i then i - 1 else if i = k then j else i) is)"
  by (simp add: app_apps subst_apps comp_def subst_Bound)

lemma ppat_subst:
  "ppat t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> 0 \<le> y \<Longrightarrow> \<not> loose_bvar1 t (y + lev + 1) \<Longrightarrow> ppat (t[Bound (y + lev)/lev])"
proof (induction arbitrary: lev rule: ppat.induct)
  case (ppat_Abs t a T)
  have "ppat (t[Bound (y + (lev + 1))/lev + 1])"
    using ppat_Abs.prems by (intro ppat_Abs.IH) (simp_all add: algebra_simps)
  with ppat_Abs.prems show ?case by (auto simp: algebra_simps intro: ppat.ppat_Abs)
next
  case (ppat_rigid h ts)
  have "rigid (h[Bound (y + lev)/lev])" using ppat_rigid.hyps(1) by (cases h) (auto simp: subst_Bound)
  moreover have "ppat (t[Bound (y + lev)/lev])" if "t \<in> set ts" for t
    using ppat_rigid.IH that ppat_rigid.prems by (auto simp: loose_bvar1_apps)
  ultimately show ?case by (auto simp: subst_apps intro!: ppat.ppat_rigid)
next
  case (ppat_flex "is" x T)
  let ?g = "\<lambda>i. if lev < i then i - 1 else if i = lev then y + lev else i"
  have nin: "y + lev + 1 \<notin> set is" using ppat_flex.prems(3) by (simp add: loose_bvar1_app)
  have "inj_on ?g (set is)"
  proof (rule inj_onI)
    fix i j assume "i \<in> set is" "j \<in> set is" "?g i = ?g j"
    moreover have "\<forall>k\<in>set is. k \<noteq> y + lev + 1" using nin by blast
    ultimately show "i = j" using ppat_flex.prems(1,2) by (auto split: if_splits simp: integer_arith)
  qed
  with ppat_flex.hyps have "ppat (app (Var x T) (map ?g is))" by (intro ppat.ppat_flex) (simp add: distinct_map)
  then show ?case by (simp add: subst_app)
qed

lemma vars_subst_ge: "vars t \<subseteq> vars (t[s/k])"
proof (induction t arbitrary: s k)
  case (App t1 t2)
  have "vars t1 \<subseteq> vars (t1[s/k])" "vars t2 \<subseteq> vars (t2[s/k])" by (rule App.IH(1), rule App.IH(2))
  then show ?case by auto
next
  case (Abs a T t)
  then show ?case using Abs.IH[of "lift s 0" "k + 1"] by simp
qed auto


subsection \<open>Occurrences of unbound variables reachable through bindings\<close>

definition occt :: "env \<Rightarrow> indexname \<Rightarrow> pterm \<Rightarrow> bool" where
  "occt env F t \<longleftrightarrow> vt_lookup (tenv env) F = None \<and> (\<exists>y\<in>fst ` vars t. (F, y) \<in> (dep env)\<^sup>*)"

lemma occt_mono: "occt env F t \<Longrightarrow> vars t \<subseteq> vars t' \<Longrightarrow> occt env F t'"
  unfolding occt_def by blast

lemma occt_simps [simp]:
  "occt env F (s $ t) \<longleftrightarrow> occt env F s \<or> occt env F t" "occt env F (Abs a T t) \<longleftrightarrow> occt env F t"
  "occt env F (Bound i) \<longleftrightarrow> False" "occt env F (Const c T) \<longleftrightarrow> False" "occt env F (Free c T) \<longleftrightarrow> False"
  by (auto simp: occt_def)

lemma occt_apps: "occt env F (h \<degree>\<degree> ts) \<longleftrightarrow> occt env F h \<or> (\<exists>u\<in>set ts. occt env F u)"
  by (induction ts arbitrary: h) auto

lemma occt_Var_bound:
  assumes lk: "vt_lookup (tenv env) y = Some (U, u)"
  shows "occt env F (Var y T) \<longleftrightarrow> occt env F u"
proof
  assume "occt env F (Var y T)"
  then have F: "vt_lookup (tenv env) F = None" and Fy: "(F, y) \<in> (dep env)\<^sup>*" by (simp_all add: occt_def)
  from Fy show "occt env F u"
  proof (cases rule: rtranclE)
    case base
    with F lk show ?thesis by simp
  next
    case (step z)
    from step(2) obtain U' u' T' where "vt_lookup (tenv env) y = Some (U', u')" "(z, T') \<in> vars u'"
      by (rule depE)
    with lk have "(z, T') \<in> vars u" by simp
    then have "z \<in> fst ` vars u" by force
    with step(1) F show ?thesis unfolding occt_def by blast
  qed
next
  assume "occt env F u"
  then obtain z T' where F: "vt_lookup (tenv env) F = None" and z: "(z, T') \<in> vars u" "(F, z) \<in> (dep env)\<^sup>*"
    by (auto simp: occt_def)
  have "(z, y) \<in> dep env" by (rule depI[OF lk z(1)])
  with z(2) F show "occt env F (Var y T)" by (simp add: occt_def)
qed

lemma occt_Var_unbound: "vt_lookup (tenv env) y = None \<Longrightarrow> occt env F (Var y T) \<longleftrightarrow> F = y"
  by (auto simp: occt_def elim: rtranclE elim!: depE)

lemma occurs_occt:
  assumes "occurs F t env = Some r"
  shows "r = Ok True \<Longrightarrow> occt env F t"
  using assms
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 oc F t env r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "occt env F u" if "ok (oc F u env) True" for u using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var G T)
    with h obtain lr where lr: "ok (lookup env G T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> oc F u env | None \<Rightarrow> return (F = G)) True"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest lr Var show ?thesis by (simp add: ok_lookup_None occt_Var_unbound)
    next
      case (Some u)
      with lr obtain U where "vt_lookup (tenv env) G = Some (U, u)" by (auto elim: ok_lookup_Some)
      with IH[of u] rest Some Var show ?thesis by (simp add: occt_Var_bound)
    qed
  next
    case (App t1 t2)
    with h obtain b where "ok (oc F t1 env) b" "ok (if b then return True else oc F t2 env) True" by auto
    with IH App show ?thesis by (cases b) auto
  qed (use h IH in auto)
qed


subsection \<open>Head normalization of patterns\<close>

lemma head_norm_ppat:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> env_pinv env \<Longrightarrow> ppat t \<Longrightarrow> bnds_nonneg t \<Longrightarrow>
    ppat t' \<and> bnds_nonneg t' \<and> (\<forall>k\<ge>0. loose_bvar1 t' k \<longrightarrow> loose_bvar1 t k) \<and>
    (occt env F t \<longrightarrow> occt env F t') \<and> (\<forall>h ts. rigid h \<longrightarrow> t = h \<degree>\<degree> ts \<longrightarrow> t' = t)"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ei = "1.prems"(2) and pt = "1.prems"(3)
    and nt = "1.prems"(4)
  have IH: "ppat u' \<and> bnds_nonneg u' \<and> (\<forall>k\<ge>0. loose_bvar1 u' k \<longrightarrow> loose_bvar1 u k) \<and>
      (occt env F u \<longrightarrow> occt env F u') \<and> (\<forall>h ts. rigid h \<longrightarrow> u = h \<degree>\<degree> ts \<longrightarrow> u' = u)"
    if "ok (hn env u) u'" "ppat u" "bnds_nonneg u" for u u'
    using "1.IH"[OF that(1) refl ei that(2,3)] .
  show ?case
  proof (cases t)
    case (Var x T)
    have nr: "\<forall>h ts. rigid h \<longrightarrow> t \<noteq> h \<degree>\<degree> ts"
      using Var atom_eq_apps_conv[of "Var x T"] by auto
    from h Var obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest pt nt show ?thesis by simp
    next
      case (Some u)
      with lr obtain U where lk: "vt_lookup (tenv env) x = Some (U, u)" by (auto elim: ok_lookup_Some)
      note u = env_pinvD[OF ei lk]
      from IH[of u t'] rest Some u(1,3) have "ppat t'" "bnds_nonneg t'"
        "\<forall>k\<ge>0. loose_bvar1 t' k \<longrightarrow> loose_bvar1 u k" "occt env F u \<longrightarrow> occt env F t'"
        by simp_all
      with closed_loose_bvar1[OF u(2)] occt_Var_bound[OF lk] nr Var show ?thesis by auto
    qed
  next
    case (Abs a T body)
    have nr: "\<forall>h ts. rigid h \<longrightarrow> t \<noteq> h \<degree>\<degree> ts" using Abs by auto
    from h Abs obtain body' where hb: "ok (hn env body) body'" and t': "t' = Abs a T body'" by auto
    have pb: "ppat body" using pt Abs by (simp add: ppat_AbsD)
    from IH[OF hb pb] nt Abs have "ppat body'" "bnds_nonneg body'"
      "\<forall>k\<ge>0. loose_bvar1 body' k \<longrightarrow> loose_bvar1 body k" "occt env F body \<longrightarrow> occt env F body'"
      by simp_all
    with t' Abs nr show ?thesis by (auto intro: ppat_Abs simp: integer_arith)
  next
    case (App f u)
    from pt[unfolded App] show ?thesis
    proof (cases rule: ppat_AppE)
      case (rigid h0 ts0)
      from rigid(2) obtain ts' where f: "f = h0 \<degree>\<degree> ts'" and ts0: "ts0 = ts' @ [u]"
        using rigid_atom[OF rigid(1)] by (cases ts0 rule: rev_cases) auto
      have nA: "\<not> is_Abs f" using f rigid_atom[OF rigid(1)] by (simp add: not_is_Abs_atom_apps)
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      have "ppat f" using rigid(1,3) ts0 f by (auto intro: ppat_rigid)
      with IH[OF nf] nt App rigid(1) f have "nf = f" by auto
      with rest nA have "t' = t" using App by (cases f) auto
      with pt nt show ?thesis by simp
    next
      case (flex x T iss i)
      have nr: "\<forall>h ts. rigid h \<longrightarrow> t \<noteq> h \<degree>\<degree> ts"
      proof (intro allI impI)
        fix h ts assume "rigid h"
        have t: "t = Var x T \<degree>\<degree> map Bound (iss @ [i])" using App flex(1,2) by (simp add: app_apps)
        have "atom (Var x T)" "atom h" using rigid_atom[OF \<open>rigid h\<close>] by simp_all
        note c = atom_apps_eq_atom_apps_conv[OF this]
        show "t \<noteq> h \<degree>\<degree> ts"
        proof
          assume "t = h \<degree>\<degree> ts"
          with t c have "Var x T = h" by blast
          with \<open>rigid h\<close> show False by auto
        qed
      qed
      have nA: "\<not> is_Abs f" using flex(1) by (simp add: app_apps not_is_Abs_atom_apps)
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      have pf: "ppat f" using flex(1,3) by (auto intro: ppat_flex)
      have nf0: "bnds_nonneg f" "0 \<le> i" using nt App flex(2) by simp_all
      from IH[OF nf pf nf0(1)] have pnf: "ppat nf" and nnf: "bnds_nonneg nf"
        and lnf: "\<forall>k\<ge>0. loose_bvar1 nf k \<longrightarrow> k \<in> set iss" and onf: "occt env F f \<longrightarrow> occt env F nf"
        by (simp_all add: flex(1) loose_bvar1_app)
      have ni: "i \<notin> set iss" using flex(3) by simp
      have lt: "loose_bvar1 t k \<longleftrightarrow> k = i \<or> k \<in> set iss" for k
        using App flex(1,2) by (auto simp: loose_bvar1_app)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfA: "nf = Abs b U0 body" by (cases nf) auto
        with rest have hb: "ok (hn env (body[Bound i/0])) t'" by (simp add: subst_bound_subst flex(2))
        have pb: "ppat body" using pnf nfA by (simp add: ppat_AbsD)
        have "\<not> loose_bvar1 body (i + 0 + 1)" using lnf nfA ni nf0(2) by auto
        then have ps: "ppat (body[Bound i/0])" using ppat_subst[OF pb _ nf0(2), of 0] by simp
        have ns: "bnds_nonneg (body[Bound i/0])" using nnf nfA nf0(2) by (simp add: bnds_nonneg_subst)
        from IH[OF hb ps ns] have r: "ppat t'" "bnds_nonneg t'"
          "\<forall>k\<ge>0. loose_bvar1 t' k \<longrightarrow> loose_bvar1 (body[Bound i/0]) k"
          "occt env F (body[Bound i/0]) \<longrightarrow> occt env F t'"
          by simp_all
        have "loose_bvar1 t k" if "0 \<le> k" "loose_bvar1 (body[Bound i/0]) k" for k
          using that lnf nfA lt by (auto simp: integer_arith)
        moreover have "occt env F t \<Longrightarrow> occt env F t'"
          using r(4) onf nfA App flex(2) occt_mono[OF _ vars_subst_ge] by auto
        ultimately show ?thesis using r(1-3) nr by blast
      next
        case False
        with rest have t': "t' = nf $ Bound i" using flex(2) by (cases nf) auto
        have "ppat t'"
          using pnf False
        proof (cases rule: ppat_nonAbsE)
          case (rigid h ts)
          then show ?thesis using t' ppat_atom[of "Bound i"] ppat_rigid[of h "ts @ [Bound i]"] by auto
        next
          case (flex y V jss)
          have "i \<notin> set jss" using lnf flex(1) ni nf0(2) by (auto simp: loose_bvar1_app)
          then have "ppat (app (Var y V) (jss @ [i]))" using flex(2) by (intro ppat.ppat_flex) simp
          then show ?thesis using t' flex(1) by (simp add: app_def)
        qed
        moreover have "bnds_nonneg t'" using t' nnf nf0(2) by simp
        moreover have "\<forall>k\<ge>0. loose_bvar1 t' k \<longrightarrow> loose_bvar1 t k" using t' lnf lt by auto
        moreover have "occt env F t \<longrightarrow> occt env F t'" using t' onf App flex(2) by auto
        ultimately show ?thesis using nr by blast
      qed
    qed
  qed (use h pt nt in auto)
qed

lemma ints_of'_Bounds: "distinct is \<Longrightarrow> ints_of' env (map Bound is) = return is"
proof -
  assume d: "distinct is"
  have "mapM (head_norm env) (map Bound is) = return (map Bound is)"
    by (induction "is") (simp_all, subst head_norm.simps, simp)
  moreover have "ints_of (map Bound is) = return is" using ok_ints_of[of "map Bound is" "is"] d
    by (simp add: return_def)
  ultimately show ?thesis by (simp add: ints_of'_def)
qed


subsection \<open>The occurs check on patterns\<close>

lemma existsM_FalseD: "existsM P xs = Some (Ok False) \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x = Some (Ok False)"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits res.splits if_splits)

text \<open>In a pattern, every occurrence of an unbound variable reachable through bindings is rigid:\<close>

lemma rigid_occurs_ppat:
  assumes "rigid_occurs F t env = Some r"
  shows "r = Ok b \<Longrightarrow> env_pinv env \<Longrightarrow> ppat t \<Longrightarrow> bnds_nonneg t \<Longrightarrow> occt env F t \<Longrightarrow> b"
  using assms
proof (induction F t env r arbitrary: b rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t env r)
  note ei = "1.prems"(2)
  have IH: "b'" if "ok (ro F u env) b'" "ppat u" "bnds_nonneg u" "occt env F u" for u b'
    using "1.IH"[OF that(1) refl ei that(2-4)] .
  define B where "B = (\<lambda>t'. case t' of
        Abs _ _ u \<Rightarrow> ro F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              Var G _ \<Rightarrow>
                if G = F then
                  handle (ints_of' env ts \<bind> (\<lambda>_. return True))
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts)))"
  from "1.hyps" "1.prems"(1) have "ok (head_norm env t \<bind> B) b" by (simp add: B_def)
  then obtain t' where hn: "ok (head_norm env t) t'" and Bt: "ok (B t') b" by auto
  from head_norm_ppat[OF hn refl ei "1.prems"(3,4), of F] "1.prems"(5)
  have pt': "ppat t'" and nt': "bnds_nonneg t'" and ot': "occt env F t'" by simp_all
  show "b"
  proof (cases "is_Abs t'")
    case True
    then obtain a T u where t': "t' = Abs a T u" by (cases t') auto
    from Bt t' have "ok (ro F u env) b" by (simp add: B_def)
    moreover have "ppat u" using pt' t' by (simp add: ppat_AbsD)
    ultimately show ?thesis using IH nt' ot' t' by simp
  next
    case nA: False
    from pt' nA show ?thesis
    proof (cases rule: ppat_nonAbsE)
      case (rigid h ts)
      have sc: "strip_comb t' = (h, ts)"
        using rigid(1,2) rigid_atom[OF rigid(1)] by (simp add: strip_comb_atom_apps)
      have ex: "ok (existsM (\<lambda>u. ro F u env) ts) b"
        using Bt sc nA rigid(1) unfolding B_def by (cases t'; cases h) simp_all
      have "occt env F h \<longleftrightarrow> False" using rigid(1) by (cases h) simp_all
      with ot' rigid(2) obtain u where u: "u \<in> set ts" "occt env F u" by (auto simp: occt_apps)
      have "ppat u" "bnds_nonneg u" using rigid(2,3) nt' u(1) by (auto simp: bnds_nonneg_apps)
      show ?thesis
      proof (rule ccontr)
        assume "\<not> b"
        with ex have "ok (existsM (\<lambda>u. ro F u env) ts) False" by simp
        from existsM_FalseD[OF this u(1)] have "ok (ro F u env) False" .
        from IH[OF this \<open>ppat u\<close> \<open>bnds_nonneg u\<close> u(2)] show False .
      qed
    next
      case (flex x T "is")
      have sc: "strip_comb t' = (Var x T, map Bound is)"
        using flex(1) by (simp add: app_apps strip_comb_atom_apps)
      have "vt_lookup (tenv env) x = None" using head_norm_Var_head[OF hn refl] sc by simp
      with ot' flex(1) have Fx: "F = x" by (auto simp: app_apps occt_apps occt_Var_unbound)
      have "B t' = handle (ints_of' env (map Bound is) \<bind> (\<lambda>_. return True))
            (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)"
        using sc nA Fx unfolding B_def by (cases t') simp_all
      also have "\<dots> = return True" using ints_of'_Bounds[OF flex(2)] by simp
      finally show ?thesis using Bt by (simp add: return_def)
    qed
  qed
qed

text \<open>Hence the occurs check never gives up on patterns:\<close>

lemma occurs_rigid_occurs_ppat:
  assumes "ok (occurs F t env) True" "ok (rigid_occurs F t env) b"
    and "env_pinv env" "ppat t" "bnds_nonneg t"
  shows b
  using rigid_occurs_ppat[OF assms(2) refl assms(3-5) occurs_occt[OF assms(1) refl]] .


subsection \<open>New bindings of flex-flex problems\<close>

lemma binding_pat:
  assumes "ok (mkabs bs is (app (Var x T) ks)) u" "distinct ks" "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength is"
  shows "ppat u" "closed u" "bnds_nonneg u"
proof -
  from assms(1) have u: "u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (app (Var x T) ks)"
    by (simp add: ok_mkabs)
  show "ppat u" unfolding u by (rule ppat_abs_list[OF ppat_flex[OF assms(2)]])
  show "closed u" unfolding u using assms(3) by (intro closed_abs_list) (simp add: loose_bvar_app_Var)
  show "bnds_nonneg u" unfolding u using assms(3) by (simp add: bnds_nonneg_app)
qed

lemma idx_binding_pat:
  assumes "ok (mapM (idx xs) ys) ks" "distinct ys" "ok (mkabs bs xs (app (Var x T) ks)) u"
  shows "ppat u" "closed u" "bnds_nonneg u"
proof -
  note k = ok_mapM_idx[OF assms(1)]
  have "distinct ks" using k assms(2) by (auto simp: distinct_map)
  with binding_pat[OF assms(3) this] k show "ppat u" "closed u" "bnds_nonneg u" by simp_all
qed

lemma env_pinv_genvar: "genvar a env T = (env', G) \<Longrightarrow> env_pinv env' \<longleftrightarrow> env_pinv env"
  by (rule env_pinv_tenv[OF genvar_simps(1)])

lemma mk_new_hnf_pinv:
  assumes "env_pinv env" "distinct ks" "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength is"
  shows "pok env_pinv (mk_new_hnf env bs is F T ks)"
  unfolding mk_new_hnf_def
proof (rule pok_bindM[OF no_pat_type_of_G])
  fix Gty
  obtain env1 G where g: "genvar (fst F) env Gty = (env1, G)" by force
  have "pok env_pinv (mk_hnf bs is G ks \<bind> (\<lambda>t. update (F, T) t env1))"
  proof (rule pok_bindM[OF no_pat_mkabs[of bs "is" "app G ks", folded mk_hnf_def]])
    fix t assume t: "ok (mk_hnf bs is G ks) t"
    note b = binding_pat[OF t[unfolded mk_hnf_def genvar_simps(4)[OF g]] assms(2,3)]
    show "pok env_pinv (update (F, T) t env1)"
      by (rule pok_okI[OF no_pat_update])
        (use env_pinv_update b assms(1) env_pinv_genvar[OF g] in blast)
  qed
  then show "pok env_pinv (let (env', G) = genvar (fst F) env Gty in
      mk_hnf bs is G ks \<bind> (\<lambda>t. update (F, T) t env'))" by (simp add: g)
qed

lemma sorted_gt_distinct: "sorted_wrt (>) xs \<Longrightarrow> distinct (xs :: integer list)"
  by (induction xs) auto

lemma mk_ff_list_aux_sorted:
  "ok (mk_ff_list_aux is js k) ks \<Longrightarrow> sorted_wrt (>) ks \<and> (\<forall>k'\<in>set ks. k' \<le> k)"
proof (induction "is" js k arbitrary: ks rule: mk_ff_list_aux.induct)
  case (2 i "is" j js k)
  then show ?case by (cases "i = j") (fastforce simp: integer_arith)+
qed auto

lemma flexflex1_pinv:
  assumes ei: "env_pinv env"
  shows "pok env_pinv (flexflex1 env bs F Fty is js)"
proof (cases "is = js")
  case False
  have "pok env_pinv (mk_ff_list is js \<bind> mk_new_hnf env bs is F Fty)"
  proof (rule pok_bindM[OF no_pat_mk_ff_list])
    fix ks assume ks: "ok (mk_ff_list is js) ks"
    have "distinct ks" using mk_ff_list_aux_sorted[OF ks[unfolded mk_ff_list_def]] sorted_gt_distinct
      by blast
    then show "pok env_pinv (mk_new_hnf env bs is F Fty ks)"
      using mk_new_hnf_pinv[OF ei] ok_mk_ff_list(2)[OF ks] by blast
  qed
  with False show ?thesis by (simp add: flexflex1_def)
qed (simp add: flexflex1_def ei)

lemma no_pat_ff: "no_pat (ff env bs F Fty is G Gty js)"
  by (auto simp: ff_def Let_def split: prod.splits
      intro!: pok_bindM pok_mapM no_pat_idx no_pat_mkabs no_pat_update no_pat_type_of_G)

lemma ff_pinv:
  assumes "env_pinv env" "distinct is" "distinct js"
  shows "pok env_pinv (ff env bs F Fty is G Gty js)"
proof (rule pok_okI[OF no_pat_ff])
  fix env' assume ff: "ok (ff env bs F Fty is G Gty js) env'"
  show "env_pinv env'"
  proof (cases "subset js is")
    case True
    with ff obtain ks u where ks: "ok (mapM (idx is) js) ks"
      and u: "ok (mkabs bs is (app (Var G Gty) ks)) u" and upd: "ok (update (F, Fty) u env) env'"
      by (auto simp: ff_def)
    from env_pinv_update[OF upd assms(1) idx_binding_pat[OF ks assms(3) u]] show ?thesis .
  next
    case False
    let ?ks = "inter js is"
    have dks: "distinct ?ks" using assms(2) by (simp add: inter_def)
    from False ff obtain ksF Hty where
      ksF: "ok (mapM (idx is) ?ks) ksF" and Hty: "ok (type_of_G env Fty (ilength is) ksF) Hty"
      and rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
        (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs bs js (app H ks'))) \<bind> (\<lambda>tG.
        (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs bs is (app H ks'))) \<bind> (\<lambda>tF.
        update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env'"
      by (auto simp: ff_def Let_def)
    obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
    with rest obtain ksG tG tF env2 where ksG: "ok (mapM (idx js) ?ks) ksG"
      and tG: "ok (mkabs bs js (app H ksG)) tG"
      and tF: "ok (mkabs bs is (app H ksF)) tF"
      and upd1: "ok (update (F, Fty) tF env1) env2" and upd2: "ok (update (G, Gty) tG env2) env'"
      using ksF by auto
    note g = genvar_simps[OF H]
    have e1: "env_pinv env1" using assms(1) env_pinv_genvar[OF H] by simp
    have e2: "env_pinv env2"
      by (rule env_pinv_update[OF upd1 e1 idx_binding_pat[OF ksF dks tF[unfolded g(4)]]])
    show ?thesis by (rule env_pinv_update[OF upd2 e2 idx_binding_pat[OF ksG dks tG[unfolded g(4)]]])
  qed
qed

lemma flexflex2_pinv:
  "env_pinv env \<Longrightarrow> distinct is \<Longrightarrow> distinct js \<Longrightarrow> pok env_pinv (flexflex2 env bs F Fty is G Gty js)"
  by (simp add: flexflex2_def ff_pinv)


subsection \<open>Projection\<close>

lemma head_norm_pok:
  assumes "env_pinv env" "ppat t" "bnds_nonneg t"
  shows "pok (\<lambda>t'. ppat t' \<and> bnds_nonneg t' \<and> (\<forall>k\<ge>0. loose_bvar1 t' k \<longrightarrow> loose_bvar1 t k))
    (head_norm env t)"
  by (rule pok_okI[OF no_pat_head_norm']) (use head_norm_ppat[OF _ refl assms] in blast)

lemma mapAccM_pinv:
  assumes "\<And>s env. s \<in> set ss \<Longrightarrow> env_pinv env \<Longrightarrow>
      pok (\<lambda>(u, env'). env_pinv env' \<and> ppat u \<and> bnds_nonneg u) (f s env)"
    and "env_pinv env"
  shows "pok (\<lambda>(us, env'). env_pinv env' \<and> (\<forall>u\<in>set us. ppat u \<and> bnds_nonneg u)) (mapAccM f ss env)"
  using assms
proof (induction ss arbitrary: env)
  case (Cons s ss)
  show ?case unfolding mapAccM.simps
  proof (rule pok_bindM[OF Cons.prems(1)[OF _ Cons.prems(2)]], simp, clarify)
    fix u env1 assume "env_pinv env1" "ppat u" "bnds_nonneg u"
    with Cons.IH[of env1] Cons.prems(1)
    show "pok (\<lambda>(us, env'). env_pinv env' \<and> (\<forall>u\<in>set us. ppat u \<and> bnds_nonneg u))
        (mapAccM f ss env1 \<bind> (\<lambda>(ys, s2). return (u # ys, s2)))"
      by (auto intro!: pok_bindM)
  qed
qed simp

lemma ok_trans_inj:
  assumes "ok (trans xs d z1) l" "ok (trans xs d z2) l" "0 \<le> d" "0 \<le> z1" "0 \<le> z2"
  shows "z1 = z2"
proof (cases "l < d")
  case True
  with ok_trans(2)[OF assms(1,3,4)] ok_trans(2)[OF assms(2,3,5)] show ?thesis by simp
next
  case False
  with ok_trans(3)[OF assms(1,3,4)] ok_trans(3)[OF assms(2,3,5)] show ?thesis by simp
qed

lemma map_filter_id_simps:
  "List.map_filter id [] = []"
  "List.map_filter id (None # os) = List.map_filter id os"
  "List.map_filter id (Some l # os) = l # List.map_filter id os"
  by (simp_all add: List.map_filter_def)

lemma try_trans_distinct:
  "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) zs os \<Longrightarrow> distinct zs \<Longrightarrow> \<forall>z\<in>set zs. 0 \<le> z \<Longrightarrow>
    0 \<le> d \<Longrightarrow> distinct (List.map_filter id os) \<and>
    (\<forall>l\<in>set (List.map_filter id os). \<exists>z\<in>set zs. ok (trans xs d z) l)"
  unfolding id_def
proof (induction zs arbitrary: os)
  note mf = map_filter_id_simps[unfolded id_def]
  case Nil
  then show ?case by (simp add: mf)
next
  case (Cons z zs)
  from Cons.prems(1) obtain opt os' where os: "os = opt # os'" "ok (try_trans xs d z) opt"
    "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) zs os'"
    by (cases os) auto
  note mf = map_filter_id_simps[unfolded id_def]
  from Cons.IH[OF os(3)] Cons.prems(2-4) have IH: "distinct (List.map_filter (\<lambda>x. x) os')"
    "\<forall>l\<in>set (List.map_filter (\<lambda>x. x) os'). \<exists>z\<in>set zs. ok (trans xs d z) l" by simp_all
  show ?case
  proof (cases opt)
    case None
    then show ?thesis using IH os by (simp add: mf)
  next
    case (Some l)
    have tl: "ok (trans xs d z) l" using os(2) Some by (simp add: ok_try_trans)
    have "l \<notin> set (List.map_filter (\<lambda>x. x) os')"
    proof
      assume "l \<in> set (List.map_filter (\<lambda>x. x) os')"
      with IH(2) obtain z' where "z' \<in> set zs" "ok (trans xs d z') l" by blast
      with ok_trans_inj[OF tl _ Cons.prems(4)] Cons.prems(2,3) show False by auto
    qed
    with IH tl Some os show ?thesis by (auto simp: mf)
  qed
qed

lemma mk_proj_list_aux_sorted:
  "sorted_wrt (>) (mk_proj_list_aux os j) \<and> (\<forall>k\<in>set (mk_proj_list_aux os j). k \<le> j)"
proof (induction os j rule: mk_proj_list_aux.induct)
  case (1 i "is" j)
  then have IH: "sorted_wrt (>) (mk_proj_list_aux is (j - 1))"
    "\<forall>k\<in>set (mk_proj_list_aux is (j - 1)). k \<le> j - 1" by (cases i; simp)+
  then have "\<forall>k\<in>set (mk_proj_list_aux is (j - 1)). k < j \<and> k \<le> j" by (auto simp: integer_arith)
  with IH show ?case by auto
qed simp

lemma pr_pinv:
  assumes "pr xs s env d bs = Some r"
  shows "env_pinv env \<Longrightarrow> ppat s \<Longrightarrow> bnds_nonneg s \<Longrightarrow> 0 \<le> d \<Longrightarrow> \<forall>x\<in>set xs. 0 \<le> x \<Longrightarrow>
    pok (\<lambda>(u, env'). env_pinv env' \<and> ppat u \<and> bnds_nonneg u) (Some r)"
  using assms
proof (induction xs s env d bs r rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d bs r)
  note ei = "1.prems"(1) and d = "1.prems"(4) and xs0 = "1.prems"(5)
  let ?P = "\<lambda>(u, env'). env_pinv env' \<and> ppat u \<and> bnds_nonneg u"
  have IH: "pok ?P (prr xs s1 env1 d1 bs1)"
    if "env_pinv env1" "ppat s1" "bnds_nonneg s1" "0 \<le> d1" for s1 env1 d1 bs1
    by (rule pok_IH) (rule "1.IH"[OF _ that xs0])
  have "pok ?P (head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs))"
  proof (rule pok_bindM[OF head_norm_pok[OF ei "1.prems"(2,3)]], clarify)
    fix s' assume ps': "ppat s'" and ns': "bnds_nonneg s'"
    show "pok ?P (pr_step prr xs s' env d bs)"
    proof (cases "is_Abs s'")
      case True
      then obtain a T t where s': "s' = Abs a T t" by (cases s') auto
      have "pok ?P (prr xs t env (d + 1) ((a, T) # bs) \<bind> (\<lambda>(t', env'). return (Abs a T t', env')))"
        using ps' ns' s' d ei by (auto intro!: pok_bindM[OF IH] ppat_Abs simp: ppat_AbsD)
      then show ?thesis by (simp add: pr_step_def s')
    next
      case nA: False
      from ps' nA show ?thesis
      proof (cases rule: ppat_nonAbsE)
        case (rigid h ts)
        have sc: "strip_comb s' = (h, ts)"
          using rigid(1,2) rigid_atom[OF rigid(1)] by (simp add: strip_comb_atom_apps)
        have nh: "\<not> is_Var h" "\<not> is_Abs h" using rigid(1) by (cases h; simp)+
        let ?h = "case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h"
        have eq: "pr_step prr xs s' env d bs = ?h \<bind> (\<lambda>h'.
            mapAccM (\<lambda>s env. prr xs s env d bs) ts env \<bind> (\<lambda>(ts', env'). return (list_comb h' ts', env')))"
          using nA sc nh by (simp add: pr_step_def)
        have hp: "pok (\<lambda>h'. rigid h' \<and> bnds_nonneg h') ?h"
        proof (cases h)
          case (Bound i)
          have "0 \<le> i" using ns' rigid(2) Bound by (simp add: bnds_nonneg_apps)
          then show ?thesis using Bound d
            by (auto intro!: pok_bindM[OF no_pat_trans] dest: ok_trans(1))
        qed (use rigid(1) in simp_all)
        have tsp: "\<forall>u\<in>set ts. ppat u \<and> bnds_nonneg u" using rigid(3) ns' rigid(2) by (simp add: bnds_nonneg_apps)
        have "pok ?P (?h \<bind> (\<lambda>h'.
            mapAccM (\<lambda>s env. prr xs s env d bs) ts env \<bind> (\<lambda>(ts', env'). return (list_comb h' ts', env'))))"
        proof (rule pok_bindM[OF hp], elim conjE)
          fix h' assume h': "rigid h'" "bnds_nonneg h'"
          have m: "pok (\<lambda>(us, env'). env_pinv env' \<and> (\<forall>u\<in>set us. ppat u \<and> bnds_nonneg u))
              (mapAccM (\<lambda>s env. prr xs s env d bs) ts env)"
            by (rule mapAccM_pinv[OF _ ei]) (use IH tsp d in blast)
          show "pok ?P (mapAccM (\<lambda>s env. prr xs s env d bs) ts env \<bind>
              (\<lambda>(ts', env'). return (list_comb h' ts', env')))"
            using h' by (auto intro!: pok_bindM[OF m] ppat_rigid simp: list_comb_apps bnds_nonneg_apps)
        qed
        then show ?thesis by (simp only: eq)
      next
        case (flex F Fty js)
        have sc: "strip_comb s' = (Var F Fty, map Bound js)"
          using flex(1) by (simp add: app_apps strip_comb_atom_apps)
        have js0: "\<forall>j\<in>set js. 0 \<le> j" using ns' flex(1) by (simp add: bnds_nonneg_app)
        let ?R = "mapM (try_trans xs d) js \<bind> (\<lambda>js'.
              type_of_G env Fty (ilength js) (mk_proj_list js') \<bind> (\<lambda>Hty.
              let (env', H) = genvar (fst F) env Hty in
              mk_hnf bs js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env' \<bind>
                (\<lambda>env''. return (app H (List.map_filter id js'), env'')))))"
        have eq: "pr_step prr xs s' env d bs = ?R"
          using nA sc by (simp add: pr_step_def ints_of'_Bounds[OF flex(2)] Let_def)
        have "no_pat ?R"
          by (auto simp: mk_hnf_def split: prod.splits intro!: pok_bindM pok_mapM no_pat_try_trans
              no_pat_type_of_G no_pat_mkabs no_pat_update)
        moreover have "?P p" if R: "ok ?R p" for p
        proof -
          from R obtain js' Hty where js': "ok (mapM (try_trans xs d) js) js'"
            and rest: "ok (let (env', H) = genvar (fst F) env Hty in
              mk_hnf bs js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env' \<bind>
                (\<lambda>env''. return (app H (List.map_filter id js'), env'')))) p"
            by auto
          obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
          let ?ks = "mk_proj_list js'" and ?ls = "List.map_filter id js'"
          from rest G obtain t env' where t: "ok (mkabs bs js (app H ?ks)) t"
            and upd: "ok (update (F, Fty) t env1) env'" and p: "p = (app H ?ls, env')"
            by (auto simp: mk_hnf_def)
          note g = genvar_simps[OF G]
          have l2: "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) js js'" using js' by (simp add: ok_mapM)
          then have len: "length js = length js'" by (rule list_all2_lengthD)
          have "distinct ?ks" using mk_proj_list_aux_sorted sorted_gt_distinct
            by (simp add: mk_proj_list_def)
          note b = binding_pat[OF t[unfolded g(4)] this mk_proj_list_bren(1)[OF len]]
          have e1: "env_pinv env1" using ei env_pinv_genvar[OF G] by simp
          have e': "env_pinv env'" by (rule env_pinv_update[OF upd e1 b])
          note tt = try_trans_distinct[OF l2 flex(2) js0 d]
          have "\<forall>l\<in>set ?ls. 0 \<le> l" using tt js0 ok_trans(1)[OF _ d] by blast
          then have "bnds_nonneg (app H ?ls)" by (simp add: g(4) bnds_nonneg_app)
          moreover have "ppat (app H ?ls)" using tt by (simp add: g(4) ppat_flex)
          ultimately show ?thesis using e' p by simp
        qed
        ultimately show ?thesis unfolding eq by (rule pok_okI)
      qed
    qed
  qed
  then show ?case using "1.hyps" "1.prems" unfolding pr_step_def by simp
qed


subsection \<open>Flex-rigid problems\<close>

lemma pok_conj: "pok P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> Q x) \<Longrightarrow> pok (\<lambda>x. P x \<and> Q x) m"
  by (auto simp: pok_def split: option.splits res.splits)

lemma proj_pinv:
  assumes ei: "env_pinv env" and t: "ppat t" "bnds_nonneg t" "\<not> loose_bvar t (ilength bs)"
    and is0: "\<forall>x\<in>set is. 0 \<le> x"
  shows "pok (\<lambda>(u, env'). env_pinv env' \<and> ppat u \<and> bnds_nonneg u \<and> \<not> loose_bvar u (ilength is))
    (proj t env bs is)"
proof (cases "downto0 is (ilength bs - 1)")
  case True
  then have "ilength is = ilength bs" using downto0_bren[OF True] by simp
  with True ei t show ?thesis by (simp add: proj_def)
next
  case False
  have "pok (\<lambda>p. (case p of (u, env') \<Rightarrow> env_pinv env' \<and> ppat u \<and> bnds_nonneg u) \<and>
      (case p of (u, env') \<Rightarrow> \<not> loose_bvar u (ilength is))) (pr is t env 0 bs)"
  proof (rule pok_conj)
    show "pok (\<lambda>(u, env'). env_pinv env' \<and> ppat u \<and> bnds_nonneg u) (pr is t env 0 bs)"
      by (rule pok_IH) (rule pr_pinv[OF _ ei t(1,2) order_refl is0])
    fix p assume "ok (pr is t env 0 bs) p"
    then show "case p of (u, env') \<Rightarrow> \<not> loose_bvar u (ilength is)"
      using pr_sound[OF _ _ order_refl is0] by (auto simp: pr_ok_def split: prod.splits)
  qed
  then have "pok (\<lambda>(u, env'). env_pinv env' \<and> ppat u \<and> bnds_nonneg u \<and> \<not> loose_bvar u (ilength is))
      (pr is t env 0 bs)" by (rule pok_mono) auto
  with False show ?thesis by (simp add: proj_def)
qed

lemma flexrigid_pinv:
  assumes ei: "env_pinv env" and t: "ppat t" "bnds_nonneg t" "\<not> loose_bvar t (ilength bs)"
    and is0: "\<forall>x\<in>set is. 0 \<le> x"
  shows "pok env_pinv (flexrigid env bs F Fty is t)"
  unfolding flexrigid_def
proof (rule pok_bindM[OF no_pat_occurs'])
  fix b assume ob: "ok (occurs F t env) b"
  show "pok env_pinv (if b then do {
        b' \<leftarrow> rigid_occurs F t env;
        if b' then raise (Unif (Ocheck_Fail F t bs env)) else raise Pattern}
      else handle
        (do {(u, env') \<leftarrow> proj t env bs is; u' \<leftarrow> mkabs bs is u; update (F, Fty) u' env'})
        (\<lambda>e. case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env bs F is t)) | _ \<Rightarrow> raise e))"
  proof (cases b)
    case True
    have "pok env_pinv (rigid_occurs F t env \<bind>
        (\<lambda>b'. if b' then raise (Unif (Ocheck_Fail F t bs env)) else raise Pattern))"
    proof (rule pok_bindM[OF no_pat_rigid_occurs'])
      fix b' assume "ok (rigid_occurs F t env) b'"
      moreover have "ok (occurs F t env) True" using ob True by simp
      ultimately have b' using occurs_rigid_occurs_ppat ei t(1,2) by blast
      then show
        "pok env_pinv (if b' then raise (Unif (Ocheck_Fail F t bs env)) else raise Pattern)" by simp
    qed
    with True show ?thesis by simp
  next
    case False
    have "pok env_pinv (do {(u, env') \<leftarrow> proj t env bs is; u' \<leftarrow> mkabs bs is u; update (F, Fty) u' env'})"
    proof (rule pok_bindM[OF proj_pinv[OF ei t is0]], clarify)
      fix u env' assume e': "env_pinv env'" and u: "ppat u" "bnds_nonneg u" "\<not> loose_bvar u (ilength is)"
      show "pok env_pinv (mkabs bs is u \<bind> (\<lambda>u'. update (F, Fty) u' env'))"
      proof (rule pok_bindM[OF no_pat_mkabs])
        fix u' assume "ok (mkabs bs is u) u'"
        then have u': "u' = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) u" by (simp add: ok_mkabs)
        have "ppat u'" "closed u'" "bnds_nonneg u'"
          using u by (simp_all add: u' ppat_abs_list closed_abs_list)
        then show "pok env_pinv (update (F, Fty) u' env')"
          by (intro pok_okI[OF no_pat_update]) (use env_pinv_update e' in blast)
      qed
    qed
    then show ?thesis using False by (auto intro!: pok_handle split: exn.splits)
  qed
qed


subsection \<open>Unification\<close>

text \<open>The invariant of the terms of a problem under binders \<open>bs\<close>:\<close>

definition pterm_inv :: "binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "pterm_inv bs t \<longleftrightarrow> ppat t \<and> bnds_nonneg t \<and> \<not> loose_bvar t (ilength bs)"

lemma head_norm_pterm_inv:
  assumes "env_pinv env" "pterm_inv bs t"
  shows "pok (pterm_inv bs) (head_norm env t)"
proof (rule pok_mono[OF head_norm_pok[OF assms(1)]])
  show "ppat t" "bnds_nonneg t" using assms(2) by (simp_all add: pterm_inv_def)
  fix t' assume t': "ppat t' \<and> bnds_nonneg t' \<and> (\<forall>k\<ge>0. loose_bvar1 t' k \<longrightarrow> loose_bvar1 t k)"
  have "\<not> loose_bvar t' (ilength bs)"
  proof
    assume "loose_bvar t' (ilength bs)"
    then obtain k where "ilength bs \<le> k" "loose_bvar1 t' k" by (auto simp: loose_bvar_loose_bvar1)
    moreover have "0 \<le> k" using \<open>ilength bs \<le> k\<close> ilength_nonneg[of bs] by (meson order_trans)
    ultimately have "loose_bvar1 t k" using t' by blast
    with \<open>ilength bs \<le> k\<close> assms(2) show False by (auto simp: pterm_inv_def loose_bvar_loose_bvar1)
  qed
  with t' show "pterm_inv bs t'" by (simp add: pterm_inv_def)
qed

lemma pterm_inv_Abs:
  "pterm_inv bs (Abs a T t) \<Longrightarrow> pterm_inv (b # bs) t"
  by (auto simp: pterm_inv_def ppat_AbsD)

lemma pterm_inv_eta:
  assumes "pterm_inv bs t" "\<not> is_Abs t"
  shows "pterm_inv (b # bs) (incr t $ Bound 0)"
proof -
  have "\<not> loose_bvar (lift t 0) (ilength bs + 1)"
    using assms(1) loose_bvar_lift[of 0 "ilength bs" t] by (simp add: pterm_inv_def)
  moreover have "0 < ilength bs + 1" using ilength_nonneg[of bs] by (simp add: integer_arith)
  ultimately show ?thesis using assms ppat_lift_Bound0[of t]
    by (auto simp: pterm_inv_def incr_def incr_aux_lift bnds_nonneg_incr_bv integer_arith)
qed

lemma pterm_inv_args:
  "pterm_inv bs (h \<degree>\<degree> ts) \<Longrightarrow> \<forall>u\<in>set ts. ppat u \<Longrightarrow> u \<in> set ts \<Longrightarrow> pterm_inv bs u"
  by (auto simp: pterm_inv_def bnds_nonneg_apps loose_bvar_apps)

lemma no_pat_rigid_clash: "pok P (rigid_clash bs h1 h2)"
  by (auto simp: rigid_clash_def split: pterm.splits)

lemma rigid_rigid_pinv:
  assumes IH: "\<And>s t env1. (s, t) \<in> set (zip ss ts) \<Longrightarrow> env_pinv env1 \<Longrightarrow> pok env_pinv (uni alg' bs s t env1)"
    and ei: "env_pinv env"
  shows "pok env_pinv (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg' Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg' Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht)"
proof -
  have f: "pok env_pinv (zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env1))"
    if "env_pinv env1" for env1
    using that by (auto simp: ok_zip_eq intro!: pok_bindM[OF no_pat_zip_eq] pok_foldM IH)
  have u: "pok env_pinv (unify_types alg' Ta Tb env \<bind> (\<lambda>env'. zip_eq ss ts \<bind>
      (\<lambda>ps. foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env')))" for Ta Tb
    by (rule pok_bindM[OF no_pat_unify_types]) (use f ei env_pinv_tenv in metis)
  show ?thesis
    by (cases hs; cases ht) (simp_all add: u f[OF ei] no_pat_rigid_clash)
qed

lemma unif_step_pinv:
  assumes IH: "\<And>bs1 s1 t1 env1. env_pinv env1 \<Longrightarrow> pterm_inv bs1 s1 \<Longrightarrow> pterm_inv bs1 t1 \<Longrightarrow>
      pok env_pinv (uni alg' bs1 s1 t1 env1)"
    and ei: "env_pinv env" and s': "pterm_inv bs s'" and t': "pterm_inv bs t'"
  shows "pok env_pinv (unif_step uni alg' bs s' t' env)"
proof (cases "is_Abs s'")
  case sAbs: True
  then obtain ns Ts ts where s'A: "s' = Abs ns Ts ts" by (cases s') auto
  show ?thesis
  proof (cases "is_Abs t'")
    case True
    then obtain nt Tt tt where t'A: "t' = Abs nt Tt tt" by (cases t') auto
    have eq: "unif_step uni alg' bs s' t' env =
        unify_types alg' Ts Tt env \<bind> uni alg' ((if ns = STR '''' then nt else ns, Ts) # bs) ts tt"
      by (simp add: unif_step_def s'A t'A Let_def)
    show ?thesis unfolding eq
    proof (rule pok_bindM[OF no_pat_unify_types])
      fix env1 assume "tenv env1 = tenv env"
      from env_pinv_tenv[OF this] ei have "env_pinv env1" by blast
      with IH pterm_inv_Abs[OF s'[unfolded s'A]] pterm_inv_Abs[OF t'[unfolded t'A]]
      show "pok env_pinv (uni alg' ((if ns = STR '''' then nt else ns, Ts) # bs) ts tt env1)" by blast
    qed
  next
    case False
    have "pok env_pinv (uni alg' ((ns, Ts) # bs) ts (incr t' $ Bound 0) env)"
      using IH ei pterm_inv_Abs[OF s'[unfolded s'A]] pterm_inv_eta[OF t' False] by blast
    with False show ?thesis by (simp add: unif_step_def s'A)
  qed
next
  case nsAbs: False
  show ?thesis
  proof (cases "is_Abs t'")
    case True
    then obtain nt Tt tt where t'A: "t' = Abs nt Tt tt" by (cases t') auto
    have "pok env_pinv (uni alg' ((nt, Tt) # bs) (incr s' $ Bound 0) tt env)"
      using IH ei pterm_inv_Abs[OF t'[unfolded t'A]] pterm_inv_eta[OF s' nsAbs] by blast
    with nsAbs show ?thesis by (simp add: unif_step_def t'A)
  next
    case ntAbs: False
    have ps': "ppat s'" and pt': "ppat t'" using s' t' by (simp_all add: pterm_inv_def)
    from ps' nsAbs show ?thesis
    proof (cases rule: ppat_nonAbsE)
      case srig: (rigid h1 ss)
      have sc1: "strip_comb s' = (h1, ss)"
        using srig(1,2) rigid_atom[OF srig(1)] by (simp add: strip_comb_atom_apps)
      have nh1: "\<not> is_Var h1" "\<not> is_Abs h1" using srig(1) by (cases h1; simp)+
      from pt' ntAbs show ?thesis
      proof (cases rule: ppat_nonAbsE)
        case trig: (rigid h2 ts)
        have sc2: "strip_comb t' = (h2, ts)"
          using trig(1,2) rigid_atom[OF trig(1)] by (simp add: strip_comb_atom_apps)
        have nh2: "\<not> is_Var h2" "\<not> is_Abs h2" using trig(1) by (cases h2; simp)+
        have "pok env_pinv (case (h1, h2) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg' Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg' Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs h1 h2)"
        proof (rule rigid_rigid_pinv[OF _ ei])
          fix s t env1 assume st: "(s, t) \<in> set (zip ss ts)" and e1: "env_pinv env1"
          have "pterm_inv bs s" using pterm_inv_args[OF s'[unfolded srig(2)] srig(3) set_zip_leftD[OF st]] .
          moreover have "pterm_inv bs t" using pterm_inv_args[OF t'[unfolded trig(2)] trig(3) set_zip_rightD[OF st]] .
          ultimately show "pok env_pinv (uni alg' bs s t env1)" using IH e1 by blast
        qed
        then show ?thesis using nsAbs ntAbs sc1 sc2 nh1 nh2 by (simp add: unif_step_def)
      next
        case tflex: (flex G Gty js)
        have sc2: "strip_comb t' = (Var G Gty, map Bound js)"
          using tflex(1) by (simp add: app_apps strip_comb_atom_apps)
        have "\<forall>j\<in>set js. 0 \<le> j" using t' tflex(1) by (simp add: pterm_inv_def bnds_nonneg_app)
        then have "pok env_pinv (flexrigid env bs G Gty js s')"
          using flexrigid_pinv[OF ei] s' by (simp add: pterm_inv_def)
        then show ?thesis using nsAbs ntAbs sc1 sc2 nh1
          by (simp add: unif_step_def ints_of'_Bounds[OF tflex(2)])
      qed
    next
      case sflex: (flex F Fty "is")
      have sc1: "strip_comb s' = (Var F Fty, map Bound is)"
        using sflex(1) by (simp add: app_apps strip_comb_atom_apps)
      have is0: "\<forall>i\<in>set is. 0 \<le> i" using s' sflex(1) by (simp add: pterm_inv_def bnds_nonneg_app)
      from pt' ntAbs show ?thesis
      proof (cases rule: ppat_nonAbsE)
        case trig: (rigid h2 ts)
        have sc2: "strip_comb t' = (h2, ts)"
          using trig(1,2) rigid_atom[OF trig(1)] by (simp add: strip_comb_atom_apps)
        have nh2: "\<not> is_Var h2" using trig(1) by (cases h2) simp_all
        have "pok env_pinv (flexrigid env bs F Fty is t')"
          using flexrigid_pinv[OF ei] t' is0 by (simp add: pterm_inv_def)
        then show ?thesis using nsAbs ntAbs sc1 sc2 nh2
          by (simp add: unif_step_def ints_of'_Bounds[OF sflex(2)])
      next
        case tflex: (flex G Gty js)
        have sc2: "strip_comb t' = (Var G Gty, map Bound js)"
          using tflex(1) by (simp add: app_apps strip_comb_atom_apps)
        have "pok env_pinv (if F = G then flexflex1 env bs F Fty is js else flexflex2 env bs F Fty is G Gty js)"
          using flexflex1_pinv[OF ei] flexflex2_pinv[OF ei sflex(2) tflex(2)] by simp
        then show ?thesis using nsAbs ntAbs sc1 sc2
          by (simp add: unif_step_def ints_of'_Bounds[OF sflex(2)] ints_of'_Bounds[OF tflex(2)])
      qed
    qed
  qed
qed

theorem unif_pinv:
  assumes "unif alg' bs s t env = Some r"
  shows "env_pinv env \<Longrightarrow> pterm_inv bs s \<Longrightarrow> pterm_inv bs t \<Longrightarrow> pok env_pinv (Some r)"
  using assms
proof (induction alg' bs s t env r rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg' bs s t env r)
  have IH: "pok env_pinv (uni alg' bs1 s1 t1 env1)"
    if "env_pinv env1" "pterm_inv bs1 s1" "pterm_inv bs1 t1" for bs1 s1 t1 env1
    by (rule pok_IH) (rule "1.IH"[OF _ that])
  have body: "head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. unif_step uni alg' bs s' t' env)) = Some r"
    using "1.hyps" unfolding unif_step_def .
  have "pok env_pinv (head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. unif_step uni alg' bs s' t' env)))"
    by (intro pok_bindM[OF head_norm_pterm_inv[OF "1.prems"(1,2)]]
        pok_bindM[OF head_norm_pterm_inv[OF "1.prems"(1,3)]]
        unif_step_pinv[where uni = uni and alg' = alg', OF IH "1.prems"(1)])
  then show ?case by (simp only: body)
qed

text \<open>
  \<^const>\<open>unify\<close> does not give up (raise \<open>Pattern\<close>) on closed \<open>\<beta>\<close>-normal patterns whose bound
  variables are not negative, in an environment of such patterns; and the resulting
  environment binds such patterns only.
\<close>

theorem unify_ppat:
  assumes "unify alg' s t env = Some r" "ppat s" "ppat t" "env_ppat env" "closed s" "closed t"
    "closed_env env" "bnds_nonneg s" "bnds_nonneg t" "env_nonneg env"
  shows "r \<noteq> Err Pattern" and "r = Ok env' \<Longrightarrow> env_ppat env' \<and> closed_env env' \<and> env_nonneg env'"
proof -
  have "pterm_inv [] s" "pterm_inv [] t" using assms(2,3,5,6,8,9) by (simp_all add: pterm_inv_def closed_def)
  moreover have "env_pinv env" using assms(4,7,10) by (simp add: env_pinv_def)
  ultimately have "pok env_pinv (Some r)" using unif_pinv[OF assms(1)[unfolded unify_def]] by blast
  then show "r \<noteq> Err Pattern" and "r = Ok env' \<Longrightarrow> env_ppat env' \<and> closed_env env' \<and> env_nonneg env'"
    by (auto simp: pok_def env_pinv_def split: res.splits)
qed

end

end
