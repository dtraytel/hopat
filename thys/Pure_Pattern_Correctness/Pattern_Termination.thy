section \<open>Termination of Pattern Unification\<close>

theory Pattern_Termination
  imports Pattern_Size Pattern_Exceptions
begin

context csig
begin

text \<open>
  We show that \<^const>\<open>unify\<close> terminates (with a result or an exception) on well-typed terms in
  acyclic, well-typed environments. Neither the terms nor the bindings need to be patterns or
  \<open>\<beta>\<close>-normal.
\<close>

subsection \<open>Head normalisation without exceptions\<close>

partial_function (option) hn :: "env \<Rightarrow> pterm \<Rightarrow> pterm option" where
  "hn env t =
    (case t of
      Var x T \<Rightarrow> (case lk env x T of Some u \<Rightarrow> hn env u | None \<Rightarrow> Some t)
    | Abs a T body \<Rightarrow> Option.bind (hn env body) (\<lambda>body'. Some (Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> Option.bind (hn env f) (\<lambda>nf.
            case nf of
              Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
            | _ \<Rightarrow> Some (nf $ u)))
    | _ \<Rightarrow> Some t)"

lemma lookup_lk:
  assumes "vt_is_empty (tyenv env)"
  shows "lookup env x T = (case vt_lookup (tenv env) x of
      Some (U, u) \<Rightarrow> if U = T then return (lk env x T) else var_clash x T U
    | None \<Rightarrow> return None)"
  using assms by (auto simp: lookup_def lk_def unified_empty split: option.splits)

lemma head_norm_hn:
  assumes "head_norm env t = Some r" "vt_is_empty (tyenv env)"
  shows "r = Ok t' \<Longrightarrow> hn env t = Some t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 h env t r)
  show ?case
  proof (cases t)
    case (Var x T)
    with 1 show ?thesis
      by (subst hn.simps) (auto simp: lookup_lk lk_def var_clash_def split: option.splits if_splits)
  next
    case (Abs a T b)
    with 1 show ?thesis by (subst hn.simps) auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where "f = Abs a T b" by (cases f) auto
      with 1 App show ?thesis by (subst hn.simps) auto
    next
      case False
      with 1 App obtain nf where nf: "h env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      have hf: "hn env f = Some nf" using "1.IH"[OF nf refl] 1 by simp
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T b where "nf = Abs a T b" by (cases nf) auto
        with rest 1 App False hf show ?thesis by (subst hn.simps) (cases f; auto)
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with 1 App False hf nA show ?thesis by (subst hn.simps) (cases f; cases nf; auto)
      qed
    qed
  qed (use 1 in \<open>subst hn.simps; auto\<close>)+
qed

lemma hn_vps:
  assumes "hn env t = Some t'"
  shows "vps t' \<subseteq> reach env (vps t)"
  using assms
proof (induction env t t' rule: hn.raw_induct[rotated, consumes 1])
  case (1 h env t t')
  show ?case
  proof (cases t)
    case (Var x T)
    show ?thesis
    proof (cases "lk env x T")
      case None
      with 1 Var show ?thesis by (auto intro: reach_incl[THEN subsetD])
    next
      case (Some u)
      with 1 Var have "h env u = Some t'" by simp
      from subset_trans[OF "1.IH"[OF this] reach_lk[OF Some]] Var show ?thesis by simp
    qed
  next
    case (Abs a T b)
    with 1 obtain b' where "h env b = Some b'" "t' = Abs a T b'" by (auto split: Option.bind_splits)
    with "1.IH" Abs show ?thesis by auto
  next
    case (App f u)
    have vt: "vps t = vps f \<union> vps u" using App by simp
    have sub: "reach env (vps (subst_bound u body)) \<subseteq> reach env (vps t)"
      if "vps body \<subseteq> reach env (vps t)" for body
      using vps_subst_bound[of u body] that vt
      by (intro reach_mono) (auto intro: reach_incl[THEN subsetD])
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where f: "f = Abs a T b" by (cases f) auto
      with 1 App have "h env (subst_bound u b) = Some t'" by simp
      then have "vps t' \<subseteq> reach env (vps (subst_bound u b))" by (rule "1.IH")
      moreover have "vps b \<subseteq> reach env (vps t)" using f vt reach_incl[of "vps t" env] by auto
      ultimately show ?thesis using sub[of b] by blast
    next
      case False
      with 1 App obtain nf where nf: "h env f = Some nf"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
        by (cases f) (auto split: Option.bind_splits)
      have vnf: "vps nf \<subseteq> reach env (vps t)"
        using "1.IH"[OF nf] vt reach_subset[of "vps f" "vps t" env] by auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T b where nfa: "nf = Abs a T b" by (cases nf) auto
        with rest have "h env (subst_bound u b) = Some t'" by simp
        then have "vps t' \<subseteq> reach env (vps (subst_bound u b))" by (rule "1.IH")
        moreover have "vps b \<subseteq> reach env (vps t)" using vnf nfa by simp
        ultimately show ?thesis using sub[of b] by blast
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with vnf vt show ?thesis by (auto intro: reach_incl[THEN subsetD])
      qed
    qed
  qed (use 1 in auto)
qed

lemma hn_head_norm:
  assumes "hn env t = Some t'"
  shows "vt_is_empty (tyenv env) \<Longrightarrow> head_norm env t = Some (Ok t') \<or> (\<exists>e. head_norm env t = Some (Err e))"
  using assms
proof (induction env t t' rule: hn.raw_induct[rotated, consumes 1])
  case (1 h env t t')
  have e: "vt_is_empty (tyenv env)" using 1 by simp
  note IH = "1.IH"[OF _ e]
  show ?case
  proof (cases t)
    case (Var x T)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case None
      with 1 Var have "t' = t" by (simp add: lk_def)
      with None Var show ?thesis by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e return_def bindM_def)
    next
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      show ?thesis
      proof (cases "U = T")
        case True
        with Some p 1 Var have hu: "h env u = Some t'" by (simp add: lk_def)
        from IH[OF hu] Some p True Var show ?thesis
          by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e lk_def bindM_def return_def)
      next
        case False
        with Some p Var show ?thesis
          by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e lk_def var_clash_def raise_def bindM_def)
      qed
    qed
  next
    case (Abs a T b)
    with 1 obtain b' where hb: "h env b = Some b'" and t': "t' = Abs a T b'"
      by (auto split: Option.bind_splits)
    from IH[OF hb] t' Abs show ?thesis
      by (auto simp: head_norm.simps[of env "Abs a T b"] bindM_def raise_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where f: "f = Abs a T b" by (cases f) auto
      with 1 App have "h env (subst_bound u b) = Some t'" by simp
      from IH[OF this] App f show ?thesis by (simp add: head_norm.simps[of env "Abs a T b $ u"])
    next
      case False
      with 1 App obtain nf where nf: "h env f = Some nf"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
        by (cases f) (auto split: Option.bind_splits)
      have hn_eq: "head_norm env (f $ u) = bindM (head_norm env f) (\<lambda>nf. case nf of
          pterm.Abs _ _ body \<Rightarrow> head_norm env (subst_bound u body) | _ \<Rightarrow> return (nf $ u))"
        using False by (subst head_norm.simps) (cases f; simp)
      from IH[OF nf] show ?thesis
      proof
        assume hf: "head_norm env f = Some (Ok nf)"
        show ?thesis
        proof (cases "is_Abs nf")
          case True
          then obtain a T b where nfa: "nf = Abs a T b" by (cases nf) auto
          with rest have "h env (subst_bound u b) = Some t'" by simp
          from IH[OF this] hf nfa App hn_eq show ?thesis by (simp add: bindM_def)
        next
          case nA: False
          with rest have "t' = nf $ u" by (cases nf) auto
          with hf nA App hn_eq show ?thesis by (cases nf) (simp_all add: return_def bindM_def)
        qed
      next
        assume "\<exists>e. head_norm env f = Some (Err e)"
        with App hn_eq show ?thesis by (auto simp: bindM_def)
      qed
    qed
  next
    case (Const c T)
    with 1 have "t' = t" by simp
    with Const show ?thesis by (simp add: head_norm.simps[of env "Const c T"] return_def)
  next
    case (Free c T)
    with 1 have "t' = t" by simp
    with Free show ?thesis by (simp add: head_norm.simps[of env "Free c T"] return_def)
  next
    case (Bound i)
    with 1 have "t' = t" by simp
    with Bound show ?thesis by (simp add: head_norm.simps[of env "Bound i"] return_def)
  qed
qed


subsection \<open>Terminating computations\<close>

lemma mapM_term: "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>r. f x = Some r) \<Longrightarrow> \<exists>r. mapM f xs = Some r"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits res.splits)

lemma bindM_term:
  "\<exists>r. m = Some r \<Longrightarrow> (\<And>x. m = Some (Ok x) \<Longrightarrow> \<exists>r. f x = Some r) \<Longrightarrow> \<exists>r. bindM m f = Some r"
  by (auto simp: bindM_def split: res.splits)

lemma handle_term:
  "\<exists>r. m = Some r \<Longrightarrow> (\<And>e. m = Some (Err e) \<Longrightarrow> \<exists>r. h e = Some r) \<Longrightarrow> \<exists>r. handle m h = Some r"
  by (auto simp: handle_def split: res.splits)

lemma return_term[simp]: "\<exists>r. return x = Some r" and raise_term[simp]: "\<exists>r. raise e = Some r"
  by (simp_all add: return_def raise_def)

lemma nth_term: "\<exists>r. nth xs i = Some r"
  by (induction xs i rule: nth.induct) auto

lemma mkabs_term: "\<exists>r. mkabs binders is t = Some r"
  by (induction "is") (auto intro!: bindM_term nth_term split: prod.splits)

lemma update_term: "\<exists>r. update xT t env = Some r"
  by (auto simp: update_def update_new_def split: env.splits intro!: bindM_term)

lemma ints_of_term: "\<exists>r. ints_of ts = Some r"
  by (induction ts rule: ints_of.induct) (auto intro!: bindM_term)

lemma idx_term: "\<exists>r. idx is j = Some r"
  by (induction "is") auto

lemma split_type_term: "\<exists>r. split_type T n Ts = Some r"
  by (induction T n Ts rule: split_type.induct) (subst split_type.simps; auto split: ptyp.splits list.splits)

lemma type_of_G_term: "vt_is_empty (tyenv env) \<Longrightarrow> \<exists>r. type_of_G env T n ks = Some r"
  by (auto simp: type_of_G_def norm_type_def intro!: bindM_term split_type_term mapM_term nth_term
      split: prod.splits)

lemma try_trans_term: "\<exists>r. try_trans xs d i = Some r"
  by (auto simp: try_trans_def intro!: handle_term bindM_term idx_term)

lemma trans_term: "\<exists>r. trans xs d i = Some r"
  by (auto simp: trans_def intro!: bindM_term idx_term)

lemma mapAccM_inv:
  assumes f: "\<And>x e. x \<in> set xs \<Longrightarrow> R e \<Longrightarrow>
      \<exists>r. f x e = Some r \<and> (\<forall>y e'. r = Ok (y, e') \<longrightarrow> R e' \<and> S e e' \<and> Q x y e')"
    and trans: "\<And>e1 e2 e3. S e1 e2 \<Longrightarrow> S e2 e3 \<Longrightarrow> S e1 e3" and refl: "\<And>e. S e e"
    and mono: "\<And>x y e1 e2. Q x y e1 \<Longrightarrow> S e1 e2 \<Longrightarrow> Q x y e2"
    and R: "R e"
  shows "\<exists>r. mapAccM f xs e = Some r \<and>
    (\<forall>ys e'. r = Ok (ys, e') \<longrightarrow> R e' \<and> S e e' \<and> list_all2 (\<lambda>x y. Q x y e') xs ys)"
  using f R
proof (induction xs arbitrary: e)
  case Nil
  then show ?case by (auto simp: return_def refl)
next
  case (Cons x xs)
  from Cons.prems(1)[of x e] Cons.prems(2) obtain r where r: "f x e = Some r"
    and rp: "\<forall>y e'. r = Ok (y, e') \<longrightarrow> R e' \<and> S e e' \<and> Q x y e'" by auto
  show ?case
  proof (cases r)
    case (Ok p)
    obtain y e1 where p: "p = (y, e1)" by force
    with rp Ok have e1: "R e1" "S e e1" "Q x y e1" by auto
    from Cons.IH[OF _ e1(1)] Cons.prems(1) obtain r2 where r2: "mapAccM f xs e1 = Some r2"
      and rp2: "\<forall>ys e'. r2 = Ok (ys, e') \<longrightarrow> R e' \<and> S e1 e' \<and> list_all2 (\<lambda>x y. Q x y e') xs ys"
      by auto
    show ?thesis
    proof (cases r2)
      case (Ok q)
      obtain ys e' where q: "q = (ys, e')" by force
      with rp2 Ok have "R e'" "S e1 e'" "list_all2 (\<lambda>x y. Q x y e') xs ys" by auto
      with e1 have "R e' \<and> S e e' \<and> list_all2 (\<lambda>x y. Q x y e') (x # xs) (y # ys)"
        by (auto intro: trans mono)
      with r r2 \<open>r = Ok p\<close> p Ok q show ?thesis by (simp add: return_def bindM_def)
    next
      case (Err e')
      with r r2 \<open>r = Ok p\<close> p show ?thesis by (simp add: bindM_def)
    qed
  next
    case (Err e')
    with r show ?thesis by (simp add: bindM_def raise_def)
  qed
qed

lemma list_all2_set2': "list_all2 P xs ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. P x y"
  by (induction rule: list_all2_induct) auto

lemma existsM_term: "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>r. P x = Some r) \<Longrightarrow> \<exists>r. existsM P xs = Some r"
  by (induction xs) (auto intro!: bindM_term)

lemma handler_term: "\<exists>r. (case e of Unif x \<Rightarrow> raise a | _ \<Rightarrow> raise e) = Some r"
  by (cases e) (simp_all add: raise_def)

lemma mk_ff_list_term: "\<exists>r. mk_ff_list is js = Some r"
proof -
  have "\<exists>r. mk_ff_list_aux is js k = Some r" for k
    by (induction "is" js k rule: mk_ff_list_aux.induct) (auto intro!: bindM_term)
  then show ?thesis by (simp add: mk_ff_list_def)
qed

lemma idx_mapM_term: "\<exists>r. mapM (idx is) js = Some r"
  by (rule mapM_term) (rule idx_term)

lemma nat_of_integer_pos: "0 < i \<Longrightarrow> nat_of_integer i = Suc (nat_of_integer (i - 1))"
  by (simp add: nat_of_integer.rep_eq less_integer.rep_eq Suc_nat_eq_nat_zadd1)

lemma ok_split_type:
  "ok (split_type T n Acc) (Ts, U) \<Longrightarrow>
    0 \<le> n \<and> (\<exists>Us. T = foldr fun_type Us U \<and> Ts = rev Us @ Acc \<and> length Us = nat_of_integer n)"
proof (induction T arbitrary: n Acc)
  case (Type a Ts0)
  show ?case
  proof (cases "n = 0")
    case True
    with Type.prems show ?thesis by (subst (asm) split_type.simps) (auto simp: integer_reps)
  next
    case False
    with Type.prems obtain T1 T2 where T: "a = STR ''fun''" "Ts0 = [T1, T2]"
      and r: "ok (split_type T2 (n - 1) (T1 # Acc)) (Ts, U)"
      by (subst (asm) split_type.simps) (auto split: list.splits if_splits)
    from Type.IH[OF _ r] T obtain Us where
      "0 \<le> n - 1" "T2 = foldr fun_type Us U" "Ts = rev Us @ T1 # Acc" "length Us = nat_of_integer (n - 1)"
      by auto
    moreover from \<open>0 \<le> n - 1\<close> have "0 < n" by (simp add: integer_reps)
    ultimately show ?thesis using T
      by (intro conjI exI[of _ "T1 # Us"]) (auto simp: nat_of_integer_pos)
  qed
next
  case (TFree b S)
  then show ?case by (subst (asm) split_type.simps) (auto simp: integer_reps split: if_splits)
next
  case (TVar v S)
  then show ?case by (subst (asm) split_type.simps) (auto simp: integer_reps split: if_splits)
qed

lemma ok_type_of_G':
  assumes "ok (type_of_G env T n ks) Hty" "vt_is_empty (tyenv env)"
  obtains Us U Vs where "T = foldr fun_type Us U" "length Us = nat_of_integer n"
    "Hty = foldr fun_type Vs U" "length Vs = length ks" "\<forall>k\<in>set ks. 0 \<le> k"
proof -
  from assms obtain Ts U Vs where st: "ok (split_type T n []) (Ts, U)"
    and Vs: "list_all2 (\<lambda>i U. ok (nth Ts i) U) ks Vs" and H: "Hty = foldr fun_type Vs U"
    by (auto simp: type_of_G_def norm_type_def ok_mapM)
  from ok_split_type[OF st] obtain Us where "T = foldr fun_type Us U" "length Us = nat_of_integer n"
    by auto
  moreover have "length Vs = length ks" using Vs by (simp add: list_all2_lengthD)
  moreover have "\<forall>k\<in>set ks. 0 \<le> k" using Vs
    by (induction ks Vs rule: list_all2_induct) (auto simp: ok_nth)
  ultimately show ?thesis using H that by blast
qed


subsection \<open>Termination of the occurs check\<close>

lemma occurs_term:
  assumes ac: "acyc env" and wf: "wf_env ar env"
  shows "\<exists>r. occurs F t env = Some r"
proof -
  define Q where "Q x \<longleftrightarrow> (\<exists>r. occurs F (Var (fst x) (snd x)) env = Some r)" for x
  have L: "\<exists>r. occurs F t env = Some r" if "\<forall>y\<in>vps t. Q y" for t
    using that
  proof (induction t)
    case (Var x T)
    then show ?case by (simp add: Q_def)
  next
    case (Abs a T t)
    then show ?case by (subst occurs.simps) simp
  next
    case (App t1 t2)
    then obtain r1 r2 where "occurs F t1 env = Some r1" "occurs F t2 env = Some r2" by auto
    then show ?case
      by (subst occurs.simps) (cases r1; auto simp: bindM_def return_def split: res.splits)
  qed (subst occurs.simps; simp add: return_def)+
  have "Q x" for x
  proof (induction x rule: wf_induct[OF wf_trancl[OF wf_dep[OF ac]]])
    case (1 x)
    obtain xn T where x: "x = (xn, T)" by (cases x)
    show ?case
    proof (cases "vt_lookup (tenv env) xn")
      case None
      then show ?thesis using wf_envD(1)[OF wf]
        by (simp add: Q_def x occurs.simps[of F "Var xn T"] lookup_lk return_def bindM_def)
    next
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      show ?thesis
      proof (cases "U = T")
        case False
        with Some p wf_envD(1)[OF wf] show ?thesis
          by (simp add: Q_def x occurs.simps[of F "Var xn T"] lookup_lk var_clash_def raise_def bindM_def)
      next
        case True
        with Some p have lu: "lk env xn T = Some u" by (simp add: lk_def)
        have "\<forall>y\<in>vps u. Q y"
          using 1 reach_lk_trancl[OF lu] reach_incl x by blast
        from L[OF this] lu Some p True wf_envD(1)[OF wf] show ?thesis
          by (simp add: Q_def x occurs.simps[of F "Var xn T"] lookup_lk)
      qed
    qed
  qed
  then show ?thesis using L by blast
qed

lemma occurs_False:
  assumes "occurs F t env = Some r"
  shows "r = Ok False \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> vt_lookup (tenv env) F = None \<Longrightarrow>
    \<forall>y\<in>reach env (vps t). fst y \<noteq> F"
  using assms
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 oc F t env r)
  have e: "vt_is_empty (tyenv env)" and F: "vt_lookup (tenv env) F = None" using 1 by simp_all
  note IH = "1.IH"[OF _ refl e F]
  show ?case
  proof (cases t)
    case (Var G T)
    show ?thesis
    proof (cases "lk env G T")
      case None
      with 1 Var e have "G \<noteq> F"
        by (auto simp: lookup_lk lk_def var_clash_def split: option.splits if_splits)
      with None Var show ?thesis by (simp add: reach_unbound)
    next
      case (Some u)
      with 1 Var e have "oc F u env = Some (Ok False)"
        by (auto simp: lookup_lk lk_def split: option.splits if_splits)
      from IH[OF this] have "\<forall>y\<in>reach env (vps u). fst y \<noteq> F" .
      moreover have "G \<noteq> F" using F lkD[OF Some] by auto
      moreover have "reach env {(G, T)} \<subseteq> insert (G, T) (reach env (vps u))"
      proof
        fix y assume "y \<in> reach env {(G, T)}"
        then have "(y, (G, T)) \<in> (dep env)\<^sup>*" by (simp add: reach_def)
        then show "y \<in> insert (G, T) (reach env (vps u))"
        proof (cases rule: rtranclE)
          case (step w)
          then have "w \<in> vps u" using Some by (auto simp: dep_def)
          with step(1) show ?thesis by (auto simp: reach_def)
        qed simp
      qed
      ultimately show ?thesis using Var by auto
    qed
  next
    case (App t1 t2)
    with 1 obtain b1 where o1: "oc F t1 env = Some (Ok b1)"
      and rest: "(if b1 then return True else oc F t2 env) = Some (Ok False)"
      by (auto simp: bindM_def split: option.splits res.splits)
    then have "b1 = False" "oc F t2 env = Some (Ok False)" by (auto simp: return_def split: if_splits)
    with IH o1 App show ?thesis by (auto simp: reach_Un)
  next
    case (Abs a T b)
    with 1 IH show ?thesis by simp
  qed (use 1 in \<open>auto simp: reach_def\<close>)
qed


text \<open>
  On well-typed terms in an acyclic, well-typed environment, \<^const>\<open>unify\<close> terminates; the terms
  need not be patterns or \<open>\<beta>\<close>-normal. Head normalisation terminates because instances of
  well-typed terms are strongly normalising. The other recursions decrease the size
  \<^const>\<open>Ms\<close> of the \<open>\<beta>\<close>-normal form of the instance, or, when variables are bound, the number of
  unbound variables reachable from the problem.
\<close>

subsection \<open>Strong normalisation with subterms\<close>

definition subt :: "dB \<Rightarrow> dB \<Rightarrow> bool" where
  "subt s t \<longleftrightarrow> s = dB.Abs t \<or> (\<exists>u. s = t \<degree> u) \<or> (\<exists>u. s = u \<degree> t)"

lemma termip_subt: "termip subt t"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case by (rule accp.accI) (use less in \<open>auto simp: subt_def\<close>)
qed

lemma subt_beta: "subt x x1 \<Longrightarrow> x1 \<rightarrow>\<^sub>\<beta> w1 \<Longrightarrow> \<exists>w. x \<rightarrow>\<^sub>\<beta> w \<and> subt w w1"
  by (auto simp: subt_def)

lemma subts_beta: "subt\<^sup>*\<^sup>* x y \<Longrightarrow> y \<rightarrow>\<^sub>\<beta> z \<Longrightarrow> \<exists>w. x \<rightarrow>\<^sub>\<beta> w \<and> subt\<^sup>*\<^sup>* w z"
proof (induction rule: converse_rtranclp_induct)
  case (step x x1)
  from step.IH[OF step.prems] obtain w1 where "x1 \<rightarrow>\<^sub>\<beta> w1" "subt\<^sup>*\<^sup>* w1 z" by blast
  with subt_beta[OF step.hyps(1)] show ?case by (meson converse_rtranclp_into_rtranclp)
qed blast

lemma termip_beta_subt:
  assumes "termip beta t"
  shows "termip (sup beta subt) t"
proof (rule termip_sup[OF _ termip_subt assms])
  show "subt\<^sup>*\<^sup>* OO beta \<le> beta\<^sup>+\<^sup>+ OO subt\<^sup>*\<^sup>*"
  proof (rule predicate2I)
    fix x y assume "(subt\<^sup>*\<^sup>* OO beta) x y"
    then obtain b where "subt\<^sup>*\<^sup>* x b" "b \<rightarrow>\<^sub>\<beta> y" by auto
    from subts_beta[OF this] obtain w where "x \<rightarrow>\<^sub>\<beta> w" "subt\<^sup>*\<^sup>* w y" by blast
    then show "(beta\<^sup>+\<^sup>+ OO subt\<^sup>*\<^sup>*) x y" by auto
  qed
qed

lemma beta_reds_sup: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> (sup beta subt)\<^sup>*\<^sup>* s t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

definition sn_less :: "(dB \<times> dB) set" where
  "sn_less = {(y, x). termip (sup beta subt) x \<and> (sup beta subt)\<^sup>+\<^sup>+ x y}"

lemma wf_sn_less: "wf sn_less"
proof (rule wfI_pf)
  fix A assume A: "A \<subseteq> sn_less `` A"
  show "A = {}"
  proof (rule ccontr)
    assume "A \<noteq> {}"
    then obtain x where "x \<in> A" by blast
    have "\<forall>x. termip (sup beta subt) x \<longrightarrow> (\<forall>y. (sup beta subt)\<^sup>*\<^sup>* x y \<longrightarrow> y \<notin> A)"
    proof (rule allI, rule impI)
      fix x assume "termip (sup beta subt) x"
      then show "\<forall>y. (sup beta subt)\<^sup>*\<^sup>* x y \<longrightarrow> y \<notin> A"
      proof (induction rule: accp_induct_rule)
        case (1 x)
        show ?case
        proof (intro allI impI notI)
          fix y assume xy: "(sup beta subt)\<^sup>*\<^sup>* x y" and yA: "y \<in> A"
          from yA A obtain z where z: "z \<in> A" "(z, y) \<in> sn_less" by blast
          then have "(sup beta subt)\<^sup>+\<^sup>+ y z" by (simp add: sn_less_def)
          with xy have "(sup beta subt)\<^sup>+\<^sup>+ x z" by (rule rtranclp_tranclp_tranclp)
          then obtain x' where x': "sup beta subt x x'" "(sup beta subt)\<^sup>*\<^sup>* x' z"
            by (auto dest: tranclpD)
          have "conversep (sup beta subt) x' x" using x'(1) by (rule conversepI)
          from "1.IH"[OF this] have "\<forall>ya. (sup beta subt)\<^sup>*\<^sup>* x' ya \<longrightarrow> ya \<notin> A" .
          with x'(2) z(1) show False by blast
        qed
      qed
    qed
    moreover from \<open>x \<in> A\<close> A obtain z where "(z, x) \<in> sn_less" by blast
    then have "termip (sup beta subt) x" by (simp add: sn_less_def)
    ultimately show False using \<open>x \<in> A\<close> by blast
  qed
qed

lemma typable_termip_subt: "typable t \<Longrightarrow> termip (sup beta subt) t"
  by (rule termip_beta_subt[OF typable_termip])

lemma sn_lessI: "typable x \<Longrightarrow> (sup beta subt)\<^sup>+\<^sup>+ x y \<Longrightarrow> (y, x) \<in> sn_less"
  by (simp add: sn_less_def typable_termip_subt)


subsection \<open>Termination of head normalisation\<close>

context
  fixes ar env W
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
begin

abbreviation inst :: "pterm \<Rightarrow> dB" where
  "inst t \<equiv> mk_subst (env_inst env) (tr t)"

lemma head_norm_Ok_typed:
  assumes "hn env t = Some t'" "has_type W Ts t T"
  shows "head_norm env t = Some (Ok t')"
  using hn_head_norm[OF assms(1) wf_envD(1)[OF wf]] head_norm_no_exn[OF wf ety assms(2)]
  by (auto simp: no_exn_def)

lemma reach_card_less:
  assumes "lk env x U = Some u"
  shows "card (reach env (vps u)) < card (reach env (vps (pterm.Var x U)))"
proof (rule psubset_card_mono)
  show "finite (reach env (vps (pterm.Var x U)))" by (simp add: finite_reach)
  have "reach env (vps u) \<subseteq> reach env {(x, U)}" by (rule reach_lk[OF assms])
  moreover have "(x, U) \<notin> reach env (vps u)"
  proof
    assume "(x, U) \<in> reach env (vps u)"
    from reach_lk_trancl[OF assms this] ac show False unfolding acyc_def acyclic_def by blast
  qed
  moreover have "(x, U) \<in> reach env {(x, U)}" by (rule set_mp[OF reach_incl]) simp
  ultimately show "reach env (vps u) \<subset> reach env (vps (pterm.Var x U))" by auto
qed

lemma hn_term: "has_type W Ts t T \<Longrightarrow> \<exists>t'. hn env t = Some t'"
proof (induction t arbitrary: Ts T rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (inst t, card (reach env (vps t)))"]])
  case (1 t)
  have red: "\<exists>t'. hn env u = Some t'"
    if "(sup beta subt)\<^sup>+\<^sup>+ (inst t) (inst u)" "has_type W Us u U" for u Us U
    using "1.IH"[OF _ that(2)] sn_lessI[OF inst_typable[OF ac wf ety "1.prems"] that(1)] by simp
  show ?case
  proof (cases t)
    case (Var x U)
    show ?thesis
    proof (cases "lk env x U")
      case (Some u)
      note lk = lkD[OF Some]
      from env_typedD[OF ety lk] have tyu: "has_type W [] u U" by simp
      have "\<exists>t'. hn env u = Some t'"
        using "1.IH"[OF _ tyu] reach_card_less[OF Some] inst_bound[OF ac wf ety lk] Var by simp
      with Some Var show ?thesis by (subst hn.simps) simp
    qed (use Var in \<open>subst hn.simps; simp\<close>)
  next
    case (Abs a U b)
    from "1.prems" Abs obtain V where tyb: "has_type W (U # Ts) b V" by (auto elim: has_type_elims)
    have "\<exists>t'. hn env b = Some t'"
      by (rule red[OF _ tyb]) (auto simp: Abs subt_def)
    with Abs show ?thesis by (subst hn.simps) auto
  next
    case (App f u)
    from "1.prems" App obtain U where tyf: "has_type W Ts f (U \<rightarrow>\<^sub>T T)" and tyu: "has_type W Ts u U"
      by (auto elim: has_type_elims)
    have pu: "proper u" by (rule has_type_proper[OF tyu])
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a U' body where f: "f = pterm.Abs a U' body" by (cases f) auto
      from tyf f have tyb: "has_type W (U # Ts) body T" by (auto elim: has_type_elims)
      have pb: "proper body" by (rule has_type_proper[OF tyb])
      have "\<exists>t'. hn env (subst_bound u body) = Some t'"
      proof (rule red[OF _ has_type_subst_bound[OF tyb tyu]])
        have "inst t \<rightarrow>\<^sub>\<beta> inst (subst_bound u body)"
          using App f by (simp add: inst_subst_bound[OF ac wf ety pb pu])
        then show "(sup beta subt)\<^sup>+\<^sup>+ (inst t) (inst (subst_bound u body))" by auto
      qed
      with App f show ?thesis by (subst hn.simps) simp
    next
      case False
      have "\<exists>t'. hn env f = Some t'"
        by (rule red[OF _ tyf]) (auto simp: App subt_def)
      then obtain nf where nf: "hn env f = Some nf" by blast
      have hf: "head_norm env f = Some (Ok nf)" by (rule head_norm_Ok_typed[OF nf tyf])
      have tynf: "has_type W Ts nf (U \<rightarrow>\<^sub>T T)" by (rule head_norm_typed[OF hf refl wf ety tyf])
      have rf: "inst f \<rightarrow>\<^sub>\<beta>\<^sup>* inst nf"
        using head_norm_inst[OF ac wf ety hf has_type_proper[OF tyf]] by simp
      have rest: "\<exists>t'. (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
      proof (cases "is_Abs nf")
        case True
        then obtain a U' body where nfa: "nf = pterm.Abs a U' body" by (cases nf) auto
        from tynf nfa have tyb: "has_type W (U # Ts) body T" by (auto elim: has_type_elims)
        have pb: "proper body" by (rule has_type_proper[OF tyb])
        have "\<exists>t'. hn env (subst_bound u body) = Some t'"
        proof (rule red[OF _ has_type_subst_bound[OF tyb tyu]])
          have "inst t \<rightarrow>\<^sub>\<beta>\<^sup>* inst nf \<degree> inst u" using rf App by (simp add: rtrancl_beta_AppL)
          moreover have "inst nf \<degree> inst u \<rightarrow>\<^sub>\<beta> inst (subst_bound u body)"
            using nfa by (simp add: inst_subst_bound[OF ac wf ety pb pu])
          ultimately show "(sup beta subt)\<^sup>+\<^sup>+ (inst t) (inst (subst_bound u body))"
            by (auto intro: rtranclp_into_tranclp1 beta_reds_sup)
        qed
        with nfa show ?thesis by simp
      qed (cases nf; simp)
      with False App nf show ?thesis by (subst hn.simps) (cases f; auto)
    qed
  qed (subst hn.simps; simp)+
qed

lemma head_norm_term: "has_type W Ts t T \<Longrightarrow> \<exists>t'. head_norm env t = Some (Ok t')"
  using hn_term head_norm_Ok_typed by blast

lemma ints_of'_term: "\<forall>t\<in>set ts. \<exists>U. has_type W Ts t U \<Longrightarrow> \<exists>r. ints_of' env ts = Some r"
  unfolding ints_of'_def
  by (rule bindM_term[OF mapM_term ints_of_term]) (use head_norm_term in blast)

end


subsection \<open>Pruning steps\<close>

text \<open>
  \<open>prunes ar W env W' env' S\<close>: \<open>env'\<close> extends \<open>env\<close> by bindings that prune the arguments of
  variables in \<open>S\<close> or of new variables; \<open>W'\<close> types \<open>env'\<close> and agrees with \<open>W\<close> on the old variables.
\<close>

definition prunes :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "prunes ar W env W' env' S \<longleftrightarrow> extends env' env \<and> maxidx env \<le> maxidx env' \<and> env_inv ar W' env' \<and>
    agreeV (maxidx env) W W' \<and>
    (\<forall>X. reach env' X \<subseteq> reach env X \<union> fr env) \<and>
    (\<forall>X. finite X \<longrightarrow> (\<forall>y\<in>X. snd (fst y) \<le> maxidx env) \<longrightarrow> card (unb env' X) \<le> card (unb env X)) \<and>
    (\<forall>t Ts T. has_type W Ts t T \<longrightarrow> below (maxidx env) t \<longrightarrow> Ms env' W' t = Ms env W t) \<and>
    (\<forall>x X. lk env x X = None \<longrightarrow> lk env' x X \<noteq> None \<longrightarrow> (x, X) \<in> S \<union> fr env)"

lemma prunes_refl: "env_inv ar W env \<Longrightarrow> prunes ar W env W env S"
  by (auto simp: prunes_def)

lemma prunesD:
  assumes "prunes ar W env W' env' S"
  shows "extends env' env" "maxidx env \<le> maxidx env'" "env_inv ar W' env'" "agreeV (maxidx env) W W'"
    "reach env' X \<subseteq> reach env X \<union> fr env"
    "finite X \<Longrightarrow> \<forall>y\<in>X. snd (fst y) \<le> maxidx env \<Longrightarrow> card (unb env' X) \<le> card (unb env X)"
    "has_type W Ts t T \<Longrightarrow> below (maxidx env) t \<Longrightarrow> Ms env' W' t = Ms env W t"
    "lk env x XT = None \<Longrightarrow> lk env' x XT \<noteq> None \<Longrightarrow> (x, XT) \<in> S \<union> fr env"
  using assms unfolding prunes_def by blast+

lemma prunes_mono: "prunes ar W env W' env' S \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> prunes ar W env W' env' S'"
  unfolding prunes_def by blast

lemma prunes_trans:
  assumes p1: "prunes ar W env W1 env1 S" and p2: "prunes ar W1 env1 W2 env2 S'" and S': "S' \<subseteq> S \<union> fr env"
  shows "prunes ar W env W2 env2 S"
proof -
  have m: "maxidx env \<le> maxidx env1" "maxidx env1 \<le> maxidx env2" using p1 p2 by (simp_all add: prunes_def)
  note f = fr_mono[OF m(1)]
  have "reach env2 X \<subseteq> reach env X \<union> fr env" for X
    using prunesD(5)[OF p1, of X] prunesD(5)[OF p2, of X] f by blast
  moreover have "card (unb env2 X) \<le> card (unb env X)"
    if "finite X" "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" for X
  proof -
    have "\<forall>y\<in>X. snd (fst y) \<le> maxidx env1" using that(2) m(1) by force
    with prunesD(6)[OF p1 that] prunesD(6)[OF p2 that(1)] show ?thesis by linarith
  qed
  moreover have "Ms env2 W2 t = Ms env W t" if "has_type W Ts t T" "below (maxidx env) t" for t Ts T
  proof -
    have "has_type W1 Ts t T" by (rule has_type_agreeV[OF that prunesD(4)[OF p1]])
    moreover have "below (maxidx env1) t" using that(2) m(1) by (rule below_mono)
    ultimately show ?thesis using prunesD(7)[OF p1 that] prunesD(7)[OF p2] by simp
  qed
  moreover have "(x, X) \<in> S \<union> fr env" if "lk env x X = None" "lk env2 x X \<noteq> None" for x X
  proof (cases "lk env1 x X = None")
    case True
    with prunesD(8)[OF p2 True that(2)] S' f show ?thesis by blast
  next
    case False
    with prunesD(8)[OF p1 that(1)] show ?thesis by blast
  qed
  moreover have "agreeV (maxidx env) W W2"
    using agreeV_trans[OF prunesD(4)[OF p1] prunesD(4)[OF p2] m(1)] .
  ultimately show ?thesis using p1 p2 m unfolding prunes_def by (auto intro: extends_trans)
qed

lemma has_type_vps: "has_type V Ts u U \<Longrightarrow> (y, T) \<in> vps u \<Longrightarrow> V y = T"
  by (induction rule: has_type.induct) auto

lemma prune_step:
  assumes ti: "env_inv ar W env"
    and gv: "genvar a env Hty = (env1, H)" and upd: "ok (update (G, Gty) u env1) env2"
    and u: "ok (mkabs binders js (app H ks)) u" and ks: "\<forall>k\<in>set ks. 0 \<le> k"
    and T: "Gty = foldr fun_type Us U" "length Us = length js"
      "Hty = foldr fun_type Vs U" "length Vs = length ks"
    and G: "snd G \<le> maxidx env"
    and wf2: "wf_env ar env2" and ety2: "env_typed W' env2" and ag: "agreeV (maxidx env) W W'"
  shows "prunes ar W env W' env2 {(G, Gty)}"
proof -
  note t0 = env_invD[OF ti]
  have fr: "fresh_env env" by (rule t0(4))
  define m where "m = maxidx env"
  define Hn where "Hn = (a, m + 1)"
  note g = genvar_simps[OF gv, folded m_def]
  note up = ok_update[OF upd]
  have H: "H = Var Hn Hty" using g(4) by (simp add: Hn_def)
  have G0: "vt_lookup (tenv env) G = None" using up(1) g(1) by simp
  have t2: "tenv env2 = vt_update (G, (Gty, u)) (tenv env)" using up(2) g(1) by simp
  have vu: "vps u = {(Hn, Hty)}" using vps_mkabs[OF u] H by simp
  have m1: "m < snd Hn" by (simp add: Hn_def)
  have lH: "lk env Hn Hty = None" using lk_fresh[OF fr] m1 by (simp add: m_def)
  have rH: "reach env (vps u) = {(Hn, Hty)}" using vu reach_unbound[OF lH] by simp
  have GH: "(G, Gty) \<notin> reach env (vps u)" using rH G m1 by (auto simp: m_def)
  have d2: "dep env2 = dep env \<union> (\<lambda>y. (y, (G, Gty))) ` vps u" by (rule dep_update[OF t2 G0])
  have ac2: "acyc env2" using acyclic_update[OF d2 GH] t0(1) by (simp add: acyc_def)
  have mx2: "maxidx env2 = m + 1" using up(4) g(3) by simp
  have fr2: "fresh_env env2"
    unfolding fresh_env_def
  proof (intro allI impI)
    fix x U' u' assume "vt_lookup (tenv env2) x = Some (U', u')"
    then consider "x = G" "u' = u" | "vt_lookup (tenv env) x = Some (U', u')"
      using t2 by (auto split: if_splits)
    then show "snd x \<le> maxidx env2 \<and> below (maxidx env2) u'"
    proof cases
      case 1
      have "vars u = {Hn}" using vars_mkabs[OF u] H by (simp add: vars_app)
      with 1 G show ?thesis by (simp add: mx2 below_def m_def Hn_def)
    next
      case 2
      from fresh_envD[OF fr 2] show ?thesis by (auto simp: mx2 m_def intro: below_mono)
    qed
  qed
  have ext: "extends env2 env"
    using ok_update_extends[OF upd] genvar_extends[OF gv] by (rule extends_trans)
  have lk2: "lk env2 x X = (if x = G then (if X = Gty then Some u else None) else lk env x X)" for x X
    by (simp add: lk_update[OF t2])
  have r2: "reach env2 X = reach env X \<union> (if (G, Gty) \<in> reach env X then {(Hn, Hty)} else {})" for X
    using reach_update[OF d2 GH] rH by simp
  have u2: "unb env2 X = (unb env X - {(G, Gty)}) \<union> (if (G, Gty) \<in> reach env X then {(Hn, Hty)} else {})"
    for X
  proof -
    have "unb env (vps u) = {(Hn, Hty)}" using rH lH by (auto simp: unb_def)
    then show ?thesis using unb_update[OF t2 G0 GH] by simp
  qed
  have "card (unb env2 X) \<le> card (unb env X)"
    if X: "finite X" "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" for X
  proof -
    have fu: "finite (unb env X)" by (rule finite_unb[OF X(1)])
    have nH: "(Hn, Hty) \<notin> unb env X"
    proof
      assume "(Hn, Hty) \<in> unb env X"
      then have "(Hn, Hty) \<in> reach env X" by (simp add: unb_def)
      from reach_old[OF fr X(2) this] m1 show False by (simp add: m_def)
    qed
    show ?thesis
    proof (cases "(G, Gty) \<in> reach env X")
      case True
      then have G1: "(G, Gty) \<in> unb env X" using G0 by (simp add: unb_def lk_def)
      have "card (unb env2 X) = card (insert (Hn, Hty) (unb env X - {(G, Gty)}))" using True by (simp add: u2)
      also have "\<dots> = Suc (card (unb env X - {(G, Gty)}))" using fu nH by simp
      also have "\<dots> = card (unb env X)" by (rule card_Suc_Diff1[OF fu G1])
      finally show ?thesis by simp
    next
      case False
      then show ?thesis using fu by (simp add: u2 card_Diff1_le)
    qed
  qed
  moreover have "Ms env2 W' t = Ms env W t" if "has_type W Ts t T" "below (maxidx env) t" for t Ts T
  proof (rule Ms_prune[OF t0(1-4) ac2 wf2 ety2 ext ag _ that])
    show "prunes_inst W' env env2"
      unfolding prunes_inst_def
    proof (intro allI impI)
      fix y assume y: "vt_lookup (tenv env) y = None" "vt_lookup (tenv env2) y \<noteq> None"
      then have yG: "y = G" using t2 by (auto split: if_splits)
      have lkG: "vt_lookup (tenv env2) G = Some (Gty, u)" using t2 by simp
      have Hu: "vt_lookup (tenv env2) Hn = None"
        using t2 fresh_envD[OF fr, of Hn] m1 G by (cases "vt_lookup (tenv env) Hn") (auto simp: m_def)
      from env_typedD[OF ety2 lkG] have WG: "W' G = Gty" and tyu: "has_type W' [] u Gty" by auto
      have WH: "W' Hn = Hty" using has_type_vps[OF tyu] vu by simp
      have "tr u = Abs_m (length js) (dB.Var (code (AVar Hn)) \<degree>\<degree> map BVar (nats ks))"
        using ok_mkabs[OF u] H by (simp add: tr_app')
      then have "env_inst env2 (code (AVar G)) =
          Abs_m (length js) (dB.Var (code (AVar Hn)) \<degree>\<degree> map BVar (nats ks))"
        by (simp add: inst_bound[OF ac2 wf2 ety2 lkG] inst_unbound[OF ac2 wf2 ety2 Hu] comp_def)
      moreover have "ty_arity (trty (W' G)) = length js + ty_arity (trty U)"
        using WG T by (simp add: trty_foldr ty_arity_funs)
      moreover have "ty_arity (trty (W' Hn)) = length (nats ks) + ty_arity (trty U)"
        using WH T by (simp add: trty_foldr ty_arity_funs)
      ultimately show "\<exists>H ks m a. env_inst env2 (code (AVar y)) = Abs_m m (dB.Var (code (AVar H)) \<degree>\<degree> map BVar ks) \<and>
          vt_lookup (tenv env2) H = None \<and> ty_arity (trty (W' y)) = m + a \<and> ty_arity (trty (W' H)) = length ks + a"
        using yG Hu by blast
    qed
  qed
  moreover have "reach env2 X \<subseteq> reach env X \<union> fr env" for X
    using r2 m1 by (auto simp: fr_def m_def)
  moreover have "(x, X) \<in> {(G, Gty)} \<union> fr env" if "lk env x X = None" "lk env2 x X \<noteq> None" for x X
    using that lk2[of x X] by (auto split: if_splits)
  moreover have "env_inv ar W' env2" using ac2 wf2 ety2 fr2 by (simp add: env_inv_def)
  ultimately show ?thesis using ext mx2 ag by (simp add: prunes_def m_def)
qed


subsection \<open>Termination of projections\<close>

lemma nat_of_integer_succ: "0 \<le> d \<Longrightarrow> nat_of_integer (d + 1) = Suc (nat_of_integer d)"
  by (simp add: integer_eq_iff nat_of_integer_add)

lemma pr_term:
  "Ms env W s = n \<Longrightarrow> env_inv ar W env \<Longrightarrow> has_type W (map snd binders) s T \<Longrightarrow> typs_ok ar s \<Longrightarrow>
    below (maxidx env) s \<Longrightarrow> binders_ok ar binders \<Longrightarrow> 0 \<le> d \<Longrightarrow> nat_of_integer d \<le> length binders \<Longrightarrow>
    \<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer d + nat_of_integer x < length binders \<Longrightarrow>
    \<exists>r. pr xs s env d binders = Some r \<and>
      (\<forall>s' env'. r = Ok (s', env') \<longrightarrow> (\<exists>W'. prunes ar W env W' env' (reach env (vps s))) \<and>
        vps s' \<subseteq> reach env' (vps s) \<and> below (maxidx env') s')"
proof (induction n arbitrary: s env W d binders T rule: less_induct)
  case (less n s env W d binders T)
  have pz: "Ms env W s = n" and ti: "env_inv ar W env" and tys: "has_type W (map snd binders) s T"
    and ts: "typs_ok ar s" and bs: "below (maxidx env) s" and bok: "binders_ok ar binders"
    and d0: "0 \<le> d" and dl: "nat_of_integer d \<le> length binders"
    and xs0: "\<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer d + nat_of_integer x < length binders"
    using less.prems by simp_all
  note t0 = env_invD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(2)])
  have ps: "proper s" by (rule has_type_proper[OF tys])
  from head_norm_term[OF t0(1-3) tys] obtain s0 where ok: "head_norm env s = Some (Ok s0)" by blast
  define R where "R = (\<lambda>s0. if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> pr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty \<Rightarrow> do {
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
            return (list_comb h' ts', env')}))"
  define P where "P r \<longleftrightarrow> (\<forall>s' env'. r = Ok (s', env') \<longrightarrow> (\<exists>W'. prunes ar W env W' env' (reach env (vps s))) \<and>
    vps s' \<subseteq> reach env' (vps s) \<and> below (maxidx env') s')" for r
  have pr_hn: "pr xs s env d binders = head_norm env s \<bind> R"
    unfolding R_def by (subst pr.simps) (rule refl)
  have hh: "head_norm env s = return s0" using ok by (simp add: return_def)
  have pr_eq: "pr xs s env d binders = R s0" by (simp add: pr_hn hh)
  have vs0: "vps s0 \<subseteq> reach env (vps s)" by (rule hn_vps[OF head_norm_hn[OF ok e refl]])
  have tys0: "has_type W (map snd binders) s0 T" by (rule head_norm_typed[OF ok refl t0(2,3) tys])
  have pz0: "Ms env W s0 = n" using Ms_head_norm[OF t0(1-3) ok ps tys] pz by simp
  from head_norm_sound[OF ok refl t0(2) ps ts] have ts0: "typs_ok ar s0" by simp
  have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF ok refl t0(2,4) bs])
  have vmono: "reach env' (vps s0) \<subseteq> reach env' (vps s)" if "extends env' env" for env'
    using vs0 reach_extends[OF that] by (intro reach_mono) blast
  have rmono: "reach env (vps x) \<subseteq> reach env (vps s)" if "vps x \<subseteq> vps s0" for x
    using that vs0 by (intro reach_mono) blast
  have "\<exists>r. pr xs s env d binders = Some r \<and> P r"
  proof (cases "is_Abs s0")
    case True
    then obtain a U t where s0: "s0 = Abs a U t" by (cases s0) auto
    from tys0 s0 obtain V where tyt: "has_type W (U # map snd binders) t V" by (auto elim: has_type_elims)
    have m: "Ms env W t + 2 = n" using Ms_Abs[OF t0(1-3) tys0[unfolded s0]] pz0 s0 by simp
    have tt: "typs_ok ar t" "ground ar U" using ts0 s0 by simp_all
    have bt: "below (maxidx env) t" using bs0 s0 by simp
    have bok': "binders_ok ar ((a, U) # binders)" using bok tt(2) by (simp add: binders_ok_def)
    have d1: "0 \<le> d + 1" "nat_of_integer (d + 1) \<le> length ((a, U) # binders)"
      using d0 dl by (simp_all add: nat_of_integer_succ)
    have xs1: "\<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer (d + 1) + nat_of_integer x < length ((a, U) # binders)"
      using xs0 d0 by (simp add: nat_of_integer_succ)
    from less.IH[OF _ refl ti _ tt(1) bt bok' d1 xs1, of V] m tyt
    obtain r where r: "pr xs t env (d + 1) ((a, U) # binders) = Some r"
      and rP: "\<forall>s' env'. r = Ok (s', env') \<longrightarrow> (\<exists>W'. prunes ar W env W' env' (reach env (vps t))) \<and>
        vps s' \<subseteq> reach env' (vps t) \<and> below (maxidx env') s'"
      by auto
    show ?thesis
    proof (cases r)
      case (Ok p)
      obtain t' env' where p: "p = (t', env')" by force
      with rP Ok obtain W' where pr1: "prunes ar W env W' env' (reach env (vps t))"
        and v1: "vps t' \<subseteq> reach env' (vps t)" and b1: "below (maxidx env') t'" by auto
      have "prunes ar W env W' env' (reach env (vps s))" using pr1 rmono[of t] s0 by (auto intro: prunes_mono)
      moreover have "vps (Abs a U t') \<subseteq> reach env' (vps s)"
        using v1 vmono[OF prunesD(1)[OF pr1]] s0 by auto
      ultimately have "P (Ok (Abs a U t', env'))" using b1 by (auto simp: P_def)
      with pr_eq r Ok p s0 show ?thesis by (simp add: R_def return_def bindM_def)
    next
      case (Err e')
      with pr_eq r s0 show ?thesis by (simp add: R_def bindM_def P_def)
    qed
  next
    case nA: False
    obtain h ts where sc: "strip_comb s0 = (h, ts)" by force
    have s0e: "s0 = list_comb h ts" by (rule strip_comb_list_comb[OF sc])
    have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF sc])
    from tys0 s0e obtain Us where tyh: "has_type W (map snd binders) h (foldr fun_type Us T)"
      and tyts: "list_all2 (has_type W (map snd binders)) ts Us"
      by (auto simp: has_type_list_comb)
    have tts': "\<forall>t\<in>set ts. \<exists>U. has_type W (map snd binders) t U"
      using tyts by (metis in_set_conv_nth list_all2_conv_all_nth)
    consider (flex) F Fty where "h = Var F Fty" | (abs) "is_Abs h" | (rigid) "is_rigid h"
      using nApp has_type_proper[OF tyh] by (cases h) (auto simp: is_rigid_def)
    then show ?thesis
    proof cases
      case abs
      with nA sc have "R s0 = raise Pattern" by (cases h) (simp_all add: R_def)
      with pr_eq show ?thesis by (simp add: raise_def P_def)
    next
      case flex
      have trm: "\<exists>r. R s0 = Some r"
        using nA sc flex unfolding R_def
        by (auto simp: Let_def mk_hnf_def split: prod.splits
            intro!: bindM_term ints_of'_term[OF t0(1-3) tts'] mapM_term try_trans_term type_of_G_term[OF e]
              mkabs_term update_term)
      then obtain r where r: "R s0 = Some r" by blast
      have "P r"
        unfolding P_def
      proof (intro allI impI)
        fix s' env'' assume rOk: "r = Ok (s', env'')"
        with r nA sc flex obtain js js' Hty where js: "ok (ints_of' env ts) js"
          and js': "ok (mapM (try_trans xs d) js) js'"
          and Hty: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty"
          and rest2: "ok (case genvar (fst F) env Hty of (env1, H) \<Rightarrow>
            mk_hnf binders js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env1 \<bind>
              (\<lambda>env''. return (app H (List.map_filter id js'), env'')))) (s', env'')"
          unfolding R_def by (auto simp: Let_def)
        obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
        with rest2 obtain t where t: "ok (mkabs binders js (app H (mk_proj_list js'))) t"
          and env'': "ok (update (F, Fty) t env1) env''" and s': "s' = app H (List.map_filter id js')"
          by (auto simp: mk_hnf_def)
        have prs: "pr xs s env d binders = Some (Ok (s', env''))" using pr_eq r rOk by simp
        from pr_exn[OF prs t0(2) bok t0(3,4) ps ts tys bs d0 dl xs0] obtain W'' where
          te: "ty_ext ar W env W'' env''" by auto
        note te' = te[unfolded ty_ext_def]
        from ok_type_of_G'[OF Hty e] obtain Us' U Vs where
          T: "Fty = foldr fun_type Us' U" "length Us' = length js"
            "Hty = foldr fun_type Vs U" "length Vs = length (mk_proj_list js')"
            and ks: "\<forall>k\<in>set (mk_proj_list js'). 0 \<le> k"
          by auto
        have Fm: "snd F \<le> maxidx env" using bs0 s0e flex by (simp add: below_list_comb)
        have p1: "prunes ar W env W'' env'' {(F, Fty)}"
          by (rule prune_step[OF ti G env'' t ks T Fm]) (use te' in simp_all)
        have Fr: "(F, Fty) \<in> reach env (vps s)" using vs0 s0e flex by (auto simp: vps_list_comb)
        have "prunes ar W env W'' env'' (reach env (vps s))" using p1 Fr by (auto intro: prunes_mono)
        moreover have "vps s' \<subseteq> reach env'' (vps s)"
        proof
          fix y assume "y \<in> vps s'"
          then have y: "y = ((fst F, maxidx env + 1), Hty)" using s' genvar_simps(4)[OF G] by simp
          have "lk env'' F Fty = Some t" using ok_update_lookup[OF env''] by (simp add: lk_def)
          moreover have "y \<in> vps t" using vps_mkabs[OF t] genvar_simps(4)[OF G] y by simp
          ultimately have "(y, (F, Fty)) \<in> dep env''" by (auto simp: dep_iff)
          moreover have "(F, Fty) \<in> reach env'' (vps s)"
            using Fr reach_extends[OF prunesD(1)[OF p1]] by blast
          ultimately show "y \<in> reach env'' (vps s)" by (rule reach_pred)
        qed
        moreover have "below (maxidx env'') s'"
          using s' genvar_simps(3,4)[OF G] ok_update(4)[OF env''] by (simp add: below_app)
        ultimately show "(\<exists>W'. prunes ar W env W' env'' (reach env (vps s))) \<and> vps s' \<subseteq> reach env'' (vps s) \<and>
          below (maxidx env'') s'" by blast
      qed
      with r pr_eq show ?thesis by simp
    next
      case rigid
      have nV: "\<not> is_Var h" "\<not> is_Abs h" using rigid by (auto simp: is_rigid_def)
      define hc where "hc = (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h)"
      have hc: "\<exists>r. hc = Some r \<and> (\<forall>h'. r = Ok h' \<longrightarrow> vps h' = {} \<and> vars h' = {})"
        using rigid trans_term[of xs d]
        by (auto simp: hc_def is_rigid_def return_def bindM_def split: option.splits res.splits)
      define R0 where "R0 e \<longleftrightarrow> (\<exists>We. prunes ar W env We e (reach env (vps s)))" for e
      define S0 where "S0 e e' \<longleftrightarrow> extends e' e \<and> maxidx e \<le> maxidx e'" for e e'
      define Q0 where "Q0 x y e' \<longleftrightarrow> vps y \<subseteq> reach e' (vps x) \<and> below (maxidx e') y" for x y e'
      have tts: "\<forall>t\<in>set ts. typs_ok ar t" "\<forall>t\<in>set ts. below (maxidx env) t"
        using ts0 bs0 s0e by (simp_all add: typs_ok_list_comb below_list_comb)
      have vts: "vps x \<subseteq> vps s0" if "x \<in> set ts" for x using that s0e by (auto simp: vps_list_comb)
      have Msum: "Ms env W s0 = 1 + sum_list (map (Ms env W) ts)"
        using Ms_rigid[OF t0(1-3) rigid tys0[unfolded s0e]] s0e by simp
      have mp: "\<exists>r. mapAccM (\<lambda>s env. pr xs s env d binders) ts env = Some r \<and>
          (\<forall>ys e'. r = Ok (ys, e') \<longrightarrow> R0 e' \<and> S0 env e' \<and> list_all2 (\<lambda>x y. Q0 x y e') ts ys)"
      proof (rule Pattern_Termination.csig.mapAccM_inv)
        fix x e assume x: "x \<in> set ts" and Re: "R0 e"
        from Re obtain We where pe: "prunes ar W env We e (reach env (vps s))" by (auto simp: R0_def)
        from x tyts obtain Ux where tyx: "has_type W (map snd binders) x Ux"
          by (metis in_set_conv_nth list_all2_conv_all_nth)
        have bx0: "below (maxidx env) x" using tts(2) x by simp
        have "Ms env W x < n"
          using Msum pz0 x by (induction ts) (auto simp: sum_list_map_remove1[of x] dest: member_le_sum_list)
        then have m: "Ms e We x < n" using prunesD(7)[OF pe tyx bx0] by simp
        have tyx': "has_type We (map snd binders) x Ux" by (rule has_type_agreeV[OF tyx bx0 prunesD(4)[OF pe]])
        have bx: "below (maxidx e) x" using bx0 prunesD(2)[OF pe] by (rule below_mono)
        from less.IH[OF m refl prunesD(3)[OF pe] tyx' _ bx bok d0 dl xs0] tts(1) x
        obtain r where r: "pr xs x e d binders = Some r"
          and rP: "\<forall>y e'. r = Ok (y, e') \<longrightarrow> (\<exists>W'. prunes ar We e W' e' (reach e (vps x))) \<and>
            vps y \<subseteq> reach e' (vps x) \<and> below (maxidx e') y"
          by blast
        have "R0 e' \<and> S0 e e' \<and> Q0 x y e'" if "r = Ok (y, e')" for y e'
        proof -
          from rP that obtain W' where p2: "prunes ar We e W' e' (reach e (vps x))"
            and q: "vps y \<subseteq> reach e' (vps x)" "below (maxidx e') y" by auto
          have "reach e (vps x) \<subseteq> reach env (vps s) \<union> fr env"
            using prunesD(5)[OF pe, of "vps x"] rmono[OF vts[OF x]] by blast
          with prunes_trans[OF pe p2] have "R0 e'" by (auto simp: R0_def)
          moreover have "S0 e e'" using prunesD(1,2)[OF p2] by (simp add: S0_def)
          ultimately show ?thesis using q by (simp add: Q0_def)
        qed
        with r show "\<exists>r. pr xs x e d binders = Some r \<and>
          (\<forall>y e'. r = Ok (y, e') \<longrightarrow> R0 e' \<and> S0 e e' \<and> Q0 x y e')" by blast
      next
        show "S0 e1 e3" if "S0 e1 e2" "S0 e2 e3" for e1 e2 e3
          using that by (auto simp: S0_def intro: extends_trans)
      next
        show "S0 e e" for e by (simp add: S0_def)
      next
        show "Q0 x y e2" if "Q0 x y e1" "S0 e1 e2" for x y e1 e2
          using that reach_extends[of e2 e1] by (auto simp: Q0_def S0_def intro: below_mono)
      next
        show "R0 env" using prunes_refl[OF ti] by (auto simp: R0_def)
      qed
      from hc obtain rh where rh: "hc = Some rh" and rhP: "\<forall>h'. rh = Ok h' \<longrightarrow> vps h' = {} \<and> vars h' = {}"
        by blast
      from mp obtain rm where rm: "mapAccM (\<lambda>s env. pr xs s env d binders) ts env = Some rm"
        and rmP: "\<forall>ys e'. rm = Ok (ys, e') \<longrightarrow> R0 e' \<and> S0 env e' \<and> list_all2 (\<lambda>x y. Q0 x y e') ts ys"
        by blast
      have R_eq: "R s0 = hc \<bind> (\<lambda>h'. mapAccM (\<lambda>s env. pr xs s env d binders) ts env \<bind>
          (\<lambda>(ts', env'). return (list_comb h' ts', env')))"
        using nA sc nV unfolding R_def hc_def by simp
      show ?thesis
      proof (cases rh)
        case (Err e')
        with R_eq rh pr_eq show ?thesis by (simp add: bindM_def P_def)
      next
        case (Ok h')
        note hv = rhP[rule_format, OF Ok]
        show ?thesis
        proof (cases rm)
          case (Err e')
          with R_eq rh rm Ok pr_eq show ?thesis by (simp add: bindM_def P_def)
        next
          case (Ok q)
          obtain ts' env' where q: "q = (ts', env')" by force
          with rmP Ok have R0': "R0 env'" and S0': "S0 env env'" and Q: "list_all2 (\<lambda>x y. Q0 x y env') ts ts'"
            by auto
          have "vps (list_comb h' ts') \<subseteq> reach env' (vps s)"
          proof -
            have "vps y \<subseteq> reach env' (vps s)" if "y \<in> set ts'" for y
            proof -
              from list_all2_set2'[OF Q] that obtain x where x: "x \<in> set ts" "Q0 x y env'"
                by blast
              have e': "extends env' env" using S0' by (simp add: S0_def)
              have "reach env' (vps x) \<subseteq> reach env' (vps s)"
                using reach_subset[OF vts[OF x(1)], of env'] vmono[OF e'] by (rule order_trans)
              with x(2) show ?thesis by (auto simp: Q0_def)
            qed
            with hv show ?thesis by (auto simp: vps_list_comb)
          qed
          moreover have "below (maxidx env') (list_comb h' ts')"
          proof -
            have "below (maxidx env') y" if "y \<in> set ts'" for y
              using list_all2_set2'[OF Q] that by (auto simp: Q0_def)
            moreover have "below (maxidx env') h'" using hv by (simp add: below_def)
            ultimately show ?thesis by (simp add: below_list_comb)
          qed
          ultimately have "P (Ok (list_comb h' ts', env'))" using R0' by (auto simp: P_def R0_def)
          with R_eq rh rm \<open>rh = Ok h'\<close> Ok q pr_eq show ?thesis by (simp add: bindM_def return_def)
        qed
      qed
    qed
  qed
  then show ?case by (simp add: P_def)
qed

lemma proj_term:
  assumes ti: "env_inv ar W env" and ty: "has_type W (map snd binders) t T" and ts: "typs_ok ar t"
    and bt: "below (maxidx env) t" and bok: "binders_ok ar binders"
    and is0: "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders"
  shows "\<exists>r. proj t env binders is = Some r \<and>
    (\<forall>u env'. r = Ok (u, env') \<longrightarrow> (\<exists>W'. prunes ar W env W' env' (reach env (vps t))) \<and>
      vps u \<subseteq> reach env' (vps t) \<and> below (maxidx env') u)"
proof (cases "downto0 is (ilength binders - 1)")
  case True
  then show ?thesis using prunes_refl[OF ti] reach_incl[of "vps t" env] bt
    by (auto simp: proj_def return_def)
next
  case False
  have "\<forall>x\<in>set is. 0 \<le> x \<and> nat_of_integer 0 + nat_of_integer x < length binders" using is0 by simp
  from pr_term[OF refl ti ty ts bt bok _ _ this] False show ?thesis by (simp add: proj_def)
qed


subsection \<open>Termination of the rigid occurs check\<close>

lemma rigid_occurs_term:
  assumes ti: "env_inv ar W env"
  shows "has_type W Ts t T \<Longrightarrow> \<exists>r. rigid_occurs F t env = Some r"
proof (induction "Ms env W t" arbitrary: t Ts T rule: less_induct)
  case less
  note t0 = env_invD[OF ti]
  from head_norm_term[OF t0(1-3) less.prems] obtain t' where hn: "head_norm env t = Some (Ok t')"
    by blast
  have tyt': "has_type W Ts t' T" by (rule head_norm_typed[OF hn refl t0(2,3) less.prems])
  have pz: "Ms env W t' = Ms env W t" by (rule Ms_head_norm[OF t0(1-3) hn has_type_proper less.prems])
    (rule less.prems)
  have IH: "\<exists>r. rigid_occurs F u env = Some r" if "has_type W Us u U" "Ms env W u < Ms env W t'" for u Us U
    using less.hyps[OF _ that(1)] that(2) pz by simp
  define B where "B = (\<lambda>t'. case t' of
        pterm.Abs _ _ u \<Rightarrow> rigid_occurs F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              pterm.Var G _ \<Rightarrow>
                if G = F then
                  handle (ints_of' env ts \<bind> (\<lambda>_. return True))
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | pterm.Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u env) ts)))"
  have ro: "rigid_occurs F t env = head_norm env t \<bind> B"
    by (subst rigid_occurs.simps) (simp add: B_def)
  have "\<exists>r. B t' = Some r"
  proof (cases "is_Abs t'")
    case True
    then obtain a U u where t'a: "t' = pterm.Abs a U u" by (cases t') auto
    from tyt' t'a obtain V where tyu: "has_type W (U # Ts) u V" by (auto elim: has_type_elims)
    have "Ms env W t' = Ms env W u + 2" using Ms_Abs[OF t0(1-3) tyt'[unfolded t'a]] t'a by simp
    with IH[OF tyu] t'a show ?thesis by (simp add: B_def)
  next
    case nA: False
    obtain h ts where sc: "strip_comb t' = (h, ts)" by force
    note t'e = strip_comb_list_comb[OF sc]
    have B: "B t' = (case h of
        pterm.Var G _ \<Rightarrow>
          if G = F then
            handle (ints_of' env ts \<bind> (\<lambda>_. return True))
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
          else return False
      | pterm.Abs _ _ _ \<Rightarrow> return False
      | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u env) ts)"
      using sc nA unfolding B_def by (cases t') simp_all
    from tyt' t'e obtain Us where tyh: "has_type W Ts h (foldr fun_type Us T)"
      and tyts: "list_all2 (has_type W Ts) ts Us"
      by (auto simp: has_type_list_comb)
    have tts: "\<forall>u\<in>set ts. \<exists>U. has_type W Ts u U"
      using tyts by (metis in_set_conv_nth list_all2_conv_all_nth)
    have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF sc])
    consider (V) G U where "h = Var G U" | (A) "is_Abs h" | (R) "is_rigid h"
      using nApp has_type_proper[OF tyh] by (cases h) (auto simp: is_rigid_def)
    then show ?thesis
    proof cases
      case R
      have "Ms env W t' = 1 + sum_list (map (Ms env W) ts)"
        using Ms_rigid[OF t0(1-3) R tyt'[unfolded t'e]] t'e by simp
      then have "Ms env W u < Ms env W t'" if "u \<in> set ts" for u
        using member_le_sum_list[of "Ms env W u" "map (Ms env W) ts"] that by simp
      with IH tyts have "\<exists>r. existsM (\<lambda>u. rigid_occurs F u env) ts = Some r"
        by (intro existsM_term) (metis in_set_conv_nth list_all2_conv_all_nth)
      with B R show ?thesis by (cases h) (simp_all add: is_rigid_def)
    next
      case V
      from ints_of'_term[OF t0(1-3) tts] have "\<exists>r. handle (ints_of' env ts \<bind> (\<lambda>_. return True))
          (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) = Some r"
        by (auto intro!: handle_term bindM_term split: exn.splits)
      with B V show ?thesis by simp
    next
      case A
      with B show ?thesis by (cases h) simp_all
    qed
  qed
  then show ?case using hn ro by (auto intro!: bindM_term)
qed


subsection \<open>Termination of the flexible cases\<close>

lemma flexrigid_term:
  assumes ti: "env_inv ar W env" and tyF: "has_type W (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type W (map snd binders) t T" and pt: "typs_ok ar t"
    and bt: "below (maxidx env) t" and Fm: "snd F \<le> maxidx env" and bok: "binders_ok ar binders"
    and gF: "ground ar Fty"
  shows "\<exists>r. flexrigid env binders F Fty is t = Some r \<and> (\<forall>env''. r = Ok env'' \<longrightarrow>
    (\<exists>W''. env_inv ar W'' env'' \<and> agreeV (maxidx env) W W'') \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      vps t \<subseteq> reach env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y)))"
proof -
  note t0 = env_invD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(2)])
  have is0: "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders"
    using has_type_app_Var(1)[OF tyF] by simp
  have hnd: "\<not> ok (case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env binders F is t)) | _ \<Rightarrow> raise e) y"
    for e and y :: env by (cases e) simp_all
  from occurs_term[OF t0(1,2)] obtain ro where ro: "occurs F t env = Some ro" by blast
  from proj_term[OF ti tyt pt bt bok is0] obtain rp where rp: "proj t env binders is = Some rp"
    and rpP: "\<forall>u env'. rp = Ok (u, env') \<longrightarrow> (\<exists>W'. prunes ar W env W' env' (reach env (vps t))) \<and>
      vps u \<subseteq> reach env' (vps t) \<and> below (maxidx env') u" by blast
  from rigid_occurs_term[OF ti tyt] obtain rro where rro: "rigid_occurs F t env = Some rro" by blast
  have "\<exists>r. flexrigid env binders F Fty is t = Some r"
    unfolding flexrigid_def using ro rp rro
    by (auto intro!: bindM_term handle_term mkabs_term update_term handler_term split: prod.splits res.splits)
  then obtain r where r: "flexrigid env binders F Fty is t = Some r" by blast
  have "(\<exists>W''. env_inv ar W'' env'' \<and> agreeV (maxidx env) W W'') \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      vps t \<subseteq> reach env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))" if rOk: "r = Ok env''" for env''
  proof -
    have frg: "flexrigid env binders F Fty is t = Some (Ok env'')" using r rOk by simp
    from frg obtain u env1 u' where occ: "occurs F t env = Some (Ok False)"
      and pj: "ok (proj t env binders is) (u, env1)"
      and u': "ok (mkabs binders is u) u'" and env'': "ok (update (F, Fty) u' env1) env''"
      by (auto simp: flexrigid_def ok_handle hnd split: if_splits prod.splits)
    from rpP pj rp obtain W1 where p1: "prunes ar W env W1 env1 (reach env (vps t))"
      and vu: "vps u \<subseteq> reach env1 (vps t)" and bu: "below (maxidx env1) u" by auto
    note pd = prunesD[OF p1]
    note t1 = env_invD[OF pd(3)]
    have F1: "vt_lookup (tenv env1) F = None" by (rule ok_update(1)[OF env''])
    have F0: "vt_lookup (tenv env) F = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env) F \<noteq> None"
      then obtain b where "vt_lookup (tenv env) F = Some b" by blast
      with pd(1) have "vt_lookup (tenv env1) F = Some b" unfolding extends_def by blast
      with F1 show False by simp
    qed
    have noF: "\<forall>y\<in>reach env (vps t). fst y \<noteq> F" by (rule occurs_False[OF occ refl e F0])
    have vu': "vps u' = vps u" by (rule vps_mkabs[OF u'])
    have ru: "reach env1 (vps u') \<subseteq> reach env1 (vps t)" using vu vu' by (intro reach_mono) simp
    have nc: "(F, Fty) \<notin> reach env1 (vps u')"
      using ru pd(5)[of "vps t"] noF Fm by (force simp: fr_def)
    have Fm1: "snd F \<le> maxidx env1" using Fm pd(2) by simp
    have bu': "below (maxidx env1) u'" using bu vars_mkabs[OF u'] by (simp add: below_def)
    note bs = bind_step[OF t1(1,4) env'' nc Fm1 bu']
    from flexrigid_exn[OF frg t0(2) bok t0(3,4) Fm gF tyF tyt has_type_proper[OF tyt] pt bt F0]
    obtain W'' where te: "ty_ext ar W env W'' env''" by blast
    note te' = te[unfolded ty_ext_def]
    have ti'': "env_inv ar W'' env''" using bs(1) te' by (simp add: env_inv_def)
    have ext: "extends env'' env" by (rule extends_trans[OF bs(3) pd(1)])
    have mx: "maxidx env \<le> maxidx env''" using bs(4) pd(2) by simp
    have "card (unb env'' Y) < card (unb env Y)"
      if Y: "finite Y" "\<forall>y\<in>Y. snd (fst y) \<le> maxidx env" "(F, Fty) \<in> unb env Y" "vps t \<subseteq> reach env Y" for Y
    proof -
      have rY: "reach env Y \<subseteq> reach env1 Y" by (rule reach_extends[OF pd(1)])
      have "reach env1 (vps t) \<subseteq> reach env1 Y" using Y(4) rY by (intro reach_mono) blast
      with ru have uu: "unb env1 (vps u') \<subseteq> unb env1 Y" by (auto simp: unb_def)
      have e1: "unb env'' Y \<subseteq> (unb env1 Y - {(F, Fty)}) \<union> unb env1 (vps u')"
        using bs(6)[of Y] by (cases "(F, Fty) \<in> reach env1 Y") simp_all
      have e2: "(F, Fty) \<notin> unb env1 (vps u')" using nc by (simp add: unb_def)
      from e1 e2 uu have sub: "unb env'' Y \<subseteq> unb env1 Y - {(F, Fty)}" by blast
      have F1Y: "(F, Fty) \<in> unb env1 Y" using Y(3) rY F1 by (auto simp: unb_def lk_def)
      have fin1: "finite (unb env1 Y)" by (rule finite_unb[OF Y(1)])
      have "card (unb env'' Y) \<le> card (unb env1 Y - {(F, Fty)})" using sub fin1 by (intro card_mono) auto
      also have "\<dots> < card (unb env1 Y)" by (rule card_Diff1_less[OF fin1 F1Y])
      also have "\<dots> \<le> card (unb env Y)" by (rule pd(6)[OF Y(1,2)])
      finally show ?thesis .
    qed
    with ti'' te' ext mx show ?thesis by blast
  qed
  with r show ?thesis by blast
qed

lemma flexflex1_term:
  assumes ti: "env_inv ar W env" and Fm: "snd F \<le> maxidx env" and gF: "ground ar Fty"
    and bok: "binders_ok ar binders" and Fu: "vt_lookup (tenv env) F = None"
    and tys: "has_type W (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type W (map snd binders) (app (pterm.Var F Fty) js) T"
  shows "\<exists>r. flexflex1 env binders F Fty is js = Some r \<and>
    (\<forall>env''. r = Ok env'' \<longrightarrow> (\<exists>W''. prunes ar W env W'' env'' {(F, Fty)}))"
proof -
  note t0 = env_invD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(2)])
  have "\<exists>r. flexflex1 env binders F Fty is js = Some r"
    unfolding flexflex1_def mk_new_hnf_def mk_hnf_def using mk_ff_list_term[of "is" js]
    by (auto intro!: bindM_term type_of_G_term[OF e] mkabs_term update_term split: prod.splits)
  then obtain r where r: "flexflex1 env binders F Fty is js = Some r" by blast
  have "\<exists>W''. prunes ar W env W'' env'' {(F, Fty)}" if rOk: "r = Ok env''" for env''
  proof (cases "is = js")
    case True
    with r rOk have "env'' = env" by (simp add: flexflex1_def return_def)
    with prunes_refl[OF ti] show ?thesis by blast
  next
    case False
    have f1: "flexflex1 env binders F Fty is js = Some (Ok env'')" using r rOk by simp
    from flexflex1_exn[OF f1 t0(2) bok t0(3,4) Fm gF Fu tys tyt] obtain W'' where
      te: "ty_ext ar W env W'' env''" by auto
    note te' = te[unfolded ty_ext_def]
    from f1 False obtain ks where ks: "ok (mk_ff_list is js) ks"
      and hnf: "ok (mk_new_hnf env binders is F Fty ks) env''"
      by (auto simp: flexflex1_def)
    from hnf obtain Gty env1 G t where Gty: "ok (type_of_G env Fty (ilength is) ks) Gty"
      and G: "genvar (fst F) env Gty = (env1, G)" and t: "ok (mkabs binders is (app G ks)) t"
      and env'': "ok (update (F, Fty) t env1) env''"
      by (rule ok_mk_new_hnf)
    from ok_type_of_G'[OF Gty e] obtain Us U Vs where
      T: "Fty = foldr fun_type Us U" "length Us = length is" "Gty = foldr fun_type Vs U" "length Vs = length ks"
      and ks0: "\<forall>k\<in>set ks. 0 \<le> k" by auto
    have "prunes ar W env W'' env'' {(F, Fty)}"
      by (rule prune_step[OF ti G env'' t ks0 T Fm]) (use te' in simp_all)
    then show ?thesis by blast
  qed
  with r show ?thesis by blast
qed

lemma ff_term:
  assumes ti: "env_inv ar W env" and Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env"
    and gF: "ground ar Fty" and gG: "ground ar Gty" and bok: "binders_ok ar binders"
    and dist: "distinct is" "distinct js" and FG: "F \<noteq> G"
    and Fu: "vt_lookup (tenv env) F = None" and Gu: "vt_lookup (tenv env) G = None"
    and tys: "has_type W (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type W (map snd binders) (app (pterm.Var G Gty) js) T"
  shows "\<exists>r. ff env binders F Fty is G Gty js = Some r \<and> (\<forall>env''. r = Ok env'' \<longrightarrow>
    (\<exists>W''. env_inv ar W'' env'' \<and> agreeV (maxidx env) W W'') \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      (G, Gty) \<in> unb env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y)))"
proof -
  note t0 = env_invD[OF ti]
  have fr: "fresh_env env" by (rule t0(4))
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(2)])
  have lG: "lk env G Gty = None" using Gu by (simp add: lk_def)
  have "\<exists>r. ff env binders F Fty is G Gty js = Some r"
    unfolding ff_def Let_def
    by (auto intro!: bindM_term idx_mapM_term type_of_G_term[OF e] mkabs_term update_term
        split: prod.splits)
  then obtain r where r: "ff env binders F Fty is G Gty js = Some r" by blast
  have "(\<exists>W''. env_inv ar W'' env'' \<and> agreeV (maxidx env) W W'') \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      (G, Gty) \<in> unb env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))" if rOk: "r = Ok env''" for env''
  proof -
    have f: "ff env binders F Fty is G Gty js = Some (Ok env'')" using r rOk by simp
    from ff_exn[OF f t0(2) bok t0(3,4) Fm Gm FG gF gG Fu Gu tys tyt dist] obtain W'' where
      te: "ty_ext ar W env W'' env''" by auto
    note te' = te[unfolded ty_ext_def]
    show ?thesis
    proof (cases "subset js is")
      case True
      with f obtain ks t where ks: "ok (mapM (idx is) js) ks"
        and t: "ok (mkabs binders is (app (pterm.Var G Gty) ks)) t"
        and env'': "ok (update (F, Fty) t env) env''"
        by (auto simp: ff_def)
      have vt: "vps t = {(G, Gty)}" using vps_mkabs[OF t] by simp
      have nc: "(F, Fty) \<notin> reach env (vps t)" using vt reach_unbound[OF lG] FG by simp
      have bt: "below (maxidx env) t" using vars_mkabs[OF t] Gm by (simp add: below_def vars_app)
      note bs = bind_step[OF t0(1) fr env'' nc Fm bt]
      have "card (unb env'' Y) < card (unb env Y)"
        if Y: "finite Y" "(F, Fty) \<in> unb env Y" "(G, Gty) \<in> unb env Y" for Y
      proof -
        have "unb env (vps t) = {(G, Gty)}" using vt reach_unbound[OF lG] lG by (auto simp: unb_def)
        then have "unb env'' Y \<subseteq> unb env Y - {(F, Fty)}" using bs(6)[of Y] Y(3) FG by auto
        moreover have fu: "finite (unb env Y)" by (rule finite_unb[OF Y(1)])
        ultimately have "card (unb env'' Y) \<le> card (unb env Y - {(F, Fty)})" by (intro card_mono) auto
        also have "\<dots> < card (unb env Y)" by (rule card_Diff1_less[OF fu Y(2)])
        finally show ?thesis .
      qed
      moreover have "env_inv ar W'' env''" using bs(1) te' by (simp add: env_inv_def)
      ultimately show ?thesis using bs te' by auto
    next
      case False
      let ?ks = "inter js is"
      from False f obtain ks' Hty where
        Hty: "ok (type_of_G env Fty (ilength is) ks') Hty"
        and rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
          (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs binders js (app H ks'))) \<bind> (\<lambda>tG.
          (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs binders is (app H ks'))) \<bind> (\<lambda>tF.
          update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env''"
        by (auto simp: ff_def Let_def)
      obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
      with rest obtain ksG tG ksF tF env2 where
        tG: "ok (mkabs binders js (app H ksG)) tG"
        and tF: "ok (mkabs binders is (app H ksF)) tF"
        and env2: "ok (update (F, Fty) tF env1) env2" and env'': "ok (update (G, Gty) tG env2) env''"
        by auto
      note g = genvar_simps[OF H]
      define Hn where "Hn = (fst G, maxidx env + 1)"
      have HV: "H = Var Hn Hty" using g(4) by (simp add: Hn_def)
      have ac1: "acyc env1" using t0(1) unfolding acyc_def dep_tenv[OF g(1)] .
      have fr1: "fresh_env env1" by (rule fresh_env_genvar[OF H fr])
      have lH1: "lk env1 Hn Hty = None" using lk_fresh[OF fr, of Hn Hty] lk_tenv[OF g(1)] by (simp add: Hn_def)
      have sH: "snd Hn = maxidx env + 1" by (simp add: Hn_def)
      have GH: "G \<noteq> Hn" "F \<noteq> Hn"
        using Gm Fm int_succ_not_le[of "maxidx env"] sH by metis+
      have vF: "vps tF = {(Hn, Hty)}" and vG: "vps tG = {(Hn, Hty)}"
        using vps_mkabs[OF tF] vps_mkabs[OF tG] HV by simp_all
      have nc1: "(F, Fty) \<notin> reach env1 (vps tF)" using vF reach_unbound[OF lH1] GH by auto
      have bF: "below (maxidx env1) tF" using vars_mkabs[OF tF] HV g(3) by (simp add: below_def vars_app Hn_def)
      have Fm1: "snd F \<le> maxidx env1" using Fm g(3) by simp
      note b1 = bind_step[OF ac1 fr1 env2 nc1 Fm1 bF]
      have lH2: "lk env2 Hn Hty = None"
        using lk_update[OF ok_update(2)[OF env2], of Hn Hty] lH1 GH by auto
      have nc2: "(G, Gty) \<notin> reach env2 (vps tG)" using vG reach_unbound[OF lH2] GH by auto
      have bG: "below (maxidx env2) tG" using vars_mkabs[OF tG] HV g(3) b1(4) by (simp add: below_def vars_app Hn_def)
      have Gm2: "snd G \<le> maxidx env2" using Gm g(3) b1(4) by simp
      note b2 = bind_step[OF b1(1,2) env'' nc2 Gm2 bG]
      have ext: "extends env'' env"
        using extends_trans[OF b2(3) extends_trans[OF b1(3) genvar_extends[OF H]]] .
      have mx: "maxidx env \<le> maxidx env''" using b2(4) b1(4) g(3) by simp
      have "card (unb env'' Y) < card (unb env Y)"
        if Y: "finite Y" "(F, Fty) \<in> unb env Y" "(G, Gty) \<in> unb env Y" for Y
      proof -
        have u1: "unb env1 = unb env" by (rule unb_tenv[OF g(1)])
        have "unb env1 (vps tF) \<subseteq> {(Hn, Hty)}" using vF by (auto simp: unb_def reach_unbound[OF lH1])
        moreover have "unb env2 (vps tG) \<subseteq> {(Hn, Hty)}" using vG by (auto simp: unb_def reach_unbound[OF lH2])
        ultimately have s1: "unb env2 Y \<subseteq> (unb env Y - {(F, Fty)}) \<union> {(Hn, Hty)}"
          and s2: "unb env'' Y \<subseteq> (unb env2 Y - {(G, Gty)}) \<union> {(Hn, Hty)}"
          using b2(6)[of Y] b1(6)[of Y] u1 by (auto split: if_splits)
        have sub: "unb env'' Y \<subseteq> (unb env Y - {(F, Fty), (G, Gty)}) \<union> {(Hn, Hty)}"
          using s1 s2 GH by blast
        have fu: "finite (unb env Y)" by (rule finite_unb[OF Y(1)])
        have D: "{(F, Fty), (G, Gty)} \<subseteq> unb env Y" using Y(2,3) by simp
        have c: "card {(Hn, Hty)} < card {(F, Fty), (G, Gty)}" using FG by simp
        show ?thesis by (rule card_unb_less[OF fu sub D c]) simp
      qed
      moreover have "env_inv ar W'' env''" using b2(1) te' by (simp add: env_inv_def)
      ultimately show ?thesis using ext mx te' by auto
    qed
  qed
  with r show ?thesis by blast
qed

lemma flexflex2_term:
  assumes "env_inv ar W env" "snd F \<le> maxidx env" "snd G \<le> maxidx env"
    "ground ar Fty" "ground ar Gty" "binders_ok ar binders" "distinct is" "distinct js" "F \<noteq> G"
    "vt_lookup (tenv env) F = None" "vt_lookup (tenv env) G = None"
    "has_type W (map snd binders) (app (pterm.Var F Fty) is) T"
    "has_type W (map snd binders) (app (pterm.Var G Gty) js) T"
  shows "\<exists>r. flexflex2 env binders F Fty is G Gty js = Some r \<and> (\<forall>env''. r = Ok env'' \<longrightarrow>
    (\<exists>W''. env_inv ar W'' env'' \<and> agreeV (maxidx env) W W'') \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      (G, Gty) \<in> unb env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y)))"
proof (cases "indexname_less G F")
  case True
  with ff_term[OF assms(1-13)] show ?thesis by (simp add: flexflex2_def)
next
  case False
  from ff_term[OF assms(1,3,2,5,4,6,8,7) assms(9)[symmetric] assms(11,10,13,12)] False show ?thesis
    by (auto simp: flexflex2_def)
qed


subsection \<open>The measure of typed unification problems\<close>

text \<open>
  As for patterns, a unification problem is measured lexicographically by the number of unbound
  variables reachable from its terms and by its size, where the size \<^const>\<open>Ms\<close> of a term is that
  of the \<beta>-normal form of its instance (Section \<open>Pattern_Size\<close>). The context \<open>C\<close> consists of
  well-typed terms that are still to be unified.
\<close>

definition vsl :: "pterm list \<Rightarrow> (indexname \<times> ptyp) set" where
  "vsl ts = \<Union> (vps ` set ts)"

abbreviation lexr :: "((nat \<times> nat) \<times> (nat \<times> nat)) set" where
  "lexr \<equiv> less_than <*lex*> less_than"

definition lexle :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "lexle a b \<longleftrightarrow> fst a < fst b \<or> (fst a = fst b \<and> snd a \<le> snd b)"

lemma lexr_iff: "(a, b) \<in> lexr \<longleftrightarrow> fst a < fst b \<or> (fst a = fst b \<and> snd a < snd b)"
  by (cases a; cases b) auto

lemma lexle_trans: "lexle a b \<Longrightarrow> lexle b c \<Longrightarrow> lexle a c"
  by (auto simp: lexle_def)

lemma lexle_lexr: "lexle a b \<Longrightarrow> (b, c) \<in> lexr \<Longrightarrow> (a, c) \<in> lexr"
  by (auto simp: lexle_def lexr_iff)

lemma lexr_lexle: "(a, b) \<in> lexr \<Longrightarrow> lexle b c \<Longrightarrow> (a, c) \<in> lexr"
  by (auto simp: lexle_def lexr_iff)

lemma le_lexle: "fst a \<le> fst b \<Longrightarrow> snd a \<le> snd b \<Longrightarrow> lexle a b"
  by (auto simp: lexle_def)

lemma le_lexr: "fst a \<le> fst b \<Longrightarrow> snd a < snd b \<Longrightarrow> (a, b) \<in> lexr"
  by (auto simp: lexr_iff)

lemma vsl_simps[simp]: "vsl [] = {}" "vsl (t # ts) = vps t \<union> vsl ts" "vsl (xs @ ys) = vsl xs \<union> vsl ys"
  by (auto simp: vsl_def)

lemma finite_vsl[simp]: "finite (vsl ts)"
  by (simp add: vsl_def)

definition pairs :: "(pterm \<times> pterm) list \<Rightarrow> pterm list" where
  "pairs ps = concat (map (\<lambda>(a, b). [a, b]) ps)"

lemma pairs_simps[simp]: "pairs [] = []" "pairs ((a, b) # ps) = a # b # pairs ps"
  by (simp_all add: pairs_def)

lemma pairs_zip: "length xs = length ys \<Longrightarrow> vsl (pairs (zip xs ys)) = vsl xs \<union> vsl ys"
  by (induction xs ys rule: list_induct2) auto

lemma pairs_zip_sum: "length xs = length ys \<Longrightarrow>
    sum_list (map g (pairs (zip xs ys))) = sum_list (map g xs) + sum_list (map (g :: pterm \<Rightarrow> nat) ys)"
  by (induction xs ys rule: list_induct2) auto

lemma pairs_zip_set: "(a, b) \<in> set (zip xs ys) \<Longrightarrow> a \<in> set xs \<and> b \<in> set ys"
  by (auto dest: set_zip_leftD set_zip_rightD)

lemma unb_vsl_member:
  "lk env x T = None \<Longrightarrow> (x, T) \<in> vsl P \<Longrightarrow> (x, T) \<in> unb env (vsl (P @ C))"
  using reach_incl[of "vsl (P @ C)" env] by (auto simp: unb_def)

definition mu :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> pterm list \<Rightarrow> nat \<times> nat" where
  "mu env W ts = (card (unb env (vsl ts)), sum_list (map (Ms env W) ts))"

definition oldC :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> pterm list \<Rightarrow> bool" where
  "oldC W env C \<longleftrightarrow> (\<forall>c\<in>set C. (\<exists>Ts T. has_type W Ts c T) \<and> below (maxidx env) c)"

lemma oldC_simps[simp]: "oldC W env []"
  "oldC W env (t # ts) \<longleftrightarrow> (\<exists>Ts T. has_type W Ts t T) \<and> below (maxidx env) t \<and> oldC W env ts"
  "oldC W env (xs @ ys) \<longleftrightarrow> oldC W env xs \<and> oldC W env ys"
  by (auto simp: oldC_def)

lemma oldC_mono:
  assumes "oldC W env C" "agreeV (maxidx env) W W'" "maxidx env \<le> maxidx env'"
  shows "oldC W' env' C"
  unfolding oldC_def
proof
  fix c assume "c \<in> set C"
  with assms(1) obtain Ts T where "has_type W Ts c T" "below (maxidx env) c" by (auto simp: oldC_def)
  with assms(2,3) show "(\<exists>Ts T. has_type W' Ts c T) \<and> below (maxidx env') c"
    by (blast intro: has_type_agreeV below_mono)
qed

lemma oldC_vsl: "oldC W env C \<Longrightarrow> \<forall>y\<in>vsl C. snd (fst y) \<le> maxidx env"
  using below_vps by (fastforce simp: oldC_def vsl_def)

lemma old_vsl:
  "below (maxidx env) s \<Longrightarrow> below (maxidx env) t \<Longrightarrow> oldC W env C \<Longrightarrow>
    \<forall>y\<in>vsl ([s, t] @ C). snd (fst y) \<le> maxidx env"
  using below_vps[of "maxidx env" s] below_vps[of "maxidx env" t] oldC_vsl[of W env C] by auto

lemma mu_fst_mono: "vsl xs \<subseteq> reach env (vsl ys) \<Longrightarrow> fst (mu env W xs) \<le> fst (mu env W ys)"
  by (simp add: mu_def card_mono finite_unb unb_reach_mono)

lemma mu_fst_append: "fst (mu env W C) \<le> fst (mu env W (P @ C))"
  using reach_incl[of "vsl (P @ C)" env] by (intro mu_fst_mono) auto

text \<open>The property of results of \<^const>\<open>unif\<close> established by induction.\<close>

definition uq :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> pterm list \<Rightarrow> env res \<Rightarrow> bool" where
  "uq ar W env P r \<longleftrightarrow> (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>W'. env_inv ar W' env' \<and> agreeV (maxidx env) W W' \<and>
    extends env' env \<and> maxidx env \<le> maxidx env' \<and>
    (\<forall>C. oldC W env C \<longrightarrow> lexle (mu env' W' C) (mu env W (P @ C)))))"

lemma uq_Err[simp]: "uq ar W env P (Err e)"
  by (simp add: uq_def)

lemma uq_mono:
  "uq ar W env P r \<Longrightarrow> (\<And>C. oldC W env C \<Longrightarrow> lexle (mu env W (P @ C)) (mu env W (Q @ C))) \<Longrightarrow>
    uq ar W env Q r"
  unfolding uq_def by (blast intro: lexle_trans)

lemma uq_bindM:
  assumes "\<exists>r. m = Some r" "\<And>x. m = Some (Ok x) \<Longrightarrow> \<exists>r. f x = Some r \<and> uq ar W env P r"
  shows "\<exists>r. bindM m f = Some r \<and> uq ar W env P r"
  using assms by (auto simp: bindM_def split: res.splits)

lemma uq_prunes:
  assumes p: "prunes ar W env W' env' S"
  shows "uq ar W env P (Ok env')"
  unfolding uq_def
proof (intro allI impI)
  fix e assume "Ok env' = Ok e"
  then have e: "e = env'" by simp
  have "lexle (mu env' W' C) (mu env W (P @ C))" if c: "oldC W env C" for C
  proof (rule le_lexle)
    have "card (unb env' (vsl C)) \<le> card (unb env (vsl C))"
      by (rule prunesD(6)[OF p finite_vsl oldC_vsl[OF c]])
    with mu_fst_append[of env W C P] show "fst (mu env' W' C) \<le> fst (mu env W (P @ C))"
      by (simp add: mu_def)
    have "sum_list (map (Ms env' W') C) = sum_list (map (Ms env W) C)"
    proof (intro arg_cong[where f = sum_list] map_cong refl)
      fix c assume "c \<in> set C"
      with c obtain Ts T where "has_type W Ts c T" "below (maxidx env) c" by (auto simp: oldC_def)
      from prunesD(7)[OF p this] show "Ms env' W' c = Ms env W c" .
    qed
    then show "snd (mu env' W' C) \<le> snd (mu env W (P @ C))" by (simp add: mu_def)
  qed
  with prunesD(1-4)[OF p] e
  show "\<exists>W'. env_inv ar W' e \<and> agreeV (maxidx env) W W' \<and> extends e env \<and> maxidx env \<le> maxidx e \<and>
    (\<forall>C. oldC W env C \<longrightarrow> lexle (mu e W' C) (mu env W (P @ C)))" by blast
qed

lemma uq_unb_less:
  assumes "env_inv ar W'' env''" "agreeV (maxidx env) W W''" "extends env'' env" "maxidx env \<le> maxidx env''"
    and "\<And>C. oldC W env C \<Longrightarrow> card (unb env'' (vsl (P @ C))) < card (unb env (vsl (P @ C)))"
  shows "uq ar W env P (Ok env'')"
proof -
  have "lexle (mu env'' W'' C) (mu env W (P @ C))" if "oldC W env C" for C
  proof -
    have "unb env'' (vsl C) \<subseteq> unb env'' (vsl (P @ C))" by (rule unb_subset) simp
    then have "fst (mu env'' W'' C) \<le> card (unb env'' (vsl (P @ C)))"
      unfolding mu_def by (auto intro!: card_mono finite_unb)
    with assms(5)[OF that] show ?thesis by (simp add: lexle_def mu_def)
  qed
  with assms(1-4) show ?thesis unfolding uq_def by blast
qed

lemma foldM_measure:
  assumes "\<And>a b e We U. (a, b) \<in> set ps \<Longrightarrow> env_inv ar We e \<Longrightarrow> has_type We Ts a U \<Longrightarrow> has_type We Ts b U \<Longrightarrow>
      below (maxidx e) a \<Longrightarrow> below (maxidx e) b \<Longrightarrow> (mu e We [a, b], m) \<in> lexr \<Longrightarrow>
      \<exists>r. f a b e = Some r \<and> uq ar We e [a, b] r"
    and "\<forall>(a, b)\<in>set ps. \<exists>U. has_type W Ts a U \<and> has_type W Ts b U \<and> below (maxidx env) a \<and>
      below (maxidx env) b"
    and "(mu env W (pairs ps), m) \<in> lexr" and "env_inv ar W env"
  shows "\<exists>r. foldM (\<lambda>(a, b) e. f a b e) ps env = Some r \<and> uq ar W env (pairs ps) r"
  using assms
proof (induction ps arbitrary: env W)
  case Nil
  have "uq ar W env [] (Ok env)" unfolding uq_def
    using Nil.prems(4) by (auto simp: lexle_def agreeV_def)
  then show ?case by (simp add: return_def)
next
  case (Cons p ps)
  obtain a b where p: "p = (a, b)" by force
  from Cons.prems(2) p obtain U where ab: "has_type W Ts a U" "has_type W Ts b U"
    "below (maxidx env) a" "below (maxidx env) b" by auto
  have ps: "\<forall>(a, b)\<in>set ps. \<exists>U. has_type W Ts a U \<and> has_type W Ts b U \<and> below (maxidx env) a \<and>
      below (maxidx env) b"
    using Cons.prems(2) by auto
  have oR: "oldC W env (pairs ps)" using ps
  proof (induction ps)
    case (Cons q qs)
    then show ?case by (cases q) (auto; blast)
  qed simp
  have "lexle (mu env W [a, b]) (mu env W (pairs (p # ps)))"
  proof (rule le_lexle)
    show "fst (mu env W [a, b]) \<le> fst (mu env W (pairs (p # ps)))"
      using reach_incl[of "vsl (pairs (p # ps))" env] p by (intro mu_fst_mono) auto
    show "snd (mu env W [a, b]) \<le> snd (mu env W (pairs (p # ps)))" using p by (simp add: mu_def)
  qed
  then have lt: "(mu env W [a, b], m) \<in> lexr" using Cons.prems(3) by (rule lexle_lexr)
  from Cons.prems(1)[OF _ Cons.prems(4) ab lt] p
  obtain r1 where r1: "f a b env = Some r1" and q1: "uq ar W env [a, b] r1" by auto
  show ?case
  proof (cases r1)
    case (Err e')
    with r1 p show ?thesis by (simp add: bindM_def)
  next
    case (Ok e1)
    with q1 obtain W1 where e1: "env_inv ar W1 e1" "agreeV (maxidx env) W W1" "extends e1 env"
        "maxidx env \<le> maxidx e1"
      and L1: "\<And>C. oldC W env C \<Longrightarrow> lexle (mu e1 W1 C) (mu env W (a # b # C))"
      by (auto simp: uq_def)
    have ps1: "\<forall>(a, b)\<in>set ps. \<exists>U. has_type W1 Ts a U \<and> has_type W1 Ts b U \<and> below (maxidx e1) a \<and>
        below (maxidx e1) b"
      using ps e1(2,4) by (fastforce intro: below_mono has_type_agreeV)
    have lt1: "(mu e1 W1 (pairs ps), m) \<in> lexr"
      using lexle_lexr[OF L1[OF oR]] Cons.prems(3) p by simp
    have "\<exists>r. foldM (\<lambda>(a, b) e. f a b e) ps e1 = Some r \<and> uq ar W1 e1 (pairs ps) r"
      by (rule Cons.IH[OF _ ps1 lt1 e1(1)], rule Cons.prems(1)) simp_all
    then obtain r2 where r2: "foldM (\<lambda>(a, b) e. f a b e) ps e1 = Some r2" and q2: "uq ar W1 e1 (pairs ps) r2"
      by auto
    have "uq ar W env (pairs (p # ps)) r2"
      unfolding uq_def
    proof (intro allI impI)
      fix env' assume "r2 = Ok env'"
      with q2 obtain W' where q: "env_inv ar W' env'" "agreeV (maxidx e1) W1 W'" "extends env' e1"
          "maxidx e1 \<le> maxidx env'"
        and L2: "\<And>C. oldC W1 e1 C \<Longrightarrow> lexle (mu env' W' C) (mu e1 W1 (pairs ps @ C))"
        by (auto simp: uq_def)
      have "lexle (mu env' W' C) (mu env W (pairs (p # ps) @ C))" if "oldC W env C" for C
        using lexle_trans[OF L2[OF oldC_mono[OF that e1(2,4)]] L1[of "pairs ps @ C"]] that oR p by simp
      moreover have "agreeV (maxidx env) W W'" by (rule agreeV_trans[OF e1(2) q(2) e1(4)])
      ultimately show "\<exists>W'. env_inv ar W' env' \<and> agreeV (maxidx env) W W' \<and> extends env' env \<and>
          maxidx env \<le> maxidx env' \<and>
          (\<forall>C. oldC W env C \<longrightarrow> lexle (mu env' W' C) (mu env W (pairs (p # ps) @ C)))"
        using q e1 by (auto intro: extends_trans)
    qed
    with r1 r2 Ok p show ?thesis by (simp add: bindM_def)
  qed
qed


subsection \<open>Termination of unification on well-typed terms\<close>

lemma unif_term:
  "mu env W [s, t] = m \<Longrightarrow> env_inv ar W env \<Longrightarrow> binders_ok ar bs \<Longrightarrow>
    wf_term ar (length bs) s \<Longrightarrow> wf_term ar (length bs) t \<Longrightarrow>
    has_type W (map snd bs) s T \<Longrightarrow> has_type W (map snd bs) t T \<Longrightarrow>
    below (maxidx env) s \<Longrightarrow> below (maxidx env) t \<Longrightarrow>
    \<exists>r. unif alg bs s t env = Some r \<and> uq ar W env [s, t] r"
proof (induction m arbitrary: env W s t bs T rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  case (1 m env W s t bs T)
  have mu: "mu env W [s, t] = m" and ti: "env_inv ar W env"
    and bok: "binders_ok ar bs" and ws: "wf_term ar (length bs) s" and wt: "wf_term ar (length bs) t"
    and tys: "has_type W (map snd bs) s T" and tyt: "has_type W (map snd bs) t T"
    and bs: "below (maxidx env) s" and bt: "below (maxidx env) t"
    using "1.prems" by simp_all
  have IH: "\<exists>r. unif alg bs' a b env' = Some r \<and> uq ar W' env' [a, b] r"
    if "(mu env' W' [a, b], m) \<in> lexr" "env_inv ar W' env'" "binders_ok ar bs'"
      "wf_term ar (length bs') a" "wf_term ar (length bs') b"
      "has_type W' (map snd bs') a U" "has_type W' (map snd bs') b U"
      "below (maxidx env') a" "below (maxidx env') b" for env' W' a b bs' U
    using "1.IH"[OF that(1) refl that(2-)] .
  note iv = env_invD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF iv(2)])
  let ?Bs = "map snd bs" and ?n = "length bs"
  define R where "R = (\<lambda>s0 t0. if is_Abs s0 \<and> is_Abs t0 then
        (case (s0, t0) of
          (pterm.Abs ns Ts ts, pterm.Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            unif alg ((name, Ts) # bs) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s0 then
        (case s0 of
          pterm.Abs ns Ts ts \<Rightarrow> unif alg ((ns, Ts) # bs) ts (incr t0 $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t0 then
        (case t0 of
          pterm.Abs nt Tt tt \<Rightarrow> unif alg ((nt, Tt) # bs) (incr s0 $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s0; (ht, ts) = strip_comb t0 in
          if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (pterm.Var F Fty, pterm.Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env bs F Fty is js
                else flexflex2 env bs F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env bs F Fty is t0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env bs F Fty is s0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht)))"
  have u_eq: "unif alg bs s t env = head_norm env s \<bind> (\<lambda>s0. head_norm env t \<bind> (\<lambda>t0. R s0 t0))"
    unfolding R_def by (subst unif.simps) (rule refl)
  from head_norm_term[OF iv(1-3) tys] obtain s0 where hhs: "head_norm env s = Some (Ok s0)" by blast
  from head_norm_term[OF iv(1-3) tyt] obtain t0 where hht: "head_norm env t = Some (Ok t0)" by blast
  have hs: "hn env s = Some s0" by (rule head_norm_hn[OF hhs e refl])
  have ht: "hn env t = Some t0" by (rule head_norm_hn[OF hht e refl])
  have Mss: "Ms env W s0 = Ms env W s" by (rule Ms_head_norm[OF iv(1-3) hhs has_type_proper[OF tys] tys])
  have Mst: "Ms env W t0 = Ms env W t" by (rule Ms_head_norm[OF iv(1-3) hht has_type_proper[OF tyt] tyt])
  have red: "lexle (mu env W ([s0, t0] @ C)) (mu env W ([s, t] @ C))" for C
  proof (rule le_lexle)
    let ?Y = "vsl ([s, t] @ C)"
    have "vps s0 \<subseteq> reach env ?Y" using hn_vps[OF hs] reach_subset[of "vps s" ?Y env] by auto
    moreover have "vps t0 \<subseteq> reach env ?Y" using hn_vps[OF ht] reach_subset[of "vps t" ?Y env] by auto
    moreover have "vsl C \<subseteq> reach env ?Y" using reach_incl[of ?Y env] by simp
    ultimately have "vsl ([s0, t0] @ C) \<subseteq> reach env ?Y" by simp
    then show "fst (mu env W ([s0, t0] @ C)) \<le> fst (mu env W ([s, t] @ C))" by (rule mu_fst_mono)
    show "snd (mu env W ([s0, t0] @ C)) \<le> snd (mu env W ([s, t] @ C))" using Mss Mst by (simp add: mu_def)
  qed
  have main: "\<exists>r. R s0 t0 = Some r \<and> uq ar W env [s0, t0] r"
  proof -
    from head_norm_sound[OF hhs refl iv(2)] ws have ws0: "wf_term ar ?n s0" by (auto simp: wf_term_def)
    from head_norm_sound[OF hht refl iv(2)] wt have wt0: "wf_term ar ?n t0" by (auto simp: wf_term_def)
    have tys0: "has_type W ?Bs s0 T" by (rule head_norm_typed[OF hhs refl iv(2,3) tys])
    have tyt0: "has_type W ?Bs t0 T" by (rule head_norm_typed[OF hht refl iv(2,3) tyt])
    have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF hhs refl iv(2,4) bs])
    have bt0: "below (maxidx env) t0" by (rule below_head_norm[OF hht refl iv(2,4) bt])
    have m0: "lexle (mu env W [s0, t0]) m" using red[of "[]"] mu by simp
    have rigI: "is_rigid h" if "\<not> is_Var h" "\<not> is_Abs h" "\<not> (\<exists>f u. h = f $ u)" "wf_term ar ?n h" for h
      using that by (cases h) (auto simp: is_rigid_def wf_term_def)
    have eta: "Ms env W (incr u $ Bound 0) + 1 \<le> Ms env W u + 2"
      if hu: "head_norm env v = Some (Ok u)" and nA: "\<not> is_Abs u" and wu: "wf_term ar ?n u"
        and tyu: "has_type W ?Bs u (U' \<rightarrow>\<^sub>T V')" for u v U' V'
    proof -
      obtain h us where shu: "strip_comb u = (h, us)" by force
      note ue = strip_comb_list_comb[OF shu]
      have hd: "is_rigid h \<or> (\<exists>F U. h = pterm.Var F U \<and> vt_lookup (tenv env) F = None)"
      proof (cases "is_Var h")
        case True
        then obtain F U where "h = pterm.Var F U" by (cases h) auto
        with head_norm_head_unbound[OF hu refl e] shu show ?thesis by auto
      next
        case False
        have "\<not> is_Abs h" using head_norm_head[OF hu refl nA] shu by simp
        moreover have "\<not> (\<exists>f u. h = f $ u)" using strip_comb_head[OF shu] .
        moreover have "wf_term ar ?n h" using wu ue by (simp add: wf_term_list_comb)
        ultimately show ?thesis using False rigI by blast
      qed
      have tyu': "has_type W ?Bs (list_comb h us) (U' \<rightarrow>\<^sub>T V')" using tyu ue by simp
      from Ms_eta[OF iv(1-3) hd has_type_proper[OF tyu'] tyu'] ue show ?thesis by simp
    qed
    show ?thesis
    proof (cases "is_Abs s0")
      case sA: True
      then obtain ns Ts ts where s0a: "s0 = pterm.Abs ns Ts ts" by (cases s0) auto
      have gTs: "ground ar Ts" using ws0 s0a by (simp add: wf_term_def)
      from tys0 s0a obtain V0 where T: "T = Ts \<rightarrow>\<^sub>T V0" and tyts: "has_type W (Ts # ?Bs) ts V0"
        by (auto elim: has_type_elims)
      have bts: "below (maxidx env) ts" using bs0 s0a by simp
      have wts: "wf_term ar (Suc ?n) ts" using ws0 s0a by (simp add: wf_term_def)
      have Mzs: "Ms env W s0 = Ms env W ts + 2" using Ms_Abs[OF iv(1-3)] tys0 s0a by simp
      show ?thesis
      proof (cases "is_Abs t0")
        case True
        then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
        from tyt0 t0a T have Tt: "Tt = Ts" and tytt: "has_type W (Ts # ?Bs) tt V0"
          by (auto elim: has_type_elims)
        have btt: "below (maxidx env) tt" using bt0 t0a by simp
        have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
        have Mzt: "Ms env W t0 = Ms env W tt + 2" using Ms_Abs[OF iv(1-3)] tyt0 t0a by simp
        define nm where "nm = (if ns = STR '''' then nt else ns)"
        have Req: "R s0 t0 = unif alg ((nm, Ts) # bs) ts tt env"
          using sA True s0a t0a Tt
          by (simp add: R_def Let_def nm_def unify_types_ground[OF gTs gTs] return_def bindM_def)
        have bok': "binders_ok ar ((nm, Ts) # bs)" using bok gTs by (simp add: binders_ok_def)
        have le: "lexle (mu env W ([ts, tt] @ C)) (mu env W ([s0, t0] @ C))" for C
          using s0a t0a Mzs Mzt by (intro le_lexle) (simp_all add: mu_def)
        have "(mu env W [ts, tt], mu env W [s0, t0]) \<in> lexr"
          using s0a t0a Mzs Mzt by (intro le_lexr) (simp_all add: mu_def)
        from lexr_lexle[OF this m0] have lt: "(mu env W [ts, tt], m) \<in> lexr" .
        from IH[where U = V0, OF lt ti bok' _ _ _ _ bts btt] wts wtt tyts tytt
        obtain r where r: "unif alg ((nm, Ts) # bs) ts tt env = Some r" and q: "uq ar W env [ts, tt] r"
          by auto
        have "uq ar W env [s0, t0] r" using uq_mono[OF q le] .
        with r Req show ?thesis by simp
      next
        case False
        have Req: "R s0 t0 = unif alg ((ns, Ts) # bs) ts (incr t0 $ Bound 0) env"
          using sA False s0a by (simp add: R_def)
        have bok': "binders_ok ar ((ns, Ts) # bs)" using bok gTs by (simp add: binders_ok_def)
        have wi: "wf_term ar (Suc ?n) (incr t0 $ Bound 0)"
          using wt0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
            intro: no_loose_bound_lift)
        have tyi: "has_type W (Ts # ?Bs) (incr t0 $ Bound 0) V0"
          using has_type_incr[OF tyt0, of Ts] T by (intro has_type.App[of _ _ _ Ts]) (auto simp: has_type_Bound_iff)
        have bi: "below (maxidx env) (incr t0 $ Bound 0)" using bt0 by (simp add: below_def vars_incr)
        have vi: "vps (incr t0 $ Bound 0) = vps t0" by simp
        have Mzi: "Ms env W (incr t0 $ Bound 0) + 1 \<le> Ms env W t0 + 2"
          by (rule eta[OF hht False wt0]) (use tyt0 T in simp)
        have le: "lexle (mu env W ([ts, incr t0 $ Bound 0] @ C)) (mu env W ([s0, t0] @ C))" for C
          using s0a vi Mzs Mzi by (intro le_lexle) (simp_all add: mu_def)
        have "(mu env W [ts, incr t0 $ Bound 0], mu env W [s0, t0]) \<in> lexr"
          using s0a vi Mzs Mzi by (intro le_lexr) (simp_all add: mu_def)
        from lexr_lexle[OF this m0] have lt: "(mu env W [ts, incr t0 $ Bound 0], m) \<in> lexr" .
        from IH[where U = V0, OF lt ti bok' _ _ _ _ bts bi] wts wi tyts tyi
        obtain r where r: "unif alg ((ns, Ts) # bs) ts (incr t0 $ Bound 0) env = Some r"
          and q: "uq ar W env [ts, incr t0 $ Bound 0] r"
          by auto
        have "uq ar W env [s0, t0] r" using uq_mono[OF q le] .
        with r Req show ?thesis by simp
      qed
    next
      case nsA: False
      show ?thesis
      proof (cases "is_Abs t0")
        case True
        then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
        have gTt: "ground ar Tt" using wt0 t0a by (simp add: wf_term_def)
        from tyt0 t0a obtain V0 where T: "T = Tt \<rightarrow>\<^sub>T V0" and tytt: "has_type W (Tt # ?Bs) tt V0"
          by (auto elim: has_type_elims)
        have btt: "below (maxidx env) tt" using bt0 t0a by simp
        have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
        have Mzt: "Ms env W t0 = Ms env W tt + 2" using Ms_Abs[OF iv(1-3)] tyt0 t0a by simp
        have Req: "R s0 t0 = unif alg ((nt, Tt) # bs) (incr s0 $ Bound 0) tt env"
          using nsA True t0a by (simp add: R_def)
        have bok': "binders_ok ar ((nt, Tt) # bs)" using bok gTt by (simp add: binders_ok_def)
        have wi: "wf_term ar (Suc ?n) (incr s0 $ Bound 0)"
          using ws0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
            intro: no_loose_bound_lift)
        have tyi: "has_type W (Tt # ?Bs) (incr s0 $ Bound 0) V0"
          using has_type_incr[OF tys0, of Tt] T by (intro has_type.App[of _ _ _ Tt]) (auto simp: has_type_Bound_iff)
        have bi: "below (maxidx env) (incr s0 $ Bound 0)" using bs0 by (simp add: below_def vars_incr)
        have vi: "vps (incr s0 $ Bound 0) = vps s0" by simp
        have Mzi: "Ms env W (incr s0 $ Bound 0) + 1 \<le> Ms env W s0 + 2"
          by (rule eta[OF hhs nsA ws0]) (use tys0 T in simp)
        have le: "lexle (mu env W ([incr s0 $ Bound 0, tt] @ C)) (mu env W ([s0, t0] @ C))" for C
          using t0a vi Mzt Mzi by (intro le_lexle) (simp_all add: mu_def)
        have "(mu env W [incr s0 $ Bound 0, tt], mu env W [s0, t0]) \<in> lexr"
          using t0a vi Mzt Mzi by (intro le_lexr) (simp_all add: mu_def)
        from lexr_lexle[OF this m0] have lt: "(mu env W [incr s0 $ Bound 0, tt], m) \<in> lexr" .
        from IH[where U = V0, OF lt ti bok' _ _ _ _ bi btt] wi wtt tyi tytt
        obtain r where r: "unif alg ((nt, Tt) # bs) (incr s0 $ Bound 0) tt env = Some r"
          and q: "uq ar W env [incr s0 $ Bound 0, tt] r"
          by auto
        have "uq ar W env [s0, t0] r" using uq_mono[OF q le] .
        with r Req show ?thesis by simp
      next
        case ntA: False
        obtain hs ss where shs: "strip_comb s0 = (hs, ss)" by force
        obtain ht ts where sht: "strip_comb t0 = (ht, ts)" by force
        note s0e = strip_comb_list_comb[OF shs] and t0e = strip_comb_list_comb[OF sht]
        have wss: "wf_term ar ?n hs" "\<forall>t\<in>set ss. wf_term ar ?n t"
          using ws0 s0e by (simp_all add: wf_term_list_comb)
        have wts: "wf_term ar ?n ht" "\<forall>t\<in>set ts. wf_term ar ?n t"
          using wt0 t0e by (simp_all add: wf_term_list_comb)
        have pss: "\<forall>t\<in>set ss. proper t \<and> typs_ok ar t" and pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
          using wss(2) wts(2) by (auto simp: wf_term_def)
        have wt0': "typs_ok ar t0" and ws0': "typs_ok ar s0"
          using wt0 ws0 by (simp_all add: wf_term_def)
        have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
          using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
        have nAh: "\<not> is_Abs hs" "\<not> is_Abs ht"
          using head_norm_head[OF hhs refl nsA] head_norm_head[OF hht refl ntA] shs sht by simp_all
        have tss: "\<forall>u\<in>set ss. \<exists>U. has_type W ?Bs u U"
          using tys0[unfolded s0e] by (rule has_type_list_comb_args)
        have tts: "\<forall>u\<in>set ts. \<exists>U. has_type W ?Bs u U"
          using tyt0[unfolded t0e] by (rule has_type_list_comb_args)
        have unbF: "vt_lookup (tenv env) F = None" if "hs = pterm.Var F U" for F U
          using head_norm_head_unbound[OF hhs refl e] shs that by simp
        have unbG: "vt_lookup (tenv env) F = None" if "ht = pterm.Var F U" for F U
          using head_norm_head_unbound[OF hht refl e] sht that by simp
        have memF: "(F, U) \<in> vsl [s0, t0]" if "hs = pterm.Var F U" for F U
          using that s0e by (simp add: vps_list_comb)
        have memG: "(F, U) \<in> vsl [s0, t0]" if "ht = pterm.Var F U" for F U
          using that t0e by (simp add: vps_list_comb)
        consider (VV) F Fty G Gty where "hs = pterm.Var F Fty" "ht = pterm.Var G Gty"
          | (VR) F Fty where "hs = pterm.Var F Fty" "\<not> is_Var ht"
          | (RV) G Gty where "\<not> is_Var hs" "ht = pterm.Var G Gty"
          | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
          by (cases hs; cases ht) auto
        then show ?thesis
        proof cases
          case (VV F Fty G Gty)
          from nsA ntA shs sht VV have Req: "R s0 t0 = ints_of' env ss \<bind> (\<lambda>is. ints_of' env ts \<bind> (\<lambda>js.
              if F = G then flexflex1 env bs F Fty is js else flexflex2 env bs F Fty is G Gty js))"
            by (simp add: R_def)
          have gF: "ground ar Fty" and gG: "ground ar Gty"
            using wss(1) wts(1) VV by (simp_all add: wf_term_def)
          have Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env"
            using bs0 bt0 s0e t0e VV by (simp_all add: below_list_comb)
          note Fu = unbF[OF VV(1)] and Gu = unbG[OF VV(2)]
          have lF: "lk env F Fty = None" and lG: "lk env G Gty = None"
            using Fu Gu by (simp_all add: lk_def)
          show ?thesis unfolding Req
          proof (rule uq_bindM[OF ints_of'_term[OF iv(1-3) tss]])
            fix "is" assume iS: "ints_of' env ss = Some (Ok is)"
            note iS' = ints_of'_sound[OF iS iv(2) pss]
            have tyF: "has_type W ?Bs (app (pterm.Var F Fty) is) T"
              using has_type_ints_of'[OF iS iv(2,3)] tys0 s0e VV by simp
            show "\<exists>r. ints_of' env ts \<bind> (\<lambda>js. if F = G then flexflex1 env bs F Fty is js
                else flexflex2 env bs F Fty is G Gty js) = Some r \<and> uq ar W env [s0, t0] r"
            proof (rule uq_bindM[OF ints_of'_term[OF iv(1-3) tts]])
              fix js assume jS: "ints_of' env ts = Some (Ok js)"
              note jS' = ints_of'_sound[OF jS iv(2) pts]
              have tyG: "has_type W ?Bs (app (pterm.Var G Gty) js) T"
                using has_type_ints_of'[OF jS iv(2,3)] tyt0 t0e VV by simp
              show "\<exists>r. (if F = G then flexflex1 env bs F Fty is js
                  else flexflex2 env bs F Fty is G Gty js) = Some r \<and> uq ar W env [s0, t0] r"
              proof (cases "F = G")
                case True
                have "Gty = Fty" using has_type_app_Var(2)[OF tyF] has_type_app_Var(2)[OF tyG] True by simp
                then have tyG': "has_type W ?Bs (app (pterm.Var F Fty) js) T" using tyG True by simp
                from flexflex1_term[OF ti Fm gF bok Fu tyF tyG'] obtain r
                  where r: "flexflex1 env bs F Fty is js = Some r"
                    and p: "\<forall>env''. r = Ok env'' \<longrightarrow> (\<exists>W''. prunes ar W env W'' env'' {(F, Fty)})" by blast
                have "uq ar W env [s0, t0] r" using p by (cases r) (auto intro: uq_prunes)
                with r True show ?thesis by simp
              next
                case False
                from flexflex2_term[OF ti Fm Gm gF gG bok iS'(1) jS'(1) False Fu Gu tyF tyG]
                obtain r where r: "flexflex2 env bs F Fty is G Gty js = Some r"
                  and q: "\<forall>env''. r = Ok env'' \<longrightarrow>
                    (\<exists>W''. env_inv ar W'' env'' \<and> agreeV (maxidx env) W W'') \<and> extends env'' env \<and>
                    maxidx env \<le> maxidx env'' \<and>
                    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
                      (G, Gty) \<in> unb env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))"
                  by blast
                have "uq ar W env [s0, t0] r"
                proof (cases r)
                  case (Ok e')
                  with q obtain W'' where e': "env_inv ar W'' e'" "agreeV (maxidx env) W W''" "extends e' env"
                      "maxidx env \<le> maxidx e'"
                    and lt: "\<And>Y. finite Y \<Longrightarrow> \<forall>y\<in>Y. snd (fst y) \<le> maxidx env \<Longrightarrow> (F, Fty) \<in> unb env Y \<Longrightarrow>
                      (G, Gty) \<in> unb env Y \<Longrightarrow> card (unb e' Y) < card (unb env Y)"
                    by auto
                  have "card (unb e' (vsl ([s0, t0] @ C))) < card (unb env (vsl ([s0, t0] @ C)))"
                    if "oldC W env C" for C
                    using lt[OF finite_vsl old_vsl[OF bs0 bt0 that] unb_vsl_member[OF lF memF[OF VV(1)]]
                      unb_vsl_member[OF lG memG[OF VV(2)]]] .
                  then have "uq ar W env [s0, t0] (Ok e')" by (rule uq_unb_less[OF e'])
                  with Ok show ?thesis by simp
                qed simp
                with r False show ?thesis by simp
              qed
            qed
          qed
        next
          case (VR F Fty)
          from nsA ntA shs sht VR have Req: "R s0 t0 = ints_of' env ss \<bind> (\<lambda>is. flexrigid env bs F Fty is t0)"
            by (cases ht) (simp_all add: R_def)
          have gF: "ground ar Fty" using wss(1) VR by (simp add: wf_term_def)
          have Fm: "snd F \<le> maxidx env" using bs0 s0e VR by (simp add: below_list_comb)
          have lF: "lk env F Fty = None" using unbF[OF VR(1)] by (simp add: lk_def)
          show ?thesis unfolding Req
          proof (rule uq_bindM[OF ints_of'_term[OF iv(1-3) tss]])
            fix "is" assume iS: "ints_of' env ss = Some (Ok is)"
            have tyF: "has_type W ?Bs (app (pterm.Var F Fty) is) T"
              using has_type_ints_of'[OF iS iv(2,3)] tys0 s0e VR by simp
            from flexrigid_term[OF ti tyF tyt0 wt0' bt0 Fm bok gF]
            obtain r where r: "flexrigid env bs F Fty is t0 = Some r"
              and q: "\<forall>env''. r = Ok env'' \<longrightarrow>
                (\<exists>W''. env_inv ar W'' env'' \<and> agreeV (maxidx env) W W'') \<and> extends env'' env \<and>
                maxidx env \<le> maxidx env'' \<and>
                (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
                  vps t0 \<subseteq> reach env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))"
              by blast
            have "uq ar W env [s0, t0] r"
            proof (cases r)
              case (Ok e')
              with q obtain W'' where e': "env_inv ar W'' e'" "agreeV (maxidx env) W W''" "extends e' env"
                  "maxidx env \<le> maxidx e'"
                and lt: "\<And>Y. finite Y \<Longrightarrow> \<forall>y\<in>Y. snd (fst y) \<le> maxidx env \<Longrightarrow> (F, Fty) \<in> unb env Y \<Longrightarrow>
                  vps t0 \<subseteq> reach env Y \<Longrightarrow> card (unb e' Y) < card (unb env Y)"
                by auto
              have "card (unb e' (vsl ([s0, t0] @ C))) < card (unb env (vsl ([s0, t0] @ C)))"
                if "oldC W env C" for C
                using lt[OF finite_vsl old_vsl[OF bs0 bt0 that] unb_vsl_member[OF lF memF[OF VR(1)]]]
                  reach_incl[of "vsl ([s0, t0] @ C)" env] by auto
              then have "uq ar W env [s0, t0] (Ok e')" by (rule uq_unb_less[OF e'])
              with Ok show ?thesis by simp
            qed simp
            with r show "\<exists>r. flexrigid env bs F Fty is t0 = Some r \<and> uq ar W env [s0, t0] r" by blast
          qed
        next
          case (RV G Gty)
          from nsA ntA shs sht RV have Req: "R s0 t0 = ints_of' env ts \<bind> (\<lambda>js. flexrigid env bs G Gty js s0)"
            by (cases hs) (simp_all add: R_def)
          have gG: "ground ar Gty" using wts(1) RV by (simp add: wf_term_def)
          have Gm: "snd G \<le> maxidx env" using bt0 t0e RV by (simp add: below_list_comb)
          have lG: "lk env G Gty = None" using unbG[OF RV(2)] by (simp add: lk_def)
          show ?thesis unfolding Req
          proof (rule uq_bindM[OF ints_of'_term[OF iv(1-3) tts]])
            fix js assume jS: "ints_of' env ts = Some (Ok js)"
            have tyG: "has_type W ?Bs (app (pterm.Var G Gty) js) T"
              using has_type_ints_of'[OF jS iv(2,3)] tyt0 t0e RV by simp
            from flexrigid_term[OF ti tyG tys0 ws0' bs0 Gm bok gG]
            obtain r where r: "flexrigid env bs G Gty js s0 = Some r"
              and q: "\<forall>env''. r = Ok env'' \<longrightarrow>
                (\<exists>W''. env_inv ar W'' env'' \<and> agreeV (maxidx env) W W'') \<and> extends env'' env \<and>
                maxidx env \<le> maxidx env'' \<and>
                (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (G, Gty) \<in> unb env Y \<longrightarrow>
                  vps s0 \<subseteq> reach env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))"
              by blast
            have "uq ar W env [s0, t0] r"
            proof (cases r)
              case (Ok e')
              with q obtain W'' where e': "env_inv ar W'' e'" "agreeV (maxidx env) W W''" "extends e' env"
                  "maxidx env \<le> maxidx e'"
                and lt: "\<And>Y. finite Y \<Longrightarrow> \<forall>y\<in>Y. snd (fst y) \<le> maxidx env \<Longrightarrow> (G, Gty) \<in> unb env Y \<Longrightarrow>
                  vps s0 \<subseteq> reach env Y \<Longrightarrow> card (unb e' Y) < card (unb env Y)"
                by auto
              have "card (unb e' (vsl ([s0, t0] @ C))) < card (unb env (vsl ([s0, t0] @ C)))"
                if "oldC W env C" for C
                using lt[OF finite_vsl old_vsl[OF bs0 bt0 that] unb_vsl_member[OF lG memG[OF RV(2)]]]
                  reach_incl[of "vsl ([s0, t0] @ C)" env] by auto
              then have "uq ar W env [s0, t0] (Ok e')" by (rule uq_unb_less[OF e'])
              with Ok show ?thesis by simp
            qed simp
            with r show "\<exists>r. flexrigid env bs G Gty js s0 = Some r \<and> uq ar W env [s0, t0] r" by blast
          qed
        next
          case RR
          have rs: "is_rigid hs" by (rule rigI[OF RR(1) nAh(1) nApp(1) wss(1)])
          have rt: "is_rigid ht" by (rule rigI[OF RR(2) nAh(2) nApp(2) wts(1)])
          have gh: "typs_ok ar hs" "typs_ok ar ht" using wss(1) wts(1) by (simp_all add: wf_term_def)
          show ?thesis
          proof (cases "hs = ht")
            case False
            have "\<exists>e'. R s0 t0 = Some (Err e')"
              using nsA ntA shs sht RR rs rt nAh False gh
              by (cases hs; cases ht)
                (auto simp: R_def is_rigid_def unify_types_ground rigid_clash_def raise_def bindM_def
                  split: if_splits)
            then show ?thesis by auto
          next
            case hsht: True
            from tys0 s0e obtain Us where tyhs: "has_type W ?Bs hs (foldr fun_type Us T)"
              and tyss: "list_all2 (has_type W ?Bs) ss Us"
              by (auto simp: has_type_list_comb)
            from tyt0 t0e obtain Us' where tyht: "has_type W ?Bs ht (foldr fun_type Us' T)"
              and tyts: "list_all2 (has_type W ?Bs) ts Us'"
              by (auto simp: has_type_list_comb)
            have "Us' = Us"
              using has_type_unique[OF tyhs tyht[folded hsht]] by (auto dest: foldr_fun_type_inj)
            note tyts = tyts[unfolded this]
            have len: "length ss = length ts" using list_all2_lengthD[OF tyss] list_all2_lengthD[OF tyts] by simp
            have Req: "R s0 t0 = foldM (\<lambda>(s, t) env. unif alg bs s t env) (zip ss ts) env"
            proof -
              from rs consider (C) c U where "hs = Const c U" | (Fr) c U where "hs = Free c U"
                | (B) i where "hs = Bound i" by (auto simp: is_rigid_def)
              then show ?thesis
              proof cases
                case C
                with gh have "ground ar U" by simp
                with nsA ntA shs sht C hsht len show ?thesis
                  by (simp add: R_def unify_types_ground zip_eq_return)
              next
                case Fr
                with gh have "ground ar U" by simp
                with nsA ntA shs sht Fr hsht len show ?thesis
                  by (simp add: R_def unify_types_ground zip_eq_return)
              next
                case B
                with hsht have hb: "hs = Bound i" "ht = Bound i" by simp_all
                from nsA ntA shs sht len show ?thesis by (simp add: R_def hb zip_eq_return)
              qed
            qed
            have bss: "\<forall>t\<in>set ss. below (maxidx env) t" using bs0 s0e by (simp add: below_list_comb)
            have bts: "\<forall>t\<in>set ts. below (maxidx env) t" using bt0 t0e by (simp add: below_list_comb)
            have Mzs: "Ms env W s0 = 1 + sum_list (map (Ms env W) ss)"
              using Ms_rigid[OF iv(1-3) rs] tys0 s0e by simp
            have Mzt: "Ms env W t0 = 1 + sum_list (map (Ms env W) ts)"
              using Ms_rigid[OF iv(1-3) rt] tyt0 t0e by simp
            let ?ps = "zip ss ts"
            have le: "lexle (mu env W (pairs ?ps @ C)) (mu env W ([s0, t0] @ C))" for C
            proof (rule le_lexle)
              have "vsl (pairs ?ps @ C) \<subseteq> vsl ([s0, t0] @ C)"
                using pairs_zip[OF len] s0e t0e by (auto simp: vps_list_comb vsl_def)
              then show "fst (mu env W (pairs ?ps @ C)) \<le> fst (mu env W ([s0, t0] @ C))"
                using reach_incl[of "vsl ([s0, t0] @ C)" env] by (intro mu_fst_mono) blast
              show "snd (mu env W (pairs ?ps @ C)) \<le> snd (mu env W ([s0, t0] @ C))"
                using Mzs Mzt pairs_zip_sum[OF len] by (simp add: mu_def)
            qed
            have lt: "(mu env W (pairs ?ps), m) \<in> lexr"
            proof (rule lexr_lexle[OF _ m0], rule le_lexr)
              show "fst (mu env W (pairs ?ps)) \<le> fst (mu env W [s0, t0])" using le[of "[]"] by (auto simp: lexle_def)
              show "snd (mu env W (pairs ?ps)) < snd (mu env W [s0, t0])"
                using Mzs Mzt pairs_zip_sum[OF len] by (simp add: mu_def)
            qed
            have prem: "\<forall>(a, b)\<in>set ?ps. \<exists>U. has_type W ?Bs a U \<and> has_type W ?Bs b U \<and>
                below (maxidx env) a \<and> below (maxidx env) b"
            proof
              fix x assume "x \<in> set ?ps"
              then obtain i where i: "i < length ss" "x = (ss ! i, ts ! i)" using len by (auto simp: in_set_zip)
              then show "case x of (a, b) \<Rightarrow> \<exists>U. has_type W ?Bs a U \<and> has_type W ?Bs b U \<and>
                  below (maxidx env) a \<and> below (maxidx env) b"
                using tyss tyts bss bts len by (auto simp: list_all2_conv_all_nth) blast
            qed
            have step: "\<exists>r. unif alg bs a b e = Some r \<and> uq ar We e [a, b] r"
              if "(a, b) \<in> set ?ps" "env_inv ar We e" "has_type We ?Bs a U" "has_type We ?Bs b U"
                "below (maxidx e) a" "below (maxidx e) b" "(mu e We [a, b], m) \<in> lexr" for a b We e U
            proof -
              from that(1) have "a \<in> set ss" "b \<in> set ts" by (auto dest: pairs_zip_set)
              with wss(2) wts(2) have "wf_term ar ?n a" "wf_term ar ?n b" by simp_all
              from IH[OF that(7,2) bok this that(3-6)] show ?thesis .
            qed
            have "\<exists>r. foldM (\<lambda>(a, b) e. unif alg bs a b e) ?ps env = Some r \<and> uq ar W env (pairs ?ps) r"
              by (rule foldM_measure[where f = "\<lambda>a b e. unif alg bs a b e", OF _ prem lt ti])
                (rule step; assumption)
            then obtain r where r: "foldM (\<lambda>(a, b) e. unif alg bs a b e) ?ps env = Some r"
              and q: "uq ar W env (pairs ?ps) r" by blast
            have "uq ar W env [s0, t0] r" using uq_mono[OF q le] .
            with r Req show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
  from main obtain r where r: "R s0 t0 = Some r" and q: "uq ar W env [s0, t0] r" by blast
  have "uq ar W env [s, t] r" using uq_mono[OF q red] by simp
  with r hhs hht u_eq show ?case by (simp add: bindM_def)
qed

end

end
