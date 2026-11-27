section \<open>Termination of the Occurs Checks\<close>

theory Unify_Occurs_Termination
  imports Unify_Occurs_Sound Unify_Simpl_Inv
begin
context pure_sig_gen
begin

context
  fixes env assumes tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)" and ac: "acyc env"
begin

lemma tok_binding: "tok env (vars t \<union> evars env) \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow>
    tok env (vars u \<union> evars env)"
  using evarsI2[of env x U u] by (auto intro: tok_mono)

lemma occur_dfd:
  "card (bset env - set seen) \<le> k \<Longrightarrow> tok env (vars t \<union> evars env) \<Longrightarrow> dfd (occur t env v seen)"
proof (induction k arbitrary: t seen rule: less_induct)
  case (less k)
  show ?case using less.prems
  proof (induction t arbitrary: seen)
    case (Var w T)
    have lk: "lookup env w T = (case vt_lookup (tenv env) w of None \<Rightarrow> return None
      | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash w T U)"
      by (rule lookup_def_tok[OF tac tc tok_mono[OF Var.prems(2)]]) auto
    have cl: "loose \<noteq> {}" if "vt_lookup (tenv env) w = Some (U, u)" "tnorm (tyenv env) T \<noteq> tnorm (tyenv env) U" for U u
      by (rule tok_clash_ne[OF Var.prems(2) _ that]) auto
    show ?case
    proof (cases "w \<in> set seen \<or> v = w")
      case True
      then show ?thesis by (subst occur.simps) auto
    next
      case False
      show ?thesis
      proof (cases "vt_lookup (tenv env) w")
        case (Some b)
        obtain U u where b: "b = (U, u)" by force
        have lt: "card (bset env - set (w # seen)) < k"
          using card_bset_less[of w seen env] False Some Var.prems(1) by simp
        have "dfd (occur u env v (w # seen))"
          by (rule less.IH[OF lt order_refl tok_binding[OF Var.prems(2) Some[unfolded b]]])
        then show ?thesis using False Some b lk cl[OF Some[unfolded b]]
          by (subst occur.simps) (simp add: dfd_def var_clash_def raise_def bindM_def return_def clashx_def)
      qed (use False lk in \<open>subst occur.simps, simp\<close>)
    qed
  next
    case (Abs a T body)
    from Abs.IH[of seen] Abs.prems show ?case by (subst occur.simps) simp
  next
    case (App f u)
    have d1: "dfd (occur u env v seen)" by (rule App.IH(2)) (use App.prems in \<open>auto intro: tok_mono\<close>)
    show ?case
    proof (subst occur.simps, simp, rule dfd_bindM[OF d1])
      fix r assume r: "occur u env v seen = Some (Ok r)"
      obtain b1 s1 where r': "r = (b1, s1)" by force
      from occur_sound[OF r[unfolded r'] refl ac] have s: "set seen \<subseteq> set s1" by blast
      have "dfd (occur f env v s1)"
        by (rule App.IH(1)) (use App.prems card_bset_mono[OF s, of env] in \<open>auto intro: tok_mono\<close>)
      then show "dfd (if fst r then return (True, snd r) else occur f env v (snd r))" by (simp add: r')
    qed
  qed (subst occur.simps; simp)+
qed

lemma occurs_list_dfd:
  "tok env (\<Union>(vars ` set ts) \<union> evars env) \<Longrightarrow> dfd (occurs_list env v seen ts)"
proof (induction ts arbitrary: seen)
  case (Cons t ts)
  have d1: "dfd (occur t env v seen)" by (rule occur_dfd[OF order_refl]) (use Cons.prems in \<open>auto intro: tok_mono\<close>)
  show ?case
  proof (simp, rule dfd_bindM[OF d1])
    fix r assume "occur t env v seen = Some (Ok r)"
    have "dfd (occurs_list env v (snd r) ts)" by (rule Cons.IH) (use Cons.prems in \<open>auto intro: tok_mono\<close>)
    then show "dfd (if fst r then return (True, snd r) else occurs_list env v (snd r) ts)" by simp
  qed
qed simp

lemma occurs_terms_dfd: "tok env (\<Union>(vars ` set ts) \<union> evars env) \<Longrightarrow> dfd (occurs_terms env v ts)"
  unfolding occurs_terms_def by (rule dfd_bindM[OF occurs_list_dfd]) simp_all

lemma nonrigid_dfd: "tok env (vars t \<union> evars env) \<Longrightarrow> dfd (nonrigid env v seen t)"
  unfolding nonrigid_def by (rule dfd_bindM[OF occurs_list_dfd]) (auto split: prod.splits)

lemma head_of_in_dfd: "tok env (vars t \<union> evars env) \<Longrightarrow> dfd (head_of_in env t)"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_less_than],
    of "\<lambda>t. (size (unfc env t), hrk env t)"]])
  case (1 t)
  note IH = "1.IH"[simplified, rule_format]
  show ?case
  proof (cases t)
    case (Var x T)
    have lk: "lookup env x T = (case vt_lookup (tenv env) x of None \<Rightarrow> return None
      | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash x T U)"
      by (rule lookup_def_tok[OF tac tc tok_mono[OF "1.prems"]]) (auto simp: Var)
    have cl: "loose \<noteq> {}" if "vt_lookup (tenv env) x = Some (U, u)" "tnorm (tyenv env) T \<noteq> tnorm (tyenv env) U" for U u
      by (rule tok_clash_ne[OF "1.prems" _ that]) (auto simp: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      show ?thesis
      proof (cases "tnorm (tyenv env) T = tnorm (tyenv env) U")
        case True
        have tcU: "tcons (tyenv env) T" "tcons (tyenv env) U"
        proof -
          have "(x, U) \<in> evars env" using Some b unfolding evars_def bnds_def by (cases x) blast
          then show "tcons (tyenv env) T" "tcons (tyenv env) U" using "1.prems" Var by (auto simp: tok_def)
        qed
        have ue: "ok (unified (tyenv env) T U) True" using unified_ok[OF tac tc tcU] True by (simp add: return_def)
        have u: "unfc env u = unfc env t" using Some b Var ue by (simp add: unfc_Var_bound[OF ac])
        have "hrk env u < hrk env t"
        proof (cases u)
          case (Var y U')
          have "(y, x) \<in> dep env" using depI[OF Some[unfolded b], of y U'] Var by simp
          then show ?thesis using rk_less[OF ac] Var \<open>t = Var x T\<close> by (simp add: hrk_def)
        qed (simp_all add: hrk_def \<open>t = Var x T\<close>)
        then have "dfd (head_of_in env u)" using IH[of u] u tok_binding[OF "1.prems" Some[unfolded b]] by simp
        then show ?thesis using lk Var Some b True by (subst head_of_in.simps) (simp add: dfd_def)
      qed (use lk Var Some b cl[OF Some[unfolded b]] in \<open>subst head_of_in.simps, simp add: var_clash_def clashx_def\<close>)
    qed (use lk Var in \<open>subst head_of_in.simps, simp\<close>)
  next
    case (App f u)
    have "dfd (head_of_in env f)" using IH[of f] "1.prems" App by (auto intro: tok_mono)
    then show ?thesis using App by (subst head_of_in.simps) simp
  qed (subst head_of_in.simps, simp)+
qed

context
  assumes cl: "closed_env env"
begin

lemma rigid_head_dfd: "tok env (vars t \<union> evars env) \<Longrightarrow> termip (sup beta subt) (unfc env t) \<Longrightarrow>
    dfd (rigid_head env t)"
  unfolding rigid_head_def using head_norm_def[OF ac cl tac tc] by (intro dfd_bindM) auto

lemma rigid_occ_dfd: "tok env (vars t \<union> evars env) \<Longrightarrow> termip (sup beta subt) (unfc env t) \<Longrightarrow>
    dfd (rigid_occ env v t)"
proof -
  assume tk: "tok env (vars t \<union> evars env)" and sn: "termip (sup beta subt) (unfc env t)"
  obtain h ts where hts: "strip_comb t = (h, ts)" by force
  have t: "t = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
  have "dfd (rigid_head env u)" if u: "u \<in> set ts" for u
  proof (rule rigid_head_dfd)
    show "tok env (vars u \<union> evars env)" using tk t u by (auto simp: vars_apps intro: tok_mono)
    show "termip (sup beta subt) (unfc env u)"
      by (rule termip_sup_reds[OF tranclp_into_rtranclp sn])
        (use u t sup_subt_apps[of "unfc env u" "map (unfc env) ts"] in \<open>simp add: unfc_apps\<close>)
  qed
  then show ?thesis using hts by (auto simp: rigid_occ_def intro: allM_dfd split: pterm.splits)
qed

lemma occomb_dfd:
  assumes H: "\<And>s seen'. size s < size t0 \<Longrightarrow> set seen0 \<subseteq> set seen' \<Longrightarrow> tok env (vars s \<union> evars env) \<Longrightarrow>
      (sup beta subt)\<^sup>*\<^sup>* (unfc env t0) (unfc env s) \<Longrightarrow> dfd (oc seen' s)"
    and G: "\<And>s seen' r. oc seen' s = Some (Ok r) \<Longrightarrow> set seen' \<subseteq> set (snd r)"
  shows "size t \<le> size t0 \<Longrightarrow> (\<exists>f u. t = f $ u) \<or> size t < size t0 \<Longrightarrow> set seen0 \<subseteq> set seen \<Longrightarrow>
    tok env (vars t \<union> evars env) \<Longrightarrow> (sup beta subt)\<^sup>*\<^sup>* (unfc env t0) (unfc env t) \<Longrightarrow>
    dfd (occomb oc seen t)"
proof (induction t arbitrary: seen)
  case (App f x)
  have x: "size x < size t0" "tok env (vars x \<union> evars env)" using App.prems(1,4) by (auto intro: tok_mono)
  have st: "subt (unfc env (f $ x)) (unfc env x)" "subt (unfc env (f $ x)) (unfc env f)"
    by (simp_all add: subt_def)
  have sx: "(sup beta subt)\<^sup>*\<^sup>* (unfc env t0) (unfc env x)"
    using App.prems(5) st(1) by (meson rtranclp.rtrancl_into_rtrancl sup2I2)
  have sf: "(sup beta subt)\<^sup>*\<^sup>* (unfc env t0) (unfc env f)"
    using App.prems(5) st(2) by (meson rtranclp.rtrancl_into_rtrancl sup2I2)
  show ?case
  proof (simp, rule dfd_bindM[OF H[OF x(1) App.prems(3) x(2) sx]])
    fix r1 assume r1: "oc seen x = Some (Ok r1)"
    have s0: "set seen0 \<subseteq> set (snd r1)" using App.prems(3) G[OF r1] by blast
    have sz: "size f \<le> size t0" "size f < size t0" using App.prems(1) by auto
    have tf: "tok env (vars f \<union> evars env)" using App.prems(4) by (auto intro: tok_mono)
    have "dfd (occomb oc (snd r1) f)" by (rule App.IH(1)[OF sz(1) disjI2[OF sz(2)] s0 tf sf])
    then show "dfd (if fst r1 = Rigid then return (Rigid, snd r1)
        else bindM (occomb oc (snd r1) f) (\<lambda>r2. return (if fst r2 = NoOcc then fst r1 else fst r2, snd r2)))"
      by (auto intro: dfd_bindM)
  qed
qed (use H in fastforce)+

lemma rocc_dfd:
  "card (bset env - set seen) \<le> k \<Longrightarrow> tok env (vars t \<union> evars env) \<Longrightarrow> termip (sup beta subt) (unfc env t) \<Longrightarrow>
    dfd (rocc t env v seen)"
proof (induction k arbitrary: t seen rule: less_induct)
  case (less k)
  show ?case using less.prems
  proof (induction "size t" arbitrary: t seen rule: less_induct)
    case less2: less
    show ?case
    proof (cases t)
      case (Var w T)
      have lk: "lookup env w T = (case vt_lookup (tenv env) w of None \<Rightarrow> return None
        | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash w T U)"
        by (rule lookup_def_tok[OF tac tc tok_mono[OF less2.prems(2)]]) (auto simp: Var)
      have cl: "loose \<noteq> {}" if "vt_lookup (tenv env) w = Some (U, u)" "tnorm (tyenv env) T \<noteq> tnorm (tyenv env) U" for U u
        by (rule tok_clash_ne[OF less2.prems(2) _ that]) (auto simp: Var)
      show ?thesis
      proof (cases "w \<in> set seen \<or> v = w")
        case True
        then show ?thesis using Var by (subst rocc.simps) auto
      next
        case False
        show ?thesis
        proof (cases "vt_lookup (tenv env) w")
          case (Some b)
          obtain U u where b: "b = (U, u)" by force
          show ?thesis
          proof (cases "tnorm (tyenv env) T = tnorm (tyenv env) U")
            case True
            have lt: "card (bset env - set (w # seen)) < k"
              using card_bset_less[of w seen env] False Some less2.prems(1) by simp
            have tcU: "tcons (tyenv env) T" "tcons (tyenv env) U"
            proof -
              have "(w, U) \<in> evars env" using Some b unfolding evars_def bnds_def by (cases w) blast
              then show "tcons (tyenv env) T" "tcons (tyenv env) U" using less2.prems(2) Var by (auto simp: tok_def)
            qed
            have ue: "ok (unified (tyenv env) T U) True" using unified_ok[OF tac tc tcU] True by (simp add: return_def)
            have "unfc env u = unfc env t" using Some b Var ue by (simp add: unfc_Var_bound[OF ac])
            then have sn: "termip (sup beta subt) (unfc env u)" using less2.prems(3) by simp
            have "dfd (rocc u env v (w # seen))"
              by (rule less.IH[OF lt order_refl tok_binding[OF less2.prems(2) Some[unfolded b]] sn])
            then show ?thesis using False Some b lk Var True by (subst rocc.simps) (simp add: dfd_def)
          qed (use False Some b lk Var cl[OF Some[unfolded b]] in \<open>subst rocc.simps, simp add: var_clash_def clashx_def\<close>)
        qed (use False lk Var in \<open>subst rocc.simps, simp\<close>)
      qed
    next
      case (Abs a T body)
      have "termip (sup beta subt) (unfc env body)"
        by (rule termip_sup_reds[OF _ less2.prems(3)]) (use Abs in \<open>auto simp: subt_def\<close>)
      with less2.hyps[of body seen] less2.prems Abs show ?thesis
        by (subst rocc.simps) (simp add: tok_mono)
    next
      case (App f u)
      have vf: "tok env (vars f \<union> evars env)" using less2.prems App by (auto intro: tok_mono)
      have hd: "dfd (head_of_in env f)" by (rule head_of_in_dfd[OF vf])
      have nr: "dfd (nonrigid env v seen t)" by (rule nonrigid_dfd[OF less2.prems(2)])
      have ro: "dfd (rigid_occ env v t)" by (rule rigid_occ_dfd[OF less2.prems(2,3)])
      have oc: "dfd (occomb (\<lambda>seen t. rocc t env v seen) seen t)"
      proof (rule occomb_dfd[where t0 = t and seen0 = seen])
        fix s seen' assume s: "size s < size t" "set seen \<subseteq> set seen'" "tok env (vars s \<union> evars env)"
          "(sup beta subt)\<^sup>*\<^sup>* (unfc env t) (unfc env s)"
        have "card (bset env - set seen') \<le> k" using card_bset_mono[OF s(2), of env] less2.prems by simp
        moreover have "termip (sup beta subt) (unfc env s)" by (rule termip_sup_reds[OF s(4) less2.prems(3)])
        ultimately show "dfd (rocc s env v seen')" by (rule less2.hyps[OF s(1) _ s(3)])
      next
        fix s seen' r assume "rocc s env v seen' = Some (Ok r)"
        from rocc_sound[OF this refl ac] show "set seen' \<subseteq> set (snd r)" by blast
      qed (use App less2.prems in auto)
      show ?thesis
      proof (subst rocc.simps, simp only: App pterm.case, rule dfd_bindM[OF hd])
        fix h assume "head_of_in env f = Some (Ok h)"
        show "dfd (case h of
          Var w _ \<Rightarrow> do {
            b \<leftarrow> if v = w then rigid_occ env v (f $ u) else return False;
            if b then return (Rigid, seen) else nonrigid env v seen (f $ u)}
        | Abs _ _ _ \<Rightarrow> nonrigid env v seen (f $ u)
        | _ \<Rightarrow> occomb (\<lambda>seen t. rocc t env v seen) seen (f $ u))"
          using nr ro oc App by (cases h) (auto intro!: dfd_bindM simp del: occomb.simps)
      qed
    qed (subst rocc.simps, simp)+
  qed
qed

theorem rigid_occurs_term_dfd:
  "tok env (vars t \<union> evars env) \<Longrightarrow> termip (sup beta subt) (unfc env t) \<Longrightarrow> dfd (rigid_occurs_term env v t)"
  unfolding rigid_occurs_term_def by (rule dfd_bindM[OF rocc_dfd[OF order_refl]]) simp_all

end

end

end

end
