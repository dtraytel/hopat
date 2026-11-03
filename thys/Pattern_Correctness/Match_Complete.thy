section \<open>Completeness of Matching\<close>

theory Match_Complete
  imports Match_Exceptions Pattern_Patterns
begin

context pure_sig
begin

text \<open>
  Matching a higher-order pattern against a \<open>\<beta>\<close>-normal object finds a matcher whenever one
  exists: if \<open>(\<rho>, \<sigma>)\<close> instantiates the pattern to a term equivalent to the object, then
  matching succeeds, with a result that agrees with \<open>(\<rho>, \<sigma>)\<close> on the pattern.
\<close>

subsection \<open>\<open>\<eta>\<close>-contraction of \<open>\<beta>\<close>-normal terms\<close>

lemma decr_rename0: "decr lev f = rename (\<lambda>k. k - 1) lev f"
  by (induction f arbitrary: lev) (auto simp: algebra_simps)

lemma decr_rename: "\<not> loose_bvar1 f lev \<Longrightarrow> decr lev f = rename (\<lambda>k. if k = 0 then 0 else k - 1) lev f"
  unfolding decr_rename0 by (rule rename_cong) auto

lemma is_Abs_eta_contract: "is_Abs (eta_contract t) \<Longrightarrow> is_Abs t"
  by (cases t) auto

lemma normal_eta_contract: "no_redex t \<Longrightarrow> normal (eta_contract t)"
proof (induction t)
  case (Abs a T body)
  let ?b = "eta_contract body"
  have nb: "normal ?b" using Abs by simp
  show ?case
  proof (cases "\<exists>f. ?b = f $ Bound 0 \<and> \<not> is_dependent f")
    case True
    then obtain f where b: "?b = f $ Bound 0" "\<not> is_dependent f" by blast
    have "normal f" using nb b(1) by (simp add: normal_iff)
    moreover have "nonneg (\<lambda>k. if k = 0 then 0 else k - 1)" by (auto simp: nonneg_def integer_arith)
    ultimately have "normal (decr 0 f)" using b(2) by (simp add: decr_rename is_dependent_def normal_rename)
    with b show ?thesis by simp
  next
    case False
    then have "eta_contract (Abs a T body) = Abs a T ?b" by (auto simp: Let_def split: pterm.splits)
    with nb False show ?thesis by (auto simp: normal_iff is_dependent_def)
  qed
next
  case (App s t)
  then have "\<not> is_Abs (eta_contract s)" "normal (eta_contract s)" "normal (eta_contract t)"
    using is_Abs_eta_contract by auto
  then show ?case by (simp add: normal_iff)
qed (simp_all add: normal_iff)

lemma aeconv_complete:
  assumes "no_redex s" "no_redex t" "wt s" "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  shows "aeconv s t"
proof -
  have cs: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eta_contract s"
    using assms(3) eta_contract_reds[of s] by (intro beta_eta_conv) (simp add: eta_reds_beta_eta_reds)
  have wt: "wt t" using assms(3,4) wt_conv by blast
  have ct: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eta_contract t"
    using wt eta_contract_reds[of t] by (intro beta_eta_conv) (simp add: eta_reds_beta_eta_reds)
  have c: "eta_contract s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eta_contract t"
    using cs ct assms(4) by (blast intro: conv_sym conv_trans)
  have "wt (eta_contract s)" using cs assms(3) wt_conv by blast
  from conv_normal_aconv[OF c this normal_eta_contract[OF assms(1)] normal_eta_contract[OF assms(2)]]
  show ?thesis by (simp add: aeconv_def)
qed


subsection \<open>Patterns and \<open>\<beta>\<close>-normal terms\<close>

lemma strip_comb_acc_apps_m: "strip_comb_acc (s \<degree>\<degree> ts) us = strip_comb_acc s (ts @ us)"
  by (induction ts arbitrary: s) simp_all

lemma ppat_strip:
  assumes "ppat t" "\<not> is_Abs t" "strip_comb t = (h, ts)"
  shows "(rigid h \<and> (\<forall>u\<in>set ts. ppat u)) \<or> (\<exists>x T is. h = Var x T \<and> ts = map Bound is \<and> distinct is)"
  using assms(1)
proof cases
  case (ppat_Abs u a T)
  with assms(2) show ?thesis by simp
next
  case (ppat_rigid h' ts')
  then have "\<not> (\<exists>f u. h' = f $ u)" by (cases h') auto
  with ppat_rigid assms(3) show ?thesis by (simp add: strip_comb_atom_apps)
next
  case (ppat_flex "is" x T)
  with assms(3) have "h = Var x T" "ts = map Bound is" by (simp_all add: app_apps strip_comb_atom_apps)
  with ppat_flex show ?thesis by blast
qed

lemma rigid_lift: "rigid (lift h k) \<longleftrightarrow> rigid h"
  by (cases h) simp_all

lemma inj_lift_index: "inj (\<lambda>i::integer. if k \<le> i then i + 1 else i)"
  by (rule injI) (auto split: if_splits simp: integer_arith)

lemma lift_Bounds: "map (\<lambda>t. lift t k) (map Bound is) = map Bound (map (\<lambda>i. if k \<le> i then i + 1 else i) is)"
  by auto

lemma distinct_lift_index:
  "distinct (is :: integer list) \<Longrightarrow> distinct (map (\<lambda>i. if k \<le> i then i + 1 else i) is)"
  using inj_on_subset[OF inj_lift_index[of k], of "set is"] by (simp add: distinct_map)

lemma ppat_lift: "ppat t \<Longrightarrow> ppat (lift t k)"
proof (induction arbitrary: k rule: ppat.induct)
  case (ppat_Abs t a T)
  then show ?case by (simp add: ppat.ppat_Abs)
next
  case (ppat_rigid h ts)
  then show ?case by (simp add: ppat.ppat_rigid rigid_lift)
next
  case (ppat_flex "is" x T)
  have "ppat (app (Var x T) (map (\<lambda>i. if k \<le> i then i + 1 else i) is))"
    using ppat_flex by (intro ppat.ppat_flex distinct_lift_index)
  then show ?case by (simp add: app_apps lift_Bounds del: map_map)
qed

lemma ppat_incr_Bound0:
  assumes "ppat t" "\<not> is_Abs t"
  shows "ppat (incr t $ Bound 0)"
  using assms(1)
proof cases
  case (ppat_Abs u a T)
  with assms(2) show ?thesis by simp
next
  case (ppat_rigid h ts)
  have "ppat (lift h 0 \<degree>\<degree> (map (\<lambda>t. lift t 0) ts @ [Bound 0]))"
    using ppat_rigid ppat_lift by (intro ppat.ppat_rigid) (auto simp: rigid_lift ppat_atom)
  moreover have "incr t $ Bound 0 = lift h 0 \<degree>\<degree> (map (\<lambda>t. lift t 0) ts @ [Bound 0])"
    by (simp add: ppat_rigid incr_def incr_aux_lift)
  ultimately show ?thesis by simp
next
  case (ppat_flex "is" x T)
  let ?f = "\<lambda>i::integer. if 0 \<le> i then i + 1 else i"
  have nz: "?f i \<noteq> 0" for i by (simp add: integer_arith)
  have "distinct (map ?f is @ [0])"
    using distinct_lift_index[OF ppat_flex(2), of 0] nz by auto
  then have "ppat (app (Var x T) (map ?f is @ [0]))" by (rule ppat.ppat_flex)
  moreover have "incr t $ Bound 0 = app (Var x T) (map ?f is @ [0])"
    using lift_Bounds[of 0 "is"] by (simp add: ppat_flex incr_def incr_aux_lift app_apps del: map_map)
  ultimately show ?thesis by simp
qed

lemma no_redex_lift: "no_redex (incr_bv n k t) \<longleftrightarrow> no_redex t"
proof (induction t arbitrary: k)
  case (App s t)
  then show ?case by (cases s) auto
qed auto

lemma no_redex_apps_head: "no_redex (h \<degree>\<degree> ts) \<Longrightarrow> ts \<noteq> [] \<Longrightarrow> \<not> is_Abs h"
proof (induction ts arbitrary: h)
  case (Cons t ts)
  show ?case
  proof (cases "ts = []")
    case True
    with Cons.prems show ?thesis by simp
  next
    case False
    from Cons.IH[OF _ False] Cons.prems have "\<not> is_Abs (h $ t)" by simp
    have "no_redex (h $ t)" using Cons.prems(1) no_redex_apps[of "h $ t" ts] by simp
    then show ?thesis by simp
  qed
qed simp

lemma no_redex_strip:
  assumes "no_redex t" "\<not> is_Abs t" "strip_comb t = (h, ts)"
  shows "atom h" "\<forall>u\<in>set ts. no_redex u"
proof -
  have t: "t = h \<degree>\<degree> ts" by (rule mt_strip_comb_apps[OF assms(3)])
  have nh: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF assms(3)])
  have "\<not> is_Abs h"
  proof (cases "ts = []")
    case True
    with assms(2) t show ?thesis by simp
  qed (use no_redex_apps_head assms(1) t in blast)
  with nh show "atom h" by (cases h) auto
  with assms(1) show "\<forall>u\<in>set ts. no_redex u" using no_redex_apps[of h ts] t
    by (cases h) auto
qed

lemma red_no_redex: "ok (red t is js) u \<Longrightarrow> no_redex t \<Longrightarrow> no_redex u"
proof (induction t "is" js arbitrary: u rule: red.induct)
  case (1 a T s i "is" js)
  then show ?case by simp
next
  case (2 t)
  then show ?case by simp
qed (auto simp: app_apps no_redex_apps simp del: mapbnd.simps dest!: ok_mapbnd_nth)

lemma no_redex_abs_list: "no_redex (abs_list bs t) \<longleftrightarrow> no_redex t"
  by (induction bs) (auto simp: case_prod_unfold abs_list_def)

lemma bs_env_cert: "bs_env TVar e bs \<Longrightarrow> 0 \<le> k \<Longrightarrow> k < ilength bs \<Longrightarrow> cert_typ alg ar (e k)"
proof -
  assume bs: "bs_env TVar e bs" and k: "0 \<le> k" "k < ilength bs"
  then have "e k = snd (bs ! nat_of_integer k)" by (simp add: bs_env_def)
  moreover have "bs ! nat_of_integer k \<in> set bs" using nat_of_integer_less_ilength[OF k] by simp
  ultimately show "cert_typ alg ar (e k)" using bs by (auto simp: bs_env_def case_prod_unfold)
qed

lemma subst_type_agree:
  assumes "tvars T \<subseteq> tbnd tye" "tagrees tye \<rho> A" "tvars T \<subseteq> A"
  shows "ok (subst_type tye T) (tsubst \<rho> T)"
proof -
  have ag: "vt_lookup tye v = Some (S', U') \<Longrightarrow> S' = S \<and> \<rho> v S = U'" if "(v, S) \<in> tvars T" for v S S' U'
    using assms(2,3) that unfolding tagrees_def by fastforce
  then have "\<forall>(v, S)\<in>tvars T. \<forall>S' U. vt_lookup tye v = Some (S', U) \<longrightarrow> S' = S" by blast
  then obtain T' where st: "ok (subst_type tye T) T'" using subst_type_ok by blast
  have "T' = tsubst (mtinst tye) T" by (rule ok_subst_type[OF st])
  also have "\<dots> = tsubst \<rho> T"
  proof (rule tsubst_cong)
    fix v S assume vS: "(v, S) \<in> tvars T"
    then obtain S' U' where "vt_lookup tye v = Some (S', U')" using assms(1) by (auto simp: tbnd_def)
    with ag[OF vS] show "mtinst tye v S = \<rho> v S" by (simp add: mtinst_def)
  qed
  finally show ?thesis using st by simp
qed

lemma match_bind_ok:
  assumes "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> k \<in> set is" "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    "vt_lookup itms x = None"
  shows "\<exists>itms'. ok (match_bind itms bs x T is t) itms'"
proof -
  obtain r where m: "match_bind itms bs x T is t = Some r" using match_bind_term by blast
  have up: "ok (update_new (x, (T, u)) itms) (vt_update (x, (T, u)) itms)" for u
    using assms(3) by (simp add: ok_update_new)
  show ?thesis
  proof (cases "is = []")
    case True
    with assms(1) have "set (loose_bnos t) = {}" using set_loose_bnos[of t] by auto
    then have "loose_bnos t = []" by simp
    with True up[of t] show ?thesis by (auto simp: match_bind_def)
  next
    case False
    have sb: "subset (loose_bnos t) is" using assms(1) by (auto simp: subset_iff_set set_loose_bnos)
    have "\<exists>t'. ok (if downto0 is (ilength bs - 1) then return t else mapbnd (idx is) 0 t) t'"
      using ok_mapbnd_idx[of t 0 "is"] assms(1) by auto
    then obtain t' where t': "ok (if downto0 is (ilength bs - 1) then return t else mapbnd (idx is) 0 t) t'" ..
    have mk: "ok (mkabs bs is t') (abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) t')"
      using assms(2) by (simp add: ok_mkabs)
    show ?thesis
      using t' mk up False sb by (auto simp: match_bind_def Let_def simp del: mapbnd.simps)
  qed
qed

text \<open>The arguments of rigid heads have the same types:\<close>

lemma rigid_args_typing:
  assumes "e \<turnstile> inst \<rho> (h \<degree>\<degree> ps) : Ty" "e \<turnstile> h' \<degree>\<degree> qs : Ty" "inst \<rho> h = h'" "length ps = length qs"
  shows "list_all2 (\<lambda>p q. \<exists>T. e \<turnstile> inst \<rho> p : T \<and> e \<turnstile> q : T) ps qs"
proof -
  from assms(1,3) have "e \<turnstile> h' \<degree>\<degree> map (inst \<rho>) ps : Ty" by (simp add: inst_apps)
  then obtain As where ha: "e \<turnstile> h' : As \<Rrightarrow> Ty" and pa: "e \<tturnstile> map (inst \<rho>) ps : As"
    by (rule list_app_typeE)
  from assms(2) obtain Bs where hb: "e \<turnstile> h' : Bs \<Rrightarrow> Ty" and qb: "e \<tturnstile> qs : Bs"
    by (rule list_app_typeE)
  have "As \<Rrightarrow> Ty = Bs \<Rrightarrow> Ty" using typing_unique[OF ha hb] .
  moreover have "length As = length Bs" using typings_nth[OF pa] typings_nth[OF qb] assms(4) by simp
  ultimately have "As = Bs" using funs_eq by blast
  then show ?thesis using typings_nth[OF pa] typings_nth[OF qb] assms(4)
    by (auto simp: list_all2_conv_all_nth)
qed

text \<open>The bindings of the pattern variables agree with \<open>(\<rho>, \<sigma>)\<close>:\<close>

definition magree :: "tinst \<Rightarrow> vsubst \<Rightarrow> tenv \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "magree \<rho> \<sigma> te X \<longleftrightarrow> (\<forall>x T U u. (x, T) \<in> X \<longrightarrow> vt_lookup te x = Some (U, u) \<longrightarrow>
    U = T \<and> closed u \<and> no_redex u \<and> (\<forall>e. e \<turnstile> u : tsubst \<rho> T) \<and> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> x (tsubst \<rho> T))"

lemma magree_unbound: "\<forall>(x, T)\<in>X. vt_lookup te x = None \<Longrightarrow> magree \<rho> \<sigma> te X"
  unfolding magree_def by fastforce

lemma magreeD:
  "magree \<rho> \<sigma> te X \<Longrightarrow> (x, T) \<in> X \<Longrightarrow> vt_lookup te x = Some (U, u) \<Longrightarrow>
    U = T \<and> closed u \<and> no_redex u \<and> (\<forall>e. e \<turnstile> u : tsubst \<rho> T) \<and> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> x (tsubst \<rho> T)"
  unfolding magree_def by blast

lemma typ_match_m_ok: "ok (typ_match alg' T U tye) tye' \<Longrightarrow> typ_match_m alg' T U tye = Some (Ok tye')"
  by (simp add: typ_match_m_def)


subsection \<open>Higher-order matching\<close>

lemma mtch_complete:
  assumes "ppat pt" "no_redex ob" "bs_env TVar e bs" "e \<turnstile> inst \<rho> pt : Ty" "e \<turnstile> ob : Ty"
    "\<not> loose_bvar pt (ilength bs)" "\<forall>T\<in>typs pt. wft ar T" "ptvs pt \<subseteq> A" "scons A"
    "tagrees (fst env) \<rho> A" "abs_bound (tbnd (fst env)) pt" "vars pt \<subseteq> X" "vfun X"
    "magree \<rho> \<sigma> (snd env) X" "wt_subst \<sigma>" "ap \<rho> \<sigma> pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
  shows "\<exists>env'. ok (mtch alg bs pt ob env) env' \<and> tagrees (fst env') \<rho> A \<and>
    textends (fst env) (fst env') \<and> magree \<rho> \<sigma> (snd env') X"
  using assms
proof (induction "(pt, ob)" arbitrary: bs pt ob env e Ty
    rule: wf_induct[OF wf_measures[of "[\<lambda>(pt, ob). nabs pt + nabs ob, \<lambda>(pt, ob). size pt + size ob]"]])
  case 1
  note prems = "1.prems"
  have IH: "\<exists>env'. ok (mtch alg bs' p q env0) env' \<and> tagrees (fst env') \<rho> A \<and>
      textends (fst env0) (fst env') \<and> magree \<rho> \<sigma> (snd env') X"
    if "nabs p + nabs q < nabs pt + nabs ob \<or> nabs p + nabs q \<le> nabs pt + nabs ob \<and> size p + size q < size pt + size ob"
      "ppat p" "no_redex q" "bs_env TVar e' bs'" "e' \<turnstile> inst \<rho> p : T'" "e' \<turnstile> q : T'"
      "\<not> loose_bvar p (ilength bs')" "\<forall>T\<in>typs p. wft ar T" "ptvs p \<subseteq> A"
      "tagrees (fst env0) \<rho> A" "abs_bound (tbnd (fst env0)) p" "vars p \<subseteq> X"
      "magree \<rho> \<sigma> (snd env0) X" "ap \<rho> \<sigma> p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> q"
    for bs' p q env0 e' T'
  proof -
    have "((p, q), (pt, ob)) \<in> measures [\<lambda>(pt, ob). nabs pt + nabs ob, \<lambda>(pt, ob). size pt + size ob]"
      using that(1) by (auto simp: order.order_iff_strict)
    with "1.hyps" that(2-) prems(9,13,15) show ?thesis by blast
  qed
  obtain iTs itms where e: "env = (iTs, itms)" by force
  have tap: "e \<turnstile> ap \<rho> \<sigma> pt : Ty" by (rule typing_ap[OF prems(4,15)])
  show ?case
  proof (cases "is_Abs pt")
    case pA: True
    then obtain ns Ts ts where pt: "pt = Abs ns Ts ts" by (cases pt) auto
    from prems(4) obtain P where TyP: "Ty = tsubst \<rho> Ts \<rightarrow>\<^sub>T P"
      and tts: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : P" and cTs: "cert_typ alg ar (tsubst \<rho> Ts)"
      by (auto simp: pt)
    have pre: "ppat ts" "\<forall>T\<in>typs ts. wft ar T" "ptvs ts \<subseteq> A" "abs_bound (tbnd (fst env)) ts" "vars ts \<subseteq> X"
      using prems(1,7,8,11,12) ppat_AbsD[of ns Ts ts] by (simp_all add: pt)
    have lts: "\<not> loose_bvar ts (ilength ((a, B) # bs))" for a B using prems(6) by (simp add: pt)
    show ?thesis
    proof (cases "is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = Abs nt Tt tt" by (cases ob) auto
      from prems(5) obtain P' where TyP': "Ty = Tt \<rightarrow>\<^sub>T P'" and ttt: "e\<langle>0:Tt\<rangle> \<turnstile> tt : P'"
        and cTt: "cert_typ alg ar Tt" by (auto simp: ob)
      have eq: "Tt = tsubst \<rho> Ts" "P' = P" using TyP TyP' by simp_all
      have "ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> tt"
        using conv_Abs_inv(2)[of e ns "tsubst \<rho> Ts" "ap \<rho> \<sigma> ts" Ty nt Tt tt] tap prems(5,16)
        by (simp add: pt ob)
      moreover have "bs_env TVar (e\<langle>0:Tt\<rangle>) ((nt, Tt) # bs)" by (rule bs_env_TVar_Cons[OF prems(3) cTt])
      moreover have "e\<langle>0:Tt\<rangle> \<turnstile> inst \<rho> ts : P'" using tts eq by simp
      moreover have "no_redex tt" using prems(2) by (simp add: ob)
      moreover have "nabs ts + nabs tt < nabs pt + nabs ob \<or>
          nabs ts + nabs tt \<le> nabs pt + nabs ob \<and> size ts + size tt < size pt + size ob"
        by (simp add: pt ob)
      ultimately obtain env' where r: "ok (mtch alg ((nt, Tt) # bs) ts tt env) env'"
        "tagrees (fst env') \<rho> A" "textends (fst env) (fst env')" "magree \<rho> \<sigma> (snd env') X"
        using IH[OF _ pre(1) _ _ _ ttt lts pre(2,3) prems(10) pre(4,5) prems(14)] by blast
      have "mtch alg bs pt ob env = mtch alg ((nt, Tt) # bs) ts tt env"
        by (subst mtch.simps) (simp add: e pt ob)
      with r show ?thesis by auto
    next
      case oA: False
      have tvT: "tvars Ts \<subseteq> tbnd iTs" "tvars Ts \<subseteq> A" using prems(8,11) by (simp_all add: pt e)
      have st: "ok (subst_type iTs Ts) (tsubst \<rho> Ts)"
        by (rule subst_type_agree[OF tvT(1) prems(10)[unfolded e fst_conv] tvT(2)])
      have il: "incr ob = lift ob 0" by (simp add: incr_def incr_aux_lift)
      have "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> lift ob 0 : tsubst \<rho> Ts \<rightarrow>\<^sub>T P"
        by (rule lift_type[OF prems(5)[unfolded TyP]]) simp
      then have tob: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> incr ob $ Bound 0 : P"
        unfolding il by (rule typing.App) auto
      have nob: "no_redex (incr ob $ Bound 0)" using prems(2) oA by (simp add: il no_redex_lift) (cases ob; simp)
      have c: "ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> incr ob $ Bound 0"
      proof -
        have ta: "e \<turnstile> Abs ns (tsubst \<rho> Ts) (ap \<rho> \<sigma> ts) : tsubst \<rho> Ts \<rightarrow>\<^sub>T P" using tap by (simp add: pt TyP)
        have "ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (Abs ns (tsubst \<rho> Ts) (ap \<rho> \<sigma> ts)) 0 $ Bound 0"
          by (rule conv_Abs_body[OF ta])
        also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift ob 0 $ Bound 0"
        proof (rule conv_App[OF _ _ conv_lift[OF _ order_refl] conv_refl])
          have "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> lift (Abs ns (tsubst \<rho> Ts) (ap \<rho> \<sigma> ts)) 0 : tsubst \<rho> Ts \<rightarrow>\<^sub>T P"
            by (rule lift_type[OF ta]) simp
          then have "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> lift (Abs ns (tsubst \<rho> Ts) (ap \<rho> \<sigma> ts)) 0 $ Bound 0 : P"
            by (rule typing.App) auto
          then show "wt (lift (Abs ns (tsubst \<rho> Ts) (ap \<rho> \<sigma> ts)) 0 $ Bound 0)"
            unfolding wt_def by blast
          show "wt (lift ob 0 $ Bound 0)" using tob unfolding wt_def il by blast
          show "Abs ns (tsubst \<rho> Ts) (ap \<rho> \<sigma> ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" using prems(16) by (simp add: pt)
        qed
        finally show ?thesis by (simp add: il)
      qed
      have "bs_env TVar (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((ns, tsubst \<rho> Ts) # bs)" by (rule bs_env_TVar_Cons[OF prems(3) cTs])
      moreover have "nabs ts + nabs (incr ob $ Bound 0) < nabs pt + nabs ob \<or>
          nabs ts + nabs (incr ob $ Bound 0) \<le> nabs pt + nabs ob \<and>
          size ts + size (incr ob $ Bound 0) < size pt + size ob"
        by (simp add: pt nabs_incr)
      ultimately obtain env' where r: "ok (mtch alg ((ns, tsubst \<rho> Ts) # bs) ts (incr ob $ Bound 0) env) env'"
        "tagrees (fst env') \<rho> A" "textends (fst env) (fst env') \<and> magree \<rho> \<sigma> (snd env') X"
        using IH[OF _ pre(1) nob _ tts tob lts pre(2,3) prems(10) pre(4,5) prems(14) c] by blast
      have "mtch alg bs pt ob env = mtch alg ((ns, tsubst \<rho> Ts) # bs) ts (incr ob $ Bound 0) env"
        by (subst mtch.simps) (simp add: e pt oA st)
      with r show ?thesis by auto
    qed
  next
    case pA: False
    show ?thesis
    proof (cases "is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = Abs nt Tt tt" by (cases ob) auto
      from prems(5) obtain P' where TyP': "Ty = Tt \<rightarrow>\<^sub>T P'" and ttt: "e\<langle>0:Tt\<rangle> \<turnstile> tt : P'"
        and cTt: "cert_typ alg ar Tt" by (auto simp: ob)
      have il: "incr t = lift t 0" for t by (simp add: incr_def incr_aux_lift)
      have "e\<langle>0:Tt\<rangle> \<turnstile> lift (inst \<rho> pt) 0 : Tt \<rightarrow>\<^sub>T P'"
        by (rule lift_type[OF prems(4)[unfolded TyP']]) simp
      then have "e\<langle>0:Tt\<rangle> \<turnstile> lift (inst \<rho> pt) 0 $ Bound 0 : P'" by (rule typing.App) auto
      then have tp: "e\<langle>0:Tt\<rangle> \<turnstile> inst \<rho> (incr pt $ Bound 0) : P'" by (simp add: il)
      have c: "ap \<rho> \<sigma> (incr pt $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> tt"
      proof -
        have "ap \<rho> \<sigma> (incr pt $ Bound 0) = lift (ap \<rho> \<sigma> pt) 0 $ Bound 0"
          using prems(15) by (simp add: il ap_lift)
        also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift ob 0 $ Bound 0"
        proof (rule conv_App[OF _ _ conv_lift[OF prems(16) order_refl] conv_refl])
          show "wt (lift (ap \<rho> \<sigma> pt) 0 $ Bound 0)"
            using typing_ap[OF tp prems(15)] prems(15) unfolding wt_def by (auto simp: il ap_lift)
          have "e\<langle>0:Tt\<rangle> \<turnstile> lift ob 0 : Tt \<rightarrow>\<^sub>T P'" by (rule lift_type[OF prems(5)[unfolded TyP']]) simp
          then have "e\<langle>0:Tt\<rangle> \<turnstile> lift ob 0 $ Bound 0 : P'" by (rule typing.App) auto
          then show "wt (lift ob 0 $ Bound 0)" unfolding wt_def by blast
        qed
        also have "lift ob 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> tt"
          using conv_Abs_body[of e nt Tt tt P'] prems(5) TyP' by (simp add: ob conv_sym)
        finally show ?thesis .
      qed
      have pre: "ppat (incr pt $ Bound 0)" "\<forall>T\<in>typs (incr pt $ Bound 0). wft ar T"
        "ptvs (incr pt $ Bound 0) \<subseteq> A" "abs_bound (tbnd (fst env)) (incr pt $ Bound 0)"
        "vars (incr pt $ Bound 0) \<subseteq> X" "no_redex tt"
        using prems(1,2,7,8,11,12) ppat_incr_Bound0[OF prems(1) pA] abs_bound_incr_Bound0[OF pA prems(11)]
        by (simp_all add: ob typs_incr vars_incr)
      have lp: "\<not> loose_bvar (incr pt $ Bound 0) (ilength ((nt, Tt) # bs))"
        using prems(6) loose_bvar_lift[of 0 "ilength bs" pt] ilength_nonneg[of bs]
        by (simp add: il integer_arith)
      have "bs_env TVar (e\<langle>0:Tt\<rangle>) ((nt, Tt) # bs)" by (rule bs_env_TVar_Cons[OF prems(3) cTt])
      moreover have "nabs (incr pt $ Bound 0) + nabs tt < nabs pt + nabs ob \<or>
          nabs (incr pt $ Bound 0) + nabs tt \<le> nabs pt + nabs ob \<and>
          size (incr pt $ Bound 0) + size tt < size pt + size ob"
        by (simp add: ob nabs_incr)
      ultimately obtain env' where r: "ok (mtch alg ((nt, Tt) # bs) (incr pt $ Bound 0) tt env) env'"
        "tagrees (fst env') \<rho> A" "textends (fst env) (fst env') \<and> magree \<rho> \<sigma> (snd env') X"
        using IH[OF _ pre(1) pre(6) _ tp ttt lp pre(2,3) prems(10) pre(4,5) prems(14) c] by blast
      have "mtch alg bs pt ob env = mtch alg ((nt, Tt) # bs) (incr pt $ Bound 0) tt env"
        by (subst mtch.simps) (simp add: e pA ob)
      with r show ?thesis by auto
    next
      case oA: False
      obtain ph pargs where sp: "strip_comb pt = (ph, pargs)" by force
      have ptc: "pt = ph \<degree>\<degree> pargs" by (rule mt_strip_comb_apps[OF sp])
      obtain oh oargs where so: "strip_comb ob = (oh, oargs)" by force
      have obc: "ob = oh \<degree>\<degree> oargs" by (rule mt_strip_comb_apps[OF so])
      note ns = no_redex_strip[OF prems(2) oA so]
      have mt: "mtch alg bs pt ob env = (if is_Var ph then
          (case ph of
            Var ixn T \<Rightarrow> do {
              is \<leftarrow> ints_of pargs;
              r \<leftarrow> lookup1 itms ixn T;
              case r of
                None \<Rightarrow> do {itms' \<leftarrow> match_bind itms bs ixn T is ob; return (iTs, itms')}
              | Some u \<Rightarrow> do {u' \<leftarrow> red u is []; if aeconv ob u' then return env else raise Match}}
          | _ \<Rightarrow> raise (Failure (STR ''mtch'')))
        else
          (case (ph, oh) of
            (Const a Ta, Const b Tb) \<Rightarrow>
              if a \<noteq> b then raise Match
              else do {iTs' \<leftarrow> typ_match_m alg Ta Tb iTs;
                handle
                  (do {ps \<leftarrow> zip_eq pargs oargs;
                       foldM (\<lambda>(p, q) e. mtch alg bs p q e) ps (iTs', itms)})
                  (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)}
          | (Free a Ta, Free b Tb) \<Rightarrow>
              if a \<noteq> b then raise Match
              else do {iTs' \<leftarrow> typ_match_m alg Ta Tb iTs;
                handle
                  (do {ps \<leftarrow> zip_eq pargs oargs;
                       foldM (\<lambda>(p, q) e. mtch alg bs p q e) ps (iTs', itms)})
                  (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)}
          | (Bound i, Bound j) \<Rightarrow> if i \<noteq> j then raise Match else
                handle
                  (do {ps \<leftarrow> zip_eq pargs oargs;
                       foldM (\<lambda>(p, q) e. mtch alg bs p q e) ps (iTs, itms)})
                  (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)
          | (Abs _ _ _, _) \<Rightarrow> raise Pattern
          | (_, Abs _ _ _) \<Rightarrow> raise Pattern
          | _ \<Rightarrow> raise Match))"
        by (subst mtch.simps) (simp add: e pA oA sp so Let_def)
      from ppat_strip[OF prems(1) pA sp] show ?thesis
      proof (elim disjE exE conjE)
        fix F T "is" assume ph: "ph = Var F T" and pargs: "pargs = map Bound is" and dis: "distinct is"
        have ptv: "pt = Var F T \<degree>\<degree> map Bound is" by (simp add: ptc ph pargs)
        have FX: "(F, T) \<in> X" using prems(12) by (auto simp: ptv vars_apps)
        from prems(4) have "e \<turnstile> Var F (tsubst \<rho> T) \<degree>\<degree> map Bound is : Ty"
          by (simp add: ptv inst_apps o_def)
        then obtain Ts where a1: "e \<turnstile> Var F (tsubst \<rho> T) : Ts \<Rrightarrow> Ty" and a2: "e \<tturnstile> map Bound is : Ts"
          by (rule list_app_typeE)
        from a1 have tT: "tsubst \<rho> T = Ts \<Rrightarrow> Ty" by (rule typing_elims(4)) (erule sym)
        from a1 have cT: "cert_typ alg ar (tsubst \<rho> T)" by (rule typing_elims(4)) simp
        from typings_BoundsD[OF a2] have Ts: "Ts = map e is" and is0: "\<forall>i\<in>set is. 0 \<le> i" by simp_all
        have isl: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
          using prems(6) is0 by (auto simp: ptv loose_bvar_apps)
        have apt: "ap \<rho> \<sigma> pt = \<sigma> F (tsubst \<rho> T) \<degree>\<degree> map Bound is" by (simp add: ptv ap_apps o_def)
        have cs: "closed (\<sigma> F (tsubst \<rho> T))" using prems(15) by (simp add: wt_subst_def closed_substD)
        have tsF: "e' \<turnstile> \<sigma> F (tsubst \<rho> T) : map e is \<Rrightarrow> Ty" for e'
          using wt_subst_typing[OF prems(15) cT] by (simp add: tT Ts)
        obtain N where N: "ob \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" using normal_form_ex[OF prems(5)] by blast
        have wob: "wt ob" using prems(5) by (auto simp: wt_def)
        have cN: "ob \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" by (rule beta_eta_conv[OF N(1) wob])
        have ints: "ints_of pargs = Some (Ok is)" using dis by (simp add: pargs ok_ints_of)
        show ?thesis
        proof (cases "vt_lookup itms F")
          case None
          then have lk: "lookup1 itms F T = Some (Ok None)" by (simp add: lookup1_def return_def)
          have lb: "k \<in> set is" if "0 \<le> k" "loose_bvar1 ob k" for k
          proof -
            have "nf_bounds ob 0 is" by (rule nf_bounds_flex[OF cs _ prems(16)[unfolded apt]])
              (rule typing_apps_Bounds[OF cs tsF is0])
            moreover have "loose_bvar1 N k" using no_redex_reds_loose[OF N(1) prems(2) that(1)] that(2) by simp
            ultimately show ?thesis using nf_boundsD[OF _ N(2) cN] that(1) by fastforce
          qed
          obtain itms' where mb: "ok (match_bind itms bs F T is ob) itms'"
            using match_bind_ok[OF lb isl None] by blast
          note b = ok_match_bind[OF mb dis]
          let ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 ob)"
          note mbd = match_binding[OF prems(3,5) b(3) b(4)]
          have bs'': "map snd (map (\<lambda>i. bs ! nat_of_integer i) is) = map e is"
            using bs_types(1)[OF prems(3) isl] by (simp add: case_prod_unfold)
          have ce: "\<forall>i\<in>set is. cert_typ alg ar (e i)" using isl bs_env_cert[OF prems(3)] by blast
          have "?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 N)"
            by (rule body_rename[OF mbd(1) mbd(2) dis is0 bs'' ce conv_trans[OF mbd(3) cN] N(2)])
          moreover have "\<sigma> F (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 N)"
            by (rule body_rename[OF cs tsF dis is0 bs'' ce _ N(2)])
              (use prems(16) cN in \<open>simp add: apt conv_trans\<close>)
          ultimately have uc: "?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F (tsubst \<rho> T)" by (blast intro: conv_sym conv_trans)
          have nu: "no_redex ?u" using prems(2) by (simp add: no_redex_abs_list)
          have "magree \<rho> \<sigma> itms' X"
            unfolding magree_def
          proof (intro allI impI)
            fix x T' U u assume xT: "(x, T') \<in> X" and l: "vt_lookup itms' x = Some (U, u)"
            show "U = T' \<and> closed u \<and> no_redex u \<and> (\<forall>e. e \<turnstile> u : tsubst \<rho> T') \<and> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> x (tsubst \<rho> T')"
            proof (cases "x = F")
              case True
              with prems(13) xT FX have "T' = T" unfolding vfun_def by blast
              with True l b(2) mbd(1) mbd(2) uc nu tT Ts show ?thesis by auto
            next
              case False
              with l b(2) have "vt_lookup itms x = Some (U, u)" by simp
              with magreeD[OF prems(14)[unfolded e snd_conv] xT] show ?thesis by blast
            qed
          qed
          moreover have "ok (mtch alg bs pt ob env) (iTs, itms')"
            using mt ph ints lk mb by (simp add: return_def)
          ultimately show ?thesis using prems(10) by (auto simp: e textends_refl_m)
        next
          case (Some b)
          then obtain U u where bu: "vt_lookup itms F = Some (U, u)" by (cases b) auto
          note mg = magreeD[OF prems(14)[unfolded e snd_conv] FX bu]
          then have lk: "lookup1 itms F T = Some (Ok (Some u))" using bu by (simp add: lookup1_def return_def)
          obtain u' where rd: "ok (red u is []) u'" using red_ok[of u "[]" "is"] mg by (auto simp: closed_def)
          have tu: "e \<turnstile> u : map e is \<Rrightarrow> Ty" using mg tT Ts by simp
          have ta: "e \<turnstile> u \<degree>\<degree> map Bound is : Ty" by (rule typing_apps_Bounds[OF _ tu is0]) (use mg in simp)
          have bb: "u \<degree>\<degree> map Bound is \<rightarrow>\<^sub>\<beta>\<^sup>* u'" using red_beta[OF rd] is0 by (simp add: rename_bren_Nil)
          have "u' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u \<degree>\<degree> map Bound is"
            using beta_eta_conv[OF beta_reds_beta_eta_reds[OF bb] wt_closedI[OF ta]] by (rule conv_sym)
          also have "u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F (tsubst \<rho> T) \<degree>\<degree> map Bound is"
          proof (rule conv_apps[OF _ wt_closedI[OF ta]])
            show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map Bound is) (map Bound is)" by (simp add: list_all2_refl)
            show "wt (\<sigma> F (tsubst \<rho> T) \<degree>\<degree> map Bound is)" using tap by (auto simp: apt wt_def)
            show "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> F (tsubst \<rho> T)" using mg by blast
          qed
          also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" using prems(16) by (simp add: apt)
          finally have cu: "u' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" .
          have tu': "e \<turnstile> u' : Ty" by (rule subject_reduction_reds[OF beta_reds_beta_eta_reds[OF bb] ta])
          have "aeconv ob u'"
            by (rule aeconv_complete[OF prems(2) red_no_redex[OF rd] wob conv_sym[OF cu]]) (use mg in simp)
          then have "ok (mtch alg bs pt ob env) env" using mt ph ints lk rd by (simp add: return_def)
          then show ?thesis using prems(10,14) by (auto simp: e textends_refl_m)
        qed
      next
        assume rh: "rigid ph" and pa: "\<forall>u\<in>set pargs. ppat u"
        have nV: "\<not> is_Var ph" using rh by (cases ph) auto
        have hap: "ap \<rho> \<sigma> ph = inst \<rho> ph" using rh by (cases ph) simp_all
        have apt: "ap \<rho> \<sigma> pt = inst \<rho> ph \<degree>\<degree> map (ap \<rho> \<sigma>) pargs" by (simp add: ptc ap_apps hap)
        have ai: "atom (inst \<rho> ph)" using rh by (cases ph) simp_all
        have wap: "wt (inst \<rho> ph \<degree>\<degree> map (ap \<rho> \<sigma>) pargs)" using tap by (auto simp: apt wt_def)
        note inv = conv_atom_apps_inv[OF ai ns(1) wap prems(16)[unfolded apt obc]]
        have hd: "inst \<rho> ph = oh" by (rule inv(1))
        have len: "length pargs = length oargs" using list_all2_lengthD[OF inv(2)] by simp
        have cargs: "list_all2 (\<lambda>p q. ap \<rho> \<sigma> p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> q) pargs oargs" using inv(2) by (simp add: list_all2_map1)
        have targs: "list_all2 (\<lambda>p q. \<exists>T. e \<turnstile> inst \<rho> p : T \<and> e \<turnstile> q : T) pargs oargs"
          by (rule rigid_args_typing[OF prems(4)[unfolded ptc] prems(5)[unfolded obc] hd len])
        have pargs_pre: "\<forall>p\<in>set pargs. ppat p \<and> \<not> loose_bvar p (ilength bs) \<and> (\<forall>T\<in>typs p. wft ar T) \<and>
            ptvs p \<subseteq> A \<and> vars p \<subseteq> X"
          using pa prems(6,7,8,12) by (auto simp: ptc loose_bvar_apps typs_apps_m ptvs_apps vars_apps)
        have oargs_nr: "\<forall>q\<in>set oargs. no_redex q" by (rule ns(2))
        text \<open>The arguments are matched from left to right:\<close>
        have args: "\<exists>env'. ok (foldM (\<lambda>(p, q) e. mtch alg bs p q e) (zip ps qs) e0) env' \<and>
            tagrees (fst env') \<rho> A \<and> textends (fst e0) (fst env') \<and> magree \<rho> \<sigma> (snd env') X"
          if "length ps = length qs" "set ps \<subseteq> set pargs" "set qs \<subseteq> set oargs"
            "list_all2 (\<lambda>p q. \<exists>T. e \<turnstile> inst \<rho> p : T \<and> e \<turnstile> q : T) ps qs"
            "list_all2 (\<lambda>p q. ap \<rho> \<sigma> p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> q) ps qs"
            "tagrees (fst e0) \<rho> A" "\<forall>p\<in>set ps. abs_bound (tbnd (fst e0)) p" "magree \<rho> \<sigma> (snd e0) X"
          for ps qs e0
          using that
        proof (induction ps qs arbitrary: e0 rule: list_induct2)
          case Nil
          then show ?case by (auto simp: return_def textends_refl_m)
        next
          case (Cons p ps q qs)
          have pq: "p \<in> set pargs" "q \<in> set oargs" using Cons.prems(1,2) by auto
          obtain T' where tp: "e \<turnstile> inst \<rho> p : T'" and tq: "e \<turnstile> q : T'" using Cons.prems(3) by auto
          have m: "nabs p + nabs q \<le> nabs pt + nabs ob" "size p + size q < size pt + size ob"
            using strip_comb_arg[OF sp pq(1)] strip_comb_arg[OF so pq(2)] by simp_all
          have m': "nabs p + nabs q < nabs pt + nabs ob \<or>
              nabs p + nabs q \<le> nabs pt + nabs ob \<and> size p + size q < size pt + size ob"
            using m by simp
          have pp: "ppat p" "\<not> loose_bvar p (ilength bs)" "\<forall>T\<in>typs p. wft ar T" "ptvs p \<subseteq> A" "vars p \<subseteq> X"
            using pargs_pre pq(1) by blast+
          have qq: "no_redex q" using oargs_nr pq(2) by blast
          have cpq: "ap \<rho> \<sigma> p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> q" using Cons.prems(4) by simp
          have abp: "abs_bound (tbnd (fst e0)) p" using Cons.prems(6) by simp
          obtain e1 where r1: "ok (mtch alg bs p q e0) e1" "tagrees (fst e1) \<rho> A"
            "textends (fst e0) (fst e1)" "magree \<rho> \<sigma> (snd e1) X"
            using IH[OF m' pp(1) qq prems(3) tp tq pp(2,3,4) Cons.prems(5) abp pp(5) Cons.prems(7) cpq]
            by blast
          have "\<forall>p\<in>set ps. abs_bound (tbnd (fst e1)) p"
            using Cons.prems(6) tbnd_mono[OF r1(3)] abs_bound_mono by auto
          with Cons.IH[of e1] Cons.prems r1 obtain env' where
            r2: "ok (foldM (\<lambda>(p, q) e. mtch alg bs p q e) (zip ps qs) e1) env'" "tagrees (fst env') \<rho> A"
            "textends (fst e1) (fst env')" "magree \<rho> \<sigma> (snd env') X"
            by auto
          from r1 r2 show ?case by (auto intro: textends_trans)
        qed
        have zip: "zip_eq pargs oargs = Some (Ok (zip pargs oargs))" using len by (simp add: ok_zip_eq)
        show ?thesis
        proof (cases ph)
          case ph: (Const a Ta)
          have oh: "oh = Const a (tsubst \<rho> Ta)" using hd by (simp add: ph)
          have wTa: "wft ar Ta" using prems(7) by (simp add: ptc ph typs_apps_m)
          have cTb: "cert_typ alg ar (tsubst \<rho> Ta)"
            using typing_typs_cert[OF prems(5)] by (simp add: obc oh typs_apps_m)
          have tvTa: "tvars Ta \<subseteq> A" using prems(8) by (simp add: ptc ph ptvs_apps)
          have sc: "scons (tvars Ta)" using prems(9) tvTa unfolding scons_def by blast
          have "tmatcher alg iTs \<rho> Ta (tsubst \<rho> Ta)"
            using tagrees_mono[OF prems(10)[unfolded e fst_conv] tvTa] by (simp add: tmatcher_tagrees)
          from typ_match_complete_aux[OF wTa cert_wft[OF cTb] sc this] obtain iTs' where
            tm: "ok (typ_match alg Ta (tsubst \<rho> Ta) iTs) iTs'" and tc: "tmcomplete \<rho> Ta iTs iTs'"
            by (auto simp: return_def)
          have ag: "tagrees iTs' \<rho> A"
            by (rule tagrees_step[OF prems(10)[unfolded e fst_conv] prems(9) tvTa tc])
          have te: "textends iTs iTs'" using tc by (simp add: tmcomplete_def)
          have "tvars Ta \<subseteq> tbnd iTs'" using tc by (auto simp: tmcomplete_def tbnd_def)
          moreover have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs \<union> tvars Ta) p"
            using prems(11) abs_bound_apps[OF rh, of "tbnd iTs" pargs] by (simp add: ptc ph e)
          ultimately have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs') p"
            using tbnd_mono[OF te] abs_bound_mono[of "tbnd iTs \<union> tvars Ta" _ "tbnd iTs'"] by blast
          with args[OF len order.refl order.refl targs cargs, of "(iTs', itms)"] ag prems(14)
          obtain env' where r: "ok (foldM (\<lambda>(p, q) e. mtch alg bs p q e) (zip pargs oargs) (iTs', itms)) env'"
            "tagrees (fst env') \<rho> A" "textends iTs' (fst env')" "magree \<rho> \<sigma> (snd env') X"
            by (auto simp: e)
          have "ok (mtch alg bs pt ob env) env'"
            using mt ph oh nV typ_match_m_ok[OF tm] zip r(1) by simp
          with r te show ?thesis by (auto simp: e intro: textends_trans)
        next
          case ph: (Free a Ta)
          have oh: "oh = Free a (tsubst \<rho> Ta)" using hd by (simp add: ph)
          have wTa: "wft ar Ta" using prems(7) by (simp add: ptc ph typs_apps_m)
          have cTb: "cert_typ alg ar (tsubst \<rho> Ta)"
            using typing_typs_cert[OF prems(5)] by (simp add: obc oh typs_apps_m)
          have tvTa: "tvars Ta \<subseteq> A" using prems(8) by (simp add: ptc ph ptvs_apps)
          have sc: "scons (tvars Ta)" using prems(9) tvTa unfolding scons_def by blast
          have "tmatcher alg iTs \<rho> Ta (tsubst \<rho> Ta)"
            using tagrees_mono[OF prems(10)[unfolded e fst_conv] tvTa] by (simp add: tmatcher_tagrees)
          from typ_match_complete_aux[OF wTa cert_wft[OF cTb] sc this] obtain iTs' where
            tm: "ok (typ_match alg Ta (tsubst \<rho> Ta) iTs) iTs'" and tc: "tmcomplete \<rho> Ta iTs iTs'"
            by (auto simp: return_def)
          have ag: "tagrees iTs' \<rho> A"
            by (rule tagrees_step[OF prems(10)[unfolded e fst_conv] prems(9) tvTa tc])
          have te: "textends iTs iTs'" using tc by (simp add: tmcomplete_def)
          have "tvars Ta \<subseteq> tbnd iTs'" using tc by (auto simp: tmcomplete_def tbnd_def)
          moreover have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs \<union> tvars Ta) p"
            using prems(11) abs_bound_apps[OF rh, of "tbnd iTs" pargs] by (simp add: ptc ph e)
          ultimately have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs') p"
            using tbnd_mono[OF te] abs_bound_mono[of "tbnd iTs \<union> tvars Ta" _ "tbnd iTs'"] by blast
          with args[OF len order.refl order.refl targs cargs, of "(iTs', itms)"] ag prems(14)
          obtain env' where r: "ok (foldM (\<lambda>(p, q) e. mtch alg bs p q e) (zip pargs oargs) (iTs', itms)) env'"
            "tagrees (fst env') \<rho> A" "textends iTs' (fst env')" "magree \<rho> \<sigma> (snd env') X"
            by (auto simp: e)
          have "ok (mtch alg bs pt ob env) env'"
            using mt ph oh nV typ_match_m_ok[OF tm] zip r(1) by simp
          with r te show ?thesis by (auto simp: e intro: textends_trans)
        next
          case ph: (Bound i)
          have oh: "oh = Bound i" using hd by (simp add: ph)
          have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs) p"
            using prems(11) abs_bound_apps[OF rh] by (simp add: ptc ph e)
          with args[OF len order.refl order.refl targs cargs, of "(iTs, itms)"] prems(10,14)
          obtain env' where r: "ok (foldM (\<lambda>(p, q) e. mtch alg bs p q e) (zip pargs oargs) (iTs, itms)) env'"
            "tagrees (fst env') \<rho> A" "textends iTs (fst env')" "magree \<rho> \<sigma> (snd env') X"
            by (auto simp: e)
          have "ok (mtch alg bs pt ob env) env'"
            using mt ph oh nV zip r(1) by simp
          with r show ?thesis by (auto simp: e)
        qed (use rh in simp_all)
      qed
    qed
  qed
qed


subsection \<open>Completeness of matching\<close>

text \<open>
  If a type instantiation \<open>\<rho>\<close>, certified and agreeing with the type environment (well-sorted on
  its unbound type variables), and a well-typed substitution \<open>\<sigma>\<close> instantiate a closed, typed
  higher-order pattern to a term equivalent to a closed, typed, \<open>\<beta>\<close>-normal object of the
  instantiated type, then matching succeeds. The variables of the pattern have unique types and
  are not bound in the term environment; its type variables have unique sorts.
\<close>

theorem match_complete:
  assumes "closed pt" "closed ob" "e \<turnstile> pt : pT" "e \<turnstile> ob : oT"
    and "ppat pt" "no_redex ob"
    and "scons (ptvs pt)" "vfun (vars pt)"
    and "tagrees (fst env) \<rho> (ptvs pt)" "\<forall>(x, T)\<in>vars pt. vt_lookup (snd env) x = None"
    and "cert_inst \<rho>" "wt_subst \<sigma>" "tsubst \<rho> pT = oT" "ap \<rho> \<sigma> pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
  shows "\<exists>env'. match alg pt ob env = Some (Ok env')"
proof -
  have wpT: "wft ar pT" using typing_cert_closed[OF assms(3,1)] by (rule cert_wft)
  have woT: "wft ar oT" using typing_cert_closed[OF assms(4,2)] by (rule cert_wft)
  have wp: "\<forall>T\<in>typs pt. wft ar T" using typing_typs_cert[OF assms(3)] by (auto simp: cert_wft)
  have E: "{i. 0 \<le> i \<and> loose_bvar1 pt i} = {}" using assms(1) by (simp add: closed_iff_loose_bvar1)
  have "tvars pT \<subseteq> ptvs pt \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 pt i}. tvars (e i))"
    by (rule typing_tvars[OF assms(3)])
  then have tv: "tvars pT \<subseteq> ptvs pt" unfolding E by simp
  have sc: "scons (tvars pT)" using assms(7) tv unfolding scons_def by blast
  have "tmatcher alg (fst env) \<rho> pT oT"
    using assms(13) tagrees_mono[OF assms(9) tv] by (simp add: tmatcher_tagrees)
  from typ_match_complete_aux[OF wpT woT sc this] obtain iTs where
    tm: "ok (typ_match alg pT oT (fst env)) iTs" and tc: "tmcomplete \<rho> pT (fst env) iTs"
    by (auto simp: return_def)
  have ag: "tagrees iTs \<rho> (ptvs pt)" by (rule tagrees_step[OF assms(9,7) tv tc])
  have "tvars pT \<subseteq> tbnd iTs" using tc by (auto simp: tmcomplete_def tbnd_def)
  then have ab: "abs_bound (tbnd iTs) pt"
    using typing_abs_bound[OF assms(3)] assms(1) by (simp add: closed_iff_loose_bvar1)
  have "(\<lambda>j. tsubst \<rho> (e j)) \<turnstile> inst \<rho> pt : oT"
    using typing_inst[OF assms(3) cert_inst_inst_ok[OF assms(11)]] by (simp add: assms(13))
  then have tp: "e \<turnstile> inst \<rho> pt : oT" using assms(1) by (simp add: typing_closed closed_inst)
  have mg: "magree \<rho> \<sigma> (snd (iTs, snd env)) (vars pt)" using assms(10) by (simp add: magree_unbound)
  have lb: "\<not> loose_bvar pt (ilength [])" using assms(1) by (simp add: closed_def)
  obtain env' where m: "ok (mtch alg [] pt ob (iTs, snd env)) env'"
    using mtch_complete[OF assms(5,6) bs_env_Nil tp assms(4) lb wp order.refl assms(7) _ _ order.refl assms(8)
      mg assms(12,14)] ag ab by auto
  have "match alg pt ob env = typ_match_m alg pT oT (fst env) \<bind> (\<lambda>iTs.
      handle (mtch alg [] pt ob (iTs, snd env))
        (\<lambda>e. case e of Pattern \<Rightarrow> first_order_match alg pt ob (iTs, snd env) | _ \<Rightarrow> raise e))"
    by (simp add: match_def Let_def fastype_of_closed[OF assms(3,1)] fastype_of_closed[OF assms(4,2)]
      return_def)
  with typ_match_m_ok[OF tm] m show ?thesis by simp
qed


subsection \<open>First-order matching\<close>

text \<open>The bindings of the pattern variables are \<open>\<alpha>\<close>-equivalent to the values of \<open>\<sigma>\<close>:\<close>

definition fagree :: "tinst \<Rightarrow> vsubst \<Rightarrow> tenv \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "fagree \<rho> \<sigma> te X \<longleftrightarrow> (\<forall>x T U u. (x, T) \<in> X \<longrightarrow> vt_lookup te x = Some (U, u) \<longrightarrow>
    U = T \<and> aconv_term u (\<sigma> x (tsubst \<rho> T)))"

lemma aconv_term_trans: "aconv_term r s \<Longrightarrow> aconv_term s t \<Longrightarrow> aconv_term r t"
  by (simp add: aconv_term_unname)

lemma aconv_term_atom: "atom h \<Longrightarrow> aconv_term h t \<longleftrightarrow> h = t"
  by (cases h; cases t) simp_all

lemma fo_mtch_var_complete:
  assumes "pt = Var x T" "\<forall>T\<in>typs pt. cert_typ alg ar T" "e \<turnstile> ob : Ty" "ptvs pt \<subseteq> A" "scons A"
    "tagrees (fst env) \<rho> A" "vars pt \<subseteq> X" "vfun X" "fagree \<rho> \<sigma> (snd env) X"
    "cert_inst \<rho>" "wt_subst \<sigma>" "aconv_term (ap \<rho> \<sigma> pt) ob"
  shows "\<exists>env'. ok (fo_mtch alg inAbs env pt ob) env' \<and> tagrees (fst env') \<rho> A \<and>
    fagree \<rho> \<sigma> (snd env') X"
proof -
  obtain iTs itms where e: "env = (iTs, itms)" by force
  have ac: "aconv_term (\<sigma> x (tsubst \<rho> T)) ob" using assms(12) by (simp add: assms(1))
  have cs: "closed (\<sigma> x (tsubst \<rho> T))" using assms(11) by (simp add: wt_subst_def closed_substD)
  then have clo: "closed ob" using loose_bvar1_aconv[OF ac] by (simp add: closed_iff_loose_bvar1)
  have xX: "(x, T) \<in> X" using assms(7) by (simp add: assms(1))
  have h: "fo_mtch alg inAbs env pt ob = do {
            r \<leftarrow> lookup1 itms x T;
            case r of
              None \<Rightarrow> do {
                tT \<leftarrow> fastype_of ob;
                tyinsts' \<leftarrow> typ_match_m alg T tT iTs;
                insts' \<leftarrow> update_new (x, (T, ob)) itms;
                return (tyinsts', insts')}
            | Some u \<Rightarrow> if aeconv ob u then return env else raise Match}"
    using clo by (subst fo_mtch.simps) (simp add: e assms(1) is_open_closed)
  show ?thesis
  proof (cases "vt_lookup itms x")
    case None
    then have lk: "lookup1 itms x T = Some (Ok None)" by (simp add: lookup1_def return_def)
    have cT: "cert_typ alg ar (tsubst \<rho> T)"
      using cert_typ_tsubst[of T \<rho>] assms(2,10) by (simp add: assms(1))
    have "e \<turnstile> ob : tsubst \<rho> T" using typing_aconv[OF ac wt_subst_typing[OF assms(11) cT]] .
    then have Ty: "Ty = tsubst \<rho> T" using typing_unique[OF assms(3)] by blast
    have ft: "fastype_of ob = Some (Ok (tsubst \<rho> T))"
      using fastype_of_closed[OF assms(3) clo] Ty by (simp add: return_def)
    have wT: "wft ar T" using assms(2) by (simp add: assms(1) cert_wft)
    have tvT: "tvars T \<subseteq> A" using assms(4) by (simp add: assms(1))
    have sc: "scons (tvars T)" using assms(5) tvT unfolding scons_def by blast
    have "tmatcher alg iTs \<rho> T (tsubst \<rho> T)"
      using tagrees_mono[OF assms(6)[unfolded e fst_conv] tvT] by (simp add: tmatcher_tagrees)
    from typ_match_complete_aux[OF wT cert_wft[OF cT] sc this] obtain iTs' where
      tm: "ok (typ_match alg T (tsubst \<rho> T) iTs) iTs'" and tc: "tmcomplete \<rho> T iTs iTs'"
      by (auto simp: return_def)
    have ag: "tagrees iTs' \<rho> A" by (rule tagrees_step[OF assms(6)[unfolded e fst_conv] assms(5) tvT tc])
    have up: "update_new (x, (T, ob)) itms = Some (Ok (vt_update (x, (T, ob)) itms))"
      using None by (simp add: update_new_def vt_defined_lookup return_def)
    have "fagree \<rho> \<sigma> (vt_update (x, (T, ob)) itms) X"
      unfolding fagree_def
    proof (intro allI impI)
      fix y T' U u assume yT: "(y, T') \<in> X" and l: "vt_lookup (vt_update (x, (T, ob)) itms) y = Some (U, u)"
      show "U = T' \<and> aconv_term u (\<sigma> y (tsubst \<rho> T'))"
      proof (cases "y = x")
        case True
        with assms(8) yT xX have "T' = T" unfolding vfun_def by blast
        with True l ac show ?thesis by (auto simp: aconv_term_sym)
      next
        case False
        with l have "vt_lookup itms y = Some (U, u)" by simp
        with assms(9) yT show ?thesis unfolding e snd_conv fagree_def by blast
      qed
    qed
    moreover have "ok (fo_mtch alg inAbs env pt ob) (iTs', vt_update (x, (T, ob)) itms)"
      using h lk ft typ_match_m_ok[OF tm] up by (simp add: return_def)
    ultimately show ?thesis using ag by auto
  next
    case (Some b)
    then obtain U u where bu: "vt_lookup itms x = Some (U, u)" by (cases b) auto
    with assms(9) xX have UT: "U = T" and au: "aconv_term u (\<sigma> x (tsubst \<rho> T))"
      unfolding e snd_conv fagree_def by blast+
    have lk: "lookup1 itms x T = Some (Ok (Some u))" using bu UT by (simp add: lookup1_def return_def)
    have ae: "aeconv ob u"
      unfolding aeconv_def using aconv_term_trans[OF aconv_term_sym[OF ac] aconv_term_sym[OF au]] by blast
    have "ok (fo_mtch alg inAbs env pt ob) env" using h lk ae by (simp add: return_def)
    then show ?thesis using assms(6,9) by auto
  qed
qed

lemma fo_mtch_complete:
  assumes "\<forall>T\<in>typs pt. cert_typ alg ar T" "e \<turnstile> ob : Ty" "ptvs pt \<subseteq> A" "scons A"
    "tagrees (fst env) \<rho> A" "vars pt \<subseteq> X" "vfun X" "fagree \<rho> \<sigma> (snd env) X"
    "cert_inst \<rho>" "wt_subst \<sigma>" "aconv_term (ap \<rho> \<sigma> pt) ob"
  shows "\<exists>env'. ok (fo_mtch alg inAbs env pt ob) env' \<and> tagrees (fst env') \<rho> A \<and>
    fagree \<rho> \<sigma> (snd env') X"
  using assms
proof (induction ob arbitrary: inAbs env pt e Ty)
  case (Abs b U u)
  note prems = Abs.prems
  obtain iTs itms where e: "env = (iTs, itms)" by force
  show ?case
  proof (cases pt)
    case pt: (Abs a T t)
    from prems(11) have U: "U = tsubst \<rho> T" and ac: "aconv_term (ap \<rho> \<sigma> t) u" by (simp_all add: pt)
    from prems(2) obtain U' where tu: "e\<langle>0:U\<rangle> \<turnstile> u : U'" and cU: "cert_typ alg ar U" by auto
    have wT: "wft ar T" using prems(1) by (simp add: pt cert_wft)
    have tvT: "tvars T \<subseteq> A" using prems(3) by (simp add: pt)
    have sc: "scons (tvars T)" using prems(4) tvT unfolding scons_def by blast
    have "tmatcher alg iTs \<rho> T U"
      using tagrees_mono[OF prems(5)[unfolded e fst_conv] tvT] U by (simp add: tmatcher_tagrees)
    from typ_match_complete_aux[OF wT cert_wft[OF cU] sc this] obtain iTs' where
      tm: "ok (typ_match alg T U iTs) iTs'" and tc: "tmcomplete \<rho> T iTs iTs'"
      by (auto simp: return_def)
    have ag: "tagrees iTs' \<rho> A" by (rule tagrees_step[OF prems(5)[unfolded e fst_conv] prems(4) tvT tc])
    from Abs.IH[OF _ tu, of t "(iTs', itms)" True] prems ag ac obtain env' where
      r: "ok (fo_mtch alg True (iTs', itms) t u) env'" "tagrees (fst env') \<rho> A" "fagree \<rho> \<sigma> (snd env') X"
      by (auto simp: pt e)
    have "fo_mtch alg inAbs env pt (Abs b U u) = fo_mtch alg True (iTs', itms) t u"
      by (subst fo_mtch.simps) (simp add: e pt typ_match_m_ok[OF tm])
    with r show ?thesis by auto
  next
    case pt: (Var x T)
    show ?thesis by (rule fo_mtch_var_complete[OF pt prems])
  qed (use prems(11) in simp_all)
next
  case (App g u)
  note prems = App.prems
  obtain iTs itms where e: "env = (iTs, itms)" by force
  show ?case
  proof (cases pt)
    case pt: (App f t)
    from prems(11) have ac: "aconv_term (ap \<rho> \<sigma> f) g" "aconv_term (ap \<rho> \<sigma> t) u" by (simp_all add: pt)
    from prems(2) obtain A' where tg: "e \<turnstile> g : A' \<rightarrow>\<^sub>T Ty" and tu: "e \<turnstile> u : A'" by auto
    from App.IH(1)[OF _ tg, of f env inAbs] prems ac obtain env1 where
      r1: "ok (fo_mtch alg inAbs env f g) env1" "tagrees (fst env1) \<rho> A" "fagree \<rho> \<sigma> (snd env1) X"
      by (auto simp: pt)
    from App.IH(2)[OF _ tu, of t env1 inAbs] prems ac r1(2,3) obtain env2 where
      r2: "ok (fo_mtch alg inAbs env1 t u) env2" "tagrees (fst env2) \<rho> A" "fagree \<rho> \<sigma> (snd env2) X"
      by (auto simp: pt)
    have "fo_mtch alg inAbs env pt (g $ u) = fo_mtch alg inAbs env f g \<bind> (\<lambda>e'. fo_mtch alg inAbs e' t u)"
      by (subst fo_mtch.simps) (simp add: e pt)
    with r1 r2 show ?thesis by auto
  next
    case pt: (Var x T)
    show ?thesis by (rule fo_mtch_var_complete[OF pt prems])
  qed (use prems(11) in simp_all)
next
  case (Const c U)
  note prems = Const.prems
  obtain iTs itms where e: "env = (iTs, itms)" by force
  show ?case
  proof (cases pt)
    case pt: (Const a T)
    from prems(11) have ab: "a = c" and U: "U = tsubst \<rho> T" by (simp_all add: pt)
    from prems(2) have cU: "cert_typ alg ar U" by auto
    have wT: "wft ar T" using prems(1) by (simp add: pt cert_wft)
    have tvT: "tvars T \<subseteq> A" using prems(3) by (simp add: pt)
    have sc: "scons (tvars T)" using prems(4) tvT unfolding scons_def by blast
    have "tmatcher alg iTs \<rho> T U"
      using tagrees_mono[OF prems(5)[unfolded e fst_conv] tvT] U by (simp add: tmatcher_tagrees)
    from typ_match_complete_aux[OF wT cert_wft[OF cU] sc this] obtain iTs' where
      tm: "ok (typ_match alg T U iTs) iTs'" and tc: "tmcomplete \<rho> T iTs iTs'"
      by (auto simp: return_def)
    have ag: "tagrees iTs' \<rho> A" by (rule tagrees_step[OF prems(5)[unfolded e fst_conv] prems(4) tvT tc])
    have "ok (fo_mtch alg inAbs env pt (Const c U)) (iTs', itms)"
      by (subst fo_mtch.simps) (simp add: e pt ab typ_match_m_ok[OF tm] return_def)
    with ag prems(8) show ?thesis by (auto simp: e)
  next
    case pt: (Var x T)
    show ?thesis by (rule fo_mtch_var_complete[OF pt prems])
  qed (use prems(11) in simp_all)
next
  case (Free c U)
  note prems = Free.prems
  obtain iTs itms where e: "env = (iTs, itms)" by force
  show ?case
  proof (cases pt)
    case pt: (Free a T)
    from prems(11) have ab: "a = c" and U: "U = tsubst \<rho> T" by (simp_all add: pt)
    from prems(2) have cU: "cert_typ alg ar U" by auto
    have wT: "wft ar T" using prems(1) by (simp add: pt cert_wft)
    have tvT: "tvars T \<subseteq> A" using prems(3) by (simp add: pt)
    have sc: "scons (tvars T)" using prems(4) tvT unfolding scons_def by blast
    have "tmatcher alg iTs \<rho> T U"
      using tagrees_mono[OF prems(5)[unfolded e fst_conv] tvT] U by (simp add: tmatcher_tagrees)
    from typ_match_complete_aux[OF wT cert_wft[OF cU] sc this] obtain iTs' where
      tm: "ok (typ_match alg T U iTs) iTs'" and tc: "tmcomplete \<rho> T iTs iTs'"
      by (auto simp: return_def)
    have ag: "tagrees iTs' \<rho> A" by (rule tagrees_step[OF prems(5)[unfolded e fst_conv] prems(4) tvT tc])
    have "ok (fo_mtch alg inAbs env pt (Free c U)) (iTs', itms)"
      by (subst fo_mtch.simps) (simp add: e pt ab typ_match_m_ok[OF tm] return_def)
    with ag prems(8) show ?thesis by (auto simp: e)
  next
    case pt: (Var x T)
    show ?thesis by (rule fo_mtch_var_complete[OF pt prems])
  qed (use prems(11) in simp_all)
next
  case (Bound j)
  note prems = Bound.prems
  obtain iTs itms where e: "env = (iTs, itms)" by force
  show ?case
  proof (cases pt)
    case pt: (Bound i)
    from prems(11) have ij: "i = j" by (simp add: pt)
    have "ok (fo_mtch alg inAbs env pt (Bound j)) env"
      by (subst fo_mtch.simps) (simp add: e pt ij return_def)
    with prems(5,8) show ?thesis by auto
  next
    case pt: (Var x T)
    show ?thesis by (rule fo_mtch_var_complete[OF pt prems])
  qed (use prems(11) in simp_all)
next
  case (Var y U)
  note prems = Var.prems
  show ?case
  proof (cases pt)
    case pt: (Var x T)
    show ?thesis by (rule fo_mtch_var_complete[OF pt prems])
  qed (use prems(11) in simp_all)
qed

text \<open>
  Completeness of first-order matching: if \<open>(\<rho>, \<sigma>)\<close> instantiates a pattern with certified types
  to a term \<open>\<alpha>\<close>-equivalent to a typed object, with \<open>\<rho>\<close> certified and agreeing with the type
  environment, then first-order matching succeeds.
\<close>

theorem first_order_match_complete:
  assumes "\<forall>T\<in>typs pt. cert_typ alg ar T" "e \<turnstile> ob : oT"
    and "scons (ptvs pt)" "vfun (vars pt)"
    and "tagrees (fst env) \<rho> (ptvs pt)" "\<forall>(x, T)\<in>vars pt. vt_lookup (snd env) x = None"
    and "cert_inst \<rho>" "wt_subst \<sigma>" "aconv_term (ap \<rho> \<sigma> pt) ob"
  shows "\<exists>env'. first_order_match alg pt ob env = Some (Ok env')"
proof -
  have "fagree \<rho> \<sigma> (snd env) (vars pt)" using assms(6) unfolding fagree_def by fastforce
  from fo_mtch_complete[OF assms(1,2) order.refl assms(3,5) order.refl assms(4) this assms(7-9), where inAbs = False]
  show ?thesis by (auto simp: first_order_match_def)
qed

end

end
