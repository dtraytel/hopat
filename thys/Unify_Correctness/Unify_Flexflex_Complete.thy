section \<open>Completeness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex_Complete
  imports Unify_Flexflex_Term Unify_Simpl_Complete
begin

context pure_sig
begin

subsection \<open>Loose bound variables of normal forms\<close>

lemma ffc_lift_rename: "lift t d = rename (\<lambda>k. k + 1) d t"
  by (induction t arbitrary: d) (auto simp: algebra_simps)

lemma ffc_nonneg_Suc: "nonneg (\<lambda>k. k + 1)"
  by (simp add: nonneg_def)

lemma ffc_reds_lift: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> lift s 0 \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* lift t 0"
  unfolding ffc_lift_rename by (rule reds_rename[OF _ ffc_nonneg_Suc order_refl])

lemma ffc_normal_lift: "normal (lift t 0) \<longleftrightarrow> normal t"
  unfolding ffc_lift_rename by (rule normal_rename[OF ffc_nonneg_Suc order_refl])

lemma ffc_conv_nf_loose:
  assumes "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" "wt s" "normal N" "0 \<le> k" "loose_bvar1 N k"
  shows "loose_bvar1 s k"
proof -
  obtain u v where uv: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" "N \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* v" "aconv_term u v"
    using church_rosser[OF assms(2,1)] by blast
  have "v = N" by (rule normal_reds[OF uv(2) assms(3)])
  with uv(3) assms(5) have "loose_bvar1 u k" using loose_bvar1_aconv by blast
  then show ?thesis by (rule loose_bvar1_reds[OF uv(1) assms(4)])
qed

lemma ffc_nf_bounds_eta:
  assumes nb: "nf_bounds t d xs" and ty: "e \<turnstile> t : U \<rightarrow>\<^sub>T V" and d: "0 \<le> d"
  shows "nf_bounds (lift t 0 $ Bound 0) (d + 1) xs"
proof -
  obtain N where N: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" using normal_form_ex[OF ty] .
  have ty1: "e\<langle>0:U\<rangle> \<turnstile> lift t 0 $ Bound 0 : V" using ty by auto
  have r: "lift t 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* lift N 0 $ Bound 0"
    by (rule rtrancl_beta_eta_AppL[OF ffc_reds_lift[OF N(1)]])
  have tyM: "e\<langle>0:U\<rangle> \<turnstile> lift N 0 $ Bound 0 : V" by (rule subject_reduction_reds[OF r ty1])
  obtain M where M: "lift N 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* M" "normal M" using normal_form_ex[OF tyM] .
  have w: "wt (lift t 0 $ Bound 0)" using ty1 by (auto simp: wt_def)
  have cN: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using beta_eta_conv[OF N(1)] ty by (auto simp: wt_def)
  show ?thesis
  proof (rule nf_boundsI[OF w _ M(2)])
    show "lift t 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> M" using beta_eta_conv[OF rtranclp_trans[OF r M(1)] w] .
    fix k assume k: "d + 1 \<le> k" "loose_bvar1 M k"
    have "loose_bvar1 (lift N 0 $ Bound 0) k" by (rule loose_bvar1_reds[OF M(1) _ k(2)]) (use k d in simp)
    then have "loose_bvar1 N (k - 1)" using k d by (auto simp: integer_arith)
    from nf_boundsD[OF nb N(2) cN _ this] k have "k - 1 - d \<in> set xs" by (simp add: algebra_simps)
    then show "k - (d + 1) \<in> set xs" by (simp add: algebra_simps)
  qed
qed

lemma ffc_nf_bounds_unlift:
  assumes nb: "nf_bounds (lift s 0) (d + 1) xs" and ty: "e \<turnstile> s : T" and d: "0 \<le> d"
  shows "nf_bounds s d xs"
proof -
  obtain N where N: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" using normal_form_ex[OF ty] .
  have w: "wt s" using ty by (auto simp: wt_def)
  have wl: "wt (lift s 0)" using lift_type[OF ty, of 0 T] by (auto simp: wt_def)
  have cl: "lift s 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift N 0" by (rule beta_eta_conv[OF ffc_reds_lift[OF N(1)] wl])
  show ?thesis
  proof (rule nf_boundsI[OF w beta_eta_conv[OF N(1) w] N(2)])
    fix k assume k: "d \<le> k" "loose_bvar1 N k"
    have "loose_bvar1 (lift N 0) (k + 1)" using k d by simp
    from nf_boundsD[OF nb _ cl _ this] k d N(2) have "k + 1 - (d + 1) \<in> set xs"
      by (simp add: ffc_normal_lift)
    then show "k - d \<in> set xs" by simp
  qed
qed

lemma ffc_nf_bounds_appsI:
  assumes ty: "e \<turnstile> h \<degree>\<degree> ts : T" and h: "atom h" and nb: "\<forall>t\<in>set ts. nf_bounds t d xs"
    and hb: "\<And>i. h = Bound i \<Longrightarrow> d \<le> i \<Longrightarrow> i - d \<in> set xs" and d: "0 \<le> d"
  shows "nf_bounds (h \<degree>\<degree> ts) d xs"
proof -
  have w: "wt (h \<degree>\<degree> ts)" using ty by (auto simp: wt_def)
  then have wts: "\<forall>t\<in>set ts. wt t" using wt_apps_args by blast
  obtain Ns where Ns: "list_all2 (\<lambda>t N. t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N \<and> normal N) ts Ns"
    using normal_forms_list[OF wts] by blast
  let ?M = "h \<degree>\<degree> Ns"
  have r: "h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* ?M" by (rule reds_apps, rule list_all2_mono[OF Ns]) blast
  have "\<forall>N\<in>set Ns. normal N" using Ns by (auto simp: list_all2_conv_all_nth in_set_conv_nth)
  then have nr: "no_redex ?M" using h by (subst no_redex_apps) (auto simp: normal_iff elim: atom.elims)
  have tyM: "e \<turnstile> ?M : T" by (rule subject_reduction_reds[OF r ty])
  obtain M' where M': "?M \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* M'" "normal M'" using normal_form_ex[OF tyM] .
  show ?thesis
  proof (rule nf_boundsI[OF w _ M'(2)])
    show "h \<degree>\<degree> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> M'" using beta_eta_conv[OF rtranclp_trans[OF r M'(1)] w] .
    fix k assume k: "d \<le> k" "loose_bvar1 M' k"
    have k0: "0 \<le> k" using k(1) d by simp
    have "loose_bvar1 ?M k" using no_redex_reds_loose[OF M'(1) nr k0] k(2) by simp
    then consider "loose_bvar1 h k" | N where "N \<in> set Ns" "loose_bvar1 N k"
      by (auto simp: loose_bvar1_apps)
    then show "k - d \<in> set xs"
    proof cases
      case 1
      then have "h = Bound k" using h by (cases h) auto
      then show ?thesis using hb k(1) by blast
    next
      case 2
      then obtain j where j: "j < length Ns" "N = Ns ! j" by (auto simp: in_set_conv_nth)
      have lj: "j < length ts" using j(1) list_all2_lengthD[OF Ns] by simp
      have tj: "ts ! j \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" using list_all2_nthD[OF Ns lj] j(2) by simp_all
      have "ts ! j \<in> set ts" using lj by simp
      then have "nf_bounds (ts ! j) d xs" "wt (ts ! j)" using nb wts by blast+
      then show ?thesis using nf_boundsD[OF _ tj(2) beta_eta_conv[OF tj(1)] k(1) 2(2)] by blast
    qed
  qed
qed

lemma ffc_no_redex_apps_head: "no_redex (s \<degree>\<degree> ts) \<Longrightarrow> no_redex s"
proof (induction ts arbitrary: s)
  case (Cons a ts)
  from Cons.IH[of "s $ a"] Cons.prems have "no_redex (s $ a)" by simp
  then show ?case by simp
qed simp

lemma ffc_abs_list_ty_ok: "e \<turnstile> abs_list bs t : U \<Longrightarrow> \<forall>T\<in>snd ` set bs. cert_typ alg ar T"
proof (induction bs arbitrary: e U)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by force
  with Cons.prems obtain U' where "cert_typ alg ar T" "e\<langle>0:T\<rangle> \<turnstile> abs_list bs t : U'" by auto
  with Cons.IH b show ?case by auto
qed simp

lemma ffc_no_redex_apps: "no_redex (h \<degree>\<degree> ts) \<Longrightarrow> (ts \<noteq> [] \<longrightarrow> \<not> is_Abs h) \<and> (\<forall>t\<in>set ts. no_redex t)"
  by (induction ts rule: rev_induct) auto

text \<open>
  A rigid occurrence of a banned bound variable (\<^const>\<open>rigid_bound\<close>) in a \<open>\<beta>\<close>-normal term
  persists in the normal forms of every instance:
\<close>

lemma ffc_rigid_bound_nf:
  assumes "rigid_bound lev banned s" "e \<turnstile> ap \<rho> \<sigma> s : T" "0 \<le> lev" "\<forall>j\<in>set banned. 0 \<le> j"
    "nf_bounds (ap \<rho> \<sigma> s) lev xs" "no_redex s"
  shows "\<exists>j\<in>set banned. j \<in> set xs"
  using assms
proof (induction s arbitrary: lev e T rule: measure_induct_rule[of size])
  case (less s)
  obtain h args where sc: "strip_comb s = (h, args)" by (cases "strip_comb s")
  have s: "s = h \<degree>\<degree> args" by (rule strip_comb_apps[OF sc])
  have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF sc])
  have asz: "size a < size s" if "a \<in> set args" for a by (rule strip_comb_arg_size[OF sc that])
  have rb: "case h of Bound i \<Rightarrow> (i - lev) \<in> set banned \<or> (\<exists>a\<in>set args. rigid_bound lev banned a)
      | Var _ _ \<Rightarrow> False | Abs _ _ u \<Rightarrow> rigid_bound (lev + 1) banned u \<or> (\<exists>a\<in>set args. rigid_bound lev banned a)
      | _ \<Rightarrow> (\<exists>a\<in>set args. rigid_bound lev banned a)"
    using less.prems(1) by (subst (asm) rigid_bound.simps) (simp add: sc)
  have nr: "args \<noteq> [] \<longrightarrow> \<not> is_Abs h" "\<forall>a\<in>set args. no_redex a"
    using ffc_no_redex_apps[of h args] less.prems(6) s by simp_all
  have ty: "e \<turnstile> ap \<rho> \<sigma> h \<degree>\<degree> map (ap \<rho> \<sigma>) args : T" using less.prems(2) by (simp add: s ap_apps)
  have nb: "nf_bounds (ap \<rho> \<sigma> h \<degree>\<degree> map (ap \<rho> \<sigma>) args) lev xs" using less.prems(5) by (simp add: s ap_apps)
  have argc: "\<exists>j\<in>set banned. j \<in> set xs"
    if at: "atom (ap \<rho> \<sigma> h)" and a: "a \<in> set args" "rigid_bound lev banned a" for a
  proof -
    have nb_a: "nf_bounds (ap \<rho> \<sigma> a) lev xs" using nf_bounds_apps(1)[OF ty at nb less.prems(3)] a(1) by auto
    obtain Ta where ty_a: "e \<turnstile> ap \<rho> \<sigma> a : Ta" using typing_args[OF ty] a(1) by auto
    show ?thesis by (rule less.IH[OF asz[OF a(1)] a(2) ty_a less.prems(3,4) nb_a]) (use nr(2) a(1) in blast)
  qed
  show ?case
  proof (cases h)
    case (Const c U)
    with rb argc show ?thesis by auto
  next
    case (Free c U)
    with rb argc show ?thesis by auto
  next
    case (Var x U)
    with rb show ?thesis by simp
  next
    case (Bound i)
    from rb Bound consider "i - lev \<in> set banned" | a where "a \<in> set args" "rigid_bound lev banned a"
      by auto
    then show ?thesis
    proof cases
      case 1
      have "lev \<le> i" using 1 less.prems(4) by fastforce
      with nf_bounds_apps(2)[OF ty _ nb less.prems(3)] Bound have "i - lev \<in> set xs" by simp
      with 1 show ?thesis by blast
    next
      case 2
      with argc Bound show ?thesis by simp
    qed
  next
    case (Abs x U u)
    with nr(1) have nil: "args = []" by auto
    with rb Abs have ru: "rigid_bound (lev + 1) banned u" by simp
    have tyA: "e \<turnstile> Abs x (tsubst \<rho> U) (ap \<rho> \<sigma> u) : T" using ty Abs nil by simp
    then obtain V where tyu: "e\<langle>0:tsubst \<rho> U\<rangle> \<turnstile> ap \<rho> \<sigma> u : V" by blast
    have nbu: "nf_bounds (ap \<rho> \<sigma> u) (lev + 1) xs"
      using nf_bounds_Abs[OF tyA _ less.prems(3)] nb Abs nil by simp
    have "size u < size s" using s Abs nil by simp
    have "no_redex u" using less.prems(6) s Abs nil by simp
    from less.IH[OF \<open>size u < size s\<close> ru tyu _ less.prems(4) nbu this] less.prems(3) show ?thesis by simp
  next
    case (App f a)
    with nApp show ?thesis by simp
  qed
qed

subsection \<open>Arguments used by the value of a variable\<close>

lemma ffc_ssub_apps: "ssub (s \<degree>\<degree> ts) ss = ssub s ss \<degree>\<degree> map (\<lambda>t. ssub t ss) ts"
  by (induction ss arbitrary: s ts) (simp_all add: subst_apps comp_def)

lemma ffc_ssub_atom: "atom h \<Longrightarrow> \<not> is_Bound h \<Longrightarrow> ssub h ss = h"
proof (induction ss arbitrary: h)
  case (Cons s ss)
  have "h[incr_bv (ilength ss) 0 s/ilength ss] = h" using Cons.prems by (cases h) auto
  with Cons show ?case by simp
qed simp

text \<open>
  If the \<open>\<beta>\<close>-normal body \<open>B\<close> of an abstraction uses its bound variable \<open>j\<close>, and the arguments
  have atomic heads, then the loose bound variables of the normal forms of the argument for \<open>j\<close>
  are among those of the application: Huet's argument for the deletion of arguments.
\<close>

lemma ffc_use_arg:
  assumes "no_redex B" "\<not> loose_bvar B (ilength bs)" "length ss = length bs" "0 \<le> j" "loose_bvar1 B j"
    "e \<turnstile> abs_list bs B \<degree>\<degree> ss : T" "\<forall>s\<in>set ss. \<exists>h A. atom h \<and> s = h \<degree>\<degree> A"
    "nf_bounds (abs_list bs B \<degree>\<degree> ss) d xs" "0 \<le> d"
  shows "nf_bounds (rev ss ! nat_of_integer j) d xs"
  using assms
proof (induction B arbitrary: bs ss j e T d rule: measure_induct_rule[of size])
  case (less B)
  note nr = less.prems(1) and lb = less.prems(2) and len = less.prems(3) and j0 = less.prems(4)
    and jB = less.prems(5) and ty = less.prems(6) and at = less.prems(7) and nb = less.prems(8)
    and d = less.prems(9)
  have jl: "j < ilength bs" using loose_bvar1_less[OF lb jB] .
  have jn: "nat_of_integer j < length ss" using nat_of_integer_less_ilength[OF j0 jl] len by simp
  have jm: "rev ss ! nat_of_integer j \<in> set ss" using jn by (metis length_rev nth_mem set_rev)
  obtain Uj where tyj: "e \<turnstile> rev ss ! nat_of_integer j : Uj" using typing_args[OF ty jm] by blast
  have cl: "closed (abs_list bs B)" by (rule closed_abs_list[OF lb])
  from list_app_typeD[OF ty] obtain Ts where tyC: "e \<turnstile> abs_list bs B : Ts \<Rrightarrow> T"
    and tss: "e \<tturnstile> ss : Ts" by blast
  from typing_abs_list_inv[OF tyC] obtain V where TV: "Ts \<Rrightarrow> T = map snd bs \<Rrightarrow> V"
    and tyB: "pushes e (map snd bs) \<turnstile> B : V" by blast
  have lTs: "length Ts = length (map snd bs)" using typings_nth[OF tss] len by simp
  have Ts: "Ts = map snd bs" "T = V" using funs_eq[OF lTs] TV by simp_all
  have tyok: "\<forall>U\<in>snd ` set bs. cert_typ alg ar U" by (rule ffc_abs_list_ty_ok[OF tyC])
  show ?case
  proof (cases "is_Abs B")
    case True
    then obtain a U r where B: "B = Abs a U r" by (cases B) auto
    let ?bs = "bs @ [(a, U)]"
    let ?ss = "map (\<lambda>s. lift s 0) ss @ [Bound 0]"
    from tyB B obtain W where VW: "V = U \<rightarrow>\<^sub>T W" by blast
    have tyT: "e \<turnstile> abs_list bs B \<degree>\<degree> ss : U \<rightarrow>\<^sub>T W" using ty Ts VW by simp
    have l0: "lift (abs_list bs B) 0 = abs_list bs B" by (rule incr_bv_closed[OF cl order_refl])
    have e1: "lift (abs_list bs B \<degree>\<degree> ss) 0 $ Bound 0 = abs_list ?bs r \<degree>\<degree> ?ss"
      by (simp only: lift_map l0 app_last) (simp add: B)
    have nb': "nf_bounds (abs_list ?bs r \<degree>\<degree> ?ss) (d + 1) xs"
      using ffc_nf_bounds_eta[OF nb tyT d] by (simp only: e1)
    have "e\<langle>0:U\<rangle> \<turnstile> lift (abs_list bs B \<degree>\<degree> ss) 0 : U \<rightarrow>\<^sub>T W" by (rule lift_type[OF tyT order_refl])
    then have "e\<langle>0:U\<rangle> \<turnstile> lift (abs_list bs B \<degree>\<degree> ss) 0 $ Bound 0 : W" by (rule typing.App) auto
    then have ty': "e\<langle>0:U\<rangle> \<turnstile> abs_list ?bs r \<degree>\<degree> ?ss : W" by (simp only: e1)
    have at': "\<forall>s\<in>set ?ss. \<exists>h A. atom h \<and> s = h \<degree>\<degree> A"
    proof
      fix s assume "s \<in> set ?ss"
      then consider "s = Bound 0" | s0 where "s0 \<in> set ss" "s = lift s0 0" by auto
      then show "\<exists>h A. atom h \<and> s = h \<degree>\<degree> A"
      proof cases
        case 1
        then show ?thesis by (intro exI[of _ "Bound 0"] exI[of _ "[]"]) simp
      next
        case 2
        with at obtain h A where "atom h" "s0 = h \<degree>\<degree> A" by blast
        with 2 show ?thesis by (intro exI[of _ "lift h 0"] exI[of _ "map (\<lambda>t. lift t 0) A"]) simp
      qed
    qed
    have lbr: "\<not> loose_bvar r (ilength ?bs)" using lb by (simp add: B ilength_eq algebra_simps integer_of_nat_eq_of_nat)
    have "nf_bounds (rev ?ss ! nat_of_integer (j + 1)) (d + 1) xs"
      by (rule less.IH[of r ?bs ?ss "j + 1" "e\<langle>0:U\<rangle>" W "d + 1"])
        (use nr B lbr len j0 jB ty' at' nb' d in simp_all)
    moreover have "rev ?ss ! nat_of_integer (j + 1) = lift (rev ss ! nat_of_integer j) 0"
    proof -
      have "nat_of_integer (j + 1) = Suc (nat_of_integer j)" using j0 by (simp add: integer_arith nat_of_integer.rep_eq)
      then show ?thesis using jn by (simp add: rev_map)
    qed
    ultimately have "nf_bounds (lift (rev ss ! nat_of_integer j) 0) (d + 1) xs" by simp
    then show ?thesis by (rule ffc_nf_bounds_unlift[OF _ tyj d])
  next
    case False
    obtain h A where B: "B = h \<degree>\<degree> A" and hA: "atom h \<or> (\<exists>a U u. h = Abs a U u)"
      using ex_head_tail[of B] by blast
    have h: "atom h"
    proof (rule ccontr)
      assume "\<not> atom h"
      with hA obtain a U u where hu: "h = Abs a U u" by blast
      show False
      proof (cases A)
        case Nil
        with False B hu show False by simp
      next
        case (Cons b A')
        with nr B have "no_redex (h $ b \<degree>\<degree> A')" by simp
        then have "no_redex (h $ b)" by (rule ffc_no_redex_apps_head)
        with hu show False by simp
      qed
    qed
    have nAbs: "\<not> is_Abs h" using h by (cases h) auto
    have nrA: "\<forall>a\<in>set A. no_redex a" using nr B no_redex_apps[OF nAbs] by simp
    have red: "abs_list bs B \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta>\<^sup>* ssub B ss" by (rule beta_abs_list_ssub) (use len in simp)
    have w: "wt (abs_list bs B \<degree>\<degree> ss)" using ty by (auto simp: wt_def)
    have cS: "abs_list bs B \<degree>\<degree> ss \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ssub B ss" by (rule conv_beta_eta[OF w red])
    have tyS: "e \<turnstile> ssub B ss : T" by (rule subject_reduction_beta'[OF red ty])
    have nbS: "nf_bounds (ssub B ss) d xs" by (rule nf_bounds_conv[OF cS nb])
    have Sapps: "ssub B ss = ssub h ss \<degree>\<degree> map (\<lambda>a. ssub a ss) A" by (simp add: B ffc_ssub_apps)
    have IHa: "nf_bounds (rev ss ! nat_of_integer j) d xs"
      if a: "a \<in> set A" "loose_bvar1 a j" and nba: "nf_bounds (ssub a ss) d xs" for a
    proof -
      have sz: "size a < size B" using size_apps_arg[OF a(1)] B by simp
      have lba: "\<not> loose_bvar a (ilength bs)" using lb B a(1) by (auto simp: loose_bvar_apps)
      obtain Ua where "pushes e (map snd bs) \<turnstile> a : Ua"
        using typing_args[OF tyB[unfolded B] a(1)] by blast
      from typing_abs_list[OF this tyok] have "e \<turnstile> abs_list bs a : map snd bs \<Rrightarrow> Ua" .
      then have tya: "e \<turnstile> abs_list bs a \<degree>\<degree> ss : Ua" using tss Ts by (auto intro: list_app_typeI)
      have reda: "abs_list bs a \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta>\<^sup>* ssub a ss" by (rule beta_abs_list_ssub) (use len in simp)
      have "abs_list bs a \<degree>\<degree> ss \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ssub a ss" using tya by (intro conv_beta_eta[OF _ reda]) (auto simp: wt_def)
      then have nba': "nf_bounds (abs_list bs a \<degree>\<degree> ss) d xs" by (rule nf_bounds_conv[OF conv_sym nba])
      have "no_redex a" using nrA a(1) by blast
      from less.IH[OF sz this lba len j0 a(2) tya at nba' d] show ?thesis .
    qed
    show ?thesis
    proof (cases "is_Bound h")
      case True
      then obtain i where hi: "h = Bound i" by (cases h) auto
      from tyB B hi obtain Vh where "pushes e (map snd bs) \<turnstile> Bound i : Vh"
        using list_app_typeD by fastforce
      then have i0: "0 \<le> i" by blast
      have il: "i < ilength ss" using lb B hi len by (auto simp: loose_bvar_apps ilength_eq not_le)
      have hS: "ssub h ss = rev ss ! nat_of_integer i" by (simp add: hi ssub_Bound i0 il)
      have im: "rev ss ! nat_of_integer i \<in> set ss"
        using nat_of_integer_less_ilength[OF i0 il] by (metis length_rev nth_mem set_rev)
      obtain g G where g: "atom g" "rev ss ! nat_of_integer i = g \<degree>\<degree> G" using at im by blast
      have S: "ssub B ss = g \<degree>\<degree> (G @ map (\<lambda>a. ssub a ss) A)" using Sapps hS g by simp
      have tyS': "e \<turnstile> g \<degree>\<degree> (G @ map (\<lambda>a. ssub a ss) A) : T" using tyS S by simp
      have nbS': "nf_bounds (g \<degree>\<degree> (G @ map (\<lambda>a. ssub a ss) A)) d xs" using nbS S by simp
      note na = nf_bounds_apps[OF tyS' g(1) nbS' d]
      show ?thesis
      proof (cases "j = i")
        case True
        obtain Ui where tyi: "e \<turnstile> rev ss ! nat_of_integer i : Ui" using typing_args[OF ty im] by blast
        have "nf_bounds (g \<degree>\<degree> G) d xs"
        proof (rule ffc_nf_bounds_appsI[OF _ g(1) _ _ d])
          show "e \<turnstile> g \<degree>\<degree> G : Ui" using tyi g(2) by simp
          show "\<forall>t\<in>set G. nf_bounds t d xs" using na(1) by simp
          show "\<And>i'. g = Bound i' \<Longrightarrow> d \<le> i' \<Longrightarrow> i' - d \<in> set xs" using na(2) .
        qed
        then show ?thesis using True g(2) by simp
      next
        case False
        with jB B hi obtain a where a: "a \<in> set A" "loose_bvar1 a j" by (auto simp: loose_bvar1_apps)
        have "nf_bounds (ssub a ss) d xs" using na(1) a(1) by simp
        from IHa[OF a this] show ?thesis .
      qed
    next
      case False
      have hS: "ssub h ss = h" by (rule ffc_ssub_atom[OF h False])
      have tyS': "e \<turnstile> h \<degree>\<degree> map (\<lambda>a. ssub a ss) A : T" using tyS Sapps hS by simp
      have nbS': "nf_bounds (h \<degree>\<degree> map (\<lambda>a. ssub a ss) A) d xs" using nbS Sapps hS by simp
      note na = nf_bounds_apps[OF tyS' h nbS' d]
      have "\<not> loose_bvar1 h j" using h False by (cases h) auto
      with jB B obtain a where a: "a \<in> set A" "loose_bvar1 a j" by (auto simp: loose_bvar1_apps)
      from IHa[OF a] na(1) a(1) show ?thesis by simp
    qed
  qed
qed


subsection \<open>Solutions of updated environments\<close>

lemma ffc_solution_tenv:
  "tenv env' = tenv env \<Longrightarrow> tsol (tyenv env') \<rho> \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow> solution \<rho> \<sigma> env'"
  unfolding solution_def by simp

lemma ffc_solution_update:
  assumes upd: "ok (update (F, T) t env) env'" and sol: "solution \<rho> \<sigma> env"
    and eq: "\<sigma> F (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  shows "solution \<rho> \<sigma> env'"
  using solutionD[OF sol] ok_update(2,3)[OF upd] eq unfolding solution_def by auto

text \<open>A \<^const>\<open>vupdate\<close> whose binding is solved keeps the solution:\<close>

lemma ffc_vupdate_complete:
  assumes "vupdate aU t env = Some r"
  shows "r = Ok env' \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow> wt_env \<rho> env \<Longrightarrow>
    \<sigma> (fst aU) (tsubst \<rho> (snd aU)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<Longrightarrow>
    (\<And>x T. t = Var x T \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> (snd aU)) \<Longrightarrow> solution \<rho> \<sigma> env'"
  using assms
proof (induction aU t env r arbitrary: env' rule: vupdate.raw_induct[rotated, consumes 1])
  case (1 vu aU t env r)
  obtain v T0 where aU: "aU = (v, T0)" by (cases aU)
  note sol = "1.prems"(2) and wte = "1.prems"(3) and eq = "1.prems"(4) and tv = "1.prems"(5)
  have up: "ok (case t of
      Var name' T \<Rightarrow>
        if fst aU = name' then return env
        else if indexname_less (fst aU) name' then lookup env name' T \<bind> (\<lambda>r.
          case r of None \<Rightarrow> update (name', T) (Var (fst aU) T) env | Some u \<Rightarrow> vu aU u env)
        else update aU t env
    | _ \<Rightarrow> update aU t env) env'"
    using "1.hyps" "1.prems"(1) by simp
  show ?case
  proof (cases t)
    case (Var name' T)
    have TT: "tsubst \<rho> T = tsubst \<rho> T0" using tv[OF Var] aU by simp
    consider "v = name'" | "v \<noteq> name'" "indexname_less v name'" | "v \<noteq> name'" "\<not> indexname_less v name'"
      by blast
    then show ?thesis
    proof cases
      case 1
      with up Var aU have "env' = env" by simp
      with sol show ?thesis by simp
    next
      case 2
      with up Var aU obtain lr where lk: "ok (lookup env name' T) lr"
        and rest: "ok (case lr of None \<Rightarrow> update (name', T) (Var v T) env | Some u \<Rightarrow> vu aU u env) env'"
        by auto
      show ?thesis
      proof (cases lr)
        case None
        with rest have upd: "ok (update (name', T) (Var v T) env) env'" by simp
        have "\<sigma> name' (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Var v T)"
          using conv_sym[OF eq] Var aU TT by simp
        then show ?thesis by (rule ffc_solution_update[OF upd sol])
      next
        case (Some u)
        from lk Some obtain U where lku: "vt_lookup (tenv env) name' = Some (U, u)"
          and un: "ok (unified (tyenv env) T U) True" by (auto elim: ok_lookup_Some)
        from rest Some have r: "ok (vu aU u env) env'" by simp
        have TU: "tsubst \<rho> T = tsubst \<rho> U" by (rule unified_sound[OF un solutionD(2)[OF sol]])
        have "\<sigma> name' (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" by (rule solutionD(4)[OF sol lku])
        then have eq': "\<sigma> (fst aU) (tsubst \<rho> (snd aU)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
          using eq Var aU TU by (auto intro: conv_trans)
        have tv': "tsubst \<rho> T' = tsubst \<rho> (snd aU)" if "u = Var x T'" for x T'
        proof -
          have "undefined \<turnstile> inst \<rho> u : tsubst \<rho> U" by (rule wt_envD[OF wte lku])
          with that TT TU aU show ?thesis by auto
        qed
        show ?thesis by (rule "1.IH"[OF r refl sol wte eq' tv'])
      qed
    next
      case 3
      with up Var aU have "ok (update aU t env) env'" by simp
      then show ?thesis using ffc_solution_update[of v T0 t env env'] sol eq aU by simp
    qed
  qed (use up ffc_solution_update[of v T0 t env env'] sol eq aU in auto)
qed

text \<open>Renamings with a left inverse reflect equivalence:\<close>

lemma ffc_conv_unrename:
  assumes c: "rename F 0 s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 s'" and w: "wt (rename F 0 s)" "wt s" "wt s'"
    and nF: "nonneg F" "nonneg g" and inv: "\<And>p. 0 \<le> p \<Longrightarrow> p < n \<Longrightarrow> g (F p) = p"
    and lb: "\<not> loose_bvar s n" "\<not> loose_bvar s' n"
  shows "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s'"
proof -
  have r: "rename g 0 (rename F 0 x) = x" if "\<not> loose_bvar x n" for x
  proof -
    have "rename g 0 (rename F 0 x) = rename (\<lambda>k. g (F k)) 0 x" by (rule rename_comp[OF nF(1)])
    also have "\<dots> = rename (\<lambda>k. k) 0 x"
      by (rule rename_cong) (use inv loose_bvar1_less[OF that] in simp)
    finally show ?thesis by (simp add: rename_id)
  qed
  have "rename g 0 (rename F 0 s) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename g 0 (rename F 0 s')"
    by (rule conv_rename[OF c w(1) _ _ nF(2) order_refl]) (simp_all add: r lb w(2,3))
  then show ?thesis by (simp add: r lb)
qed

subsection \<open>Banned bound variables\<close>

lemma ffc_add_index_banned:
  "foldr (add_index lt lu) xs (bn0, rb0) = (bn, rb') \<Longrightarrow> j \<in> set bn \<Longrightarrow>
    j \<in> set bn0 \<or> (\<exists>x. (j, x) \<in> set xs \<and> \<not> (j \<in> set lt \<and> j \<in> set lu))"
proof (induction xs arbitrary: bn rb')
  case (Cons jx xs)
  obtain j0 x where jx: "jx = (j0, x)" by (metis surj_pair)
  obtain bn1 rb1 where f: "foldr (add_index lt lu) xs (bn0, rb0) = (bn1, rb1)" by force
  from Cons.prems(1) f jx have st: "add_index lt lu (j0, x) (bn1, rb1) = (bn, rb')" by simp
  show ?case
  proof (cases "j0 \<in> set lt \<and> j0 \<in> set lu")
    case True
    with st have "bn = bn1" by (simp add: add_index_def)
    with Cons.IH[OF f] Cons.prems(2) jx show ?thesis by auto
  next
    case False
    with st have bn: "bn = j0 # bn1" by (simp add: add_index_def)
    show ?thesis
    proof (cases "j = j0")
      case True
      then show ?thesis by (intro disjI2 exI[of _ x]) (use jx False in auto)
    next
      case False
      with Cons.IH[OF f] Cons.prems(2) bn show ?thesis by auto
    qed
  qed
qed simp

lemma ffc_clean_binder:
  assumes "foldr (add_index lt lu) (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
  shows "\<exists>F. bren_ok banned rb rb' F \<and> (\<forall>p. 0 \<le> p \<longrightarrow> p < ilength rb' \<longrightarrow> sqz banned (F p) = p)"
proof -
  from add_index_fold[of lt lu 0 rb banned rb'] assms
  obtain keep where rb': "rb' = map (\<lambda>j. rb ! j) keep"
    and un: "set banned \<union> integer_of_nat ` set keep = integer_of_nat ` {0..<length rb}"
    and di: "set banned \<inter> integer_of_nat ` set keep = {}"
    and sq: "\<forall>p<length keep. sqz banned (integer_of_nat (keep ! p)) = integer_of_nat p"
    by (auto simp: upto_list_def)
  define F where "F p = (if 0 \<le> p \<and> p < ilength keep then integer_of_nat (keep ! nat_of_integer p) else p)"
    for p
  have lk: "length rb' = length keep" by (simp add: rb')
  have keep_lt: "j < length rb" if "j \<in> set keep" for j
  proof -
    from that un have "integer_of_nat j \<in> integer_of_nat ` {0..<length rb}" by blast
    then obtain j' where "j' < length rb" "integer_of_nat j = integer_of_nat j'" by auto
    then show ?thesis by (simp add: integer_of_nat_eq_of_nat)
  qed
  have "nonneg F" by (auto simp: nonneg_def F_def integer_of_nat_eq_of_nat)
  moreover have "F (sqz banned j) = j \<and> 0 \<le> sqz banned j \<and> sqz banned j < ilength rb'"
    if j: "0 \<le> j" "j < ilength rb" "j \<notin> set banned" for j
  proof -
    have "j \<in> integer_of_nat ` {0..<length rb}"
      using j(1,2) by (auto simp: image_iff ilength_eq integer_reps intro!: bexI[of _ "nat_of_integer j"])
    with un j(3) have "j \<in> integer_of_nat ` set keep" by blast
    then obtain q where q: "q < length keep" "j = integer_of_nat (keep ! q)"
      by (auto simp: in_set_conv_nth)
    from sq q have s: "sqz banned j = integer_of_nat q" by simp
    have "0 \<le> integer_of_nat q" "integer_of_nat q < ilength keep"
      using q(1) by (simp_all add: ilength_eq integer_of_nat_eq_of_nat)
    then show ?thesis using q s lk by (simp add: F_def ilength_eq)
  qed
  moreover have "0 \<le> F p \<and> F p < ilength rb \<and> rb' ! nat_of_integer p = rb ! nat_of_integer (F p) \<and>
      sqz banned (F p) = p"
    if p: "0 \<le> p" "p < ilength rb'" for p
  proof -
    have q: "nat_of_integer p < length keep" using nat_of_integer_less_ilength[OF p] lk by simp
    have Fp: "F p = integer_of_nat (keep ! nat_of_integer p)" using p lk by (simp add: F_def ilength_eq)
    have "keep ! nat_of_integer p < length rb" using keep_lt[OF nth_mem[OF q]] .
    moreover have "sqz banned (F p) = p"
    proof -
      have "sqz banned (F p) = integer_of_nat (nat_of_integer p)" using sq q Fp by simp
      then show ?thesis using integer_of_nat_nat_of_integer[OF p(1)] by simp
    qed
    ultimately show ?thesis using Fp q by (simp add: rb' ilength_eq integer_of_nat_eq_of_nat)
  qed
  ultimately show ?thesis unfolding bren_ok_def by blast
qed

lemma ffc_banned:
  assumes "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    and "j \<in> set banned"
  shows "0 \<le> j" "j < ilength rb" "\<not> (loose_bvar1 t j \<and> loose_bvar1 u j)"
proof -
  from ffc_add_index_banned[OF assms] obtain x where
    jx: "(j, x) \<in> set (zip (upto_list (length rb)) rb)"
    and nl: "\<not> (j \<in> set (loose_bnos t) \<and> j \<in> set (loose_bnos u))" by auto
  from set_zip_leftD[OF jx] obtain k where "k < length rb" "j = integer_of_nat k"
    by (auto simp: upto_list_def)
  then show "0 \<le> j" "j < ilength rb" by (simp_all add: ilength_eq integer_of_nat_eq_of_nat)
  with nl show "\<not> (loose_bvar1 t j \<and> loose_bvar1 u j)" by (simp add: set_loose_bnos)
qed

text \<open>The normal forms of a solved pair have no loose banned bound variables:\<close>

lemma ffc_nf_bounds_pair:
  assumes bn: "\<forall>j\<in>set banned. \<not> (loose_bvar1 t j \<and> loose_bvar1 u j)"
    and eq: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" and w: "wt (ap \<rho> \<sigma> t)" and cs: "closed_subst \<sigma>"
    and lb: "\<not> loose_bvar t (ilength rb)"
  shows "nf_bounds (ap \<rho> \<sigma> t) 0 (filter (\<lambda>j. j \<notin> set banned) (upto_list (length rb)))"
  unfolding nf_bounds_def
proof (intro allI impI)
  fix N k assume N: "normal N" "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" and k: "0 \<le> k" "loose_bvar1 N k"
  have lt: "loose_bvar1 t k" using ffc_conv_nf_loose[OF N(2) w N(1) k] cs k(1) by (simp add: ap_def)
  have kl: "k < ilength rb" by (rule loose_bvar1_less[OF lb lt])
  have cu: "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using conv_trans[OF conv_sym[OF eq] N(2)] .
  have wu: "wt (ap \<rho> \<sigma> u)" using w eq wt_conv by blast
  have "loose_bvar1 (ap \<rho> \<sigma> u) k" by (rule ffc_conv_nf_loose[OF cu wu N(1) k])
  then have "loose_bvar1 u k" using cs k(1) by (simp add: ap_def)
  with lt bn have nb: "k \<notin> set banned" by blast
  have "k \<in> set (upto_list (length rb))"
    using k(1) kl by (auto simp: upto_list_def image_iff ilength_eq integer_reps
        intro!: bexI[of _ "nat_of_integer k"])
  with nb show "k - 0 \<in> set (filter (\<lambda>j. j \<notin> set banned) (upto_list (length rb)))" by simp
qed

subsection \<open>Cleaning terms\<close>

lemma ffc_change_arg_cases:
  "okW (change_arg del banned a cas1) cas \<Longrightarrow>
    set cas1 \<subseteq> set cas \<and> ((\<exists>a'\<in>set cas. fl_j a' = fl_j a) \<or> (del \<and> rigid_bound 0 banned (fl_t a)))"
  by (cases a) (auto simp: change_arg_def split: if_splits)

lemma ffc_foldrW_change_arg_del:
  "okW (foldrW (change_arg del banned) fas acc) cas \<Longrightarrow> a \<in> set fas \<Longrightarrow>
    (\<exists>a'\<in>set cas. fl_j a' = fl_j a) \<or> (del \<and> rigid_bound 0 banned (fl_t a))"
proof (induction fas arbitrary: cas)
  case (Cons b fas)
  then obtain cas1 where c1: "okW (foldrW (change_arg del banned) fas acc) cas1"
    and c: "okW (change_arg del banned b cas1) cas" by auto
  note cc = ffc_change_arg_cases[OF c]
  show ?case
  proof (cases "a = b")
    case True
    with cc show ?thesis by blast
  next
    case False
    with Cons.prems(2) have "a \<in> set fas" by simp
    from Cons.IH[OF c1 this] cc show ?thesis by blast
  qed
qed simp

lemma ffc_flexargs:
  "okW (flexargs js ts Ts) fas \<Longrightarrow>
    length fas = length ts \<and> (\<forall>k<length ts. fas ! k = Flarg (js ! k) (ts ! k) (Ts ! k))"
proof (induction js ts Ts arbitrary: fas rule: flexargs.induct)
  case (2 j js t ts T Ts)
  then obtain args where "okW (flexargs js ts Ts) args" "fas = Flarg j t T # args" by auto
  with "2.IH"[OF this(1)] show ?case by (auto simp: nth_Cons')
qed auto

lemma ffc_rigid_headed_ap:
  assumes "rigid_headed s"
  shows "\<exists>h A. atom h \<and> ap \<rho> \<sigma> (eta_contract s) = h \<degree>\<degree> A"
proof -
  let ?s = "eta_contract s"
  have s: "?s = head_of ?s \<degree>\<degree> snd (strip_comb ?s)" by (rule t_apps)
  have "atom (ap \<rho> \<sigma> (head_of ?s))" using assms by (cases "head_of ?s") (auto simp: rigid_headed_def)
  moreover have "ap \<rho> \<sigma> ?s = ap \<rho> \<sigma> (head_of ?s) \<degree>\<degree> map (ap \<rho> \<sigma>) (snd (strip_comb ?s))"
    by (subst s) (simp add: ap_apps)
  ultimately show ?thesis by metis
qed

lemma ffc_eta_reds_ap: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> ap \<rho> \<sigma> s \<rightarrow>\<^sub>\<eta>\<^sup>* ap \<rho> \<sigma> t"
proof (induction rule: rtranclp_induct)
  case (step t u)
  have "closed_subst \<sigma>" using step.prems by (simp add: wt_subst_def)
  then have "ap \<rho> \<sigma> t \<rightarrow>\<^sub>\<eta> ap \<rho> \<sigma> u" unfolding ap_def by (rule eta_vsubst[OF eta_inst[OF step.hyps(2)]])
  with step.IH[OF step.prems] show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed simp

text \<open>An argument and the instance of its \<open>\<eta>\<close>-contraction:\<close>

lemma ffc_eta_contract_ap:
  assumes "wt_subst \<sigma>" "e \<turnstile> ap \<rho> \<sigma> s : T"
  shows "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (eta_contract s)" "e \<turnstile> ap \<rho> \<sigma> (eta_contract s) : T"
proof -
  have r: "ap \<rho> \<sigma> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* ap \<rho> \<sigma> (eta_contract s)"
    by (rule eta_reds_beta_eta_reds[OF ffc_eta_reds_ap[OF eta_contract_reds assms(1)]])
  show "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (eta_contract s)"
    by (rule beta_eta_conv[OF r]) (use assms(2) in \<open>auto simp: wt_def\<close>)
  show "e \<turnstile> ap \<rho> \<sigma> (eta_contract s) : T" by (rule subject_reduction_reds[OF r assms(2)])
qed

text \<open>
  Completeness of \<^const>\<open>clean_term\<close>: if the normal forms of the solved instance of the term have
  no loose banned bound variables, the arguments that \<^const>\<open>clean_term\<close> deletes are not used by
  the value of the head variable, which is then the abstraction of a value of the new variable
  applied to the kept arguments.
\<close>

lemma clean_term_complete:
  assumes ct: "okW (clean_term banned env t) (env', t')"
    and sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and vi: "vinv \<rho> env (X \<union> vars t)"
    and ty: "e \<turnstile> inst \<rho> t : T"
    and nb: "nf_bounds (ap \<rho> \<sigma> t) 0 xs" and xb: "set xs \<inter> set banned = {}"
    and b0: "\<forall>j\<in>set banned. 0 \<le> j" and nr: "no_redex t"
  shows "\<exists>\<sigma>'. solution \<rho> \<sigma>' env' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
proof -
  obtain h ts where sc: "strip_comb t = (h, ts)" by (cases "strip_comb t")
  have "\<exists>v T0. h = Var v T0" using ct sc by (cases h) (auto simp: clean_term_def)
  then obtain v T0 where h: "h = Var v T0" by blast
  have t: "t = Var v T0 \<degree>\<degree> ts" using strip_comb_apps[OF sc] h by simp
  let ?n = "length ts"
  from ct sc h obtain Ts U fas cas where st: "ok (strip_type env T0) (Ts, U)"
    and fa: "okW (flexargs (downto0_list ?n) ts Ts) fas"
    and ca: "okW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) cas"
    and rest: "okW (let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T0) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T0) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')})) (env', t')"
    by (auto simp: clean_term_def Let_def split: prod.splits)
  define args where "args = sort_args cas"
  define ts' where "ts' = map fl_t args"
  have lTs: "length Ts = ?n" using flexargs_ok[OF fa] by simp
  note s = solutionD[OF sol]
  have tsol: "tsol (tyenv env) \<rho>" by (rule s(2))
  have cs: "closed_subst \<sigma>" using s(3) by (simp add: wt_subst_def)
  have td: "cert_typ alg ar (tsubst \<rho> T0) \<and> tsubst \<rho> T0 = map (tsubst \<rho>) Ts \<Rrightarrow> T \<and> tsubst \<rho> U = T \<and>
      (\<forall>k<?n. e \<turnstile> inst \<rho> (ts ! k) : tsubst \<rho> (Ts ! k))"
  proof -
    from ty have "e \<turnstile> Var v (tsubst \<rho> T0) \<degree>\<degree> map (inst \<rho>) ts : T" by (simp add: t inst_apps)
    then obtain Us where tv: "e \<turnstile> Var v (tsubst \<rho> T0) : Us \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us"
      by (rule list_app_typeE)
    from tv have c: "cert_typ alg ar (tsubst \<rho> T0)" and eq: "tsubst \<rho> T0 = Us \<Rrightarrow> T" by auto
    from typings_nth[OF tts] have lu: "length Us = ?n" and nth: "\<forall>i<?n. e \<turnstile> inst \<rho> (ts ! i) : Us ! i"
      by simp_all
    from strip_type_sound[OF st tsol] eq have "map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> U = Us \<Rrightarrow> T" by simp
    with funs_eq[of "map (tsubst \<rho>) Ts" Us] lu lTs have UT: "map (tsubst \<rho>) Ts = Us" "tsubst \<rho> U = T"
      by simp_all
    with c eq nth lTs show ?thesis by auto
  qed
  show ?thesis
  proof (cases "decreasing (ilength Ts) args")
    case True
    with rest have "env' = env" by (simp add: Let_def args_def)
    with sol show ?thesis by (intro exI[of _ \<sigma>]) simp
  next
    case False
    define Gty where "Gty = foldr fun_type (map fl_T args) U"
    obtain env1 v' where g: "genvar (fst v) env Gty = (env1, v')" by (cases "genvar (fst v) env Gty")
    define ks where "ks = map fl_j args"
    define body where "body = v' \<degree>\<degree> map Bound ks"
    from rest False g obtain env2 where vu: "ok (vupdate (v, T0) (types_abs Ts body) env1) env2"
      and env': "env' = env2"
      by (auto simp: Let_def args_def ts'_def body_def ks_def Gty_def list_comb_apps comp_def)
    note gs = genvar_simps[OF g]
    let ?G = "(fst v, maxidx env + 1)"
    let ?Us = "map (tsubst \<rho>) Ts"
    have ak: "0 \<le> fl_j a \<and> fl_j a < ilength ts \<and> rev ?Us ! nat_of_integer (fl_j a) = tsubst \<rho> (fl_T a)"
      if a: "a \<in> set args" for a
    proof -
      from a have "a \<in> set cas" by (simp add: args_def set_sort_args)
      with foldrW_change_arg[OF ca] obtain a0 where "a0 \<in> set fas" "fl_j a = fl_j a0" "fl_T a = fl_T a0"
        by auto
      with flexargs_ok[OF fa] obtain k where k: "k < ?n" "fl_j a = integer_of_nat (?n - 1 - k)"
        "fl_T a = Ts ! k"
        by (fastforce simp: downto0_list_nth)
      have j: "nat_of_integer (fl_j a) = ?n - 1 - k" using k(2) by (simp add: integer_reps)
      have rv: "rev xs ! (?n - 1 - k) = xs ! k" if "length xs = ?n" for xs :: "ptyp list"
        using k(1) that by (simp add: rev_nth)
      have "0 \<le> fl_j a" "fl_j a < ilength ts" using k(1,2) by (simp_all add: ilength_eq integer_reps)
      moreover have "rev ?Us ! nat_of_integer (fl_j a) = ?Us ! k" unfolding j by (rule rv) (simp add: lTs)
      ultimately show ?thesis using k(1,3) lTs by simp
    qed
    have tyG: "tsubst \<rho> Gty = map (\<lambda>a. tsubst \<rho> (fl_T a)) args \<Rrightarrow> tsubst \<rho> U"
      by (simp add: Gty_def tsubst_funs comp_def)
    have c0: "cert_typ alg ar (?Us \<Rrightarrow> T)" using td by metis
    then have "(\<forall>V\<in>set ?Us. cert_typ alg ar V) \<and> cert_typ alg ar T"
      using cert_typ_funs[where Ts = ?Us and T = T] by blast
    then have cUs: "\<forall>V\<in>set ?Us. cert_typ alg ar V" and cT: "cert_typ alg ar T" by blast+
    have cA: "\<forall>a\<in>set args. cert_typ alg ar (tsubst \<rho> (fl_T a))"
    proof
      fix a assume "a \<in> set args"
      note k = ak[OF this]
      have "nat_of_integer (fl_j a) < length (rev ?Us)"
        using k lTs nat_of_integer_less_ilength[of "fl_j a" ts] by simp
      then have "rev ?Us ! nat_of_integer (fl_j a) \<in> set ?Us" by (metis nth_mem set_rev)
      then have "tsubst \<rho> (fl_T a) \<in> set ?Us" using k by metis
      with cUs show "cert_typ alg ar (tsubst \<rho> (fl_T a))" by blast
    qed
    have cG: "cert_typ alg ar (tsubst \<rho> Gty)"
      using cA cT td by (simp add: tyG cert_typ_funs)
    text \<open>The value of the cleaned variable, and its canonical body:\<close>
    let ?f = "\<sigma> v (tsubst \<rho> T0)"
    have cf: "closed ?f" by (rule closed_substD[OF cs])
    have tyf: "e \<turnstile> ?f : ?Us \<Rrightarrow> T" using wt_subst_typing[OF s(3) conjunct1[OF td]] td by simp
    obtain B where B: "normal B" "\<not> loose_bvar B (ilength ?Us)" "\<And>e'. pushes e' ?Us \<turnstile> B : T"
      "\<And>bs. map snd bs = ?Us \<Longrightarrow> \<forall>U\<in>set ?Us. cert_typ alg ar U \<Longrightarrow> ?f \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs B"
      "\<And>xs. length xs = length ?Us \<Longrightarrow> \<forall>i\<in>set xs. 0 \<le> i \<Longrightarrow>
        ?f \<degree>\<degree> map Bound xs \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* rename (bren (rev xs)) 0 B"
      using canonical_body[OF cf tyf] by metis
    let ?bs = "map (\<lambda>T. (STR '''', tsubst \<rho> T)) Ts"
    have bsU: "map snd ?bs = ?Us" by simp
    have cbs: "\<forall>T\<in>snd ` set ?bs. cert_typ alg ar T" using cUs by auto
    have fB: "?f \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs B" by (rule B(4)[OF bsU cUs])
    let ?ss = "map (ap \<rho> \<sigma>) ts"
    have tss: "e \<tturnstile> ?ss : ?Us"
      by (rule typings_nthI) (use td lTs typing_ap[OF _ s(3)] in auto)
    have "pushes e (map snd ?bs) \<turnstile> B : T" using B(3)[of e] by (simp only: bsU)
    from typing_abs_list[OF this cbs] have "e \<turnstile> abs_list ?bs B : ?Us \<Rrightarrow> T" by (simp only: bsU)
    then have tyBs: "e \<turnstile> abs_list ?bs B \<degree>\<degree> ?ss : T" using tss by (rule list_app_typeI)
    have apt: "ap \<rho> \<sigma> t = ?f \<degree>\<degree> ?ss" by (simp add: t ap_apps)
    have wt1: "wt (?f \<degree>\<degree> ?ss)" using wt_ap[OF ty s(3)] apt by simp
    have cB: "?f \<degree>\<degree> ?ss \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs B \<degree>\<degree> ?ss"
      by (rule conv_apps[OF _ wt1 _ fB]) (use tyBs in \<open>auto simp: list_all2_refl wt_def\<close>)
    have nbB: "nf_bounds (abs_list ?bs B \<degree>\<degree> ?ss) 0 xs" using nf_bounds_conv[OF cB] nb apt by simp
    have lbB: "\<not> loose_bvar B (ilength ?bs)" using B(2) by (simp add: ilength_eq)
    have lss: "length ?ss = length ?bs" by (simp add: lTs)
    have nrB: "no_redex B" using B(1) by (simp add: normal_iff)
    text \<open>The body only uses the kept arguments:\<close>
    have key: "k \<in> set ks" if k: "0 \<le> k" "loose_bvar1 B k" for k
    proof (rule ccontr)
      assume nk: "k \<notin> set ks"
      have kl: "k < ilength ?Us" by (rule loose_bvar1_less[OF B(2) k(2)])
      then have kn: "nat_of_integer k < ?n" using nat_of_integer_less_ilength[OF k(1) kl] lTs by simp
      define i where "i = ?n - Suc (nat_of_integer k)"
      have i: "i < ?n" using kn by (simp add: i_def)
      have fai: "fas ! i = Flarg k (ts ! i) (Ts ! i)"
      proof -
        have "fas ! i = Flarg (downto0_list ?n ! i) (ts ! i) (Ts ! i)" using ffc_flexargs[OF fa] i by blast
        moreover have "?n - 1 - i = nat_of_integer k" using kn by (simp add: i_def)
        then have "downto0_list ?n ! i = k"
          using downto0_list_nth[OF i] integer_of_nat_nat_of_integer[OF k(1)] by simp
        ultimately show ?thesis by simp
      qed
      have "i < length fas" using i ffc_flexargs[OF fa] by simp
      then have "fas ! i \<in> set fas" by (rule nth_mem)
      from ffc_foldrW_change_arg_del[OF ca this] fai consider (kept) "\<exists>a'\<in>set cas. fl_j a' = k"
        | (del) "list_all rigid_headed ts" "rigid_bound 0 banned (ts ! i)" by auto
      then show False
      proof cases
        case kept
        then have "k \<in> set ks" by (auto simp: ks_def args_def set_sort_args)
        with nk show False by simp
      next
        case del
        \<comment> \<open>the arguments are rigid-headed after \<open>\<eta>\<close>-contraction\<close>
        let ?ss' = "map (ap \<rho> \<sigma> \<circ> eta_contract) ts"
        have tyj: "e \<turnstile> ap \<rho> \<sigma> (ts ! j) : tsubst \<rho> (Ts ! j)" if "j < ?n" for j
          using typing_ap[OF _ s(3)] td that by blast
        note ec = ffc_eta_contract_ap[OF s(3) tyj]
        have at: "\<forall>s\<in>set ?ss'. \<exists>h A. atom h \<and> s = h \<degree>\<degree> A"
          using del(1) ffc_rigid_headed_ap by (auto simp: list_all_iff)
        have tss': "e \<tturnstile> ?ss' : ?Us" by (rule typings_nthI) (use ec(2) lTs in auto)
        have tyBs': "e \<turnstile> abs_list ?bs B \<degree>\<degree> ?ss' : T"
          using \<open>e \<turnstile> abs_list ?bs B : ?Us \<Rrightarrow> T\<close> tss' by (rule list_app_typeI)
        have cB': "abs_list ?bs B \<degree>\<degree> ?ss \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs B \<degree>\<degree> ?ss'"
          by (rule conv_apps[OF _ _ _ conv_refl])
            (use ec(1) tyBs tyBs' in \<open>auto simp: list_all2_conv_all_nth wt_def\<close>)
        have nbB': "nf_bounds (abs_list ?bs B \<degree>\<degree> ?ss') 0 xs" by (rule nf_bounds_conv[OF cB' nbB])
        have lss': "length ?ss' = length ?bs" by (simp add: lTs)
        have "nf_bounds (rev ?ss' ! nat_of_integer k) 0 xs"
          by (rule ffc_use_arg[OF nrB lbB lss' k(1) k(2) tyBs' at nbB' order_refl])
        moreover have "rev ?ss' ! nat_of_integer k = ap \<rho> \<sigma> (eta_contract (ts ! i))"
          using kn by (simp add: rev_nth i_def)
        ultimately have "nf_bounds (ap \<rho> \<sigma> (eta_contract (ts ! i))) 0 xs" by simp
        then have nbi: "nf_bounds (ap \<rho> \<sigma> (ts ! i)) 0 xs" by (rule nf_bounds_conv[OF conv_sym[OF ec(1)[OF i]]])
        have "e \<turnstile> ap \<rho> \<sigma> (ts ! i) : tsubst \<rho> (Ts ! i)" by (rule tyj[OF i])
        moreover have "no_redex (ts ! i)" using ffc_no_redex_apps[of "Var v T0" ts] nr i by (simp add: t)
        ultimately show False using ffc_rigid_bound_nf[OF del(2) _ order_refl b0 nbi] xb by blast
      qed
    qed
    text \<open>The value of the new variable:\<close>
    let ?e0 = "pushes e ?Us"
    have e0k: "?e0 (fl_j a) = tsubst \<rho> (fl_T a)" if "a \<in> set args" for a
      using ak[OF that] pushes_nth[of "fl_j a" e ?Us] lTs by (simp add: ilength_eq)
    have cks: "\<forall>k\<in>set ks. cert_typ alg ar (?e0 k)" using e0k cA by (auto simp: ks_def)
    note w = strengthen[OF B(3)[of e] key cks]
    let ?H = "sabs ?e0 ks B"
    have mks: "map ?e0 ks = map (\<lambda>a. tsubst \<rho> (fl_T a)) args" using e0k by (simp add: ks_def)
    have tyH: "e' \<turnstile> ?H : tsubst \<rho> Gty" for e' using w(2)[of e'] mks tyG td by simp
    let ?\<sigma>' = "supd \<sigma> ?G (tsubst \<rho> Gty) ?H"
    have ws': "wt_subst ?\<sigma>'" by (rule wt_subst_supd[OF s(3) w(1) tyH])
    have sa: "sagree (maxidx env) \<sigma> ?\<sigma>'" by (rule sagree_supd) simp
    have vi0: "vinv \<rho> env X" using vi by (rule vinv_mono) simp
    have sol1: "solution \<rho> ?\<sigma>' env1"
      by (rule solution_extend[OF sol vi0 sa ws']) (simp_all add: gs)
    have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_genvar[OF g])
    have "(v, T0) \<in> X \<union> vars t \<union> evars env" by (simp add: t vars_apps)
    moreover have "below (maxidx env) (X \<union> vars t \<union> evars env)" using vi by (simp add: vinv_def)
    ultimately have vb: "snd v \<le> maxidx env" using belowD by blast
    then have "v \<noteq> ?G" by (cases v) auto
    then have s'v: "?\<sigma>' v (tsubst \<rho> T0) = ?f" by (simp add: supd_def)
    have apB: "ap \<rho> ?\<sigma>' (types_abs Ts body) = abs_list ?bs (?H \<degree>\<degree> map Bound ks)"
      by (simp add: types_abs_abs_list ap_abs_list body_def gs(4) ap_apps comp_def)
    have ks0: "\<forall>m\<in>set ks. 0 \<le> m" using ak by (auto simp: ks_def)
    have redH: "?H \<degree>\<degree> map Bound ks \<rightarrow>\<^sub>\<beta>\<^sup>* B"
    proof -
      have "?H \<degree>\<degree> map Bound ks \<rightarrow>\<^sub>\<beta>\<^sup>* rename (\<lambda>k. bren (rev ks) (bidx ks k)) 0 B"
        using w(3)[of ks] ks0 by simp
      moreover have "rename (\<lambda>k. bren (rev ks) (bidx ks k)) 0 B = B" using rename_bren_bidx[OF key] by simp
      ultimately show ?thesis by simp
    qed
    have tyHB: "e \<turnstile> abs_list ?bs (?H \<degree>\<degree> map Bound ks) : ?Us \<Rrightarrow> T"
    proof -
      have "?e0 \<tturnstile> map Bound ks : map ?e0 ks" by (rule typings_Bounds) (use ks0 in auto)
      then have "?e0 \<turnstile> ?H \<degree>\<degree> map Bound ks : T" using w(2)[of ?e0] by (rule list_app_typeI[rotated])
      then have "pushes e (map snd ?bs) \<turnstile> ?H \<degree>\<degree> map Bound ks : T" by (simp only: bsU)
      from typing_abs_list[OF this cbs] show ?thesis by (simp only: bsU)
    qed
    have "abs_list ?bs (?H \<degree>\<degree> map Bound ks) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs B"
      by (rule conv_beta_eta[OF _ beta_reds_abs_list[OF redH]]) (use tyHB in \<open>auto simp: wt_def\<close>)
    then have bind: "?\<sigma>' v (tsubst \<rho> T0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> ?\<sigma>' (types_abs Ts body)"
      using s'v apB fB by (auto intro: conv_sym conv_trans)
    have iB: "inst \<rho> (types_abs Ts body) = abs_list ?bs (Var ?G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks)"
      by (simp add: types_abs_abs_list inst_abs_list body_def gs(4) inst_apps comp_def)
    have tB: "e' \<turnstile> inst \<rho> (types_abs Ts body) : tsubst \<rho> T0" for e'
    proof -
      have "pushes e' ?Us \<tturnstile> map Bound ks : map (\<lambda>a. tsubst \<rho> (fl_T a)) args"
        unfolding ks_def map_map comp_def
      proof (rule typings_map)
        fix a assume "a \<in> set args"
        note k = ak[OF this]
        then have "pushes e' ?Us (fl_j a) = tsubst \<rho> (fl_T a)"
          using pushes_nth[of "fl_j a" e' ?Us] lTs by (simp add: ilength_eq)
        with k show "pushes e' ?Us \<turnstile> Bound (fl_j a) : tsubst \<rho> (fl_T a)" by auto
      qed
      with cG tyG have "pushes e' (map snd ?bs) \<turnstile> Var ?G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks : tsubst \<rho> U"
        by (auto intro!: list_app_typeI simp: comp_def)
      from typing_abs_list[OF this] cUs have "e' \<turnstile> abs_list ?bs (Var ?G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks) :
          map snd ?bs \<Rrightarrow> tsubst \<rho> U"
        by auto
      then show ?thesis using td by (simp add: iB comp_def)
    qed
    have tv: "tsubst \<rho> T' = tsubst \<rho> (snd (v, T0))" if "types_abs Ts body = Var x T'" for x T'
      using tB[of undefined] that by auto
    have sol2: "solution \<rho> ?\<sigma>' env2"
      by (rule ffc_vupdate_complete[OF vu refl sol1 wte1 _ tv]) (use bind in simp)
    then show ?thesis using sa env' by blast
  qed
qed

subsection \<open>Flex-flex assignments and remaining pairs\<close>

lemma ffc_downs_upt: "rev (map integer_of_nat [0..<n]) = downs n"
  by (induction n) simp_all

lemma ffc_ap_rlist_abs:
  "ap \<rho> \<sigma> (rlist_abs rb s) = abs_list (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)) (ap \<rho> \<sigma> s)"
  by (simp add: rlist_abs_abs_list ap_abs_list)

lemma ffc_conv_rlist_abs:
  assumes "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
    "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)" "wt_subst \<sigma>"
    "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  shows "ap \<rho> \<sigma> (rlist_abs rb t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs rb u)"
proof -
  have "wt (ap \<rho> \<sigma> (rlist_abs rb t))" "wt (ap \<rho> \<sigma> (rlist_abs rb u))"
    using typing_ap[OF rlist_abs_typing(1)[OF assms(1,2,4)] assms(6)]
      typing_ap[OF rlist_abs_typing(1)[OF assms(1,3,5)] assms(6)]
    by (auto simp: wt_def)
  then show ?thesis unfolding ffc_ap_rlist_abs by (rule conv_abs_list[OF _ _ assms(7)])
qed

text \<open>A flex-flex assignment keeps the solution of a solved pair:\<close>

lemma ff_assign_complete:
  assumes fa: "okW (ff_assign alg' env rb t u) env'" and tsol': "tsol (tyenv env') \<rho>"
    and sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env"
    and bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : T" and tyu: "e \<turnstile> inst \<rho> u : T"
    and lbu: "\<not> loose_bvar u (ilength rb)" and eq: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  shows "solution \<rho> \<sigma> env'"
proof -
  have "\<exists>v T0 T1 T2 env1. okW (get_eta_var rb 0 t) (v, T0) \<and> okW (cunify_types alg' T1 T2 env) env1 \<and>
      ok (vupdate (v, T0) (rlist_abs rb u) env1) env'"
    using fa by (auto simp: ff_assign_def split: if_splits)
  then obtain v T0 T1 T2 env1 where gev: "okW (get_eta_var rb 0 t) (v, T0)"
    and cu: "okW (cunify_types alg' T1 T2 env) env1" and upd: "ok (vupdate (v, T0) (rlist_abs rb u) env1) env'"
    by blast
  have ext1: "extends env1 env'" by (rule asoundD(1)[OF vupdate_asound[OF upd refl]])
  have tsol1: "tsol (tyenv env1) \<rho>" by (rule extends_tsol[OF tsol' ext1])
  have te: "tenv env1 = tenv env" by (rule cunify_types_sound(1)[OF cu])
  have sol1: "solution \<rho> \<sigma> env1" by (rule ffc_solution_tenv[OF te tsol1 sol])
  have wte1: "wt_env \<rho> env1" using wte wt_env_tenv[OF te] by simp
  define "is" where "is = rev (map integer_of_nat [0..<length rb])"
  have t: "t = app (Var v T0) is" using get_eta_var_app[OF gev] by (simp add: is_def)
  have is_ok: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength rb"
    by (auto simp: is_def ilength_eq integer_of_nat_eq_of_nat)
  have mb: "map (\<lambda>i. rb ! nat_of_integer i) is = rev rb"
    by (simp add: is_def rev_map[symmetric] map_nth comp_def)
  from tyt[unfolded t] obtain Fty_eq: "tsubst \<rho> T0 = map e is \<Rrightarrow> T" by (rule typing_appE)
  note bt = bs_types[OF bs is_ok]
  have me: "map e is = map (\<lambda>(x, T). tsubst \<rho> T) (rev rb)"
    using bt(1) mb by (simp add: split_def comp_def)
  have lbt: "\<not> loose_bvar t (ilength rb)" using is_ok by (simp add: t loose_bvar_app_Var)
  note ru = rlist_abs_typing[OF bs tyu lbu] and rt = rlist_abs_typing[OF bs tyt lbt]
  have tyR: "e' \<turnstile> inst \<rho> (rlist_abs rb u) : tsubst \<rho> T0" for e' using ru(1)[of e'] Fty_eq me by simp
  have ws: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  have c1: "ap \<rho> \<sigma> (rlist_abs rb t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs rb u)"
    by (rule ffc_conv_rlist_abs[OF bs tyt tyu lbt lbu ws eq])
  have cf: "closed (\<sigma> v (tsubst \<rho> T0))" using ws by (simp add: wt_subst_def closed_substD)
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)"
  have "ap \<rho> \<sigma> (rlist_abs rb t) = abs_list ?bs (\<sigma> v (tsubst \<rho> T0) \<degree>\<degree> map Bound (downs (length ?bs)))"
    by (simp add: ffc_ap_rlist_abs t app_apps ap_apps comp_def is_def ffc_downs_upt)
  then have r: "ap \<rho> \<sigma> (rlist_abs rb t) \<rightarrow>\<^sub>\<eta>\<^sup>* \<sigma> v (tsubst \<rho> T0)" using eta_abs_list_downs[OF cf, of ?bs] by simp
  have "wt (ap \<rho> \<sigma> (rlist_abs rb t))" using typing_ap[OF rt(1) ws] by (auto simp: wt_def)
  then have c2: "ap \<rho> \<sigma> (rlist_abs rb t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> v (tsubst \<rho> T0)"
    by (rule beta_eta_conv[OF eta_reds_beta_eta_reds[OF r]])
  have bind: "\<sigma> (fst (v, T0)) (tsubst \<rho> (snd (v, T0))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs rb u)"
    using conv_trans[OF conv_sym[OF c2] c1] by simp
  have tv: "tsubst \<rho> T' = tsubst \<rho> (snd (v, T0))" if "rlist_abs rb u = Var x T'" for x T'
    using tyR[of undefined] that by auto
  show ?thesis by (rule ffc_vupdate_complete[OF upd refl sol1 wte1 bind tv])
qed

lemma add_tpair_complete:
  assumes ds: "dsolved \<rho> \<sigma> ((rb, t, u) # tdps tps)" and dt: "dtyped \<rho> [(rb, t, u)]" and ws: "wt_subst \<sigma>"
  shows "dsolved \<rho> \<sigma> (tdps (add_tpair rb t u tps))"
proof -
  from ds have eq: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" and d: "dsolved \<rho> \<sigma> (tdps tps)" by simp_all
  from dt obtain e T where "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
    "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)" by auto
  from ffc_conv_rlist_abs[OF this ws eq] d show ?thesis by (auto simp: add_tpair_def Let_def)
qed

lemma ffc_dsolved_agree:
  assumes "dsolved \<rho> \<sigma> dps" "sagree n \<sigma> \<sigma>'" "below n (dvars dps)"
  shows "dsolved \<rho> \<sigma>' dps"
  unfolding dsolved_def
proof (intro ballI)
  fix dp assume dp: "dp \<in> set dps"
  obtain rb t u where d: "dp = (rb, t, u)" by (cases dp)
  have "below n (vars t)" "below n (vars u)"
    using assms(3) dp d by (auto simp: dvars_def below_def)
  with assms(1) dp d show "case dp of (rb, t, u) \<Rightarrow> ap \<rho> \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u"
    by (auto simp: dsolved_def ap_sagree[OF assms(2)])
qed

lemma ffc_vinv_below: "vinv \<rho> env (X \<union> Y) \<Longrightarrow> below (maxidx env) Y"
  unfolding vinv_def below_def by blast

subsection \<open>Cleaning flex-flex pairs\<close>

theorem clean_ffpair_complete:
  assumes cf: "okW (clean_ffpair alg' rb t u env tps) (env', tps')" and tsol': "tsol (tyenv env') \<rho>"
    and sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and dt: "dtyped \<rho> ((rb, t, u) # tdps tps)"
    and vi: "vinv \<rho> env (X \<union> dvars ((rb, t, u) # tdps tps))" and ds: "dsolved \<rho> \<sigma> ((rb, t, u) # tdps tps)"
    and nrt: "no_redex t" and nru: "no_redex u"
  shows "\<exists>\<sigma>'. solution \<rho> \<sigma>' env' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and> dsolved \<rho> \<sigma>' (tdps tps')"
proof -
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  from ffc_clean_binder[OF fb] obtain F where F: "bren_ok banned rb rb' F"
    and sq: "\<forall>p. 0 \<le> p \<longrightarrow> p < ilength rb' \<longrightarrow> sqz banned (F p) = p" by blast
  note s = solutionD[OF sol]
  have ws: "wt_subst \<sigma>" by (rule s(3))
  have cs: "closed_subst \<sigma>" using ws by (simp add: wt_subst_def)
  from dt obtain e T where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : T" and tyu: "e \<turnstile> inst \<rho> u : T"
    and lbt: "\<not> loose_bvar t (ilength rb)" and lbu: "\<not> loose_bvar u (ilength rb)"
    and dt': "dtyped \<rho> (tdps tps)" by auto
  from ds have eq: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" and ds': "dsolved \<rho> \<sigma> (tdps tps)" by simp_all
  have bel: "below (maxidx env) (dvars ((rb, t, u) # tdps tps))" by (rule ffc_vinv_below[OF vi])
  then have belt: "below (maxidx env) (vars t)" "below (maxidx env) (vars u)"
    and belp: "below (maxidx env) (dvars (tdps tps))" by (auto simp: below_def)
  have "(\<exists>env1 t' env2 u'. okW (clean_term banned env t) (env1, t') \<and>
      okW (clean_term banned env1 u) (env2, u') \<and>
      okW (handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')) \<or>
      (env', tps') = (env, add_tpair rb t u tps)"
    using cf fb by (auto simp: clean_ffpair_def Let_def okW_handleW dest!: okW_CHANGE_FAIL_handler)
  then consider (fail) "(env', tps') = (env, add_tpair rb t u tps)"
    | (main) env1 t' env2 u' where "okW (clean_term banned env t) (env1, t')"
      "okW (clean_term banned env1 u) (env2, u')" "okW (handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg' env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')"
    by blast
  then show ?thesis
  proof cases
    case fail
    have "dtyped \<rho> [(rb, t, u)]" using dt by simp
    from add_tpair_complete[OF ds this ws] fail sol show ?thesis by (intro exI[of _ \<sigma>]) simp
  next
    case (main env1 t' env2 u')
    note cs1 = clean_term_sound[OF main(1) F] and cs2 = clean_term_sound[OF main(2) F]
    have e1: "extends env env1" and e2: "extends env1 env2" using cs1 cs2 by (simp_all add: csound_def)
    have cl: "dstep env [(rb, t, u)] env2 [(rb', t', u')]" by (rule clean_dstep[OF cs1 cs2 F])
    from ff_handler[OF main(3)] consider (fa1) env3 where "okW (ff_assign alg' env2 rb' t' u') env3"
        "(env', tps') = (env3, tps)"
      | (fa2) env3 where "okW (ff_assign alg' env2 rb' u' t') env3" "(env', tps') = (env3, tps)"
      | (keep) "(env', tps') = (env2, add_tpair rb' t' u' tps)"
      by blast
    note hc = this
    have e3: "extends env2 env'"
      using hc
    proof cases
      case (fa1 env3)
      from dstepD(1)[OF ff_assign_sound[OF fa1(1)]] fa1(2) show ?thesis by simp
    next
      case (fa2 env3)
      from dstepD(1)[OF ff_assign_sound[OF fa2(1)]] fa2(2) show ?thesis by simp
    qed simp
    have tsol2: "tsol (tyenv env2) \<rho>" by (rule extends_tsol[OF tsol' e3])
    have tsol1: "tsol (tyenv env1) \<rho>" by (rule extends_tsol[OF tsol2 e2])
    let ?xs = "filter (\<lambda>j. j \<notin> set banned) (upto_list (length rb))"
    have b0: "\<forall>j\<in>set banned. 0 \<le> j" using ffc_banned(1)[OF fb] by blast
    have bn: "\<forall>j\<in>set banned. \<not> (loose_bvar1 t j \<and> loose_bvar1 u j)" using ffc_banned(3)[OF fb] by blast
    have bn': "\<forall>j\<in>set banned. \<not> (loose_bvar1 u j \<and> loose_bvar1 t j)" using bn by blast
    have xb: "set ?xs \<inter> set banned = {}" by auto
    have nbt: "nf_bounds (ap \<rho> \<sigma> t) 0 ?xs" by (rule ffc_nf_bounds_pair[OF bn eq wt_ap[OF tyt ws] cs lbt])
    have nbu: "nf_bounds (ap \<rho> \<sigma> u) 0 ?xs"
      by (rule ffc_nf_bounds_pair[OF bn' conv_sym[OF eq] wt_ap[OF tyu ws] cs lbu])
    text \<open>Cleaning the left-hand side:\<close>
    let ?Y = "X \<union> dvars (tdps tps) \<union> vars u"
    have vt: "vinv \<rho> env (?Y \<union> vars t)" using vi by (simp add: Un_ac)
    from clean_term_complete[OF main(1) sol wte vt tyt nbt xb b0 nrt] obtain \<sigma>1 where
      sol1: "solution \<rho> \<sigma>1 env1" and sa1: "sagree (maxidx env) \<sigma> \<sigma>1" by blast
    from ff_csoundD[OF cs1 tsol1 extends_refl wte bs tyt lbt vt]
    have r1: "wt_env \<rho> env1" "vinv \<rho> env1 (?Y \<union> vars t')" by blast+
    text \<open>Cleaning the right-hand side:\<close>
    have vu: "vinv \<rho> env1 ((X \<union> dvars (tdps tps) \<union> vars t') \<union> vars u)" using r1(2) by (simp add: Un_ac)
    have nbu1: "nf_bounds (ap \<rho> \<sigma>1 u) 0 ?xs" using nbu ap_sagree[OF sa1 belt(2)] by simp
    from clean_term_complete[OF main(2) sol1 r1(1) vu tyu nbu1 xb b0 nru] obtain \<sigma>2 where
      sol2: "solution \<rho> \<sigma>2 env2" and sa2: "sagree (maxidx env1) \<sigma>1 \<sigma>2" by blast
    have mx: "maxidx env \<le> maxidx env1" using e1 by (simp add: extends_def)
    have sa: "sagree (maxidx env) \<sigma> \<sigma>2" by (rule sagree_trans[OF sa1 sa2 mx])
    have ws2: "wt_subst \<sigma>2" by (rule solutionD(3)[OF sol2])
    text \<open>The cleaned pair is solved:\<close>
    have v0: "vinv \<rho> env (X \<union> dvars [(rb, t, u)])" using vi by (rule vinv_mono) auto
    from dstepD(2)[OF cl tsol2 extends_refl wte _ v0] dt
    have r2: "wt_env \<rho> env2" "dtyped \<rho> [(rb', t', u')]" by auto
    from r2(2) obtain e' T' where bs': "bs_env \<rho> e' rb'" and tyt': "e' \<turnstile> inst \<rho> t' : T'"
      and tyu': "e' \<turnstile> inst \<rho> u' : T'" and lbt': "\<not> loose_bvar t' (ilength rb')"
      and lbu': "\<not> loose_bvar u' (ilength rb')" by auto
    have c1: "ap \<rho> \<sigma>2 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma>2 t')"
      using cs1 tsol2 e2 wte bs tyt lbt vt sol2 unfolding csound_def by blast
    have vu': "vinv \<rho> env1 ((X \<union> dvars (tdps tps) \<union> vars t') \<union> vars u)" by (rule vu)
    have c2: "ap \<rho> \<sigma>2 u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma>2 u')"
      using cs2 tsol2 extends_refl r1(1) bs tyu lbu vu' sol2 unfolding csound_def by blast
    have "ap \<rho> \<sigma>2 t = ap \<rho> \<sigma> t" "ap \<rho> \<sigma>2 u = ap \<rho> \<sigma> u"
      using ap_sagree[OF sa belt(1)] ap_sagree[OF sa belt(2)] by simp_all
    with c1 c2 eq have cr: "rename F 0 (ap \<rho> \<sigma>2 t') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename F 0 (ap \<rho> \<sigma>2 u')"
      by (metis conv_sym conv_trans)
    have nF: "nonneg F" using F by (simp add: bren_ok_def)
    have tyr: "renv e F 0 \<turnstile> inst \<rho> t' : T"
      using ff_csoundD[OF cs1 tsol1 extends_refl wte bs tyt lbt vt] by blast
    have wr: "wt (rename F 0 (ap \<rho> \<sigma>2 t'))"
      using typing_rename[OF typing_ap[OF tyr ws2] refl nF order_refl] by (auto simp: wt_def)
    have cs2': "closed_subst \<sigma>2" using ws2 by (simp add: wt_subst_def)
    have eq2: "ap \<rho> \<sigma>2 t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>2 u'"
    proof (rule ffc_conv_unrename[OF cr wr wt_ap[OF tyt' ws2] wt_ap[OF tyu' ws2] nF])
      show "nonneg (\<lambda>k. max 0 (sqz banned k))" by (simp add: nonneg_def)
      show "max 0 (sqz banned (F p)) = p" if "0 \<le> p" "p < ilength rb'" for p using sq that by simp
      show "\<not> loose_bvar (ap \<rho> \<sigma>2 t') (ilength rb')" "\<not> loose_bvar (ap \<rho> \<sigma>2 u') (ilength rb')"
        using lbt' lbu' cs2' ilength_nonneg[of rb'] by (simp_all add: ap_def)
    qed
    have ds2: "dsolved \<rho> \<sigma>2 (tdps tps)" by (rule ffc_dsolved_agree[OF ds' sa belp])
    from hc show ?thesis
    proof cases
      case (fa1 env3)
      have "solution \<rho> \<sigma>2 env3"
        by (rule ff_assign_complete[OF fa1(1) _ sol2 r2(1) bs' tyt' tyu' lbu' eq2]) (use tsol' fa1(2) in simp)
      with fa1(2) sa ds2 show ?thesis by auto
    next
      case (fa2 env3)
      have "solution \<rho> \<sigma>2 env3"
        by (rule ff_assign_complete[OF fa2(1) _ sol2 r2(1) bs' tyu' tyt' lbt' conv_sym[OF eq2]])
          (use tsol' fa2(2) in simp)
      with fa2(2) sa ds2 show ?thesis by auto
    next
      case keep
      have "dsolved \<rho> \<sigma>2 ((rb', t', u') # tdps tps)" using eq2 ds2 by simp
      from add_tpair_complete[OF this r2(2) ws2] keep sol2 sa show ?thesis by auto
    qed
  qed
qed

subsection \<open>Flex-flex pairs\<close>

lemma ffc_swap:
  "dtyped \<rho> ((rb, t, u) # dps) \<Longrightarrow> dtyped \<rho> ((rb, u, t) # dps)"
  "vinv \<rho> env (X \<union> dvars ((rb, t, u) # dps)) \<Longrightarrow> vinv \<rho> env (X \<union> dvars ((rb, u, t) # dps))"
  "dsolved \<rho> \<sigma> ((rb, t, u) # dps) \<Longrightarrow> dsolved \<rho> \<sigma> ((rb, u, t) # dps)"
  by (auto simp: Un_ac intro: conv_sym)

subsection \<open>Normal forms of \<^const>\<open>norm_term\<close>\<close>

text \<open>\<^const>\<open>norm_term\<close> returns \<open>\<beta>\<close>-normal terms:\<close>

lemma no_redex_could_beta_contract: "\<not> could_beta_contract t \<Longrightarrow> no_redex t"
  by (induction t rule: could_beta_contract.induct) auto

lemma norm_term1_no_redex:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> no_redex t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "no_redex u'" if "ok (nt te u) u'" for u u' using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'" by auto
    then show ?thesis using IH Var by (cases lr) (auto simp: return_def)
  next
    case (Abs a T b)
    with h obtain b' where "ok (nt te b) b'" "t' = Abs a T b'" by auto
    with IH show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where "f = Abs a T b" by (cases f) auto
      with h App have "ok (nt te (subst_bound u b)) t'" by simp
      then show ?thesis by (rule IH)
    next
      case nf: False
      with h App obtain f' where f': "ok (nt te f) f'"
        and rest: "ok (case f' of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (f' $ nu)}) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs f'")
        case True
        then obtain a T b where "f' = Abs a T b" by (cases f') auto
        with rest show ?thesis by (simp add: IH)
      next
        case False
        with rest obtain u' where "ok (nt te u) u'" "t' = f' $ u'" by (cases f') auto
        with IH[OF f'] IH False show ?thesis by simp
      qed
    qed
  qed (use h in \<open>auto simp: return_def\<close>)
qed

lemma norm_term2_no_redex:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> no_redex t'"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "no_redex u'" if "ok (nt env u) u'" for u u' using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'" by auto
    then show ?thesis using IH by (cases lr) (auto simp: return_def)
  next
    case (Abs a T b)
    with h obtain T' b' where "ok (nt env b) b'" "t' = Abs a T' b'" by auto
    with IH show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where "f = Abs a T b" by (cases f) auto
      with h App have "ok (nt env (subst_bound u b)) t'" by simp
      then show ?thesis by (rule IH)
    next
      case nf: False
      with h App obtain f' where f': "ok (nt env f) f'"
        and rest: "ok (case f' of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (f' $ nu)}) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs f'")
        case True
        then obtain a T b where "f' = Abs a T b" by (cases f') auto
        with rest show ?thesis by (simp add: IH)
      next
        case False
        with rest obtain u' where "ok (nt env u) u'" "t' = f' $ u'" by (cases f') auto
        with IH[OF f'] IH False show ?thesis by simp
      qed
    qed
  qed (use h in \<open>auto simp: return_def\<close>)
qed

lemma norm_term_no_redex: "ok (norm_term env t) t' \<Longrightarrow> no_redex t'"
  unfolding norm_term_def
  by (auto simp: return_def no_redex_could_beta_contract split: if_splits
      dest: norm_term1_no_redex[OF _ refl] norm_term2_no_redex[OF _ refl])

theorem add_ffpair_complete:
  assumes af: "okW (add_ffpair alg' dp (env, tps)) (env', tps')" and tsol': "tsol (tyenv env') \<rho>"
    and sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and dt: "dtyped \<rho> (dp # tdps tps)"
    and vi: "vinv \<rho> env (X \<union> dvars (dp # tdps tps))" and ds: "dsolved \<rho> \<sigma> (dp # tdps tps)"
  shows "\<exists>\<sigma>'. solution \<rho> \<sigma>' env' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and> dsolved \<rho> \<sigma>' (tdps tps')"
proof -
  obtain rb t0 u0 where dp: "dp = (rb, t0, u0)" by (cases dp)
  from af dp obtain t u where nt: "ok (norm_term env t0) t" and nu: "ok (norm_term env u0) u"
    and rest: "okW (case (head_of t, head_of u) of
        (Var v T, Var w U) \<Rightarrow>
          if v = w then
            (if T = U then returnW (env, add_tpair rb t u tps)
             else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
          else if indexname_less v w then clean_ffpair alg' rb u t env tps
          else clean_ffpair alg' rb t u env tps
      | _ \<Rightarrow> raiseW (PExn (Term_Error (STR ''add_ffpair: Vars expected'') [t, u]))) (env', tps')"
    by (auto simp: add_ffpair_def)
  have tsol: "tsol (tyenv env) \<rho>" by (rule solutionD(2)[OF sol])
  have n: "dstep env ((rb, t0, u0) # tdps tps) env ((rb, t, u) # tdps tps)"
    using dstep_frame[where fs = "tdps tps", OF norm_term_dstep[where bs = rb, OF nt nu]] by simp
  from dstepD(2)[OF n tsol extends_refl wte, of X] dt vi dp
  have dt1: "dtyped \<rho> ((rb, t, u) # tdps tps)" and vi1: "vinv \<rho> env (X \<union> dvars ((rb, t, u) # tdps tps))"
    by blast+
  from dt dp obtain e T where tyt0: "e \<turnstile> inst \<rho> t0 : T" and tyu0: "e \<turnstile> inst \<rho> u0 : T" by auto
  have "ap \<rho> \<sigma> t0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" "ap \<rho> \<sigma> u0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    using nsoundD(4)[OF norm_term_sound[OF nt tsol wte] tyt0 sol]
      nsoundD(4)[OF norm_term_sound[OF nu tsol wte] tyu0 sol] by simp_all
  with ds dp have ds1: "dsolved \<rho> \<sigma> ((rb, t, u) # tdps tps)" by (auto intro: conv_sym conv_trans)
  from rest consider (same) "env' = env" "tps' = add_tpair rb t u tps"
    | (tu) "okW (clean_ffpair alg' rb t u env tps) (env', tps')"
    | (ut) "okW (clean_ffpair alg' rb u t env tps) (env', tps')"
    by (auto split: pterm.splits if_splits)
  then show ?thesis
  proof cases
    case same
    have "dtyped \<rho> [(rb, t, u)]" using dt1 by simp
    from add_tpair_complete[OF ds1 this solutionD(3)[OF sol]] same sol show ?thesis
      by (intro exI[of _ \<sigma>]) simp
  next
    case tu
    from clean_ffpair_complete[OF tu tsol' sol wte dt1 vi1 ds1 norm_term_no_redex[OF nt] norm_term_no_redex[OF nu]]
    show ?thesis .
  next
    case ut
    from clean_ffpair_complete[OF ut tsol' sol wte ffc_swap(1)[OF dt1] ffc_swap(2)[OF vi1] ffc_swap(3)[OF ds1]
        norm_term_no_redex[OF nu] norm_term_no_redex[OF nt]]
    show ?thesis .
  qed
qed

lemma foldrW_add_ffpair_complete_aux:
  "okW (foldrW (add_ffpair alg') ffs (env, tps)) (env', tps') \<Longrightarrow> tsol (tyenv env') \<rho> \<Longrightarrow>
    solution \<rho> \<sigma> env \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> (ffs @ tdps tps) \<Longrightarrow>
    vinv \<rho> env (X \<union> dvars (ffs @ tdps tps)) \<Longrightarrow> dsolved \<rho> \<sigma> (ffs @ tdps tps) \<Longrightarrow>
    \<exists>\<sigma>'. solution \<rho> \<sigma>' env' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and> dsolved \<rho> \<sigma>' (tdps tps')"
proof (induction ffs arbitrary: env' tps' X)
  case Nil
  then show ?case by (intro exI[of _ \<sigma>]) simp
next
  case (Cons dp ffs)
  from Cons.prems(1) obtain env1 tps1 where f: "okW (foldrW (add_ffpair alg') ffs (env, tps)) (env1, tps1)"
    and a: "okW (add_ffpair alg' dp (env1, tps1)) (env', tps')" by auto
  have ext1: "extends env1 env'" by (rule dstepD(1)[OF add_ffpair_sound[OF a]])
  have tsol1: "tsol (tyenv env1) \<rho>" by (rule extends_tsol[OF Cons.prems(2) ext1])
  have dvc: "dvars (dp # ffs @ tdps tps) = dvars [dp] \<union> dvars (ffs @ tdps tps)" by (simp add: dvars_def)
  have vi0: "vinv \<rho> env ((X \<union> dvars [dp]) \<union> dvars (ffs @ tdps tps))"
    using Cons.prems(6) dvc by (simp add: Un_ac)
  have dt0: "dtyped \<rho> (ffs @ tdps tps)" using Cons.prems(5) by (cases dp) simp
  have ds0: "dsolved \<rho> \<sigma> (ffs @ tdps tps)" using Cons.prems(7) by (cases dp) simp
  from Cons.IH[OF f tsol1 Cons.prems(3,4) dt0 vi0 ds0] obtain \<sigma>1 where
    sol1: "solution \<rho> \<sigma>1 env1" and sa1: "sagree (maxidx env) \<sigma> \<sigma>1" and dsl: "dsolved \<rho> \<sigma>1 (tdps tps1)"
    by blast
  have st: "dstep env (ffs @ tdps tps) env1 (tdps tps1)" by (rule foldrW_add_ffpair_sound[OF f])
  from dstepD(2)[OF st tsol1 extends_refl Cons.prems(4) dt0 vi0]
  have wte1: "wt_env \<rho> env1" and dtl: "dtyped \<rho> (tdps tps1)"
    and vil: "vinv \<rho> env1 ((X \<union> dvars [dp]) \<union> dvars (tdps tps1))" by blast+
  have "below (maxidx env) (dvars (dp # ffs @ tdps tps))" by (rule ffc_vinv_below[of _ _ X]) (use Cons.prems(6) in simp)
  then have bel: "below (maxidx env) (dvars [dp])" using dvc by (auto simp: below_def)
  have dsp: "dsolved \<rho> \<sigma>1 [dp]"
    by (rule ffc_dsolved_agree[OF _ sa1 bel]) (use Cons.prems(7) in \<open>cases dp; simp\<close>)
  have dt1: "dtyped \<rho> (dp # tdps tps1)" using dtl Cons.prems(5) by (cases dp) simp
  have vi1: "vinv \<rho> env1 (X \<union> dvars (dp # tdps tps1))" using vil by (cases dp) (simp add: Un_ac)
  have ds1: "dsolved \<rho> \<sigma>1 (dp # tdps tps1)" using dsp dsl by (cases dp) simp
  from add_ffpair_complete[OF a Cons.prems(2) sol1 wte1 dt1 vi1 ds1] obtain \<sigma>' where
    "solution \<rho> \<sigma>' env'" "sagree (maxidx env1) \<sigma>1 \<sigma>'" "dsolved \<rho> \<sigma>' (tdps tps')" by blast
  moreover have "maxidx env \<le> maxidx env1"
    using dstepD(1)[OF st] by (simp add: extends_def)
  ultimately show ?case using sagree_trans[OF sa1] by blast
qed

text \<open>
  Completeness of the treatment of the flex-flex pairs left by \<^const>\<open>SIMPL\<close>: it succeeds, and a
  solution of the pairs extends to a solution of the resulting environment and the remaining
  (closed) pairs, which satisfy the invariants again.
\<close>

theorem foldrW_add_ffpair_complete:
  assumes si: "sinv A K X env ffs" and sh: "\<forall>dp\<in>set ffs. ff_shape env dp \<and> ffeta env dp"
    and inv: "scinv \<rho> \<sigma> env ffs X A"
  shows "\<exists>env' tps' \<sigma>'. okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps') \<and>
    scinv \<rho> \<sigma>' env' (tdps tps') X A \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and> tyenv env' = tyenv env \<and>
    ffres A K (X \<union> dvars (tdps tps')) env' tps' \<and> extends env env'"
proof -
  from foldrW_add_ffpair_term_Nil[OF si sh] obtain env' tps' where
    f: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps')"
    and fr: "ffres A K (X \<union> dvars (tdps tps')) env' tps'" and ext: "extends env env'"
    and th: "tyenv env' = tyenv env" and ds: "dstep env ffs env' (tdps tps')" by blast
  note i = scinvD[OF inv]
  have p: "\<forall>(rb, t, u)\<in>set ffs. pok A env rb X t u" by (rule sc_sinv_pok[OF si])
  have tsol': "tsol (tyenv env') \<rho>" using solutionD(2)[OF i(1)] th by simp
  have dv: "dvars ffs \<subseteq> X \<union> evars env"
    using p unfolding dvars_def by (fastforce dest: pokD(1,2))
  have vi: "vinv \<rho> env (X \<union> dvars (ffs @ tdps []))"
    using vinv_hn[of \<rho> env X X "dvars ffs"] i(3) dv by simp
  from foldrW_add_ffpair_complete_aux[OF f tsol' i(1,2) _ vi] i(6,7) obtain \<sigma>' where
    sol': "solution \<rho> \<sigma>' env'" and sa: "sagree (maxidx env) \<sigma> \<sigma>'" and ds': "dsolved \<rho> \<sigma>' (tdps tps')"
    by auto
  have tv: "tvinv A env'" using fr by (simp add: ffres_def einv_def)
  have "scinv \<rho> \<sigma>' env' (tdps tps') X A"
    by (rule scinv_step[OF inv p ds sol' tagree_refl sa ds' tv]) (simp add: th)
  with f sa th fr ext show ?thesis by blast
qed

end

end
