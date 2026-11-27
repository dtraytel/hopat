section \<open>New Bindings\<close>

theory Pattern_Bindings
  imports Pattern_Vars
begin

subsection \<open>Integers and lists\<close>

lemmas integer_reps = nat_of_integer.rep_eq integer_of_nat.rep_eq integer_arith

lemma nat_of_integer_less_ilength: "0 \<le> i \<Longrightarrow> i < ilength xs \<Longrightarrow> nat_of_integer i < length xs"
  by (simp add: ilength_eq integer_reps)

lemma rev_nth_ilength:
  "p < length xs \<Longrightarrow> rev xs ! nat_of_integer (ilength xs - 1 - integer_of_nat p) = xs ! p"
  by (simp add: ilength_eq integer_reps rev_nth nat_diff_distrib)


subsection \<open>Function types\<close>

context signature
begin

lemma funs_eq:
  "length Ts = length Us \<Longrightarrow> Ts \<Rrightarrow> T = Us \<Rrightarrow> U \<longleftrightarrow> Ts = Us \<and> T = U"
  by (induction Ts Us rule: list_induct2) auto

end

lemma cert_typ_funs:
  "cert_typ alg ar (foldr (\<rightarrow>\<^sub>T) Ts T) \<longleftrightarrow> (\<forall>U\<in>set Ts. cert_typ alg ar U) \<and> cert_typ alg ar T"
  by (induction Ts) (auto simp: cert_typ_def tarity_def)

declare split_type.simps [simp del]

lemma ok_split_type:
  "ok (split_type T n Acc) (Us, U) \<Longrightarrow>
    \<exists>Vs. n = ilength Vs \<and> T = foldr (\<rightarrow>\<^sub>T) Vs U \<and> Us = rev Vs @ Acc"
proof (induction T n Acc rule: split_type.induct)
  case (1 T n Acc)
  show ?case
  proof (cases "n = 0")
    case True
    with "1.prems" show ?thesis by (simp add: split_type.simps)
  next
    case False
    with "1.prems" obtain T1 T2 where T: "T = T1 \<rightarrow>\<^sub>T T2"
      and r: "ok (split_type T2 (n - 1) (T1 # Acc)) (Us, U)"
      by (subst (asm) split_type.simps) (auto split: ptyp.splits list.splits if_splits)
    from "1.IH"[OF False T refl refl refl refl r] obtain Vs where
      "n - 1 = ilength Vs" "T2 = foldr (\<rightarrow>\<^sub>T) Vs U" "Us = rev Vs @ T1 # Acc"
      by blast
    with T show ?thesis by (intro exI[of _ "T1 # Vs"]) (simp add: integer_arith)
  qed
qed


subsection \<open>Iterated shifts\<close>

context signature
begin

lemma pushes_nth:
  "0 \<le> k \<Longrightarrow> pushes e Ts k = (if k < ilength Ts then rev Ts ! nat_of_integer k else e (k - ilength Ts))"
proof (induction Ts arbitrary: e)
  case (Cons T Ts)
  show ?case
  proof (cases "k < ilength Ts")
    case True
    then have "nat_of_integer k < length Ts" using Cons.prems by (simp add: nat_of_integer_less_ilength)
    with True Cons show ?thesis by (simp add: nth_append integer_arith)
  next
    case False
    then have "k - ilength Ts = 0 \<or> 0 < k - ilength Ts" by (simp add: integer_arith, linarith)
    moreover have "nat_of_integer k = length Ts" if "k - ilength Ts = 0"
      using that by (simp add: ilength_eq integer_reps)
    ultimately show ?thesis using False Cons by (auto simp: nth_append integer_arith diff_diff_eq)
  qed
qed simp

end


subsection \<open>Typing of new bindings\<close>

lemma tsubst_funs: "tsubst \<rho> (foldr (\<rightarrow>\<^sub>T) Ts T) = foldr (\<rightarrow>\<^sub>T) (map (tsubst \<rho>) Ts) (tsubst \<rho> T)"
  by (induction Ts) auto

lemma inst_apps: "inst \<rho> (s \<degree>\<degree> ts) = inst \<rho> s \<degree>\<degree> map (inst \<rho>) ts"
  by (induction ts arbitrary: s) auto

lemma length_ilength_eq: "ilength xs = ilength ys \<Longrightarrow> length xs = length ys"
  by (simp add: ilength_eq integer_reps)

lemma ilength_rev [simp]: "ilength (rev xs) = ilength xs"
  and ilength_map [simp]: "ilength (map f xs) = ilength xs"
  by (simp_all add: ilength_eq)

context pure_sig_gen
begin

lemma ap_apps: "ap \<rho> \<sigma> (s \<degree>\<degree> ts) = ap \<rho> \<sigma> s \<degree>\<degree> map (ap \<rho> \<sigma>) ts"
  by (induction ts arbitrary: s) auto

lemma ap_abs_list:
  "ap \<rho> \<sigma> (abs_list bs t) = abs_list (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs) (ap \<rho> \<sigma> t)"
  by (simp add: ap_def inst_abs_list vsubst_abs_list)

text \<open>The binders, instantiated by \<open>\<rho>\<close>, give the types of the bound variables:\<close>

definition bs_env :: "tinst \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow> bool" where
  "bs_env \<rho> e bs \<longleftrightarrow> (\<forall>i. 0 \<le> i \<longrightarrow> i < ilength bs \<longrightarrow> e i = tsubst \<rho> (snd (bs ! nat_of_integer i))) \<and>
    (\<forall>(x, T)\<in>set bs. cert_typ alg ar (tsubst \<rho> T))"

lemma typings_Bounds:
  "(\<And>k. k \<in> set ks \<Longrightarrow> 0 \<le> k \<and> e k = f k) \<Longrightarrow> e \<tturnstile> map Bound ks : map f ks"
  by (induction ks) auto

lemma typings_BoundsD: "e \<tturnstile> map Bound ks : Ts \<Longrightarrow> Ts = map e ks \<and> (\<forall>k\<in>set ks. 0 \<le> k)"
  by (induction ks arbitrary: Ts) (auto split: list.splits)

lemma type_of_G_sound:
  assumes "ok (type_of_G env Fty n ks) Gty" "tsol (tyenv env) \<rho>"
    "tsubst \<rho> Fty = Ts \<Rrightarrow> T" "ilength Ts = n"
  shows "tsubst \<rho> Gty = map (\<lambda>k. rev Ts ! nat_of_integer k) ks \<Rrightarrow> T"
    and "\<forall>k\<in>set ks. 0 \<le> k \<and> k < n"
proof -
  from assms(1) obtain T' Us0 U Us where nt: "ok (norm_type (tyenv env) Fty) T'"
    and st: "ok (split_type T' n []) (Us0, U)" and Us: "list_all2 (\<lambda>k U. ok (nth Us0 k) U) ks Us"
    and Gty: "Gty = Us \<Rrightarrow> U"
    by (auto simp: type_of_G_def ok_mapM)
  from ok_split_type[OF st] obtain Vs where Vs: "n = ilength Vs" "T' = Vs \<Rrightarrow> U" "Us0 = rev Vs"
    by auto
  have len: "length (map (tsubst \<rho>) Vs) = length Ts"
    using Vs(1) assms(4) length_ilength_eq[of Vs Ts] by simp
  from norm_type_sound[OF nt assms(2)] Vs(2) assms(3)
  have "map (tsubst \<rho>) Vs \<Rrightarrow> tsubst \<rho> U = Ts \<Rrightarrow> T" by (simp add: tsubst_funs)
  with funs_eq[OF len] have VT: "map (tsubst \<rho>) Vs = Ts" "tsubst \<rho> U = T" by simp_all
  from Us have ks: "\<forall>k\<in>set ks. 0 \<le> k \<and> k < n"
    and Us': "map (tsubst \<rho>) Us = map (\<lambda>k. rev Ts ! nat_of_integer k) ks"
  proof (induction rule: list_all2_induct)
    case (Cons k ks U Us)
    then have "0 \<le> k" "k < ilength Us0" "U = Us0 ! nat_of_integer k" by (simp_all add: ok_nth)
    moreover have "nat_of_integer k < length Vs"
      using calculation nat_of_integer_less_ilength[of k Vs] Vs(3) by simp
    ultimately show "\<forall>k\<in>set (k # ks). 0 \<le> k \<and> k < n"
      "map (tsubst \<rho>) (U # Us) = map (\<lambda>k. rev Ts ! nat_of_integer k) (k # ks)"
      using Cons Vs VT(1)[symmetric] by (auto simp: rev_map)
  qed simp_all
  show "\<forall>k\<in>set ks. 0 \<le> k \<and> k < n" by (rule ks)
  show "tsubst \<rho> Gty = map (\<lambda>k. rev Ts ! nat_of_integer k) ks \<Rrightarrow> T"
    using Gty Us' VT(2) by (simp add: tsubst_funs)
qed

text \<open>A new binding \<open>F := \<lambda>is. G ks\<close> (\<^const>\<open>mk_hnf\<close>) has the type of \<open>F\<close>.\<close>

lemma new_binding_typing:
  assumes u: "ok (mkabs bs is (app (Var G Gty) ks)) u" and bs: "bs_env \<rho> e bs"
    and F: "tsubst \<rho> Fty = Ts \<Rrightarrow> T" "cert_typ alg ar (tsubst \<rho> Fty)" and Ts: "map e is = Ts"
    and G: "tsubst \<rho> Gty = map (\<lambda>k. rev Ts ! nat_of_integer k) ks \<Rrightarrow> T"
    and ks: "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength is"
  shows "e' \<turnstile> inst \<rho> u : tsubst \<rho> Fty"
proof -
  from u have is_ok: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    and u': "u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (app (Var G Gty) ks)"
    by (simp_all add: ok_mkabs)
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)"
  have nth_in: "bs ! nat_of_integer i \<in> set bs" if "i \<in> set is" for i
    using is_ok that by (simp add: nat_of_integer_less_ilength)
  have types: "map snd ?bs = Ts"
    using Ts[symmetric] is_ok bs by (auto simp: bs_env_def split: prod.splits)
  have ok_bs: "\<forall>T\<in>snd ` set ?bs. cert_typ alg ar T"
    using bs nth_in by (fastforce simp: bs_env_def split: prod.splits)
  from F have cert: "\<forall>U\<in>set Ts. cert_typ alg ar U" "cert_typ alg ar T" by (simp_all add: cert_typ_funs)
  have len: "ilength Ts = ilength is" using Ts by auto
  have "pushes e' Ts \<turnstile> Var G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks : T"
  proof (rule list_app_typeI)
    have kin: "rev Ts ! nat_of_integer k \<in> set Ts" if "k \<in> set ks" for k
    proof -
      from ks that len have "0 \<le> k" "k < ilength Ts" by auto
      then have "nat_of_integer k < length (rev Ts)" using nat_of_integer_less_ilength by simp
      then show ?thesis by (metis nth_mem set_rev)
    qed
    have "cert_typ alg ar (tsubst \<rho> Gty)"
      using G cert kin by (auto simp: cert_typ_funs)
    then show "pushes e' Ts \<turnstile> Var G (tsubst \<rho> Gty) : map (\<lambda>k. rev Ts ! nat_of_integer k) ks \<Rrightarrow> T"
      using G by auto
    show "pushes e' Ts \<tturnstile> map Bound ks : map (\<lambda>k. rev Ts ! nat_of_integer k) ks"
      using ks len by (intro typings_Bounds) (simp add: pushes_nth)
  qed
  from typing_abs_list[OF this[folded types] ok_bs] types F(1)
  show ?thesis by (simp add: u' inst_abs_list app_apps inst_apps comp_def)
qed

text \<open>Applying the binding to bound variables renames the arguments of the new variable:\<close>

lemma binding_eqv:
  assumes lk: "vt_lookup (tenv env) F = Some (Fty, u)"
    and u: "u = abs_list bs (app (Var G Gty) ks)" "\<And>e. e \<turnstile> inst \<rho> u : tsubst \<rho> Fty"
    and ty: "e \<turnstile> inst \<rho> (app (Var F Fty) js) : T"
    and len: "length bs = length js" and ks: "\<forall>k\<in>set ks. 0 \<le> k"
  shows "eqv (binds \<rho> env) e (inst \<rho> (app (Var F Fty) js))
    (Var G (tsubst \<rho> Gty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks)"
    and "e \<turnstile> Var G (tsubst \<rho> Gty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks : T"
proof -
  from ty have tF: "e \<turnstile> Var F (tsubst \<rho> Fty) \<degree>\<degree> map Bound js : T"
    by (simp add: app_apps inst_apps comp_def)
  then obtain Us where vF: "e \<turnstile> Var F (tsubst \<rho> Fty) : Us \<Rrightarrow> T" and js: "e \<tturnstile> map Bound js : Us"
    by (rule list_app_typeE)
  then have F: "tsubst \<rho> Fty = Us \<Rrightarrow> T" by auto
  from typings_BoundsD[OF js] have js0: "\<forall>j\<in>set js. 0 \<le> j" by simp
  have tu: "e \<turnstile> inst \<rho> u \<degree>\<degree> map Bound js : T"
    using u(2) F js by (auto intro: list_app_typeI)
  have b: "(Var F (tsubst \<rho> Fty), inst \<rho> u) \<in> binds \<rho> env" unfolding binds_def using lk by blast
  have e1: "eqv (binds \<rho> env) e (Var F (tsubst \<rho> Fty) \<degree>\<degree> map Bound js) (inst \<rho> u \<degree>\<degree> map Bound js)"
    by (rule eqv_apps_head[OF eqv_ax[OF b vF] tF tu]) (use F u(2) in auto)
  have iu: "inst \<rho> u = abs_list (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs) (Var G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks)"
    by (simp add: u(1) inst_abs_list app_apps inst_apps comp_def)
  have r: "inst \<rho> u \<degree>\<degree> map Bound js \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bren (rev js)) 0 (Var G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks)"
    unfolding iu using beta_abs_list_apps[of "map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs" js] len js0 by simp
  have m: "map (rename (bren (rev js)) 0) (map Bound ks) = map (\<lambda>k. Bound (bren (rev js) k)) ks"
    using ks by (auto simp: integer_arith map_eq_conv)
  have rn: "rename (bren (rev js)) 0 (Var G (tsubst \<rho> Gty) \<degree>\<degree> map Bound ks) =
      Var G (tsubst \<rho> Gty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks"
    by (simp only: rename_apps m) simp
  have c: "inst \<rho> u \<degree>\<degree> map Bound js \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Var G (tsubst \<rho> Gty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks"
    using beta_eta_conv[OF beta_reds_beta_eta_reds[OF r]] tu by (auto simp: wt_def rn)
  show tG: "e \<turnstile> Var G (tsubst \<rho> Gty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks : T"
    using subject_reduction_beta'[OF r tu] rn by simp
  from eqv_trans[OF e1 eqv_conv[OF c tu tG]] show "eqv (binds \<rho> env) e (inst \<rho> (app (Var F Fty) js))
      (Var G (tsubst \<rho> Gty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks)"
    by (simp add: app_apps inst_apps comp_def)
qed

lemma binding_app:
  assumes sol: "solution \<rho> \<sigma> env" and lk: "vt_lookup (tenv env) F = Some (Fty, u)"
    and u: "u = abs_list bs (app (Var G Gty) ks)" "\<And>e. e \<turnstile> inst \<rho> u : tsubst \<rho> Fty"
    and ty: "e \<turnstile> inst \<rho> (app (Var F Fty) js) : T"
    and len: "length bs = length js" and ks: "\<forall>k\<in>set ks. 0 \<le> k"
  shows "ap \<rho> \<sigma> (app (Var F Fty) js) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> G (tsubst \<rho> Gty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks"
proof -
  let ?t = "Var G Gty \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks"
  have "inst \<rho> ?t = Var G (tsubst \<rho> Gty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev js) k)) ks"
    by (simp add: inst_apps comp_def)
  with binding_eqv(1)[OF lk u ty len ks] have "eqv (binds \<rho> env \<union> {}) e (inst \<rho> (app (Var F Fty) js)) (inst \<rho> ?t)"
    by simp
  from eqv_ap[OF this sol] show ?thesis by (simp add: ap_apps comp_def)
qed
end

end
