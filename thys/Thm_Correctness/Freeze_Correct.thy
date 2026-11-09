section \<open>Soundness of freezing schematic type variables\<close>

theory Freeze_Correct
  imports Instantiate_Correct
begin

text \<open>
  \<open>Thm.legacy_freezeT\<close> turns schematic type variables into free ones: an instance by a type
  instantiation.
\<close>

definition freeze_inst :: "(indexname \<times> name) list \<Rightarrow> tinst" where
  "freeze_inst alist v S = (case map_of alist v of Some a \<Rightarrow> TFree a S | None \<Rightarrow> TVar v S)"

lemma map_atyps_freeze_tvar: "map_atyps (freeze_tvar alist) T = tsubst (freeze_inst alist) T"
  by (induction T) (auto simp: freeze_tvar_def freeze_inst_def split: option.splits)

lemma map_types_tsubst: "map_types (tsubst \<rho>) t = inst \<rho> t"
  by (induction t) simp_all

lemma inst_list_implies: "inst \<rho> (list_implies As B) = list_implies (map (inst \<rho>) As) (inst \<rho> B)"
  by (induction As) simp_all

lemma ok_full_prop_of:
  assumes "ok (full_prop_of tps P) P1"
  obtains eqs where "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) tps eqs"
    "P1 = list_implies eqs P"
proof -
  from assms obtain eqs where m: "ok (mapM mk_equals tps) eqs" and P1: "P1 = list_implies eqs P"
    by (auto simp: full_prop_of_def)
  from m have "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) tps eqs"
    unfolding ok_mapM by (rule list_all2_mono) (auto simp: mk_equals_def split: prod.splits)
  from this P1 show thesis by (rule that)
qed

lemma ok_dest_equals_inst:
  assumes "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) tps eqs"
    "ok (mapM dest_equals xs) ys" "xs = rev (map (inst \<rho>) eqs)"
  shows "rev ys = map (\<lambda>(t, u). (inst \<rho> t, inst \<rho> u)) tps"
proof -
  have "list_all2 (\<lambda>q tu. ok (dest_equals q) tu) xs ys" using assms(2) by (simp add: ok_mapM)
  then have "list_all2 (\<lambda>q tu. ok (dest_equals q) tu) (map (inst \<rho>) eqs) (rev ys)"
    using assms(3) by (simp add: list_all2_rev1)
  then have L: "list_all2 (\<lambda>q tu. ok (dest_equals (inst \<rho> q)) tu) eqs (rev ys)" by (simp add: list_all2_map1)
  have "list_all2 (\<lambda>tu tu'. tu' = (inst \<rho> (fst tu), inst \<rho> (snd tu))) tps (rev ys)"
    by (rule list_all2_trans[OF _ assms(1) L]) (auto simp: dest_equals_def return_def)
  then show ?thesis by (induction rule: list_all2_induct) (auto split: prod.splits)
qed

context pure_model
begin

theorem legacy_freezeT_valid:
  assumes ok: "okT (legacy_freezeT vl th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)" and hv: "\<forall>h\<in>set hs. ttvars h = {}"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  from ok obtain P1 ts P3 tps0 where f: "ok (full_prop_of ?tps ?P) P1"
    and sp: "ok (strip_prems (integer_of_nat (length ?tps)) []
      (if legacy_freeze_names vl P1 = [] then P1 else map_types (map_atyps (freeze_tvar (legacy_freeze_names vl P1))) P1))
      (ts, P3)"
    and d: "ok (mapM dest_equals ts) tps0"
    and th: "th_tpairs th = rev tps0" "th_prop th = P3"
    by (auto simp: legacy_freezeT_def Let_def mk_rep_def split: prod.splits)
  define \<rho>0 where "\<rho>0 = freeze_inst (legacy_freeze_names vl P1)"
  have P2: "(if legacy_freeze_names vl P1 = [] then P1 else map_types (map_atyps (freeze_tvar (legacy_freeze_names vl P1))) P1)
      = inst \<rho>0 P1"
  proof (cases "legacy_freeze_names vl P1 = []")
    case True
    then have "\<rho>0 = TVar" by (auto simp: \<rho>0_def freeze_inst_def fun_eq_iff)
    with True show ?thesis by simp
  next
    case False
    then show ?thesis
      by (simp add: \<rho>0_def map_atyps_freeze_tvar[abs_def] map_types_tsubst[symmetric] comp_def)
  qed
  obtain eqs where eqs: "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) ?tps eqs"
    and P1: "P1 = list_implies eqs ?P"
    by (rule ok_full_prop_of[OF f])
  have l: "integer_of_nat (length ?tps) = ilength (map (inst \<rho>0) eqs)"
    using list_all2_lengthD[OF eqs] by (simp add: ilength_eq)
  from sp[unfolded P2, unfolded P1 inst_list_implies l strip_prems_list_implies]
  have "ts = rev (map (inst \<rho>0) eqs)" "P3 = inst \<rho>0 ?P" by (simp_all add: return_def)
  with ok_dest_equals_inst[OF eqs d] th
  have th': "th_tpairs th = map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) ?tps" "th_prop th = inst \<rho>0 ?P" by simp_all
  have c0: "cinst \<rho>0"
    unfolding cinst_def wsinst_def cert_inst_def
    by (auto simp: \<rho>0_def freeze_inst_def cert_typ_def has_sort_TFree_iff split: option.splits)
      (use class_le_refl in blast)+
  have sb: "sbound \<rho>0 Sh" by (auto simp: sbound_def \<rho>0_def freeze_inst_def split: option.splits)
  have hs: "map (inst \<rho>0) hs = hs"
  proof (rule map_idI)
    fix h assume "h \<in> set hs"
    with hv have "ttvars h = {}" by blast
    then show "inst \<rho>0 h = h" by (induction h) (auto simp: ttvars_def tsubst_no_tvars)
  qed
  from valid_tinst[OF v c0 subset_refl sb] show ?thesis by (simp add: th' hs)
qed

end

end
