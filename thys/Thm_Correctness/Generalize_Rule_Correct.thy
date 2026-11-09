section \<open>Soundness of the generalization of free variables\<close>

theory Generalize_Rule_Correct
  imports Generalize_Correct
begin

text \<open>
  \<open>Thm.generalize ([], frees) i\<close> turns the free variables with the names \<open>frees\<close>, which do not
  occur in the hypotheses, into schematic ones, in the proposition and in the flex-flex pairs.
\<close>

lemma generalizeT_Nil [simp]: "generalizeT [] i T = T"
  by (induction "[] :: name list" i T rule: generalizeT.induct) (simp_all add: map_idI)

lemma generalize_term_id:
  "(\<And>b. b \<in> set frees \<Longrightarrow> b \<notin> fnames t) \<Longrightarrow> generalize_term [] frees i t = t"
  by (induction t) auto

lemma loose_bvar_generalize_term [simp]: "loose_bvar (generalize_term [] frees i t) k \<longleftrightarrow> loose_bvar t k"
  by (induction t arbitrary: k) simp_all

lemma bad_term_frees: "\<not> bad_term [] frees t \<Longrightarrow> (b, U) \<in> pfrees t \<Longrightarrow> b \<notin> set frees"
  by (induction t) (auto split: if_splits)

lemma fresh_renaming:
  assumes "finite (N :: name set)" "distinct fs"
  obtains Gs where "length Gs = length fs" "distinct Gs" "set Gs \<inter> N = {}"
    "\<And>c. c \<in> set fs \<Longrightarrow> \<exists>G. map_of (zip fs Gs) c = Some G \<and> G \<in> set Gs \<and> map_of (zip Gs fs) G = Some c"
proof -
  obtain Gs where Gs: "length Gs = length fs" "distinct Gs" "set Gs \<inter> N = {}"
    by (rule fresh_name_list[OF assms(1)])
  have "\<exists>G. map_of (zip fs Gs) c = Some G \<and> G \<in> set Gs \<and> map_of (zip Gs fs) G = Some c" if "c \<in> set fs" for c
  proof -
    from that obtain i where i: "i < length fs" "fs ! i = c" by (auto simp: in_set_conv_nth)
    have "map_of (zip fs Gs) c = Some (Gs ! i)" using map_of_zip_nth[of fs Gs i] Gs(1) assms(2) i by simp
    moreover have "map_of (zip Gs fs) (Gs ! i) = Some c" using map_of_zip_nth[of Gs fs i] Gs(1,2) i by simp
    ultimately show ?thesis using Gs(1) i by auto
  qed
  with Gs show thesis by (intro that) auto
qed

context pure_model
begin

lemma typing_generalize_term: "e \<turnstile> t : T \<Longrightarrow> e \<turnstile> generalize_term [] frees i t : T"
  by (induction rule: typing.induct) auto

lemma sem_generalize_term:
  "sem \<eta> \<xi> bv (generalize_term [] frees i t) =
    sem \<eta> (fst \<xi>, \<lambda>b U. if b \<in> set frees then fst \<xi> (clean_index (b, i)) U else snd \<xi> b U) bv t"
  by (induction t arbitrary: bv) auto

theorem generalize_valid:
  assumes ok: "okT (generalize [] frees i hs th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof (cases "frees = []")
  case True
  with ok have "th = th0" by (simp add: generalize_def returnW_def)
  with v show ?thesis by simp
next
  case False
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0" and ?gen = "generalize_term [] frees i"
  from ok False have nb: "\<And>h. h \<in> set hs \<Longrightarrow> \<not> bad_term [] frees h"
    and th: "th_tpairs th = map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps" "th_prop th = ?gen ?P"
    by (auto simp: generalize_def returnW_def raiseW_def Let_def mk_rep_def split: if_splits)
  have wf: "wf_terms hs ?tps ?P" by (rule wt_thm_wf_terms[OF wt])
  have ge: "gterm (?gen t) T" if "gterm t T" for t T
    using that typing_generalize_term by (simp add: gterm_def closed_def)
  have wf': "wf_terms hs (map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps) (?gen ?P)"
    using wf ge by (fastforce simp: wf_terms_def)
  let ?\<xi>2 = "\<lambda>\<xi>. (fst \<xi>, \<lambda>b U. if b \<in> set frees then fst \<xi> (clean_index (b, i)) U else snd \<xi> b U)"
  have "svalid Sh hs (map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps) (?gen ?P)"
  proof (rule svalidI)
    fix \<eta> \<xi> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>"
      and tp: "\<And>t u. (t, u) \<in> set (map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps) \<Longrightarrow> eq_at \<eta> \<xi> t u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> h"
    have g2: "good \<eta> (?\<xi>2 \<xi>)"
      unfolding good_def good_v_def using goodD[OF g] by (auto simp del: split_paired_All)
    have "holds_at \<eta> (?\<xi>2 \<xi>) ?P"
    proof (rule svalidD[OF v[unfolded valid_svalid[OF wf]] sh g2])
      fix t u assume tu: "(t, u) \<in> set ?tps"
      then have "(?gen t, ?gen u) \<in> set (map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps)" by force
      from tp[OF this] show "eq_at \<eta> (?\<xi>2 \<xi>) t u" by (simp add: eq_at_def sem_generalize_term)
    next
      fix h assume h: "h \<in> set hs"
      have "sem \<eta> (?\<xi>2 \<xi>) (\<lambda>_. utrue) h = sem \<eta> \<xi> (\<lambda>_. utrue) h"
        using bad_term_frees[OF nb[OF h]] by (intro sem_agree) auto
      with hh[OF h] show "holds_at \<eta> (?\<xi>2 \<xi>) h" by (simp add: holds_at_def)
    qed
    then show "holds_at \<eta> \<xi> (?gen ?P)" by (simp add: holds_at_def sem_generalize_term)
  qed
  with valid_svalid[OF wf'] th show ?thesis by simp
qed

end

end
