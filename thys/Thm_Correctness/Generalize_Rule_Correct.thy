section \<open>Soundness of the generalization of free variables\<close>

theory Generalize_Rule_Correct
  imports Generalize_Correct
begin

text \<open>
  \<open>Thm.generalize ([], frees) i\<close> turns the free variables with the names \<open>frees\<close>, which do not
  occur in the hypotheses, into schematic ones. It is sound if these names do not occur in the
  flex-flex pairs either: an instance that solves the generalized pairs need not solve the
  original ones.
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
    and nt: "\<And>t u b. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> b \<in> set frees \<Longrightarrow> b \<notin> fnames t \<and> b \<notin> fnames u"
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
  have tps: "map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps = ?tps"
    using nt by (auto intro!: map_idI simp: generalize_term_id)
  have wP: "wtp ?P" and hw: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h \<and> vars h = {}"
    and tw: "\<And>t u. (t, u) \<in> set ?tps \<Longrightarrow> closed t \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T)"
    using wt by (fastforce simp: wt_thm_def)+
  have "valid Sh hs ?tps (?gen ?P)"
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set ?tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    let ?\<eta> = "apv_t \<eta> \<rho>" and ?\<xi> = "apv_v \<eta> \<xi> \<rho> \<sigma>"
    let ?\<xi>2 = "(fst ?\<xi>, \<lambda>b U. if b \<in> set frees then fst ?\<xi> (clean_index (b, i)) U else snd ?\<xi> b U)"
    let ?Ts = "insert ?P (set hs \<union> fst ` set ?tps \<union> snd ` set ?tps)"
    define fs where "fs = remdups frees"
    define N where "N = (\<Union>t\<in>?Ts. fnames t) \<union> (\<Union>t\<in>?Ts. \<Union>(w, U)\<in>vars t. fnames (\<sigma> w (tsubst \<rho> U))) \<union> set frees"
    have "finite N" by (auto simp: N_def)
    then obtain Gs where Gs: "length Gs = length fs" "distinct Gs" "set Gs \<inter> N = {}"
      and K1: "\<And>c. c \<in> set fs \<Longrightarrow> \<exists>G. map_of (zip fs Gs) c = Some G \<and> G \<in> set Gs \<and> map_of (zip Gs fs) G = Some c"
      by (rule fresh_renaming[of N fs]) (simp_all add: fs_def)
    have sfs: "set fs = set frees" by (simp add: fs_def)
    define f where "f = (\<lambda>b (V :: ptyp). case map_of (zip fs Gs) b of Some G \<Rightarrow> G | None \<Rightarrow> b)"
    define \<sigma>' where "\<sigma>' = (\<lambda>w U. frename f (\<sigma> w U))"
    define \<xi>' where "\<xi>' = (fst \<xi>, \<lambda>b V. if b \<in> set frees then sem \<eta> \<xi> (\<lambda>_. utrue) (\<sigma> (clean_index (b, i)) V)
      else (case map_of (zip Gs fs) b of Some c \<Rightarrow> snd \<xi> c V | None \<Rightarrow> snd \<xi> b V))"
    have M1: "map_of (zip fs Gs) b = None" if "b \<notin> set frees" for b
      using that Gs(1)[symmetric] by (simp add: sfs)
    have M2: "map_of (zip Gs fs) b = None" if "b \<notin> set Gs" for b
      using that Gs(1) by simp
    have fid: "f b V = b" if "b \<notin> set frees" for b V
      using M1[OF that] by (simp add: f_def)
    have GN: "G \<notin> N" if "G \<in> set Gs" for G using Gs(3) that by blast
    note \<sigma>c = closed_substD[OF gsubstD(2)[OF \<sigma>]]
    have \<sigma>t: "cert_typ alg ar U \<Longrightarrow> e \<turnstile> \<sigma> w U : U" for w U e
      using wt_subst_typing[OF gsubstD(1)[OF \<sigma>]] by blast
    have g': "good \<eta> \<xi>'"
    proof -
      have "sem \<eta> \<xi> (\<lambda>_. utrue) (\<sigma> w V) \<in>\<^sub>u tsem \<eta> V" if "cert_typ alg ar V" for w V
        using sem_typing[OF g \<sigma>t[OF that], of "\<lambda>_. propT"] by (simp add: bvals_def ubool_mem)
      with g show ?thesis by (auto simp: good_def good_v_def \<xi>'_def split: option.splits)
    qed
    have \<sigma>': "gsubst \<sigma>'"
      using \<sigma>c \<sigma>t by (fastforce simp: gsubst_def wt_subst_def closed_subst_def closed_def \<sigma>'_def intro: typing_frename)
    \<comment> \<open>the renamed substitution has the same values\<close>
    have sv: "sem \<eta> \<xi>' bv (\<sigma>' w (tsubst \<rho> U)) = sem \<eta> \<xi> bv (\<sigma> w (tsubst \<rho> U))"
      if "t \<in> ?Ts" "(w, U) \<in> vars t" for t w U bv
    proof -
      have "snd \<xi>' (f c V) V = snd \<xi> c V" if c: "(c, V) \<in> pfrees (\<sigma> w (tsubst \<rho> U))" for c V
      proof -
        have "c \<in> fnames (\<sigma> w (tsubst \<rho> U))" using c by (force simp: fnames_pfrees)
        moreover have "fnames (\<sigma> w (tsubst \<rho> U)) \<subseteq> N"
          using \<open>t \<in> ?Ts\<close> \<open>(w, U) \<in> vars t\<close> unfolding N_def by blast
        ultimately have cN: "c \<in> N" by blast
        show ?thesis
        proof (cases "c \<in> set frees")
          case True
          then obtain G where "map_of (zip fs Gs) c = Some G" "G \<in> set Gs" "map_of (zip Gs fs) G = Some c"
            using K1 sfs by blast
          moreover from this(2) have "G \<notin> set frees" using GN by (auto simp: N_def)
          ultimately show ?thesis by (simp add: f_def \<xi>'_def)
        next
          case False
          moreover have "c \<notin> set Gs" using cN GN by blast
          ultimately show ?thesis by (simp add: fid M2 \<xi>'_def)
        qed
      qed
      then show ?thesis unfolding \<sigma>'_def by (intro sem_frename) (simp_all add: \<xi>'_def)
    qed
    have agree: "sem ?\<eta> (apv_v \<eta> \<xi>' \<rho> \<sigma>') bv t = sem ?\<eta> ?\<xi>2 bv t" if "t \<in> ?Ts" for t bv
    proof (rule sem_agree)
      fix w U assume "(w, U) \<in> vars t"
      with sv[OF that this] show "fst (apv_v \<eta> \<xi>' \<rho> \<sigma>') w U = fst ?\<xi>2 w U"
        by (simp add: apv_v_def vinstv_def vsubstv_def \<xi>'_def)
    next
      fix b U assume bU: "(b, U) \<in> pfrees t"
      then have "b \<in> fnames t" by (force simp: fnames_pfrees)
      then have bN: "b \<in> N" using that unfolding N_def by blast
      show "snd (apv_v \<eta> \<xi>' \<rho> \<sigma>') b U = snd ?\<xi>2 b U"
      proof (cases "b \<in> set frees")
        case True
        then show ?thesis
          using sem_closed[OF \<sigma>c[of "clean_index (b, i)" "tsubst \<rho> U"], of \<eta> \<xi> "\<lambda>_. utrue" "\<lambda>_. undefined"]
          by (simp add: apv_v_def vinstv_def vsubstv_def \<xi>'_def)
      next
        case False
        moreover have "b \<notin> set Gs" using bN GN by blast
        ultimately show ?thesis by (simp add: M2 apv_v_def vinstv_def vsubstv_def \<xi>'_def)
      qed
    qed
    have "holds_at \<eta> \<xi>' (ap \<rho> \<sigma>' ?P)"
    proof (rule validD[OF v sh g' \<rho> \<rho>i \<sigma>'])
      fix t u assume tu: "(t, u) \<in> set ?tps"
      have e: "ap \<rho> \<sigma>' s = frename f (ap \<rho> \<sigma> s)" if "s = t \<or> s = u" for s
      proof -
        have "f b (tsubst \<rho> U) = b" if "(b, U) \<in> pfrees s" for b U
        proof (rule fid)
          have "b \<in> fnames s" using that by (force simp: fnames_pfrees)
          with nt[OF tu, of b] \<open>s = t \<or> s = u\<close> show "b \<notin> set frees" by blast
        qed
        then show ?thesis using ap_frename[of s f \<rho> \<sigma>] by (simp add: \<sigma>'_def)
      qed
      from tw[OF tu] obtain U where ct: "closed t" and tt: "\<And>e. e \<turnstile> t : U" by blast
      have "gterm (ap \<rho> \<sigma> t) (tsubst \<rho> U)" by (rule gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma> ct tt])
      then have "wt (ap \<rho> \<sigma> t)" unfolding gterm_def wt_def by blast
      with conv_frename[OF this sol[OF tu]] e show "ap \<rho> \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u" by simp
    next
      fix h assume h: "h \<in> set hs"
      have hT: "h \<in> ?Ts" using h by simp
      have "sem \<eta> \<xi>' (\<lambda>_. utrue) (ap \<rho> \<sigma>' h) = sem ?\<eta> (apv_v \<eta> \<xi>' \<rho> \<sigma>') (\<lambda>_. utrue) h"
        by (rule sem_ap[OF gsubstD(1)[OF \<sigma>'] wtpD(2)[of h "\<lambda>_. propT"]]) (use hw h in blast)
      also have "\<dots> = sem ?\<eta> ?\<xi>2 (\<lambda>_. utrue) h" by (rule agree[OF hT])
      also have "\<dots> = sem ?\<eta> ?\<xi> (\<lambda>_. utrue) h"
        using bad_term_frees[OF nb[OF h]] by (intro sem_agree) auto
      also have "\<dots> = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> h)"
        by (rule sem_ap[OF gsubstD(1)[OF \<sigma>] wtpD(2)[of h "\<lambda>_. propT"], symmetric]) (use hw h in blast)
      finally show "holds_at \<eta> \<xi>' (ap \<rho> \<sigma>' h)" using hh[OF h] by (simp add: holds_at_def)
    qed
    then have "sem ?\<eta> ?\<xi>2 (\<lambda>_. utrue) ?P = utrue"
      using sem_ap[OF gsubstD(1)[OF \<sigma>'] wtpD(2)[OF wP]] agree[of ?P] by (simp add: holds_at_def)
    moreover have "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> (?gen ?P)) = sem ?\<eta> ?\<xi> (\<lambda>_. utrue) (?gen ?P)"
      by (rule sem_ap[OF gsubstD(1)[OF \<sigma>] typing_generalize_term[OF wtpD(2)[OF wP]]])
    ultimately show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (?gen ?P))"
      by (simp add: holds_at_def sem_generalize_term)
  qed
  then show ?thesis using th tps by simp
qed

end

end
