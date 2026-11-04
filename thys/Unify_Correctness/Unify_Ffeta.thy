section \<open>The Flex-Flex Pairs of \<open>SIMPL\<close> and their Treatment\<close>

theory Unify_Ffeta
  imports Unify_Flexflex_Term
begin

context pure_sig
begin

text \<open>
  The flex-flex pairs that \<^const>\<open>SIMPL\<close> returns need not be of a base type in the most general
  solution of the final type environment (\<^const>\<open>ffeta\<close>): \<^const>\<open>SIMPL0\<close> \<open>\<eta>\<close>-expands a pair in
  the type environment of the moment, and a later pair may bind a type variable of its type to a
  function type. For \<open>[([], ?F, ?K), ([], x = x, g = g), ([], ?F a, ?H)]\<close> with
  \<open>?F, ?K :: \<alpha> \<Rightarrow> ?'c\<close>, \<open>?H :: ?'c\<close>, \<open>x :: ?'c\<close> and \<open>g :: \<beta> \<Rightarrow> \<beta>\<close>, the pair \<open>?F a =?= ?H\<close> is kept
  as it is, the second pair binds \<open>?'c := \<beta> \<Rightarrow> \<beta>\<close>, and the first becomes
  \<open>?F B.1 B.0 =?= ?K B.1 B.0\<close>. The treatment by \<^const>\<open>add_ffpair\<close> starts with the last pair of
  the list, the oldest one; a pair that is not of a base type is kept (\<^const>\<open>clean_term\<close> fails
  with \<open>CHANGE_FAIL\<close> on its terms, which are not saturated), unless one of its head variables
  was assigned before, which would make it an abstraction (exception \<open>TERM\<close>). This does not
  happen: the number of arguments of a head variable never decreases from older to newer pairs
  (\<open>hmono\<close>), since each pair is saturated when it is created, in a type environment that
  extends those of the older pairs, and an assignment to a head variable comes from a pair in
  which it is saturated in the final type environment.
\<close>

subsection \<open>Heads and their numbers of arguments\<close>

definition hd1 :: "pterm \<Rightarrow> (indexname \<times> nat) set" where
  "hd1 s = {(F, length (snd (strip_comb s))) | F T. head_of s = Var F T}"

definition hds :: "dpair \<Rightarrow> (indexname \<times> nat) set" where
  "hds dp = (case dp of (rb, t, u) \<Rightarrow> hd1 t \<union> hd1 u)"

text \<open>The pair \<open>q\<close> is not older than \<open>q'\<close> in the numbers of arguments:\<close>

definition hle :: "dpair \<Rightarrow> dpair \<Rightarrow> bool" where
  "hle q' q \<longleftrightarrow> (\<forall>F m n. (F, m) \<in> hds q' \<longrightarrow> (F, n) \<in> hds q \<longrightarrow> m \<le> n)"

fun hmono :: "dpair list \<Rightarrow> bool" where
  "hmono [] = True"
| "hmono (q # qs) \<longleftrightarrow> (\<forall>q'\<in>set qs. hle q' q) \<and> hmono qs"

lemma hmono_append_Cons: "hmono (pre @ q # post) \<Longrightarrow> q' \<in> set pre \<Longrightarrow> hle q q'"
  by (induction pre) auto

lemma hmono_append: "hmono (pre @ post) \<Longrightarrow> hmono post"
  by (induction pre) auto

lemma hd1_typed:
  assumes "(F, m) \<in> hd1 s" "e \<turnstile> inst \<rho> s : V"
  shows "\<exists>T. (F, T) \<in> vars s \<and> arity (tsubst \<rho> T) = m + arity V"
proof -
  from assms(1) obtain T where h: "head_of s = Var F T" and m: "m = length (snd (strip_comb s))"
    by (auto simp: hd1_def)
  define ss where "ss = snd (strip_comb s)"
  have s: "s = Var F T \<degree>\<degree> ss" using t_apps[of s] h by (simp add: ss_def)
  from ff_typed_Var_apps[OF assms(2)[unfolded s]] obtain Us where
    "tsubst \<rho> T = Us \<Rrightarrow> V" "length Us = length ss" by blast
  then have "arity (tsubst \<rho> T) = m + arity V" by (simp add: arity_funs m ss_def)
  moreover have "(F, T) \<in> vars s" by (rule ff_head_of_vars[OF h])
  ultimately show ?thesis by blast
qed

text \<open>A pair typed in \<open>\<rho>\<close> is not newer than a pair of a base type in \<open>\<rho>\<close>:\<close>

lemma hle_typed:
  assumes vc: "vcons \<rho> Y" and vs: "vars t' \<union> vars u' \<union> vars t \<union> vars u \<subseteq> Y"
    and t': "e' \<turnstile> inst \<rho> t' : T'" and u': "e' \<turnstile> inst \<rho> u' : T'"
    and t: "e \<turnstile> inst \<rho> t : T" and u: "e \<turnstile> inst \<rho> u : T" and a0: "arity T = 0"
  shows "hle (rb', t', u') (rb, t, u)"
  unfolding hle_def
proof (intro allI impI)
  fix F m n assume m: "(F, m) \<in> hds (rb', t', u')" and n: "(F, n) \<in> hds (rb, t, u)"
  from m obtain s' where s': "s' \<in> {t', u'}" "(F, m) \<in> hd1 s'" by (auto simp: hds_def)
  from n obtain s where s: "s \<in> {t, u}" "(F, n) \<in> hd1 s" by (auto simp: hds_def)
  have "e' \<turnstile> inst \<rho> s' : T'" using s'(1) t' u' by blast
  from hd1_typed[OF s'(2) this] obtain V' where V': "(F, V') \<in> vars s'" "arity (tsubst \<rho> V') = m + arity T'"
    by blast
  have "e \<turnstile> inst \<rho> s : T" using s(1) t u by blast
  from hd1_typed[OF s(2) this] obtain V where V: "(F, V) \<in> vars s" "arity (tsubst \<rho> V) = n + arity T"
    by blast
  have "(F, V') \<in> Y" "(F, V) \<in> Y" using V'(1) V(1) s'(1) s(1) vs by blast+
  from vconsD[OF vc this] V'(2) V(2) a0 show "m \<le> n" by simp
qed

text \<open>A new pair of a base type keeps \<open>hmono\<close>:\<close>

lemma hmono_Cons_ffeta:
  assumes si: "sinv A K X env (dp # ffs)" and fe: "ffeta env dp" and hm: "hmono ffs"
  shows "hmono (dp # ffs)"
proof -
  have ei: "einv A K env" and wi: "winv env X" using si by (simp_all add: sinv_def)
  note r0 = einv_rho0[OF ei]
  let ?\<rho> = "rho0 env"
  have vc: "vcons ?\<rho> (X \<union> evars env)" using winvD[OF wi r0] by (simp add: vinv_def)
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have p: "pok A env rb X t u" using si dp by (simp add: sinv_def)
  from fe dp obtain e T where ty: "e \<turnstile> inst ?\<rho> t : T" "e \<turnstile> inst ?\<rho> u : T" "arity T = 0"
    by (auto simp: ffeta_def)
  have "hle q' dp" if q': "q' \<in> set ffs" for q'
  proof -
    obtain rb' t' u' where q'e: "q' = (rb', t', u')" by (cases q')
    have p': "pok A env rb' X t' u'" using si q' q'e by (auto simp: sinv_def)
    from pokD(9)[OF p' r0] obtain e' T' where ty': "e' \<turnstile> inst ?\<rho> t' : T'" "e' \<turnstile> inst ?\<rho> u' : T'" by blast
    have "vars t' \<union> vars u' \<union> vars t \<union> vars u \<subseteq> X \<union> evars env" using pokD(1,2)[OF p'] pokD(1,2)[OF p] by blast
    from hle_typed[OF vc this ty' ty] show ?thesis by (simp add: q'e dp)
  qed
  with hm show ?thesis by simp
qed

subsection \<open>The pairs of \<open>head_norm_dpair\<close> are of a base type\<close>

lemma new_dpair_nonAbs: "\<not> is_Abs t \<Longrightarrow> \<not> is_Abs u \<Longrightarrow> new_dpair al rb t u env = returnW ((rb, t, u), env)"
  by (cases t; cases u) auto

lemma new_dpair_Abs_nonAbs: "\<not> is_Abs u \<Longrightarrow> \<not> okW (new_dpair al rb (Abs a T b) u env) r"
  by (cases u) (auto simp: raiseW_def)

lemma new_dpair_nonAbs_Abs: "\<not> is_Abs t \<Longrightarrow> \<not> okW (new_dpair al rb t (Abs a T b) env) r"
  by (cases t) (auto simp: raiseW_def)

lemma new_dpair_base:
  assumes "okW (new_dpair al rb t u env) ((rb', t', u'), env')" "\<not> is_Abs t"
    "bs_env (rho0 env) e rb" "e \<turnstile> inst (rho0 env) t : T" "e \<turnstile> inst (rho0 env) u : T" "nabs t = arity T"
  shows "env' = env \<and> ffeta env (rb', t', u')"
proof (cases "is_Abs u")
  case True
  then obtain b Ub b2 where "u = Abs b Ub b2" by (cases u) auto
  with assms(1) new_dpair_nonAbs_Abs[OF assms(2)] show ?thesis by blast
next
  case False
  from assms(1) new_dpair_nonAbs[OF assms(2) False] have "rb' = rb" "t' = t" "u' = u" "env' = env"
    by (auto simp: returnW_def)
  then show ?thesis using assms(2-6) by (cases t) (auto simp: ffeta_def)
qed

text \<open>Stripping the common abstractions of two \<open>\<eta>\<close>-long terms of the same type does not change the
  environment and yields terms of a base type:\<close>

lemma new_dpair_ffeta:
  assumes ei: "einv A K env"
  shows "okW (new_dpair al rb t u env) ((rb', t', u'), env') \<Longrightarrow> bs_env (rho0 env) e rb \<Longrightarrow>
    e \<turnstile> inst (rho0 env) t : T \<Longrightarrow> e \<turnstile> inst (rho0 env) u : T \<Longrightarrow> nabs t = arity T \<Longrightarrow>
    ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> env' = env \<and> ffeta env (rb', t', u')"
proof (induction t arbitrary: u rb e T)
  case (Abs a Ta b1)
  let ?\<rho> = "rho0 env"
  note e = einvD[OF ei]
  show ?case
  proof (cases "is_Abs u")
    case True
    then obtain b Ub b2 where u: "u = Abs b Ub b2" by (cases u) auto
    from Abs.prems(3) obtain W where T: "T = tsubst ?\<rho> Ta \<rightarrow>\<^sub>T W" and c: "cert_typ alg ar (tsubst ?\<rho> Ta)"
      and t1: "e\<langle>0:tsubst ?\<rho> Ta\<rangle> \<turnstile> inst ?\<rho> b1 : W" by auto
    from Abs.prems(4) obtain W' where T': "T = tsubst ?\<rho> Ub \<rightarrow>\<^sub>T W'"
      and t2: "e\<langle>0:tsubst ?\<rho> Ub\<rangle> \<turnstile> inst ?\<rho> b2 : W'" by (auto simp: u)
    from T T' have eq: "tsubst ?\<rho> Ta = tsubst ?\<rho> Ub" and WW: "W' = W" by simp_all
    have kT: "tvars Ta \<subseteq> tvars_env (tyenv env) \<union> A" and kU: "tvars Ub \<subseteq> tvars_env (tyenv env) \<union> A"
      using Abs.prems(6) by (auto simp: ttvars_def u)
    have cu: "cunify_types al Ta Ub env = returnW env"
      by (rule cunify_types_same[OF e(6,7) tinv_tcons[OF e(2) kT] tinv_tcons[OF e(2) kU]]) (use eq in simp)
    let ?c = "if a = STR '''' then b else a"
    have nd: "okW (new_dpair al ((?c, Ta) # rb) b1 b2 env) ((rb', t', u'), env')"
      using Abs.prems(1) cu by (simp add: u Let_def)
    have bs: "bs_env ?\<rho> (e\<langle>0:tsubst ?\<rho> Ta\<rangle>) ((?c, Ta) # rb)" by (rule bs_env_Cons[OF Abs.prems(2) c])
    have t2': "e\<langle>0:tsubst ?\<rho> Ta\<rangle> \<turnstile> inst ?\<rho> b2 : W" using t2 eq WW by simp
    have na: "nabs b1 = arity W" using Abs.prems(5) T by simp
    have tv: "ttvars b1 \<union> ttvars b2 \<subseteq> tvars_env (tyenv env) \<union> A"
      using Abs.prems(6) by (auto simp: ttvars_def u)
    from Abs.IH[OF nd bs t1 t2' na tv] show ?thesis .
  next
    case False
    with new_dpair_Abs_nonAbs[OF this] Abs.prems(1) show ?thesis by blast
  qed
qed (erule new_dpair_base; simp)+

theorem head_norm_dpair_ffeta:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    and hn: "okW (head_norm_dpair al env (rb, t, u)) ((rb', t', u'), env')"
  shows "env' = env \<and> ffeta env (rb', t', u')"
proof -
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env" and ?e = "benv (rho0 env) rb"
  note e = einvD[OF ei]
  from hn_term[OF ei wi p] obtain t1 u1 where
    h: "head_norm env t = return t1" "head_norm env u = return u1" "pok A env rb X t1 u1" by blast
  from pok_unf[OF ei wi h(3)] obtain T where T: "bs_env ?\<rho> ?e rb" "?e \<turnstile> inst ?\<rho> t1 : T"
    "?e \<turnstile> inst ?\<rho> u1 : T" by blast
  note pd1 = pokD[OF h(3)]
  have tv1: "ttvars t1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A" "ttvars u1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
    using pd1(3-5) by blast+
  from eta_norm_term[OF e(2) refl T(2) T(1) pd1(7) tv1(1)] obtain t2 where
    t2: "eta_norm env rb t1 = return t2" "ttvars t2 \<subseteq> tvars_env ?\<theta> \<union> A" "nabs t2 = arity T"
    by blast
  from eta_norm_term[OF e(2) refl T(3) T(1) pd1(8) tv1(2)] obtain u2 where
    u2: "eta_norm env rb u1 = return u2" "ttvars u2 \<subseteq> tvars_env ?\<theta> \<union> A"
    by blast
  have ty2: "?e \<turnstile> inst ?\<rho> t2 : T"
    using eta_norm_sound[OF t2(1)[unfolded return_def]] einv_rho0(1)[OF ei] T(1,2) pd1(7) by blast
  have tyu2: "?e \<turnstile> inst ?\<rho> u2 : T"
    using eta_norm_sound[OF u2(1)[unfolded return_def]] einv_rho0(1)[OF ei] T(1,3) pd1(8) by blast
  have nd: "okW (new_dpair al rb t2 u2 env) ((rb', t', u'), env')"
    using hn by (simp add: head_norm_dpair_def h(1,2) t2(1) u2(1))
  from new_dpair_ffeta[OF ei nd T(1) ty2 tyu2 t2(3)] t2(2) u2(2) show ?thesis by blast
qed

subsection \<open>The flex-flex pairs of \<open>SIMPL0\<close>\<close>

lemma cuok_okW_P: "cuok m P \<Longrightarrow> okW m x \<Longrightarrow> P x"
  by (auto simp: cuok_def)

lemma spost_sinv_ffs:
  assumes "spost A K X env ffs frs (env', ffs', frs')" "sinv A K X env ffs"
  shows "sinv A K X env' ffs'"
proof -
  from assms(1) obtain a b where p: "ffs' = a @ ffs" "sinv A K X env' (a @ b)" "sstep K X env env'"
    unfolding spost_def by auto
  have "sinv A K X env' ffs" by (rule sinv_ext[OF assms(2)]) (use p(2,3) in \<open>simp_all add: sinv_def\<close>)
  from sinv_union[OF p(2) this, of ffs'] p(1) show ?thesis by auto
qed

lemma sinv_Cons: "sinv A K X env [dp] \<Longrightarrow> sinv A K X env ffs \<Longrightarrow> sinv A K X env (dp # ffs)"
  by (rule sinv_union[of A K X env "[dp]" ffs]) auto

context
  fixes A K X B
  assumes IHh: "\<And>env1 dp1 ffs1 frs1 env' ffs' frs'. (smeas K X env1 dp1, B) \<in> ulex \<Longrightarrow>
      sinv A K X env1 (dp1 # ffs1) \<Longrightarrow> hmono ffs1 \<Longrightarrow>
      okW (SIMPL0 alg dp1 (env1, ffs1, frs1)) (env', ffs', frs') \<Longrightarrow> hmono ffs'"
    and finX: "finite X" and finK: "finite K"
begin

lemma IH0: "(smeas K X env1 dp1, B) \<in> ulex \<Longrightarrow> sinv A K X env1 [dp1] \<Longrightarrow>
    cuok (SIMPL0 alg dp1 (env1, ffs1, frs1)) (spost A K X env1 ffs1 frs1)"
  by (rule SIMPL0_term[OF finX finK])

lemma simrands_hm:
  assumes hh: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u. h' = f $ u)"
    and B: "B = (card (uvarsA (tyenv env0) K), card (ubv env0 X), d0)"
  shows "length ss = length ts \<Longrightarrow> sinv A K X env (dzip rb ss ts) \<Longrightarrow> sstep K X env0 env \<Longrightarrow>
    (tyenv env = tyenv env0 \<Longrightarrow> tenv env = tenv env0 \<Longrightarrow> sum_list (map (dm env) (dzip rb ss ts)) < d0) \<Longrightarrow>
    sinv A K X env ffs \<Longrightarrow> hmono ffs \<Longrightarrow>
    okW (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow> hmono ffs'"
proof (induction ss arbitrary: ts ffs frs env env' ffs' frs' rule: rev_induct)
  case Nil
  then have "ts = []" by simp
  with Nil show ?case using simrands_atoms[OF hh] by simp
next
  case (snoc s ss)
  from snoc.prems(1) obtain ts' t where ts: "ts = ts' @ [t]" and len: "length ss = length ts'"
    by (cases ts rule: rev_exhaust) auto
  have dz: "dzip rb (ss @ [s]) ts = dzip rb ss ts' @ [(rb, s, t)]" using len ts by simp
  have si0: "sinv A K X env (dzip rb ss ts')" by (rule sinv_mono[OF snoc.prems(2)[unfolded dz]]) auto
  have lt0: "sum_list (map (dm env) (dzip rb ss ts')) < d0"
    if "tyenv env = tyenv env0" "tenv env = tenv env0" using snoc.prems(4)[OF that, unfolded dz] by simp
  from snoc.prems(7) obtain env1 ffs1 frs1 where
    r1: "okW (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts') (env, ffs, frs)) (env1, ffs1, frs1)"
    and r2: "okW (SIMPL0 alg (rb, s, t) (env1, ffs1, frs1)) (env', ffs', frs')"
    unfolding ts simrands_snoc by auto
  have hm1: "hmono ffs1" by (rule snoc.IH[OF len si0 snoc.prems(3) lt0 snoc.prems(5,6) r1])
  have sp1: "spost A K X env ffs frs (env1, ffs1, frs1)"
    by (rule cuok_okW_P[OF simrands_term[OF IH0 finX finK hh B len si0 snoc.prems(3) lt0] r1])
  from sp1 obtain a1 b1 where s1: "sinv A K X env1 (a1 @ b1)" "sstep K X env env1"
    unfolding spost_def by auto
  have si1: "sinv A K X env1 [(rb, s, t)]"
  proof (rule sinv_ext[OF sinv_mono[OF snoc.prems(2)] _ _ s1(2)])
    show "set [(rb, s, t)] \<subseteq> set (dzip rb (ss @ [s]) ts)" unfolding dz by simp
  qed (use s1(1) in \<open>simp_all add: sinv_def\<close>)
  have m: "(smeas K X env1 (rb, s, t), B) \<in> ulex" unfolding smeas_def B
  proof (rule ulex_sstep[OF sstep_trans[OF snoc.prems(3) s1(2)]])
    assume e1: "tyenv env1 = tyenv env0" "tenv env1 = tenv env0"
    have e0: "tyenv env = tyenv env0" "tenv env = tenv env0"
      using extends_mid[OF sstepD(1)[OF snoc.prems(3)] sstepD(1)[OF s1(2)]] e1 by auto
    then have "dm env1 = dm env" using e1 dm_same[of env1 env] by simp
    with snoc.prems(4)[OF e0, unfolded dz] show "dm env1 (rb, s, t) < d0" by simp
  qed
  have sf1: "sinv A K X env1 ffs1" by (rule spost_sinv_ffs[OF sp1 snoc.prems(5)])
  from IHh[OF m sinv_Cons[OF si1 sf1] hm1 r2] show ?case .
qed

lemma rigid_rigid_hm:
  assumes hp: "hpost A K X env0 dp0 (rb, t, u) env" and B: "B = smeas K X env0 dp0"
    and st2: "sstep K X env env2" and te2: "tenv env2 = tenv env" and ei2: "einv A K env2" and wi2: "winv env2 X"
    and rh: "rigid (head_of t)" "rigid (head_of u)"
    and hh: "\<And>\<rho>. tsol (tyenv env2) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> inst \<rho> (head_of t) = inst \<rho> (head_of u)"
    and sf: "sinv A K X env2 ffs" and hm: "hmono ffs"
    and r: "okW (simrands (SIMPL0 alg) rb u0 t u (env2, ffs, frs)) (env', ffs', frs')"
  shows "hmono ffs'"
proof -
  from hp have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    and st0: "sstep K X env0 env" and dmle: "tyenv env = tyenv env0 \<Longrightarrow> dm env (rb, t, u) \<le> dm env0 dp0"
    by (simp_all add: hpost_def)
  define h where "h = head_of t"
  define ss where "ss = snd (strip_comb t)"
  define h' where "h' = head_of u"
  define ts where "ts = snd (strip_comb u)"
  have tt: "t = h \<degree>\<degree> ss" unfolding h_def ss_def by (rule t_apps)
  have uu: "u = h' \<degree>\<degree> ts" unfolding h'_def ts_def by (rule t_apps)
  have p2: "pok A env2 rb X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)"
    using pok_mono[OF p sstepD(1,2)[OF st2]] tt uu by simp
  note ra = rigid_args_pok[OF p2 rh[folded h_def h'_def] hh[folded h_def h'_def] einv_rho0[OF ei2]]
  have si2: "sinv A K X env2 (dzip rb ss ts)" by (rule sinv_dzip[OF ei2 wi2 ra(2)])
  have B': "B = (card (uvarsA (tyenv env0) K), card (ubv env0 X), dm env0 dp0)" by (simp add: B smeas_def)
  have lt: "sum_list (map (dm env2) (dzip rb ss ts)) < dm env0 dp0"
    if e: "tyenv env2 = tyenv env0" "tenv env2 = tenv env0"
  proof -
    have e1: "tyenv env = tyenv env0" by (rule extends_mid(1)[OF sstepD(1)[OF st0] sstepD(1)[OF st2] e(1)])
    then have "dm env2 = dm env" using e(1) dm_same[OF te2] by simp
    moreover have "sum_list (map (dm env) (dzip rb ss ts)) < dm env (rb, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)"
      by (rule dm_args[OF ei wi p[unfolded tt uu] rh[folded h_def h'_def] ra(1)])
    ultimately show ?thesis using dmle[OF e1] tt uu by simp
  qed
  have hA: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u'. h' = f $ u')" unfolding h_def h'_def by (simp_all add: head_of_not_App)
  show ?thesis
    by (rule simrands_hm[OF hA B' ra(1) si2 sstep_trans[OF st0 st2] lt sf hm r[unfolded tt uu]])
qed

lemma SIMPL0_rest_hm:
  assumes hp: "hpost A K X env0 dp0 (rb, t, u) env" and B: "B = smeas K X env0 dp0"
    and fe: "ffeta env (rb, t, u)" and sf: "sinv A K X env ffs" and hm: "hmono ffs"
    and r: "okW (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (env', ffs', frs')"
  shows "hmono ffs'"
proof -
  from hp have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    and aht: "ahd env t" and ahu: "ahd env u"
    by (simp_all add: hpost_def)
  let ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 rb" "e0 \<turnstile> inst ?\<rho> t : T0" "e0 \<turnstile> inst ?\<rho> u : T0"
    using pd(9)[OF r0] by blast
  have tvh: "ttvars (head_of t) \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars (head_of u) \<subseteq> tvars_env (tyenv env) \<union> A"
    using ttvars_head[of t] ttvars_head[of u] pd(3,4) by blast+
  have FR: "hmono ffs'" if hv: "head_of t = Var F Ft" and hr: "rigid (head_of u)" for F Ft
  proof -
    have "okW (handleW (bindW (assignment alg rb t u env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
      using r hv hr by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    from assign_handle_sound[OF this] hm show ?thesis by simp
  qed
  have RF: "hmono ffs'" if hv: "head_of u = Var F Fu" and hr: "rigid (head_of t)" for F Fu
  proof -
    have "okW (handleW (bindW (assignment alg rb u t env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
      using r hv hr by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    from assign_handle_sound[OF this] hm show ?thesis by simp
  qed
  have CF: "hmono ffs'"
    if ht: "head_of t = hc" and hu: "head_of u = hd"
      and c: "(hc = Const a Tc \<and> hd = Const a Tu) \<or> (hc = Free a Tc \<and> hd = Free a Tu)"
      and eq: "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
        bindW (cunify_types alg Tc Tu env) (\<lambda>env'. simrands (SIMPL0 alg) rb u t u (env', ffs, frs))"
    for hc hd a Tc Tu
  proof -
    have cT: "cert_typ alg ar (tsubst ?\<rho> Tc)"
      using c head_Const_cert[OF ty0(2)] head_Free_cert[OF ty0(2)] ht by blast
    have cU: "cert_typ alg ar (tsubst ?\<rho> Tu)"
      using c head_Const_cert[OF ty0(3)] head_Free_cert[OF ty0(3)] hu by blast
    have kT: "tvars Tc \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(1) ht c by auto
    have kU: "tvars Tu \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(2) hu c by auto
    note cu = cunify_types_term[OF ei finK kT cert_typ_rev[OF ei cT kT] kU cert_typ_rev[OF ei cU kU]]
    from r[unfolded eq] obtain env2 where c2: "okW (cunify_types alg Tc Tu env) env2"
      and s2: "okW (simrands (SIMPL0 alg) rb u t u (env2, ffs, frs)) (env', ffs', frs')" by auto
    from cuok_okW_P[OF cu c2] have ei2: "einv A K env2" and te: "tenv env2 = tenv env"
      and tx: "textends (tyenv env) (tyenv env2)"
      and mx: "maxidx env \<le> maxidx env2" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)"
      and sol: "\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> Tc = tsubst \<rho> Tu"
      and card: "tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)"
      by blast+
    have rh: "rigid (head_of t)" "rigid (head_of u)" using ht hu c by auto
    have hh: "inst \<rho> (head_of t) = inst \<rho> (head_of u)" if "tsol (tyenv env2) \<rho>" for \<rho>
      using sol that ht hu c by auto
    have st2: "sstep K X env env2" by (rule sstep_tyext[OF te tx mx tv card])
    have wi2: "winv env2 X" by (rule winv_tyext[OF wi te tx mx])
    have sf2: "sinv A K X env2 ffs" by (rule sinv_ext[OF sf ei2 wi2 st2])
    show ?thesis by (rule rigid_rigid_hm[OF hp B st2 te ei2 wi2 rh hh sf2 hm s2])
  qed
  from ahd_head[OF aht] show ?thesis
  proof
    assume rt: "rigid (head_of t)"
    from ahd_head[OF ahu] show ?thesis
    proof
      assume ru: "rigid (head_of u)"
      show ?thesis
      proof (cases "head_of t")
        case (Const a Ta)
        show ?thesis
        proof (cases "\<exists>Tb. head_of u = Const a Tb")
          case True
          then obtain Tb where hb: "head_of u = Const a Tb" by blast
          show ?thesis
            by (rule CF[OF Const hb]) (simp_all add: SIMPL0_rest_def Const hb)
        next
          case False
          then show ?thesis using r Const ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      next
        case (Free a Ta)
        show ?thesis
        proof (cases "\<exists>Tb. head_of u = Free a Tb")
          case True
          then obtain Tb where hb: "head_of u = Free a Tb" by blast
          show ?thesis
            by (rule CF[OF Free hb]) (simp_all add: SIMPL0_rest_def Free hb)
        next
          case False
          then show ?thesis using r Free ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      next
        case (Bound i)
        show ?thesis
        proof (cases "head_of u = Bound i")
          case True
          have "okW (simrands (SIMPL0 alg) rb u t u (env, ffs, frs)) (env', ffs', frs')"
            using r by (simp add: SIMPL0_rest_def Bound True)
          from rigid_rigid_hm[OF hp B sstep_refl refl ei wi rt ru _ sf hm this] show ?thesis
            by (simp add: Bound True)
        next
          case False
          then show ?thesis using r Bound ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      qed (use rt in simp_all)
    next
      assume "\<exists>F U. head_of u = Var F U \<and> vt_lookup (tenv env) F = None"
      then obtain F U where "head_of u = Var F U" by blast
      from RF[OF this rt] show ?thesis .
    qed
  next
    assume "\<exists>F U. head_of t = Var F U \<and> vt_lookup (tenv env) F = None"
    then obtain F Ft where ht: "head_of t = Var F Ft" by blast
    from ahd_head[OF ahu] show ?thesis
    proof
      assume "rigid (head_of u)"
      from FR[OF ht this] show ?thesis .
    next
      assume "\<exists>G U. head_of u = Var G U \<and> vt_lookup (tenv env) G = None"
      then obtain G Gu where hu: "head_of u = Var G Gu" by blast
      from r have "ffs' = (rb, t, u) # ffs" by (auto simp: SIMPL0_rest_def ht hu)
      moreover have "sinv A K X env ((rb, t, u) # ffs)"
        by (rule sinv_Cons[OF _ sf]) (simp add: sinv_def ei wi p)
      ultimately show ?thesis using hmono_Cons_ffeta[OF _ fe hm] by simp
    qed
  qed
qed

lemma SIMPL0_step_hm:
  assumes B: "B = smeas K X env0 dp0" and si: "sinv A K X env0 (dp0 # ffs)" and hm: "hmono ffs"
    and r: "okW (SIMPL0 alg dp0 (env0, ffs, frs)) (env', ffs', frs')"
  shows "hmono ffs'"
proof -
  obtain rb t u where dp0: "dp0 = (rb, t, u)" by (cases dp0)
  from si dp0 have ei: "einv A K env0" and wi: "winv env0 X" and p: "pok A env0 rb X t u"
    and sf: "sinv A K X env0 ffs"
    by (simp_all add: sinv_def)
  from r[unfolded SIMPL0_unfold] obtain rb' t' u' env where
    hn: "okW (head_norm_dpair alg env0 dp0) ((rb', t', u'), env)"
    and rest: "okW (SIMPL0_rest SIMPL0 alg rb' t' u' env ffs frs) (env', ffs', frs')"
    by (auto split: prod.splits)
  have hp: "hpost A K X env0 dp0 (rb', t', u') env"
    using cuok_okW_P[OF head_norm_dpair_term[OF finK ei wi p, folded dp0] hn] by simp
  from head_norm_dpair_ffeta[OF ei wi p hn[unfolded dp0]] have e: "env = env0" and fe: "ffeta env (rb', t', u')"
    by simp_all
  show ?thesis by (rule SIMPL0_rest_hm[OF hp B fe sf[folded e] hm rest])
qed

end

theorem SIMPL0_hm:
  assumes fin: "finite X" "finite K"
  shows "sinv A K X env (dp # ffs) \<Longrightarrow> hmono ffs \<Longrightarrow> okW (SIMPL0 alg dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
    hmono ffs'"
proof -
  have "\<forall>env dp ffs frs env' ffs' frs'. smeas K X env dp = m \<longrightarrow> sinv A K X env (dp # ffs) \<longrightarrow> hmono ffs \<longrightarrow>
      okW (SIMPL0 alg dp (env, ffs, frs)) (env', ffs', frs') \<longrightarrow> hmono ffs'" for m
  proof (induction m rule: wf_induct_rule[OF wf_ulex])
    case (1 m)
    show ?case
    proof (intro allI impI)
      fix env dp ffs frs env' ffs' frs' assume m: "smeas K X env dp = m" and si: "sinv A K X env (dp # ffs)"
        and hm: "hmono ffs" and r: "okW (SIMPL0 alg dp (env, ffs, frs)) (env', ffs', frs')"
      show "hmono ffs'"
      proof (rule SIMPL0_step_hm[OF _ fin m[symmetric] si hm r])
        fix env1 dp1 ffs1 frs1 env2 ffs2 frs2 assume "(smeas K X env1 dp1, m) \<in> ulex" "sinv A K X env1 (dp1 # ffs1)"
          "hmono ffs1" "okW (SIMPL0 alg dp1 (env1, ffs1, frs1)) (env2, ffs2, frs2)"
        then show "hmono ffs2" using "1.IH" by blast
      qed
    qed
  qed
  then show "sinv A K X env (dp # ffs) \<Longrightarrow> hmono ffs \<Longrightarrow> okW (SIMPL0 alg dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
    hmono ffs'" by blast
qed

lemma foldrW_SIMPL0_hm:
  assumes fin: "finite X" "finite K"
  shows "sinv A K X env (dps @ ffs) \<Longrightarrow> hmono ffs \<Longrightarrow>
    okW (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow> hmono ffs'"
proof (induction dps arbitrary: env' ffs' frs')
  case Nil
  then show ?case by simp
next
  case (Cons dp dps)
  from Cons.prems(3) obtain env1 ffs1 frs1 where
    f1: "okW (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (env1, ffs1, frs1)"
    and s1: "okW (SIMPL0 alg dp (env1, ffs1, frs1)) (env', ffs', frs')"
    by auto
  have sd: "sinv A K X env dps" and sf: "sinv A K X env ffs" and sp: "sinv A K X env [dp]"
    using sinv_mono[OF Cons.prems(1)] by auto
  have hm1: "hmono ffs1" by (rule Cons.IH[OF sinv_mono[OF Cons.prems(1)] Cons.prems(2) f1]) auto
  have sp1: "spost A K X env ffs frs (env1, ffs1, frs1)"
    by (rule cuok_okW_P[OF foldrW_SIMPL0_term[OF fin sd] f1])
  from sp1 obtain a1 b1 where s1': "sinv A K X env1 (a1 @ b1)" "sstep K X env env1"
    unfolding spost_def by auto
  have "sinv A K X env1 [dp]"
    by (rule sinv_ext[OF sp _ _ s1'(2)]) (use s1'(1) in \<open>simp_all add: sinv_def\<close>)
  from SIMPL0_hm[OF fin sinv_Cons[OF this spost_sinv_ffs[OF sp1 sf]] hm1 s1] show ?case .
qed

lemma SIMPL_hm_aux:
  assumes fin: "finite X" "finite K" and r: "SIMPL al env dps = Some r"
  shows "al = alg \<Longrightarrow> snd r = UOk (env', ffs, frs) \<Longrightarrow> sinv A K X env dps \<Longrightarrow> hmono ffs"
  using r
proof (induction al env dps r arbitrary: env' ffs frs rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 simpl al env dps r)
  note al = "1.prems"(1)
  have IH: "hmono ffs2"
    if "okW (simpl al env1 dps1) (env2, ffs2, frs2)" "sinv A K X env1 dps1" for env1 dps1 env2 ffs2 frs2
  proof -
    from that obtain evs where "simpl al env1 dps1 = Some (evs, UOk (env2, ffs2, frs2))" by blast
    from "1.IH"[OF this al _ that(2)] show ?thesis by simp
  qed
  have "\<exists>env1 ffs1 frs1. okW (foldrW (SIMPL0 al) dps (env, [], [])) (env1, ffs1, frs1) \<and>
      (okW (simpl al env1 (frs1 @ ffs1)) (env', ffs, frs) \<or> (env', ffs, frs) = (env1, ffs1, frs1))"
    using okW_of_Some[OF "1.hyps" "1.prems"(2)] by (auto simp: Let_def split: prod.splits if_splits)
  then obtain env1 ffs1 frs1 where f: "okW (foldrW (SIMPL0 alg) dps (env, [], [])) (env1, ffs1, frs1)"
    and rest: "okW (simpl al env1 (frs1 @ ffs1)) (env', ffs, frs) \<or> (env', ffs, frs) = (env1, ffs1, frs1)"
    using al by blast
  have hm1: "hmono ffs1" by (rule foldrW_SIMPL0_hm[OF fin _ _ f]) (use "1.prems"(3) in simp_all)
  have "spost A K X env [] [] (env1, ffs1, frs1)"
    by (rule cuok_okW_P[OF foldrW_SIMPL0_term[OF fin "1.prems"(3)] f])
  then have "sinv A K X env1 (frs1 @ ffs1)" unfolding spost_def by (auto intro: sinv_mono)
  with rest IH[of env1 "frs1 @ ffs1"] hm1 show ?case by blast
qed

theorem SIMPL_hm:
  "finite X \<Longrightarrow> finite K \<Longrightarrow> sinv A K X env dps \<Longrightarrow> okW (SIMPL alg env dps) (env', ffs, frs) \<Longrightarrow> hmono ffs"
  using SIMPL_hm_aux by fastforce

subsection \<open>The variables that the treatment of a flex-flex pair assigns\<close>

text \<open>The new bindings of \<open>env'\<close> are for variables of \<open>S\<close>, and their bodies have heads in \<open>S\<close>:\<close>

definition nbin :: "indexname set \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "nbin S env env' \<longleftrightarrow> extends env env' \<and> (\<forall>x U b. vt_lookup (tenv env') x = Some (U, b) \<longrightarrow>
    vt_lookup (tenv env) x = None \<longrightarrow> x \<in> S \<and> (\<exists>G V. head_of (strip_abs_body b) = Var G V \<and> G \<in> S))"

abbreviation fr :: "env \<Rightarrow> indexname set" where
  "fr env \<equiv> {x. maxidx env < snd x}"

lemma nbin_refl: "nbin S env env"
  by (simp add: nbin_def)

lemma nbin_mono: "nbin S env env' \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> nbin S' env env'"
  unfolding nbin_def by blast

lemma nbin_trans:
  assumes 1: "nbin S env env1" and 2: "nbin S' env1 env2" and S: "S' \<subseteq> S"
  shows "nbin S env env2"
proof -
  have ext: "extends env env2" using 1 2 extends_trans by (auto simp: nbin_def)
  have "x \<in> S \<and> (\<exists>G V. head_of (strip_abs_body b) = Var G V \<and> G \<in> S)"
    if x2: "vt_lookup (tenv env2) x = Some (U, b)" and x0: "vt_lookup (tenv env) x = None" for x U b
  proof (cases "vt_lookup (tenv env1) x")
    case None
    with 2 S x2 show ?thesis unfolding nbin_def by blast
  next
    case (Some p)
    obtain U1 b1 where p: "p = (U1, b1)" by (cases p)
    from 2 Some have "vt_lookup (tenv env2) x = Some p" unfolding nbin_def extends_def by blast
    with x2 p have "U1 = U" "b1 = b" by simp_all
    with 1 Some p x0 show ?thesis unfolding nbin_def by blast
  qed
  with ext show ?thesis unfolding nbin_def by blast
qed

lemma nbin_tenv: "extends env env' \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> nbin S env env'"
  by (simp add: nbin_def)

lemma nbin_update:
  assumes u: "ok (update (F, T) t env) env'" and F: "F \<in> S" and h: "head_of (strip_abs_body t) = Var G V"
    and G: "G \<in> S"
  shows "nbin S env env'"
proof -
  note o = ok_update[OF u]
  have "x \<in> S \<and> (\<exists>G V. head_of (strip_abs_body b) = Var G V \<and> G \<in> S)"
    if x2: "vt_lookup (tenv env') x = Some (U, b)" and x0: "vt_lookup (tenv env) x = None" for x U b
  proof -
    from x2 x0 o(2) have "x = F" "b = t" by (auto split: if_splits)
    with F h G show ?thesis by blast
  qed
  with extends_update[OF u] show ?thesis unfolding nbin_def by blast
qed

lemma strip_abs_body_nonAbs: "\<not> is_Abs t \<Longrightarrow> strip_abs_body t = t"
  by (cases t) auto

lemma strip_abs_body_types_abs: "strip_abs_body (types_abs Ts b) = strip_abs_body b"
  by (induction Ts) auto

lemma clean_term_nbin:
  assumes ok: "okW (clean_term banned env t) (env', t')" and t: "t = Var v T0 \<degree>\<degree> ts"
    and v: "vt_lookup (tenv env) v = None" and vb: "snd v \<le> maxidx env" and bb: "bbelow env"
  shows "nbin ({v} \<union> fr env) env env' \<and> bbelow env' \<and>
    (\<exists>x X. head_of t' = Var x X \<and> x \<in> {v} \<union> fr env \<and> vt_lookup (tenv env') x = None)"
proof -
  have sc: "strip_comb t = (Var v T0, ts)" by (simp add: t strip_comb_atom_apps)
  let ?S = "{v} \<union> fr env"
  consider (dec) Ts cas where "decreasing (ilength Ts) (sort_args cas)" "env' = env"
      "t' = list_comb (Var v T0) (map fl_t (sort_args cas))"
    | (nd) Ts U fas cas env1 v' env2 where "ok (strip_type env T0) (Ts, U)"
      "okW (flexargs (downto0_list (length ts)) ts Ts) fas"
      "okW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) cas"
      "\<not> decreasing (ilength Ts) (sort_args cas)"
      "genvar (fst v) env (foldr fun_type (map fl_T (sort_args cas)) U) = (env1, v')"
      "ok (vupdate (v, T0) (types_abs Ts (list_comb v' (map (Bound \<circ> fl_j) (sort_args cas)))) env1) env2"
      "ok (norm_term env2 (list_comb v' (map fl_t (sort_args cas)))) t'" "env' = env2"
    using ok by (auto simp: clean_term_def sc Let_def split: prod.splits if_splits) blast+
  then show ?thesis
  proof cases
    case dec
    have "head_of t' = Var v T0" by (simp add: dec(3) list_comb_apps head_of_apps')
    with dec(2) v bb show ?thesis by (auto simp: nbin_refl)
  next
    case nd
    define args where "args = sort_args (cas :: flarg list)"
    define body where "body = list_comb v' (map (Bound \<circ> fl_j) args)"
    note gs = genvar_simps[OF nd(5)]
    have lTs: "length Ts = length ts" using flexargs_ok[OF nd(2)] by simp
    have Ts0: "Ts \<noteq> []"
    proof
      assume "Ts = []"
      with lTs have ts0: "ts = []" by simp
      have "fas = []" using flexargs_ok[OF nd(2)] ts0 by (cases fas) auto
      with nd(3) have "cas = []" by simp
      with nd(4) \<open>Ts = []\<close> show False by simp
    qed
    have upd: "ok (update (v, T0) (types_abs Ts body) env1) env2"
      using nd(6) ff_types_abs_Abs[OF Ts0, of body] unfolding body_def args_def
      by (subst (asm) vupdate.simps) (auto split: pterm.splits)
    note o = ok_update[OF upd]
    let ?G = "(fst v, maxidx env + 1)"
    have G: "vt_lookup (tenv env) ?G = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env) ?G \<noteq> None"
      then obtain b where "vt_lookup (tenv env) ?G = Some b" by blast
      from bbelowD[OF bb this] show False by simp
    qed
    have Gv: "?G \<noteq> v"
    proof
      assume "?G = v"
      then have "snd v = maxidx env + 1" by (metis snd_conv)
      with vb show False by simp
    qed
    have bh: "head_of (strip_abs_body (types_abs Ts body)) = Var ?G (foldr fun_type (map fl_T args) U)"
      using strip_abs_body_nonAbs[OF not_App_apps_Abs[of v' "map (Bound \<circ> fl_j) args"]]
      by (simp add: strip_abs_body_types_abs body_def gs(4) args_def list_comb_apps head_of_apps')
    have n1: "nbin ?S env env1" by (rule nbin_tenv[OF extends_genvar[OF nd(5)] gs(1)])
    have n2: "nbin ?S env1 env2" by (rule nbin_update[OF upd _ bh]) simp_all
    have "bbelow env2" unfolding bbelow_def
    proof (intro allI impI)
      fix x b assume "vt_lookup (tenv env2) x = Some b"
      then have "x = v \<or> vt_lookup (tenv env) x = Some b" using o(2) gs(1) by (auto split: if_splits)
      then show "snd x \<le> maxidx env2" using vb bbelowD[OF bb] o(4) gs(3) by fastforce
    qed
    moreover have "\<exists>x X. head_of t' = Var x X \<and> x \<in> ?S \<and> vt_lookup (tenv env2) x = None"
    proof -
      have G2: "vt_lookup (tenv env2) ?G = None" using G gs(1) o(2) Gv by simp
      from norm_term_head[OF nd(7) _ G2, of "foldr fun_type (map fl_T args) U"] obtain X' where
        "head_of t' = Var ?G X'" by (auto simp: gs(4) args_def list_comb_apps head_of_apps')
      with G2 show ?thesis by auto
    qed
    ultimately show ?thesis using nbin_trans[OF n1 n2 order_refl] nd(8) by blast
  qed
qed

end

end
