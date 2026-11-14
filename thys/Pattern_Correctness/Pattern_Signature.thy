section \<open>The Signature of Pure\<close>

theory Pattern_Signature
  imports
    "Pure_Lambda.Pure_Normal"
    "Pure_Lambda.Pure_Subst"
    Type_Mgu
begin

text \<open>
  Terms are well-typed in a signature as \<open>Sign.cert_term\<close> checks them. The signature consists of
  the order-sorted algebra of type classes \<open>alg\<close>, the arities \<open>ar\<close> of the type constructors, and
  the declared types \<open>ctab\<close> of the constants (\<open>Consts.T\<close>).
  \<^item> A type is certified (\<open>Sign.certify_typ\<close>) if its type constructors have their arities and
    the classes of its sorts are declared.
  \<^item> A constant is used at an instance of its declared type (\<open>Consts.certify\<close>); the types of the
    constants \<^term>\<open>STR ''Pure.imp''\<close> and \<^term>\<open>STR ''Pure.all''\<close> of Pure's logic are built in.
    Declaration turns the fixed type variables of a declared type into schematic ones, so it has
    no \<open>TFree\<close>.
\<close>

fun sorts_ok :: "algebra \<Rightarrow> ptyp \<Rightarrow> bool" where
  "sorts_ok alg (Type a Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. sorts_ok alg T)"
| "sorts_ok alg (TFree a S) \<longleftrightarrow> sort_ok alg S"
| "sorts_ok alg (TVar v S) \<longleftrightarrow> sort_ok alg S"

definition cert_typ :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> ptyp \<Rightarrow> bool" where
  "cert_typ alg ar T \<longleftrightarrow> wft ar T \<and> sorts_ok alg T"

fun no_tfrees :: "ptyp \<Rightarrow> bool" where
  "no_tfrees (Type a Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. no_tfrees T)"
| "no_tfrees (TFree a S) \<longleftrightarrow> False"
| "no_tfrees (TVar v S) \<longleftrightarrow> True"

definition const_typ_ok :: "(name \<Rightarrow> ptyp option) \<Rightarrow> name \<Rightarrow> ptyp \<Rightarrow> bool" where
  "const_typ_ok ctab c T \<longleftrightarrow>
    (if c = STR ''Pure.imp'' then T = Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' []
     else if c = STR ''Pure.all'' then \<exists>U. T = (U \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []
     else \<exists>U \<rho>. ctab c = Some U \<and> no_tfrees U \<and> T = tsubst \<rho> U)"

text \<open>
  The locale \<open>pure_sig_gen\<close> has one further parameter, without assumptions, that relaxes the
  invariants of the unifiers: \<open>loose\<close> is a set of names of variables that may occur with several
  types. In the applications these are names that a run of a unifier leaves unbound
  (\<open>Envir.lookup\<close> raises an exception for an occurrence of a bound name at another type than
  that of its binding). Soundness of the unifiers is proved in \<open>pure_sig_gen\<close>. The locale
  \<open>pure_sig\<close> is the instance without loose names, in which every name has one type in every
  solution; the statements about termination and completeness, and the theorems on the kernel,
  are in it.
\<close>

locale pure_sig_gen = wf_algebra alg ar
  for alg :: algebra and ar :: "name \<Rightarrow> nat" +
  fixes ctab :: "name \<Rightarrow> ptyp option"
    and loose :: "indexname set"
begin

sublocale signature "cert_typ alg ar" "const_typ_ok ctab" .

notation typing (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50)
  and typings (\<open>_ \<tturnstile> _ : _\<close> [50, 50, 50] 50)
  and conv (infix \<open>\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>\<close> 50)

text \<open>
  Type instantiations that map type variables of certified sorts to certified types keep types
  and constants certified.
\<close>

definition cert_inst :: "tinst \<Rightarrow> bool" where
  "cert_inst \<rho> \<longleftrightarrow> (\<forall>v S. sort_ok alg S \<longrightarrow> cert_typ alg ar (\<rho> v S))"

lemma cert_typ_tsubst: "cert_typ alg ar T \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  by (induction T) (auto simp: cert_typ_def cert_inst_def)

lemma const_typ_ok_tsubst: "const_typ_ok ctab c T \<Longrightarrow> const_typ_ok ctab c (tsubst \<rho> T)"
  by (auto simp: const_typ_ok_def tsubst_tsubst split: if_splits)

lemma cert_inst_inst_ok: "cert_inst \<rho> \<Longrightarrow> inst_ok \<rho>"
  by (auto simp: inst_ok_def cert_typ_tsubst const_typ_ok_tsubst)

end

locale pure_sig = pure_sig_gen alg ar ctab "{}"
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and ctab :: "name \<Rightarrow> ptyp option"

lemma pure_sig_iff: "pure_sig alg ar \<longleftrightarrow> wf_algebra alg ar"
  by (simp add: pure_sig_def pure_sig_gen_def)

lemma pure_sig_wf: "pure_sig alg ar \<Longrightarrow> wf_algebra alg ar"
  by (simp add: pure_sig_iff)

end
