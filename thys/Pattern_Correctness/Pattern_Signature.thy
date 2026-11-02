section \<open>The Signature of Pure\<close>

theory Pattern_Signature
  imports
    "Pure_Lambda.Pure_Normal"
    "Pure_Lambda.Pure_Subst"
    "Pure_Pattern_Correctness.Type_Mgu"
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

lemma tinst_tsubst: "tinst = tsubst"
proof (intro ext)
  show "tinst \<rho> T = tsubst \<rho> T" for \<rho> T by (induction T) auto
qed

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

locale pure_sig = wf_algebra alg ar
  for alg :: algebra and ar :: "name \<Rightarrow> nat" +
  fixes ctab :: "name \<Rightarrow> ptyp option"
begin

sublocale signature "cert_typ alg ar" "const_typ_ok ctab" .

text \<open>
  Type instantiations that respect sorts and map to certified types keep types and constants
  certified.
\<close>

definition tinst_ok :: "(indexname \<Rightarrow> psort \<Rightarrow> ptyp) \<Rightarrow> bool" where
  "tinst_ok \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> (\<forall>v S. cert_typ alg ar (\<rho> v S))"

lemma cert_typ_tsubst: "cert_typ alg ar T \<Longrightarrow> tinst_ok \<rho> \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  by (induction T) (auto simp: cert_typ_def tinst_ok_def)

lemma tsubst_tsubst: "tsubst \<rho> (tsubst \<rho>' T) = tsubst (\<lambda>v S. tsubst \<rho> (\<rho>' v S)) T"
  by (induction T) auto

lemma const_typ_ok_tsubst: "const_typ_ok ctab c T \<Longrightarrow> const_typ_ok ctab c (tsubst \<rho> T)"
  by (auto simp: const_typ_ok_def tsubst_tsubst split: if_splits)

lemma tinst_ok_inst_ok: "tinst_ok \<rho> \<Longrightarrow> inst_ok \<rho>"
  by (auto simp: inst_ok_def tinst_tsubst cert_typ_tsubst const_typ_ok_tsubst)

end

end
