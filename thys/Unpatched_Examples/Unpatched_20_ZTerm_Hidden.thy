section \<open>Patch 20: variables of a tight proof that its propositions do not show\<close>

theory Unpatched_20_ZTerm_Hidden
  imports Unpatched_Base
begin

text \<open>
  \<open>ZTerm.norm_proof\<close> instantiates the variables of the visible propositions only. Here the
  environment binds \<open>?x\<close> to \<open>True\<close>, the proof applies an assumption \<open>\<And>b. b \<equiv> b\<close> to \<open>?x\<close>, and the
  visible proposition does not have \<open>?x\<close>: the normalised proof still has \<open>?x\<close>, although the environment binds
  it. With the patch, \<open>ZTerm.norm_proof\<close> raises \<open>TERM\<close> instead. This is the function on its own;
  the example does not go through an inference of the kernel.
\<close>

ML_val \<open>
  val thy = \<^theory>;
  val x = (("x", 0), \<^typ>\<open>bool\<close>);
  val env = Envir.update (x, \<^term>\<open>True\<close>) (Envir.empty 0);
  val zx = ZTerm.zterm_of thy (Var x);
  val A = ZTerm.zterm_of thy \<^prop>\<open>\<And>b::bool. b \<equiv> b\<close>;
  val prf = ZAbsp ("H", A, ZAppt (ZBoundp 0, zx));
  val ZAbsp (_, _, ZAppt (_, t)) = ZTerm.norm_proof thy env [\<^prop>\<open>True\<close>] prf;
  val _ = \<^assert> (t = zx);
\<close>

end
