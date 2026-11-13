section \<open>Patch 25: the type instance of the tight proof of \<open>Thm.combination\<close>\<close>

theory Unpatched_25_ZTerm_Combination
  imports Unpatched_Base
begin

text \<open>
  The axiom \<open>combination\<close> is \<open>f \<equiv> g \<Longrightarrow> x \<equiv> y \<Longrightarrow> f x \<equiv> g y\<close> with \<open>f, g :: 'a \<Rightarrow> 'b\<close> and
  \<open>x, y :: 'a\<close>. \<open>Thm.combination\<close> passes the type of \<open>f\<close> to \<open>ZTerm.combination_proof\<close>, which
  takes it for \<open>'a\<close>. For \<open>f :: nat \<Rightarrow> bool\<close> and \<open>x :: nat\<close>, the proof constant of the axiom in the
  tight proof has the type instance \<open>'a := nat \<Rightarrow> bool\<close>, and its instance table maps the
  variable \<open>x :: nat \<Rightarrow> bool\<close> to the term \<open>x :: nat\<close>. The classic proof records no types.
\<close>

ML_val \<open>
  val ctxt = \<^context>;
  val cert = Thm.cterm_of ctxt;
  val th = with_zproofs (fn () =>
    Thm.combination (Thm.assume (cert \<^prop>\<open>(f::nat \<Rightarrow> bool) \<equiv> g\<close>))
      (Thm.assume (cert \<^prop>\<open>(x::nat) \<equiv> y\<close>))) ();
  val _ = \<^assert> (Thm.prop_of th aconv
    Logic.mk_equals (\<^term>\<open>(f::nat \<Rightarrow> bool) x\<close>, \<^term>\<open>(g::nat \<Rightarrow> bool) y\<close>));
  val (instT, inst) =
    (case Thm.zproof_of th of
      ZAppp (ZAppp (ZConstp (_, insts), _), _) => insts
    | _ => raise Fail "unexpected proof");
  fun tvar a =
    (case filter (fn (((b, _), _), _) => b = a) (ZTVars.dest instT) of
      [(_, T)] => ZTerm.typ_of T
    | _ => raise Fail "unexpected type instances");
  fun var x =
    (case filter (fn (((y, _), _), _) => y = x) (ZVars.dest inst) of
      [(((_, _), T), _)] => ZTerm.typ_of T
    | _ => raise Fail "unexpected instances");
  (*'a is instantiated by the type of f, not by the type of x*)
  val _ = \<^assert> (tvar "'a" = \<^typ>\<open>nat \<Rightarrow> bool\<close>);
  val _ = \<^assert> (tvar "'b" = \<^typ>\<open>bool\<close>);
  (*so the variable x of the axiom has the type of f, and f the type (nat \<Rightarrow> bool) \<Rightarrow> bool*)
  val _ = \<^assert> (var "x" = \<^typ>\<open>nat \<Rightarrow> bool\<close>);
  val _ = \<^assert> (var "f" = \<^typ>\<open>(nat \<Rightarrow> bool) \<Rightarrow> bool\<close>);
\<close>

end
