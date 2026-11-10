section \<open>Patch 13: class membership propositions in tight terms\<close>

theory Unpatched_13_ZTerm_Ofclass
  imports Unpatched_Base
begin

text \<open>
  \<open>ZTerm.zterm_of\<close> converts every term \<open>c TYPE(T)\<close> with a constant \<open>c\<close> whose name ends with
  \<open>_class\<close> to \<open>OFCLASS\<close>, since \<open>Logic.match_of_class\<close> only checks the name; \<open>ZTerm.term_of\<close>
  converts it back to a class membership proposition of type \<open>prop\<close>. For a constant of another
  type, the result is not the original term and not even well-typed.
\<close>

consts foo_class :: "'a itself \<Rightarrow> zi" ZQ :: "zi \<Rightarrow> prop"

ML_val \<open>
  val thy = \<^theory>;
  val t = Const (\<^const_name>\<open>ZQ\<close>, \<^typ>\<open>zi\<close> --> propT) $
    (Const (\<^const_name>\<open>foo_class\<close>, Term.itselfT \<^typ>\<open>zi\<close> --> \<^typ>\<open>zi\<close>) $ Logic.mk_type \<^typ>\<open>zi\<close>);
  val _ = Sign.cert_term thy t;
  val t' = ZTerm.term_of thy (ZTerm.zterm_of thy t);
  val _ = \<^assert> (not (t aconv t'));
  val _ = \<^assert> (not (can (Sign.cert_term thy) t'));
\<close>

end
