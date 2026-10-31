(*  Title:      Pure/thm.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

The very core of Isabelle's Meta Logic: certified types and terms,
derivations, theorems, inference rules (including lifting and
resolution), oracles.
*)

infix 0 RS RSN;

signature BASIC_THM =
sig
  type ctyp
  type cterm
  exception CTERM of string * cterm list
  type thm
  type conv = cterm -> thm
  exception THM of string * int * thm list
  val RSN: thm * (int * thm) -> thm
  val RS: thm * thm -> thm
end;

signature THM =
sig
  include BASIC_THM
  (*certified types*)
  val typ_of: ctyp -> typ
  val global_ctyp_of: theory -> typ -> ctyp
  val ctyp_of: Proof.context -> typ -> ctyp
  val dest_ctyp: ctyp -> ctyp list
  val dest_ctypN: int -> ctyp -> ctyp
  val make_ctyp: ctyp -> ctyp list -> ctyp
  val maxidx_of_ctyp: ctyp -> int
  (*certified terms*)
  val term_of: cterm -> term
  val typ_of_cterm: cterm -> typ
  val ctyp_of_cterm: cterm -> ctyp
  val maxidx_of_cterm: cterm -> int
  val global_cterm_of: theory -> term -> cterm
  val cterm_of: Proof.context -> term -> cterm
  val renamed_term: term -> cterm -> cterm
  val fast_term_ord: cterm ord
  val term_ord: cterm ord
  val dest_comb: cterm -> cterm * cterm
  val dest_fun: cterm -> cterm
  val dest_arg: cterm -> cterm
  val dest_fun2: cterm -> cterm
  val dest_arg1: cterm -> cterm
  val dest_abs_fresh: string -> cterm -> cterm * cterm
  val dest_abs_global: cterm -> cterm * cterm
  val rename_tvar: indexname -> ctyp -> ctyp
  val free: string * ctyp -> cterm
  val var: indexname * ctyp -> cterm
  val apply: cterm -> cterm -> cterm
  val lambda_name: string * cterm -> cterm -> cterm
  val lambda: cterm -> cterm -> cterm
  val adjust_maxidx_cterm: int -> cterm -> cterm
  val incr_indexes_cterm: int -> cterm -> cterm
  val match: cterm * cterm -> ctyp TVars.table * cterm Vars.table
  val first_order_match: cterm * cterm -> ctyp TVars.table * cterm Vars.table
  (*theorems*)
  val fold_terms: {hyps: bool} -> (term -> 'a -> 'a) -> thm -> 'a -> 'a
  val fold_atomic_ctyps: {hyps: bool} ->
    ('a -> typ -> bool) -> (ctyp -> 'a -> 'a) -> thm -> 'a -> 'a
  val fold_atomic_cterms: {hyps: bool} ->
    ('a -> term -> bool) -> (cterm -> 'a -> 'a) -> thm -> 'a -> 'a
  val terms_of_tpairs: (term * term) list -> term list
  val full_prop_of: thm -> term
  val theory_id: thm -> Context.theory_id
  val theory_name: {long: bool} -> thm -> string
  val theory_long_name: thm -> string
  val theory_base_name: thm -> string
  val maxidx_of: thm -> int
  val maxidx_thm: thm -> int -> int
  val shyps_of: thm -> sort Ord_List.T
  val hyps_of: thm -> term list
  val prop_of: thm -> term
  val tpairs_of: thm -> (term * term) list
  val concl_of: thm -> term
  val prems_of: thm -> term list
  val take_prems_of: int -> thm -> term list
  val nprems_of: thm -> int
  val no_prems: thm -> bool
  val one_prem: thm -> bool
  val prem_of: thm -> int -> term
  val major_prem_of: thm -> term
  val cprop_of: thm -> cterm
  val cprem_of: thm -> int -> cterm
  val cconcl_of: thm -> cterm
  val cprems_of: thm -> cterm list
  val take_cprems_of: int -> thm -> cterm list
  val chyps_of: thm -> cterm list
  val thm_ord: thm ord
  exception CONTEXT of string * ctyp list * cterm list * thm list * Context.generic option
  val theory_of_cterm: cterm -> theory
  val theory_of_thm: thm -> theory
  val trim_context_ctyp: ctyp -> ctyp
  val trim_context_cterm: cterm -> cterm
  val transfer_ctyp: theory -> ctyp -> ctyp
  val transfer_ctyp': Proof.context -> ctyp -> ctyp
  val transfer_ctyp'': Context.generic -> ctyp -> ctyp
  val transfer_cterm: theory -> cterm -> cterm
  val transfer_cterm': Proof.context -> cterm -> cterm
  val transfer_cterm'': Context.generic -> cterm -> cterm
  val transfer: theory -> thm -> thm
  val transfer': Proof.context -> thm -> thm
  val transfer'': Context.generic -> thm -> thm
  val join_transfer: theory -> thm -> thm
  val join_transfer_context: Proof.context * thm -> Proof.context * thm
  val renamed_prop: term -> thm -> thm
  val weaken: cterm -> thm -> thm
  val weaken_sorts: sort list -> cterm -> cterm
  val proof_bodies_of: thm list -> proof_body list
  val proof_body_of: thm -> proof_body
  val zproof_of: thm -> zproof
  val proof_of: thm -> proof
  val reconstruct_proof_of: thm -> Proofterm.proof
  val consolidate: thm list -> unit
  val expose_proofs: theory -> thm list -> unit
  val expose_proof: theory -> thm -> unit
  val future: thm future -> cterm -> thm
  val thm_deps: thm -> Proofterm.thm Ord_List.T
  val extra_shyps: thm -> sort list
  val strip_shyps: thm -> thm
  val derivation_closed: thm -> bool
  val derivation_name: thm -> Thm_Name.T
  val derivation_id: thm -> Proofterm.thm_id option
  val raw_derivation_name: thm -> Thm_Name.P
  val expand_name: thm -> Proofterm.thm_header -> Thm_Name.P option
  val name_derivation: Thm_Name.P -> thm -> thm
  val close_derivation: Position.T -> thm -> thm
  val trim_context: thm -> thm
  val axiom: theory -> string -> thm
  val all_axioms_of: theory -> (string * thm) list
  val get_tags: thm -> Properties.T
  val map_tags: (Properties.T -> Properties.T) -> thm -> thm
  val norm_proof: thm -> thm
  val adjust_maxidx_thm: int -> thm -> thm
  (*type classes*)
  val the_classrel: theory -> class * class -> thm
  val the_arity: theory -> string * sort list * class -> thm
  val sorts_zproof: theory -> ZTerm.sorts_proof
  val sorts_proof: theory -> Proofterm.sorts_proof
  (*forked proofs*)
  val register_proofs: thm list lazy -> theory -> theory
  val consolidate_theory: theory -> unit
  val expose_theory: theory -> unit
  (*oracles*)
  val add_oracle: binding * ('a -> cterm) -> theory -> (string * ('a -> thm)) * theory
  val oracle_space: theory -> Name_Space.T
  val pretty_oracle: Proof.context -> string -> Pretty.T
  val extern_oracles: bool -> Proof.context -> (Markup.T list * xstring) list
  val check_oracle: Proof.context -> xstring * Position.T -> string
  (*inference rules*)
  val assume: cterm -> thm  (*exception THM*)
  val assume_cterm: cterm -> thm  (*exception CTERM*)
  val implies_intr: cterm -> thm -> thm
  val implies_elim: thm -> thm -> thm
  val forall_intr: cterm -> thm -> thm
  val forall_elim: cterm -> thm -> thm
  val reflexive: cterm -> thm
  val symmetric: thm -> thm
  val transitive: thm -> thm -> thm
  val beta_conversion: bool -> conv
  val eta_conversion: conv
  val eta_long_conversion: conv
  val abstract_rule: string -> cterm -> thm -> thm
  val combination: thm -> thm -> thm
  val equal_intr: thm -> thm -> thm
  val equal_elim: thm -> thm -> thm
  val solve_constraints: thm -> thm
  val flexflex_rule: Proof.context option -> thm -> thm Seq.seq
  val generalize: Names.set * Names.set -> int -> thm -> thm
  val generalize_cterm: Names.set * Names.set -> int -> cterm -> cterm
  val generalize_ctyp: Names.set -> int -> ctyp -> ctyp
  val instantiate: ctyp TVars.table * cterm Vars.table -> thm -> thm
  val instantiate_beta: ctyp TVars.table * cterm Vars.table -> thm -> thm
  val instantiate_cterm: ctyp TVars.table * cterm Vars.table -> cterm -> cterm
  val instantiate_beta_cterm: ctyp TVars.table * cterm Vars.table -> cterm -> cterm
  val trivial: cterm -> thm
  val of_class: ctyp * class -> thm
  val unconstrainT: thm -> thm
  val varifyT_global': TFrees.set -> thm -> ((string * sort) * (indexname * sort)) list * thm
  val varifyT_global: thm -> thm
  val legacy_freezeT: thm -> thm
  val plain_prop_of: thm -> term
  val get_zproof_serials: theory -> serial list
  val get_zproof: theory -> serial ->
    {name: Thm_Name.P, thm: thm, zboxes: ZTerm.zboxes, zproof: zproof} option
  val store_zproof: Thm_Name.P -> thm -> theory -> thm * theory
  val dest_state: thm * int -> (term * term) list * term list * term * term
  val lift_rule: cterm -> thm -> thm
  val incr_indexes: int -> thm -> thm
  val assumption: Proof.context option -> int -> thm -> thm Seq.seq
  val eq_assumption: int -> thm -> thm
  val rotate_rule: int -> int -> thm -> thm
  val permute_prems: int -> int -> thm -> thm
  val bicompose: Proof.context option -> {flatten: bool, match: bool, incremented: bool} ->
    bool * thm * int -> int -> thm -> thm Seq.seq
  val biresolution: Proof.context option -> bool -> (bool * thm) list -> int -> thm -> thm Seq.seq
  val theory_names_of_arity: {long: bool} -> theory -> string * class -> string list
  val add_classrel: thm -> theory -> theory
  val add_arity: thm -> theory -> theory
end;

(** lift_rule, bicompose_aux, biresolution: generated code **)

(*Generated from the Isabelle/HOL formalization in session Pure_Thm (theories
  Pure_Bicompose, Pure_Biresolution, Pure_Bicompose_Code), on top of the formalization of
  Pure's terms, environments and type unification in session Pure_Pattern and of unify.ML in
  session Pure_Unify.  The functions lift_rule, bicompose_aux and biresolution of structure Thm
  below are the wrappers of bicompose_wrapper.ML around this code.

  DO NOT EDIT: generated by make_thm_ML.*)

structure Str_Literal : sig
  type int = IntInf.int
  val literal_of_asciis : int list -> string
  val asciis_of_literal : string -> int list
end = struct

open IntInf;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs; (* deliberate clone not relying on List._ structure *)

fun check_ascii k =
  if 0 <= k andalso k < 128
  then k
  else raise Fail "Non-ASCII character in literal";

val char_of_ascii = Char.chr o toInt o (fn k => k mod 128);

val ascii_of_char = check_ascii o fromInt o Char.ord;

val literal_of_asciis = String.implode o map char_of_ascii;

val asciis_of_literal = map ascii_of_char o String.explode;

end;

structure Bicompose_Generated : sig
  type num
  type nat
  datatype class_error = No_Classrel of string * string |
    No_Arity of string * string | No_Subsort of string list * string list
  datatype unif_trace = No_Trace |
    Typ_Clash of (string list * typ) Vartab.table * typ * typ |
    Clash of string * string |
    Clash_BB of (string * typ) list * IntInf.int * IntInf.int |
    Clash_B of (string * typ) list * IntInf.int * string |
    Proj_Fail of
      Envir.env * (string * typ) list * (string * IntInf.int) *
        IntInf.int list * term
    | Ocheck_Fail of
        (string * IntInf.int) * term * (string * typ) list * Envir.env
  datatype exn = Unif of unif_trace | Pattern | Match | TUnify | Type_Match |
    Class_Error of class_error | Type_Error of string * typ list * term list |
    Term_Error of string * term list | Failure of string | Subscript |
    Unequal_Lengths | Dup of (string * IntInf.int)
  datatype 'a res = Ok of 'a | Err of exn
  datatype zexn = ZExn of exn |
    BAD_INST of (((string * IntInf.int) * ztyp) * zterm) list | ZOption
  datatype 'a zres = ZOk of 'a | ZErr of zexn
  datatype uexn = PExn of exn | CANTUNIFY | ASSIGN | CHANGE_FAIL | Bind
  datatype event = Ev_Unif of unif_trace | Ev_Loss of typ * typ |
    Ev_Dpairs of string * Envir.env * ((string * typ) list * (term * term)) list
    | Ev_Failure_Node | Ev_Bound_Exceeded
  type 'a uq
  type bctx
  datatype thm_args = Orule | Orule_State | State
  datatype texn = UExn of uexn | THM of string * IntInf.int * thm_args |
    ERROR of string | COMPOSE
  datatype 'a tres = TOk of 'a | TErr of texn
  datatype 'a bops =
    BOps of
      (Envir.env -> (term * term) list -> (event list * 'a tres) option) *
        ('a ->
          (event list *
            (((Envir.env * (term * term) list) * 'a) option) tres) option) *
        (string list -> string list)
  datatype newas =
    NewAs of
      term list * term list *
        ((string * string) list * (string * string) list) option * IntInf.int
  datatype bres =
    BRes of Envir.env * (term * term) list * term * term option * newas
  type eres_data
  type 'a bseq
  type 'a thm_rep_ext
  type brctx
  type ('a, 'b) rseq
  datatype ('a, 'b) rstep = RS_Done | RS_Skip of ('a, 'b) rseq |
    RS_Result of (bres * (bool * 'b)) * ('a, 'b) rseq
  val ren_term : (string * string) list * (string * string) list -> term -> term
  val bpull :
    'a bops -> 'a bseq -> (event list * ((bres * 'a bseq) option) tres) option
  val th_prop : 'a thm_rep_ext -> term
  val zlift_proof :
    (string -> typ -> (typ list) res option) ->
      term -> IntInf.int -> term list -> zproof -> zproof zres option
  val brrule : ('a, 'b) rseq -> (bool * 'b) option
  val th_maxidx : 'a thm_rep_ext -> IntInf.int
  val bicompose_aux :
    'a bops ->
      Sorts.algebra ->
        bool ->
          bool ->
            bool ->
              IntInf.int * ((term * term) list * term) ->
                (term * term) list * (term list * (term * term)) ->
                  bool ->
                    bool ->
                      IntInf.int * ((term * term) list * term) ->
                        IntInf.int -> (event list * 'a bseq tres) option
  val th_tpairs : 'a thm_rep_ext -> (term * term) list
  val lift_rule : term -> IntInf.int -> unit thm_rep_ext -> unit thm_rep_ext
  val brstep :
    'a bops ->
      Sorts.algebra ->
        ('b -> unit thm_rep_ext) ->
          ('a, 'b) rseq -> (event list * ('a, 'b) rstep tres) option
  val lift_proof :
    term -> IntInf.int -> term list -> Proofterm.proof -> Proofterm.proof
  val zbicompose_proof :
    (string -> typ -> (typ list) res option) ->
      Envir.env ->
        IntInf.int ->
          bool ->
            term list ->
              term list ->
                term option ->
                  term list ->
                    IntInf.int ->
                      IntInf.int ->
                        term list -> zproof -> zproof -> zproof zres option
  val biresolution :
    bool ->
      bool ->
        ('a -> unit thm_rep_ext) ->
          (bool * 'a) list ->
            IntInf.int ->
              unit thm_rep_ext -> (event list * ('b, 'a) rseq tres) option
  val make : IntInf.int -> (term * term) list -> term -> unit thm_rep_ext
  val bicompose_proof :
    Envir.env ->
      IntInf.int ->
        bool ->
          term list ->
            term list ->
              term option ->
                term list ->
                  IntInf.int ->
                    IntInf.int ->
                      Proofterm.proof ->
                        Proofterm.proof ->
                          (string list * Proofterm.proof res) option
  val map_proof_terms :
    (term -> term) -> (typ -> typ) -> Proofterm.proof -> Proofterm.proof
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun equal_bool false p = not p
  | equal_bool true p = p
  | equal_bool p false = not p
  | equal_bool p true = p;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

val equal_char = {equal = equal_chara} : char equal;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_literal =
  {less_eq = (fn a => fn b => ((a : string) <= b)),
    less = (fn a => fn b => ((a : string) < b))}
  : string ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_literal = {ord_preorder = ord_literal} : string preorder;

val order_literal = {preorder_order = preorder_literal} : string order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_literal = {order_linorder = order_literal} : string linorder;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

val equal_integer = {equal = (fn a => fn b => ((a : IntInf.int) = b))} :
  IntInf.int equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_integer = {plus = (fn a => fn b => IntInf.+ (a, b))} : IntInf.int plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_integer = {plus_semigroup_add = plus_integer} :
  IntInf.int semigroup_add;

val numeral_integer =
  {one_numeral = one_integer, semigroup_add_numeral = semigroup_add_integer} :
  IntInf.int numeral;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_integer = {times = (fn a => fn b => IntInf.* (a, b))} :
  IntInf.int times;

val power_integer = {one_power = one_integer, times_power = times_integer} :
  IntInf.int power;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

val ab_semigroup_add_integer =
  {semigroup_add_ab_semigroup_add = semigroup_add_integer} :
  IntInf.int ab_semigroup_add;

val semigroup_mult_integer = {times_semigroup_mult = times_integer} :
  IntInf.int semigroup_mult;

val semiring_integer =
  {ab_semigroup_add_semiring = ab_semigroup_add_integer,
    semigroup_mult_semiring = semigroup_mult_integer}
  : IntInf.int semiring;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

val mult_zero_integer =
  {times_mult_zero = times_integer, zero_mult_zero = zero_integer} :
  IntInf.int mult_zero;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

val monoid_add_integer =
  {semigroup_add_monoid_add = semigroup_add_integer,
    zero_monoid_add = zero_integer}
  : IntInf.int monoid_add;

val comm_monoid_add_integer =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_integer,
    monoid_add_comm_monoid_add = monoid_add_integer}
  : IntInf.int comm_monoid_add;

val semiring_0_integer =
  {comm_monoid_add_semiring_0 = comm_monoid_add_integer,
    mult_zero_semiring_0 = mult_zero_integer,
    semiring_semiring_0 = semiring_integer}
  : IntInf.int semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

val monoid_mult_integer =
  {semigroup_mult_monoid_mult = semigroup_mult_integer,
    power_monoid_mult = power_integer}
  : IntInf.int monoid_mult;

val semiring_numeral_integer =
  {monoid_mult_semiring_numeral = monoid_mult_integer,
    numeral_semiring_numeral = numeral_integer,
    semiring_semiring_numeral = semiring_integer}
  : IntInf.int semiring_numeral;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

val semiring_1_integer =
  {semiring_numeral_semiring_1 = semiring_numeral_integer,
    semiring_0_semiring_1 = semiring_0_integer,
    zero_neq_one_semiring_1 = zero_neq_one_integer}
  : IntInf.int semiring_1;

datatype nat = Zero_nat | Suc of nat;

datatype class_error = No_Classrel of string * string |
  No_Arity of string * string | No_Subsort of string list * string list;

datatype unif_trace = No_Trace |
  Typ_Clash of (string list * typ) Vartab.table * typ * typ |
  Clash of string * string |
  Clash_BB of (string * typ) list * IntInf.int * IntInf.int |
  Clash_B of (string * typ) list * IntInf.int * string |
  Proj_Fail of
    Envir.env * (string * typ) list * (string * IntInf.int) * IntInf.int list *
      term
  | Ocheck_Fail of
      (string * IntInf.int) * term * (string * typ) list * Envir.env;

datatype exn = Unif of unif_trace | Pattern | Match | TUnify | Type_Match |
  Class_Error of class_error | Type_Error of string * typ list * term list |
  Term_Error of string * term list | Failure of string | Subscript |
  Unequal_Lengths | Dup of (string * IntInf.int);

datatype 'a res = Ok of 'a | Err of exn;

datatype zexn = ZExn of exn |
  BAD_INST of (((string * IntInf.int) * ztyp) * zterm) list | ZOption;

datatype 'a zres = ZOk of 'a | ZErr of zexn;

datatype uexn = PExn of exn | CANTUNIFY | ASSIGN | CHANGE_FAIL | Bind;

datatype 'a ures = UOk of 'a | UErr of uexn;

datatype event = Ev_Unif of unif_trace | Ev_Loss of typ * typ |
  Ev_Dpairs of string * Envir.env * ((string * typ) list * (term * term)) list |
  Ev_Failure_Node | Ev_Bound_Exceeded;

datatype 'a uq = UQ_Cell of ((Envir.env * (term * term) list) * 'a) |
  UQ_Seq of 'a;

datatype bctx =
  BCtx of
    bool * bool * bool * IntInf.int * term list * term * term *
      (term * term) list * IntInf.int * (term * term) * (term * term) list;

datatype thm_args = Orule | Orule_State | State;

datatype texn = UExn of uexn | THM of string * IntInf.int * thm_args |
  ERROR of string | COMPOSE;

datatype 'a tres = TOk of 'a | TErr of texn;

datatype 'a bops =
  BOps of
    (Envir.env -> (term * term) list -> (event list * 'a tres) option) *
      ('a ->
        (event list *
          (((Envir.env * (term * term) list) * 'a) option) tres) option) *
      (string list -> string list);

datatype newas =
  NewAs of
    term list * term list *
      ((string * string) list * (string * string) list) option * IntInf.int;

datatype bres =
  BRes of Envir.env * (term * term) list * term * term option * newas;

datatype eres_data =
  ER of Envir.env * (string * typ) list * term * term * term * term list;

datatype 'a bseq = BS_Empty |
  BS_Its of bctx * term option * newas * 'a uq * 'a bseq |
  BS_Tryasms of bctx * eres_data * term list * IntInf.int;

datatype 'a thm_rep_ext =
  Thm_rep_ext of IntInf.int * (term * term) list * term * 'a;

datatype brctx =
  BRCtx of
    bool * bool * unit thm_rep_ext *
      ((term * term) list * (term list * (term * term))) * term * term *
      term list;

datatype ('a, 'b) rseq = RQ_Empty |
  RQ_Make of brctx * (bool * 'b) * (bool * 'b) list |
  RQ_App of (bool * 'b) * 'a bseq * ('a, 'b) rseq;

datatype ('a, 'b) rstep = RS_Done | RS_Skip of ('a, 'b) rseq |
  RS_Result of (bres * (bool * 'b)) * ('a, 'b) rseq;

fun id x = (fn xa => xa) x;

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun drop n [] = []
  | drop n (x :: xs) = (case n of Zero_nat => x :: xs | Suc m => drop m xs);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun take n [] = []
  | take n (x :: xs) = (case n of Zero_nat => [] | Suc m => x :: take m xs);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun map_of A_ [] k = NONE
  | map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun is_none NONE = true
  | is_none (SOME x) = false;

fun return x = SOME (Ok x);

fun bindM m f =
  (case m of NONE => NONE | SOME (Ok a) => f a | SOME (Err e) => SOME (Err e));

fun mapM f [] = return []
  | mapM f (x :: xs) =
    bindM (f x) (fn y => bindM (mapM f xs) (fn ys => return (y :: ys)));

fun of_bool A_ false = zero (zero_zero_neq_one A_)
  | of_bool A_ true = one (one_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);

fun allM p [] = return true
  | allM p (x :: xs) =
    bindM (p x) (fn b => (if b then allM p xs else return false));

fun insort_key B_ f x [] = [x]
  | insort_key B_ f x (y :: ys) =
    (if less_eq ((ord_preorder o preorder_order o order_linorder) B_) (f x)
          (f y)
      then x :: y :: ys else y :: insort_key B_ f x ys);

fun sort_key B_ f xs = foldr (insort_key B_ f) xs [];

fun class_le alg c1 c2 =
  ((c1 : string) = c2) orelse Sorts.class_less alg (c1, c2);

fun inter_class alg c [] = [c]
  | inter_class alg ca (c :: cs) =
    (if class_le alg c ca then c :: cs
      else (if class_le alg ca c then inter_class alg ca cs
             else c :: inter_class alg ca cs));

fun inter_sort alg s1 s2 =
  sort_key linorder_literal (fn x => x) (fold (inter_class alg) s1 s2);

fun raisea e = SOME (Err e);

fun foldM f [] b = return b
  | foldM f (x :: xs) b = bindM (f x b) (foldM f xs);

fun mg_domain alg a s =
  let
    val dom =
      (fn c =>
        (case map_of equal_literal (Symtab.lookup_list (Sorts.arities_of alg) a)
                c
          of NONE => raisea (Class_Error (No_Arity (a, c)))
          | SOME aa => return aa));
    val dom_inter =
      (fn c => fn ss =>
        bindM (dom c)
          (fn ds =>
            return (map (fn (aa, b) => inter_sort alg aa b) (zip ds ss))));
  in
    (case s of [] => raisea (Failure "Unknown domain of empty intersection")
      | c :: cs => bindM (dom c) (foldM dom_inter cs))
  end;

fun handlea m h =
  (case m of NONE => m | SOME (Ok _) => m | SOME (Err a) => h a);

fun mg_domain_unif alg a s =
  handlea (mg_domain alg a s)
    (fn e =>
      (case e of Unif _ => raisea e | Pattern => raisea e | Match => raisea e
        | TUnify => raisea e | Type_Match => raisea e
        | Class_Error _ => raisea TUnify | Type_Error (_, _, _) => raisea e
        | Term_Error (_, _) => raisea e | Failure _ => raisea e
        | Subscript => raisea e | Unequal_Lengths => raisea e
        | Dup _ => raisea e));

fun fst (x1, x2) = x1;

fun update_new kx t =
  (if Vartab.defined t (fst kx) then raisea (Dup (fst kx))
    else return (Vartab.update kx t));

fun gen_tyvar s cnt =
  (TVar ((Name.aT, IntInf.+ (cnt, (1 : IntInf.int))), s),
    IntInf.+ (cnt, (1 : IntInf.int)));

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun sort_le alg s1 s2 =
  equal_lista equal_literal s1 s2 orelse
    list_all (fn c2 => list_ex (fn c1 => class_le alg c1 c2) s1) s2;

fun tvar_clash ixn sa s =
  raisea
    (Type_Error
      ("Type variable has two distinct sorts", [TVar (ixn, sa), TVar (ixn, s)],
        []));

fun type_lookup tye ixn s =
  (case Vartab.lookup tye ixn of NONE => return NONE
    | SOME (sa, t) =>
      (if equal_lista equal_literal s sa then return (SOME t)
        else tvar_clash ixn s sa));

fun devar tye t =
  (case t of Type (_, _) => return t | TFree (_, _) => return t
    | TVar (ixn, s) =>
      bindM (type_lookup tye ixn s)
        (fn a => (case a of NONE => return t | SOME aa => devar tye aa)));

fun meet alg t s st =
  (if null s then return st
    else let
           val (tye, cnt) = st;
         in
           (case t
             of Type (a, ts) =>
               bindM (mg_domain_unif alg a s)
                 (fn ss =>
                   foldM (fn (ta, sa) => fn sta =>
                           bindM (devar (fst sta) ta)
                             (fn tb => meet alg tb sa sta))
                     (zip ts ss) st)
             | TFree (_, sa) =>
               (if sort_le alg sa s then return st else raisea TUnify)
             | TVar (xi, sa) =>
               (if sort_le alg sa s then return st
                 else let
                        val (v, cnta) = gen_tyvar (inter_sort alg sa s) cnt;
                      in
                        bindM (update_new (xi, (sa, v)) tye)
                          (fn tyea => return (tyea, cnta))
                      end))
         end);

fun returnZ x = SOME (ZOk x);

fun bindZ m f =
  (case m of NONE => NONE | SOME (ZOk a) => f a
    | SOME (ZErr e) => SOME (ZErr e));

fun mapZ f [] = returnZ []
  | mapZ f (x :: xs) =
    bindZ (f x) (fn y => bindZ (mapZ f xs) (fn ys => returnZ (y :: ys)));

fun zip_eq [] [] = return []
  | zip_eq (x :: xs) (y :: ys) =
    bindM (zip_eq xs ys) (fn zs => return ((x, y) :: zs))
  | zip_eq (v :: va) [] = raisea Unequal_Lengths
  | zip_eq [] (v :: va) = raisea Unequal_Lengths;

fun zFuns ts t = foldr (fn a => fn b => ZFun (a, b)) ts t;

fun dedup A_ [] = []
  | dedup A_ (x :: xs) = x :: dedup A_ (filter (fn y => not (eq A_ y x)) xs);

fun liftM m =
  (case m of NONE => NONE | SOME (Ok x) => SOME ([], UOk x)
    | SOME (Err e) => SOME ([], UErr (PExn e)));

fun var_clash xi ta t =
  raisea
    (Type_Error
      ("Variable has two distinct types", [], [Var (xi, t), Var (xi, ta)]));

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (Suc n);

fun size_list xs = length_tailrec xs Zero_nat;

fun equal_nat Zero_nat (Suc x2) = false
  | equal_nat (Suc x2) Zero_nat = false
  | equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2
  | equal_nat Zero_nat Zero_nat = true;

fun unified_aux tye ta t =
  bindM (devar tye ta)
    (fn u =>
      bindM (devar tye t)
        (fn ua =>
          (case (u, ua)
            of (Type (s, ts), Type (sa, tsa)) =>
              (if ((s : string) = sa)
                then bindM (allM (fn (a, b) => unified_aux tye a b)
                             (zip ts tsa))
                       (fn b =>
                         return
                           (b andalso equal_nat (size_list ts) (size_list tsa)))
                else return false)
            | (Type (_, _), TFree (_, _)) => return ((u : typ) = ua)
            | (Type (_, _), TVar (_, _)) => return ((u : typ) = ua)
            | (TFree (_, _), _) => return ((u : typ) = ua)
            | (TVar (_, _), _) => return ((u : typ) = ua))));

fun unified tye ta t =
  (if Vartab.is_empty tye then return ((ta : typ) = t)
    else unified_aux tye ta t);

fun lookup env xi t =
  (case Vartab.lookup (Envir.term_env env) xi of NONE => return NONE
    | SOME (u, ta) =>
      bindM (unified (Envir.type_env env) t u)
        (fn b => (if b then return (SOME ta) else var_clash xi t u)));

fun ilength [] = (0 : IntInf.int)
  | ilength (x :: xs) = IntInf.+ (ilength xs, (1 : IntInf.int));

fun incr_bv inc lev (Bound i) =
  (if IntInf.<= (lev, i) then Bound (IntInf.+ (i, inc)) else Bound i)
  | incr_bv inc lev (Abs (a, ta, t)) =
    Abs (a, ta, incr_bv inc (IntInf.+ (lev, (1 : IntInf.int))) t)
  | incr_bv inc lev (t $ u) = incr_bv inc lev t $ incr_bv inc lev u
  | incr_bv inc lev (Const (v, va)) = Const (v, va)
  | incr_bv inc lev (Free (v, va)) = Free (v, va)
  | incr_bv inc lev (Var (v, va)) = Var (v, va);

fun zAbsps ts p = foldr (fn a => fn b => ZAbsp ("H", a, b)) ts p;

fun zAppps p qs = foldl (fn a => fn b => ZAppp (a, b)) p qs;

fun zAppts p ts = foldl (fn a => fn b => ZAppt (a, b)) p ts;

fun liftMZ m =
  (case m of NONE => NONE | SOME (Ok x) => SOME (ZOk x)
    | SOME (Err e) => SOME (ZErr (ZExn e)));

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun liftOZ m = map_option ZOk m;

fun raiseZ e = SOME (ZErr e);

fun snd (x1, x2) = x2;

val propT : typ = Type ("prop", []);

fun typ_of (ZTVar (v, s)) =
  (if (((snd v) : IntInf.int) = (~1 : IntInf.int)) then TFree (fst v, s)
    else TVar (v, s))
  | typ_of (ZFun (t, u)) = Type ("fun", [typ_of t, typ_of u])
  | typ_of ZProp = propT
  | typ_of (ZType0 c) = Type (c, [])
  | typ_of (ZType1 (c, t)) = Type (c, [typ_of t])
  | typ_of (ZType (c, ts)) = Type (c, map typ_of ts);

fun existsM p [] = return false
  | existsM p (x :: xs) =
    bindM (p x) (fn b => (if b then return true else existsM p xs));

fun lookup1 te xi t =
  (case Vartab.lookup te xi of NONE => return NONE
    | SOME (u, ta) =>
      (if ((t : typ) = u) then return (SOME ta) else var_clash xi t u));

fun less_eq_nat Zero_nat n = true
  | less_eq_nat (Suc m) n = less_nat m n
and less_nat n Zero_nat = false
  | less_nat m (Suc n) = less_eq_nat m n;

fun minus_nat m Zero_nat = m
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat (Suc m) (Suc n) = minus_nat m n;

val class_suffix : string = "_class";

fun bit_cut_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), false)
    else let
           val (r, s) =
             IntInf.divMod (IntInf.abs k, IntInf.abs (2 : IntInf.int));
         in
           ((if IntInf.< ((0 : IntInf.int), k) then r
              else IntInf.- (IntInf.~ r, s)),
             ((s : IntInf.int) = (1 : IntInf.int)))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val (_, a) = bit_cut_integer q6;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, a)
                        end;

fun explode s = map char_of_integer (Str_Literal.asciis_of_literal s);

fun match_of_class t =
  (case t of Const (_, _) => NONE | Free (_, _) => NONE | Var (_, _) => NONE
    | Bound _ => NONE | Abs (_, _, _) => NONE
    | Const (_, _) $ Const (_, Type (_, [])) => NONE
    | Const (c, _) $ Const (d, Type (e, [ta])) =>
      let
        val s = explode class_suffix;
        val cs = explode c;
      in
        (if ((d : string) = "Pure.type") andalso
              (((e : string) = "itself") andalso
                (less_eq_nat (size_list s) (size_list cs) andalso
                  equal_lista equal_char
                    (drop (minus_nat (size_list cs) (size_list s)) cs) s))
          then SOME (ta, implode
                           (take (minus_nat (size_list cs) (size_list s)) cs))
          else NONE)
      end
    | Const (_, _) $ Const (_, Type (_, _ :: _ :: _)) => NONE
    | Const (_, _) $ Const (_, TFree (_, _)) => NONE
    | Const (_, _) $ Const (_, TVar (_, _)) => NONE
    | Const (_, _) $ Free (_, _) => NONE | Const (_, _) $ Var (_, _) => NONE
    | Const (_, _) $ Bound _ => NONE | Const (_, _) $ Abs (_, _, _) => NONE
    | Const (_, _) $ (_ $ _) => NONE | Free (_, _) $ _ => NONE
    | Var (_, _) $ _ => NONE | Bound _ $ _ => NONE | Abs (_, _, _) $ _ => NONE
    | _ $ _ $ _ => NONE);

fun mk_of_class t c =
  Const (c ^ class_suffix,
    Type ("fun", [Type ("itself", [t]), Type ("prop", [])])) $
    Const ("Pure.type", Type ("itself", [t]));

fun ztyp_of (TFree (a, s)) = ZTVar ((a, (~1 : IntInf.int)), s)
  | ztyp_of (TVar (v, s)) = ZTVar (v, s)
  | ztyp_of (Type (c, [])) =
    (if ((c : string) = "prop") then ZProp else ZType0 c)
  | ztyp_of (Type (c, [t])) = ZType1 (c, ztyp_of t)
  | ztyp_of (Type (c, [t, u])) =
    (if ((c : string) = "fun") then ZFun (ztyp_of t, ztyp_of u)
      else ZType (c, [ztyp_of t, ztyp_of u]))
  | ztyp_of (Type (c, t :: u :: v :: ts)) =
    ZType (c, map ztyp_of (t :: u :: v :: ts));

fun zterm_of ta (Free (x, t)) =
  returnZ (ZVar ((x, (~1 : IntInf.int)), ztyp_of t))
  | zterm_of ta (Var (xi, t)) = returnZ (ZVar (xi, ztyp_of t))
  | zterm_of ta (Bound i) = returnZ (ZBound i)
  | zterm_of ta (Const (c, t)) =
    bindZ (liftMZ (ta c t))
      (fn ts =>
        returnZ
          (case ts of [] => ZConst0 c | [u] => ZConst1 (c, ztyp_of u)
            | _ :: _ :: _ => ZConst (c, map ztyp_of ts)))
  | zterm_of ta (Abs (a, t, b)) =
    bindZ (zterm_of ta b) (fn ba => returnZ (ZAbs (a, ztyp_of t, ba)))
  | zterm_of ta (t $ u) =
    (case match_of_class (t $ u)
      of NONE =>
        bindZ (zterm_of ta t)
          (fn tb => bindZ (zterm_of ta u) (fn ua => returnZ (ZApp (tb, ua))))
      | SOME tc =>
        (if (((t $ u) : term) = (mk_of_class (fst tc) (snd tc)))
          then returnZ (OFCLASS (ztyp_of (fst tc), snd tc))
          else bindZ (zterm_of ta t)
                 (fn tb =>
                   bindZ (zterm_of ta u) (fn ua => returnZ (ZApp (tb, ua))))));

fun zlookup ta env xi t =
  (if Vartab.is_empty (Envir.term_env env) then returnZ NONE
    else bindZ (liftMZ (lookup env xi (typ_of t)))
           (fn a =>
             (case a of NONE => returnZ NONE
               | SOME u =>
                 bindZ (zterm_of ta u) (fn ua => returnZ (SOME ua)))));

fun zmk_app b x =
  let
    val (i, (j, p)) = x;
  in
    (if b then (IntInf.- (i, (1 : IntInf.int)), (j, ZAppp (p, ZBoundp i)))
      else (i, (IntInf.- (j, (1 : IntInf.int)), ZAppt (p, ZBound j))))
  end;

fun zvar_eq v w =
  equal_proda equal_literal equal_integer (fst v) (fst w) andalso
    (((snd v) : ztyp) = (snd w));

fun head_of (f $ uu) = head_of f
  | head_of (Const (v, va)) = Const (v, va)
  | head_of (Free (v, va)) = Free (v, va)
  | head_of (Var (v, va)) = Var (v, va)
  | head_of (Bound v) = Bound v
  | head_of (Abs (v, va, vb)) = Abs (v, va, vb);

fun list_all2 p [] ys = null ys
  | list_all2 p xs [] = null xs
  | list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys;

fun returnT x = SOME ([], TOk x);

fun bindT m f =
  (case m of NONE => NONE
    | SOME (evs, TOk x) =>
      (case evs of [] => f x
        | _ :: _ => map_option (fn (evsa, a) => (evs @ evsa, a)) (f x))
    | SOME (evs, TErr e) => SOME (evs, TErr e));

fun mapT f [] = returnT []
  | mapT f (x :: xs) =
    bindT (f x) (fn y => bindT (mapT f xs) (fn ys => returnT (y :: ys)));

fun zimp_prf (ZApp (ZApp (ZConst0 c, a), b)) i m =
  (if ((m : IntInf.int) = (0 : IntInf.int)) then ZBoundp i
    else (if ((c : string) = "Pure.imp")
           then ZAbsp ("H", a,
                  zimp_prf b (IntInf.+ (i, (1 : IntInf.int)))
                    (IntInf.- (m, (1 : IntInf.int))))
           else ZBoundp i))
  | zimp_prf (ZVar (v, va)) i m = ZBoundp i
  | zimp_prf (ZBound v) i m = ZBoundp i
  | zimp_prf (ZConst0 v) i m = ZBoundp i
  | zimp_prf (ZConst1 (v, va)) i m = ZBoundp i
  | zimp_prf (ZConst (v, va)) i m = ZBoundp i
  | zimp_prf (ZAbs (v, va, vb)) i m = ZBoundp i
  | zimp_prf (ZApp (ZVar (vb, vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZBound vb, va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZConst0 vb, va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZConst1 (vb, vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZConst (vb, vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZAbs (vb, vc, vd), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZApp (ZVar (vd, ve), vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZApp (ZBound vd, vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZApp (ZConst1 (vd, ve), vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZApp (ZConst (vd, ve), vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZApp (ZAbs (vd, ve, vf), vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZApp (ZApp (vd, ve), vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (ZApp (OFCLASS (vd, ve), vc), va)) i m = ZBoundp i
  | zimp_prf (ZApp (OFCLASS (vb, vc), va)) i m = ZBoundp i
  | zimp_prf (OFCLASS (v, va)) i m = ZBoundp i;

fun zall_prf i m (ZApp (ZConst1 (c, u), ZAbs (a, ta, t))) =
  (if ((c : string) = "Pure.all") then ZAbst (a, ta, zall_prf i m t)
    else zimp_prf (ZApp (ZConst1 (c, u), ZAbs (a, ta, t))) (IntInf.~ i) m)
  | zall_prf i m (ZVar (v, va)) = zimp_prf (ZVar (v, va)) (IntInf.~ i) m
  | zall_prf i m (ZBound v) = zimp_prf (ZBound v) (IntInf.~ i) m
  | zall_prf i m (ZConst0 v) = zimp_prf (ZConst0 v) (IntInf.~ i) m
  | zall_prf i m (ZConst1 (v, va)) = zimp_prf (ZConst1 (v, va)) (IntInf.~ i) m
  | zall_prf i m (ZConst (v, va)) = zimp_prf (ZConst (v, va)) (IntInf.~ i) m
  | zall_prf i m (ZAbs (v, va, vb)) = zimp_prf (ZAbs (v, va, vb)) (IntInf.~ i) m
  | zall_prf i m (ZApp (ZVar (vb, vc), va)) =
    zimp_prf (ZApp (ZVar (vb, vc), va)) (IntInf.~ i) m
  | zall_prf i m (ZApp (ZBound vb, va)) =
    zimp_prf (ZApp (ZBound vb, va)) (IntInf.~ i) m
  | zall_prf i m (ZApp (ZConst0 vb, va)) =
    zimp_prf (ZApp (ZConst0 vb, va)) (IntInf.~ i) m
  | zall_prf i m (ZApp (ZConst (vb, vc), va)) =
    zimp_prf (ZApp (ZConst (vb, vc), va)) (IntInf.~ i) m
  | zall_prf i m (ZApp (ZAbs (vb, vc, vd), va)) =
    zimp_prf (ZApp (ZAbs (vb, vc, vd), va)) (IntInf.~ i) m
  | zall_prf i m (ZApp (ZApp (vb, vc), va)) =
    zimp_prf (ZApp (ZApp (vb, vc), va)) (IntInf.~ i) m
  | zall_prf i m (ZApp (OFCLASS (vb, vc), va)) =
    zimp_prf (ZApp (OFCLASS (vb, vc), va)) (IntInf.~ i) m
  | zall_prf i m (ZApp (v, ZVar (vb, vc))) =
    zimp_prf (ZApp (v, ZVar (vb, vc))) (IntInf.~ i) m
  | zall_prf i m (ZApp (v, ZBound vb)) =
    zimp_prf (ZApp (v, ZBound vb)) (IntInf.~ i) m
  | zall_prf i m (ZApp (v, ZConst0 vb)) =
    zimp_prf (ZApp (v, ZConst0 vb)) (IntInf.~ i) m
  | zall_prf i m (ZApp (v, ZConst1 (vb, vc))) =
    zimp_prf (ZApp (v, ZConst1 (vb, vc))) (IntInf.~ i) m
  | zall_prf i m (ZApp (v, ZConst (vb, vc))) =
    zimp_prf (ZApp (v, ZConst (vb, vc))) (IntInf.~ i) m
  | zall_prf i m (ZApp (v, ZApp (vb, vc))) =
    zimp_prf (ZApp (v, ZApp (vb, vc))) (IntInf.~ i) m
  | zall_prf i m (ZApp (v, OFCLASS (vb, vc))) =
    zimp_prf (ZApp (v, OFCLASS (vb, vc))) (IntInf.~ i) m
  | zall_prf i m (OFCLASS (v, va)) = zimp_prf (OFCLASS (v, va)) (IntInf.~ i) m;

fun zincr_bv inc lev (ZBound i) =
  (if IntInf.<= (lev, i) then ZBound (IntInf.+ (i, inc)) else ZBound i)
  | zincr_bv inc lev (ZAbs (a, ta, t)) =
    ZAbs (a, ta, zincr_bv inc (IntInf.+ (lev, (1 : IntInf.int))) t)
  | zincr_bv inc lev (ZApp (t, u)) =
    ZApp (zincr_bv inc lev t, zincr_bv inc lev u)
  | zincr_bv inc lev (ZVar (v, va)) = ZVar (v, va)
  | zincr_bv inc lev (ZConst0 v) = ZConst0 v
  | zincr_bv inc lev (ZConst1 (v, va)) = ZConst1 (v, va)
  | zincr_bv inc lev (ZConst (v, va)) = ZConst (v, va)
  | zincr_bv inc lev (OFCLASS (v, va)) = OFCLASS (v, va);

fun combound t n Zero_nat = t
  | combound t n (Suc k) =
    combound t (IntInf.+ (n, (1 : IntInf.int))) k $ Bound n;

fun above env lim =
  (fn tab => fn lim => case Vartab.min tab of NONE => true | SOME ((x, i), y) => i > lim)
    (Envir.term_env env) lim andalso
    (fn tab => fn lim => case Vartab.min tab of NONE => true | SOME ((x, i), y) => i > lim)
      (Envir.type_env env) lim;

val implies : term =
  Const ("Pure.imp", Type ("fun", [propT, Type ("fun", [propT, propT])]));

fun mk_implies a b = implies $ a $ b;

fun all_const t =
  Const ("Pure.all", Type ("fun", [Type ("fun", [t, propT]), propT]));

fun dest_imp (Const (c, uu) $ a $ b) =
  (if ((c : string) = "Pure.imp") then SOME (a, b) else NONE)
  | dest_imp (Const (v, va)) = NONE
  | dest_imp (Free (v, va)) = NONE
  | dest_imp (Var (v, va)) = NONE
  | dest_imp (Bound v) = NONE
  | dest_imp (Abs (v, va, vb)) = NONE
  | dest_imp (Const (vb, vc) $ va) = NONE
  | dest_imp (Free (vb, vc) $ va) = NONE
  | dest_imp (Var (vb, vc) $ va) = NONE
  | dest_imp (Bound vb $ va) = NONE
  | dest_imp (Abs (vb, vc, vd) $ va) = NONE
  | dest_imp (Free (vd, ve) $ vc $ va) = NONE
  | dest_imp (Var (vd, ve) $ vc $ va) = NONE
  | dest_imp (Bound vd $ vc $ va) = NONE
  | dest_imp (Abs (vd, ve, vf) $ vc $ va) = NONE
  | dest_imp (vd $ ve $ vc $ va) = NONE;

fun dest_all (Const (c, uu) $ Abs (a, ta, t)) =
  (if ((c : string) = "Pure.all") then SOME (a, (ta, t)) else NONE)
  | dest_all (Const (v, va)) = NONE
  | dest_all (Free (v, va)) = NONE
  | dest_all (Var (v, va)) = NONE
  | dest_all (Bound v) = NONE
  | dest_all (Abs (v, va, vb)) = NONE
  | dest_all (Free (vb, vc) $ va) = NONE
  | dest_all (Var (vb, vc) $ va) = NONE
  | dest_all (Bound vb $ va) = NONE
  | dest_all (Abs (vb, vc, vd) $ va) = NONE
  | dest_all (vb $ vc $ va) = NONE
  | dest_all (v $ Const (vb, vc)) = NONE
  | dest_all (v $ Free (vb, vc)) = NONE
  | dest_all (v $ Var (vb, vc)) = NONE
  | dest_all (v $ Bound vb) = NONE
  | dest_all (v $ (vb $ vc)) = NONE;

fun raiseT e = SOME ([], TErr e);

fun liftWT m =
  (case m of NONE => NONE | SOME (evs, UOk x) => SOME (evs, TOk x)
    | SOME (evs, UErr e) => SOME (evs, TErr (UExn e)));

fun liftMT m = liftWT (liftM m);

fun could_beta_contract (Abs (uu, uv, uw) $ ux) = true
  | could_beta_contract (Const (v, va) $ u) =
    could_beta_contract (Const (v, va)) orelse could_beta_contract u
  | could_beta_contract (Free (v, va) $ u) =
    could_beta_contract (Free (v, va)) orelse could_beta_contract u
  | could_beta_contract (Var (v, va) $ u) =
    could_beta_contract (Var (v, va)) orelse could_beta_contract u
  | could_beta_contract (Bound v $ u) =
    could_beta_contract (Bound v) orelse could_beta_contract u
  | could_beta_contract (v $ va $ u) =
    could_beta_contract (v $ va) orelse could_beta_contract u
  | could_beta_contract (Abs (uy, uz, b)) = could_beta_contract b
  | could_beta_contract (Const (v, vb)) = false
  | could_beta_contract (Free (v, vb)) = false
  | could_beta_contract (Var (v, vb)) = false
  | could_beta_contract (Bound v) = false;

fun env_is_empty env =
  Vartab.is_empty (Envir.term_env env) andalso
    Vartab.is_empty (Envir.type_env env);

fun norm_type_aux tye t =
  (case t
    of Type (a, ts) =>
      bindM (mapM (norm_type_aux tye) ts) (fn tsa => return (Type (a, tsa)))
    | TFree (_, _) => return t
    | TVar (v, s) =>
      bindM (type_lookup tye v s)
        (fn a =>
          (case a of NONE => return t | SOME aa => norm_type_aux tye aa)));

fun incr_boundvars inc t =
  (if ((inc : IntInf.int) = (0 : IntInf.int)) then t
    else incr_bv inc (0 : IntInf.int) t);

fun subst_bound_aux arg lev (Bound i) =
  (if IntInf.< (i, lev) then Bound i
    else (if ((i : IntInf.int) = lev) then incr_boundvars lev arg
           else Bound (IntInf.- (i, (1 : IntInf.int)))))
  | subst_bound_aux arg lev (Abs (a, ta, t)) =
    Abs (a, ta, subst_bound_aux arg (IntInf.+ (lev, (1 : IntInf.int))) t)
  | subst_bound_aux arg lev (t $ u) =
    subst_bound_aux arg lev t $ subst_bound_aux arg lev u
  | subst_bound_aux arg lev (Const (v, va)) = Const (v, va)
  | subst_bound_aux arg lev (Free (v, va)) = Free (v, va)
  | subst_bound_aux arg lev (Var (v, va)) = Var (v, va);

fun subst_bound arg body = subst_bound_aux arg (0 : IntInf.int) body;

fun norm_term2 env t =
  (case t
    of Const (a, ta) =>
      bindM (norm_type_aux (Envir.type_env env) ta)
        (fn tb => return (Const (a, tb)))
    | Free (a, ta) =>
      bindM (norm_type_aux (Envir.type_env env) ta)
        (fn tb => return (Free (a, tb)))
    | Var (xi, ta) =>
      bindM (lookup env xi ta)
        (fn a =>
          (case a
            of NONE =>
              bindM (norm_type_aux (Envir.type_env env) ta)
                (fn tb => return (Var (xi, tb)))
            | SOME aa => norm_term2 env aa))
    | Bound _ => return t
    | Abs (a, ta, body) =>
      bindM (norm_type_aux (Envir.type_env env) ta)
        (fn tb =>
          bindM (norm_term2 env body) (fn bodya => return (Abs (a, tb, bodya))))
    | f $ u =>
      (case f
        of Const (_, _) =>
          bindM (norm_term2 env f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Bound _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term2 env (subst_bound u body)
                | _ $ _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))))
        | Free (_, _) =>
          bindM (norm_term2 env f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Bound _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term2 env (subst_bound u body)
                | _ $ _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))))
        | Var (_, _) =>
          bindM (norm_term2 env f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Bound _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term2 env (subst_bound u body)
                | _ $ _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))))
        | Bound _ =>
          bindM (norm_term2 env f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Bound _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term2 env (subst_bound u body)
                | _ $ _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))))
        | Abs (_, _, body) => norm_term2 env (subst_bound u body)
        | _ $ _ =>
          bindM (norm_term2 env f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Bound _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term2 env (subst_bound u body)
                | _ $ _ =>
                  bindM (norm_term2 env u) (fn nu => return (nf $ nu))))));

fun norm_term1 te t =
  (case t of Const (_, _) => return t | Free (_, _) => return t
    | Var (xi, ta) =>
      bindM (lookup1 te xi ta)
        (fn a => (case a of NONE => return t | SOME aa => norm_term1 te aa))
    | Bound _ => return t
    | Abs (a, ta, body) =>
      bindM (norm_term1 te body) (fn bodya => return (Abs (a, ta, bodya)))
    | f $ u =>
      (case f
        of Const (_, _) =>
          bindM (norm_term1 te f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Bound _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term1 te (subst_bound u body)
                | _ $ _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))))
        | Free (_, _) =>
          bindM (norm_term1 te f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Bound _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term1 te (subst_bound u body)
                | _ $ _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))))
        | Var (_, _) =>
          bindM (norm_term1 te f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Bound _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term1 te (subst_bound u body)
                | _ $ _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))))
        | Bound _ =>
          bindM (norm_term1 te f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Bound _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term1 te (subst_bound u body)
                | _ $ _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))))
        | Abs (_, _, body) => norm_term1 te (subst_bound u body)
        | _ $ _ =>
          bindM (norm_term1 te f)
            (fn nf =>
              (case nf
                of Const (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Free (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Var (_, _) =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Bound _ => bindM (norm_term1 te u) (fn nu => return (nf $ nu))
                | Abs (_, _, body) => norm_term1 te (subst_bound u body)
                | _ $ _ =>
                  bindM (norm_term1 te u) (fn nu => return (nf $ nu))))));

fun norm_term env t =
  (if env_is_empty env andalso not (could_beta_contract t) then return t
    else (if Vartab.is_empty (Envir.type_env env)
           then norm_term1 (Envir.term_env env) t else norm_term2 env t));

fun norm_type tye t =
  (if Vartab.is_empty tye then return t else norm_type_aux tye t);

fun norm_term_skip env n t =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then liftMT (norm_term env t)
    else (case dest_all t
           of NONE =>
             (case dest_imp t
               of NONE => raiseT (ERROR "norm_term_skip: too few assumptions??")
               | SOME (a, b) =>
                 bindT (norm_term_skip env (IntInf.- (n, (1 : IntInf.int))) b)
                   (fn ba => returnT (mk_implies a ba)))
           | SOME (a, (ta, b)) =>
             bindT (liftMT (norm_type (Envir.type_env env) ta))
               (fn tb =>
                 bindT (norm_term_skip env n b)
                   (fn ba => returnT (all_const tb $ Abs (a, tb, ba))))));

fun bc_lifted (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x3;

fun bc_nlift (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x9;

fun bc_match (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x2;

fun list_implies [] b = b
  | list_implies (a :: asa) b = implies $ a $ list_implies asa b;

fun bc_smax (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x4;

fun na_As (NewAs (x1, x2, x3, x4)) = x1;

fun norm_tpair env tu =
  let
    val (t, u) = tu;
  in
    bindM (norm_term env t)
      (fn ta => bindM (norm_term env u) (fn ua => return (ta, ua)))
  end;

fun bc_Bs (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x5;

fun bc_C (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x7;

fun addth ctx a na et =
  let
    val (env, tpairs) = et;
  in
    bindT (if env_is_empty env
            then returnT (tpairs, (bc_Bs ctx @ na_As na, bc_C ctx))
            else bindT (liftMT (mapM (norm_tpair env) tpairs))
                   (fn ntps =>
                     (if above env (bc_smax ctx)
                       then (if bc_lifted ctx
                              then bindT (mapT
   (norm_term_skip env (bc_nlift ctx)) (na_As na))
                                     (fn asa =>
                                       returnT
 (ntps, (bc_Bs ctx @ asa, bc_C ctx)))
                              else bindT (liftMT
   (mapM (norm_term env) (na_As na)))
                                     (fn asa =>
                                       returnT
 (ntps, (bc_Bs ctx @ asa, bc_C ctx))))
                       else (if bc_match ctx then raiseT COMPOSE
                              else bindT (liftMT
   (mapM (norm_term env) (bc_Bs ctx @ na_As na)))
                                     (fn hs =>
                                       bindT (liftMT (norm_term env (bc_C ctx)))
 (fn c => returnT (ntps, (hs, c))))))))
      (fn (ntpairs, (hs, c)) =>
        returnT (BRes (env, ntpairs, list_implies hs c, a, na)))
  end;

fun bo_pull (BOps (x1, x2, x3)) = x2;

fun er_params (ER (x1, x2, x3, x4, x5, x6)) = x2;

fun er_concla (ER (x1, x2, x3, x4, x5, x6)) = x4;

fun er_concl (ER (x1, x2, x3, x4, x5, x6)) = x3;

fun er_env (ER (x1, x2, x3, x4, x5, x6)) = x1;

fun bo_variants (BOps (x1, x2, x3)) = x3;

fun bo_unifiers (BOps (x1, x2, x3)) = x1;

fun er_As (ER (x1, x2, x3, x4, x5, x6)) = x6;

fun er_A1 (ER (x1, x2, x3, x4, x5, x6)) = x5;

fun bc_dpairs (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x11;

fun could_unify t u =
  (case (head_of t, head_of u)
    of (Const (literal, _), Const (b, _)) =>
      ((literal : string) = b) andalso matchrands t u
    | (Const (_, _), Free (_, _)) => false | (Const (_, _), Var (_, _)) => true
    | (Const (_, _), Bound _) => false | (Const (_, _), Abs (_, _, _)) => true
    | (Const (_, _), _ $ _) => false | (Free (_, _), Const (_, _)) => false
    | (Free (literal, _), Free (b, _)) =>
      ((literal : string) = b) andalso matchrands t u
    | (Free (_, _), Var (_, _)) => true | (Free (_, _), Bound _) => false
    | (Free (_, _), Abs (_, _, _)) => true | (Free (_, _), _ $ _) => false
    | (Var (_, _), Const (_, _)) => true | (Var (_, _), Free (_, _)) => true
    | (Var (_, _), Var (_, _)) => true | (Var (_, _), Bound _) => true
    | (Var (_, _), Abs (_, _, _)) => true | (Var (_, _), _ $ _) => true
    | (Bound _, Const (_, _)) => false | (Bound _, Free (_, _)) => false
    | (Bound _, Var (_, _)) => true
    | (Bound integer, Bound j) =>
      ((integer : IntInf.int) = j) andalso matchrands t u
    | (Bound _, Abs (_, _, _)) => true | (Bound _, _ $ _) => false
    | (Abs (_, _, _), Const (_, _)) => true
    | (Abs (_, _, _), Free (_, _)) => true | (Abs (_, _, _), Var (_, _)) => true
    | (Abs (_, _, _), Bound _) => true | (Abs (_, _, _), Abs (_, _, _)) => true
    | (Abs (_, _, _), _ $ _) => true | (_ $ _, Const (_, _)) => false
    | (_ $ _, Free (_, _)) => false | (_ $ _, Var (_, _)) => true
    | (_ $ _, Bound _) => false | (_ $ _, Abs (_, _, _)) => true
    | (_ $ _, _ $ _) => false)
and matchrands (f $ t) (g $ u) = could_unify t u andalso matchrands f g
  | matchrands (Const (v, va)) uu = true
  | matchrands (Free (v, va)) uv = true
  | matchrands (Var (v, va)) uw = true
  | matchrands (Bound v) ux = true
  | matchrands (Abs (v, va, vb)) uy = true
  | matchrands (v $ va) (Const (vb, vc)) = true
  | matchrands (v $ va) (Free (vb, vc)) = true
  | matchrands (v $ va) (Var (vb, vc)) = true
  | matchrands (v $ va) (Bound vb) = true
  | matchrands (v $ va) (Abs (vb, vc, vd)) = true;

fun bc_BBi (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x10;

fun rlist_abs [] body = body
  | rlist_abs ((a, t) :: ps) body = rlist_abs ps (Abs (a, t, body));

fun bc_rtpairs (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x8;

fun bc_flatten (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x1;

fun remove_params j n a =
  (if ((j : IntInf.int) = (0 : IntInf.int)) andalso
        IntInf.<= (n, (0 : IntInf.int))
    then return a
    else (case dest_imp a
           of NONE =>
             (case dest_all a
               of NONE =>
                 (if IntInf.< ((0 : IntInf.int), n)
                   then raisea (Term_Error ("remove_params", [a]))
                   else return a)
               | SOME (_, (_, aa)) =>
                 remove_params (IntInf.- (j, (1 : IntInf.int))) n aa)
           | SOME (h, b) =>
             (if ((n : IntInf.int) = (1 : IntInf.int))
               then remove_params j (IntInf.- (n, (1 : IntInf.int))) b
               else bindM (remove_params j (IntInf.- (n, (1 : IntInf.int))) b)
                      (fn ba => return (implies $ incr_boundvars j h $ ba)))));

fun strip_params t =
  (case dest_imp t
    of NONE =>
      (case dest_all t of NONE => []
        | SOME (a, (ta, b)) => (a, ta) :: strip_params b)
    | SOME (_, a) => strip_params a);

fun list_forall [] t = t
  | list_forall ((a, ta) :: vars) t =
    all_const ta $ Abs (a, ta, list_forall vars t);

fun flatten_params variants n a =
  let
    val params = strip_params a;
    val vars = zip (variants (map fst params)) (map snd params);
  in
    bindM (remove_params (ilength vars) n a)
      (fn aa => return (list_forall vars aa))
  end;

fun add_var_names (Var ((x, uu), uv)) xs =
  (if member equal_literal xs x then xs else x :: xs)
  | add_var_names (Abs (uw, ux, t)) xs = add_var_names t xs
  | add_var_names (t $ u) xs = add_var_names u (add_var_names t xs)
  | add_var_names (Const (v, va)) xs = xs
  | add_var_names (Free (v, va)) xs = xs
  | add_var_names (Bound v) xs = xs;

fun strip_lifted b a =
  (case (dest_imp b, dest_imp a)
    of (NONE, _) =>
      (case (dest_all b, dest_all a) of (NONE, _) => a
        | (SOME (_, (_, _)), NONE) => a
        | (SOME (_, (_, t1)), SOME (_, (_, aa))) => strip_lifted t1 aa)
    | (SOME (_, _), NONE) =>
      (case (dest_all b, dest_all a) of (NONE, _) => a
        | (SOME (_, (_, _)), NONE) => a
        | (SOME (_, (_, t1)), SOME (_, (_, aa))) => strip_lifted t1 aa)
    | (SOME (_, b1), SOME (_, aa)) => strip_lifted b1 aa);

fun distinct_fst A_ [] = []
  | distinct_fst A_ ((x, y) :: ps) =
    (x, y) :: distinct_fst A_ (filter (fn p => not (eq A_ (fst p) x)) ps);

fun del_round xs ys [] qs clash = (clash, (xs, qs))
  | del_round xs ys ((x, y) :: ps) qs clash =
    (if member equal_literal ys y then del_round (x :: xs) (x :: ys) ps qs true
      else del_round xs (y :: ys) ps ((x, y) :: qs) clash);

fun del_clashing xs ps =
  (case del_round xs xs ps [] false of (true, (xsa, qs)) => del_clashing xsa qs
    | (false, (_, qs)) => qs);

fun strip_abs_body (Abs (uu, uv, t)) = strip_abs_body t
  | strip_abs_body (Const (v, va)) = Const (v, va)
  | strip_abs_body (Free (v, va)) = Free (v, va)
  | strip_abs_body (Var (v, va)) = Var (v, va)
  | strip_abs_body (Bound v) = Bound v
  | strip_abs_body (v $ va) = v $ va;

fun match_bvs (Abs (x, uu, s)) (Abs (y, uv, t)) acc =
  match_bvs s t
    (if not ((x : string) = "") andalso not ((y : string) = "")
      then (x, y) :: acc else acc)
  | match_bvs (f $ s) (g $ t) acc = match_bvs f g (match_bvs s t acc)
  | match_bvs (Const (v, va)) ux acc = acc
  | match_bvs (Free (v, va)) ux acc = acc
  | match_bvs (Var (v, va)) ux acc = acc
  | match_bvs (Bound v) ux acc = acc
  | match_bvs (v $ va) (Const (vb, vc)) acc = acc
  | match_bvs (v $ va) (Free (vb, vc)) acc = acc
  | match_bvs (v $ va) (Var (vb, vc)) acc = acc
  | match_bvs (v $ va) (Bound vb) acc = acc
  | match_bvs (v $ va) (Abs (vb, vc, vd)) acc = acc
  | match_bvs uw (Const (v, va)) acc = acc
  | match_bvs uw (Free (v, va)) acc = acc
  | match_bvs uw (Var (v, va)) acc = acc
  | match_bvs uw (Bound v) acc = acc
  | match_bvs (Abs (vb, vc, vd)) (v $ va) acc = acc;

fun match_bvars tu acc =
  match_bvs (strip_abs_body (fst tu)) (strip_abs_body (snd tu)) acc;

fun rename_bvs dpairs tpairs b asa =
  let
    val al = foldr match_bvars dpairs [];
  in
    (if null al then ([], [])
      else let
             val unknowns =
               fold (fn (t, u) => add_var_names u o add_var_names t) tpairs
                 (fold (add_var_names o fst) dpairs []);
             val unknownsa = fold (add_var_names o strip_lifted b) asa [];
             val ala =
               distinct_fst equal_literal
                 (filter
                   (fn (x, y) =>
                     not (not (member equal_literal unknownsa x) orelse
                           (member equal_literal unknowns x orelse
                             member equal_literal unknowns y)))
                   al);
             val unchanged =
               filter (fn x => is_none (map_of equal_literal ala x)) unknownsa;
             val alaa = del_clashing unchanged ala;
           in
             (distinct_fst equal_literal alaa, distinct_fst equal_literal al)
           end)
  end;

fun rename_bvars dpairs tpairs b asa =
  let
    val r = rename_bvs dpairs tpairs b asa;
  in
    (if list_all (fn (a, ba) => ((a : string) = ba)) (fst r) andalso
          list_all (fn (a, ba) => ((a : string) = ba)) (snd r)
      then NONE else SOME r)
  end;

fun strip_apply f b a =
  (case (b, (dest_imp b, dest_imp a))
    of (Const (_, _), _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Free (_, _), _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Var (_, _), _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Bound _, _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Abs (_, _, _), _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Const (_, _) $ _, _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Free (_, _) $ _, _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Var (_, _) $ _, _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Bound _ $ _, _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (Abs (_, _, _) $ _, _) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (_ $ _ $ _, (NONE, _)) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (_ $ _ $ _, (SOME (_, _), NONE)) =>
      (case (b, (dest_all b, dest_all a)) of (Const (_, _), _) => f a
        | (Free (_, _), _) => f a | (Var (_, _), _) => f a | (Bound _, _) => f a
        | (Abs (_, _, _), _) => f a | (_ $ _, (NONE, _)) => f a
        | (_ $ _, (SOME (_, (_, _)), NONE)) => f a
        | (c $ _, (SOME (_, (_, t1)), SOME (aa, (t, t2)))) =>
          c $ Abs (aa, t, strip_apply f t1 t2))
    | (c $ _ $ _, (SOME (_, b1), SOME (a2, b2))) =>
      c $ a2 $ strip_apply f b1 b2);

fun bc_Bi (BCtx (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x6;

fun ren_name tab x =
  (case map_of equal_literal tab x of NONE => x | SOME y => y);

fun ren_term r (Var ((x, i), t)) = Var ((ren_name (fst r) x, i), t)
  | ren_term r (Abs (x, ta, t)) = Abs (ren_name (snd r) x, ta, ren_term r t)
  | ren_term r (t $ u) = ren_term r t $ ren_term r u
  | ren_term r (Const (v, va)) = Const (v, va)
  | ren_term r (Free (v, va)) = Free (v, va)
  | ren_term r (Bound v) = Bound v;

fun handleT m h =
  (case m of NONE => m | SOME (_, TOk _) => m
    | SOME (evs, TErr e) =>
      (case evs of [] => h e
        | _ :: _ => map_option (fn (evsa, a) => (evs @ evsa, a)) (h e)));

fun newAs variants ctx as0 n dpairs tpairs =
  let
    val (as1, r) =
      (if bc_lifted ctx
        then (case rename_bvars dpairs (bc_rtpairs ctx @ tpairs) (bc_Bi ctx) as0
               of NONE => (as0, NONE)
               | SOME r =>
                 (map (strip_apply (ren_term r) (bc_Bi ctx)) as0, SOME r))
        else (as0, NONE));
  in
    handleT
      (bindT
        (if bc_flatten ctx then liftMT (mapM (flatten_params variants n) as1)
          else returnT as1)
        (fn as2 => returnT (NewAs (as2, as1, r, n))))
      (fn e =>
        (case e of UExn (PExn (Unif _)) => raiseT e
          | UExn (PExn Pattern) => raiseT e | UExn (PExn Match) => raiseT e
          | UExn (PExn TUnify) => raiseT e | UExn (PExn Type_Match) => raiseT e
          | UExn (PExn (Class_Error _)) => raiseT e
          | UExn (PExn (Type_Error (_, _, _))) => raiseT e
          | UExn (PExn (Term_Error (_, _))) =>
            raiseT (THM ("bicompose: 1st premise", (0 : IntInf.int), Orule))
          | UExn (PExn (Failure _)) => raiseT e
          | UExn (PExn Subscript) => raiseT e
          | UExn (PExn Unequal_Lengths) => raiseT e
          | UExn (PExn (Dup _)) => raiseT e | UExn CANTUNIFY => raiseT e
          | UExn ASSIGN => raiseT e | UExn CHANGE_FAIL => raiseT e
          | UExn Bind => raiseT e | THM (_, _, _) => raiseT e
          | ERROR _ => raiseT e | COMPOSE => raiseT e))
  end;

fun tryasms ops ctx er [] n = returnT BS_Empty
  | tryasms ops ctx er (asm :: rest) n =
    (if could_unify asm (er_concl er)
      then let
             val asma = rlist_abs (er_params er) asm;
           in
             bindT (bo_unifiers ops (er_env er)
                     ((asma, er_concla er) :: bc_dpairs ctx))
               (fn us =>
                 bindT (bo_pull ops us)
                   (fn a =>
                     (case a
                       of NONE =>
                         tryasms ops ctx er rest
                           (IntInf.+ (n, (1 : IntInf.int)))
                       | SOME ((env, tpairs), usa) =>
                         bindT (newAs (bo_variants ops) ctx (er_As er) n
                                 [bc_BBi ctx, (er_concla er, asma)] tpairs)
                           (fn na =>
                             returnT
                               (BS_Its
                                 (ctx, SOME (er_A1 er), na,
                                   UQ_Cell ((env, tpairs), usa),
                                   BS_Tryasms
                                     (ctx, er, rest,
                                       IntInf.+ (n, (1 : IntInf.int)))))))))
           end
      else tryasms ops ctx er rest (IntInf.+ (n, (1 : IntInf.int))));

fun bpull ops s =
  (case s of BS_Empty => returnT NONE
    | BS_Its (ctx, a, na, xq, yq) =>
      bindT (case xq of UQ_Cell c => returnT (SOME c)
              | UQ_Seq aa => bo_pull ops aa)
        (fn b =>
          (case b of NONE => bpull ops yq
            | SOME (et, us) =>
              handleT
                (bindT (addth ctx a na et)
                  (fn th =>
                    returnT (SOME (th, BS_Its (ctx, a, na, UQ_Seq us, yq)))))
                (fn e =>
                  (case e of UExn _ => raiseT e | THM (_, _, _) => raiseT e
                    | ERROR _ => raiseT e
                    | COMPOSE =>
                      bpull ops (BS_Its (ctx, a, na, UQ_Seq us, yq))))))
    | BS_Tryasms (ctx, er, asms, n) =>
      bindT (tryasms ops ctx er asms n) (bpull ops));

fun emitT ev = SOME ([ev], TOk ());

fun type_occurs v tye t =
  (case t of Type (_, a) => existsM (type_occurs v tye) a
    | TFree (_, _) => return false
    | TVar (w, s) =>
      (if equal_proda equal_literal equal_integer v w then return true
        else bindM (type_lookup tye w s)
               (fn a =>
                 (case a of NONE => return false
                   | SOME aa => type_occurs v tye aa))));

fun unify_aux alg ty1 ty2 st =
  let
    val (tye, cnt) = st;
  in
    bindM (devar tye ty1)
      (fn t =>
        bindM (devar tye ty2)
          (fn u =>
            (case (t, u)
              of (Type (literal, lista), Type (b, us)) =>
                (if not ((literal : string) = b) then raisea TUnify
                  else foldM (fn (a, ba) => unify_aux alg a ba) (zip lista us)
                         st)
              | (Type (_, _), TFree (_, _)) =>
                (if ((t : typ) = u) then return st else raisea TUnify)
              | (Type (_, _), TVar (v, s)) =>
                bindM (type_occurs v tye t)
                  (fn b =>
                    (if b then raisea TUnify
                      else bindM (update_new (v, (s, t)) tye)
                             (fn tyea => meet alg t s (tyea, cnt))))
              | (TFree (_, _), Type (_, _)) =>
                (if ((t : typ) = u) then return st else raisea TUnify)
              | (TFree (_, _), TFree (_, _)) =>
                (if ((t : typ) = u) then return st else raisea TUnify)
              | (TFree (_, _), TVar (v, s)) =>
                bindM (type_occurs v tye t)
                  (fn b =>
                    (if b then raisea TUnify
                      else bindM (update_new (v, (s, t)) tye)
                             (fn tyea => meet alg t s (tyea, cnt))))
              | (TVar (v, s1), Type (_, _)) =>
                bindM (type_occurs v tye u)
                  (fn b =>
                    (if b then raisea TUnify
                      else bindM (update_new (v, (s1, u)) tye)
                             (fn tyea => meet alg u s1 (tyea, cnt))))
              | (TVar (v, s1), TFree (_, _)) =>
                bindM (type_occurs v tye u)
                  (fn b =>
                    (if b then raisea TUnify
                      else bindM (update_new (v, (s1, u)) tye)
                             (fn tyea => meet alg u s1 (tyea, cnt))))
              | (TVar (v, s1), TVar (w, s2)) =>
                (if equal_proda equal_literal equal_integer v w
                  then (if equal_lista equal_literal s1 s2 then return st
                         else tvar_clash v s1 s2)
                  else (if sort_le alg s1 s2
                         then bindM (update_new (w, (s2, t)) tye)
                                (fn tyea => return (tyea, cnt))
                         else (if sort_le alg s2 s1
                                then bindM (update_new (v, (s1, u)) tye)
                                       (fn tyea => return (tyea, cnt))
                                else let
                                       val (s, cnta) =
 gen_tyvar (inter_sort alg s1 s2) cnt;
                                     in
                                       bindM (update_new (w, (s2, s)) tye)
 (fn tyea =>
   bindM (update_new (v, (s1, s)) tyea) (fn tyeb => return (tyeb, cnta)))
                                     end))))))
  end;

fun bindP m f =
  (case m of NONE => NONE
    | SOME (ws, Ok x) =>
      (case ws of [] => f x
        | _ :: _ => map_option (fn (wsa, a) => (ws @ wsa, a)) (f x))
    | SOME (ws, Err e) => SOME (ws, Err e));

fun warnP s = SOME ([s], Ok ());

fun fastype_of_bound (t :: ts) i =
  (if ((i : IntInf.int) = (0 : IntInf.int)) then return t
    else fastype_of_bound ts (IntInf.- (i, (1 : IntInf.int))))
  | fastype_of_bound [] i =
    raisea (Term_Error ("fastype_of: Bound", [Bound i]));

fun fastype_of_atom uu (Const (uv, t)) = return t
  | fastype_of_atom uw (Free (ux, t)) = return t
  | fastype_of_atom uy (Var (uz, t)) = return t
  | fastype_of_atom ts (Bound i) = fastype_of_bound ts i
  | fastype_of_atom va (Abs (v, vc, vd)) = raisea (Failure "fastype_of_atom")
  | fastype_of_atom va (v $ vc) = raisea (Failure "fastype_of_atom");

fun range_type_ofT ta (Type (n, [t, u])) =
  (if ((n : string) = "fun") then return u
    else raisea (Term_Error ("fastype_of: expected function type", [ta])))
  | range_type_ofT t (Type (v, [])) =
    raisea (Term_Error ("fastype_of: expected function type", [t]))
  | range_type_ofT t (Type (v, [vb])) =
    raisea (Term_Error ("fastype_of: expected function type", [t]))
  | range_type_ofT t (Type (v, vb :: vd :: vf :: vg)) =
    raisea (Term_Error ("fastype_of: expected function type", [t]))
  | range_type_ofT t (TFree (v, va)) =
    raisea (Term_Error ("fastype_of: expected function type", [t]))
  | range_type_ofT t (TVar (v, va)) =
    raisea (Term_Error ("fastype_of: expected function type", [t]));

fun fastype_of_term ts (Abs (uu, ta, t)) =
  bindM (fastype_of_term (ta :: ts) t) (fn u => return (Type ("fun", [ta, u])))
  | fastype_of_term ts (t $ uv) = range_type_of ts t
  | fastype_of_term ts (Const (v, va)) = fastype_of_atom ts (Const (v, va))
  | fastype_of_term ts (Free (v, va)) = fastype_of_atom ts (Free (v, va))
  | fastype_of_term ts (Var (v, va)) = fastype_of_atom ts (Var (v, va))
  | fastype_of_term ts (Bound v) = fastype_of_atom ts (Bound v)
and range_type_of ts (Abs (uw, t, u)) = fastype_of_term (t :: ts) u
  | range_type_of ts (t $ u) =
    bindM (range_type_of ts t) (range_type_ofT (t $ u))
  | range_type_of ts (Const (v, va)) =
    bindM (fastype_of_atom ts (Const (v, va))) (range_type_ofT (Const (v, va)))
  | range_type_of ts (Free (v, va)) =
    bindM (fastype_of_atom ts (Free (v, va))) (range_type_ofT (Free (v, va)))
  | range_type_of ts (Var (v, va)) =
    bindM (fastype_of_atom ts (Var (v, va))) (range_type_ofT (Var (v, va)))
  | range_type_of ts (Bound v) =
    bindM (fastype_of_atom ts (Bound v)) (range_type_ofT (Bound v));

fun fastype_of t = fastype_of_term [] t;

fun aconv_zterm (ZApp (t1, u1)) (ZApp (t2, u2)) =
  aconv_zterm t1 t2 andalso aconv_zterm u1 u2
  | aconv_zterm (ZAbs (uu, t1a, t1)) (ZAbs (uv, t2a, t2)) =
    aconv_zterm t1 t2 andalso ((t1a : ztyp) = t2a)
  | aconv_zterm (ZVar (v, va)) a2 = (((ZVar (v, va)) : zterm) = a2)
  | aconv_zterm (ZBound v) a2 = (((ZBound v) : zterm) = a2)
  | aconv_zterm (ZConst0 v) a2 = (((ZConst0 v) : zterm) = a2)
  | aconv_zterm (ZConst1 (v, va)) a2 = (((ZConst1 (v, va)) : zterm) = a2)
  | aconv_zterm (ZConst (v, va)) a2 = (((ZConst (v, va)) : zterm) = a2)
  | aconv_zterm (ZAbs (v, va, vb)) (ZVar (vc, vd)) =
    (((ZAbs (v, va, vb)) : zterm) = (ZVar (vc, vd)))
  | aconv_zterm (ZAbs (v, va, vb)) (ZBound vc) =
    (((ZAbs (v, va, vb)) : zterm) = (ZBound vc))
  | aconv_zterm (ZAbs (v, va, vb)) (ZConst0 vc) =
    (((ZAbs (v, va, vb)) : zterm) = (ZConst0 vc))
  | aconv_zterm (ZAbs (v, va, vb)) (ZConst1 (vc, vd)) =
    (((ZAbs (v, va, vb)) : zterm) = (ZConst1 (vc, vd)))
  | aconv_zterm (ZAbs (v, va, vb)) (ZConst (vc, vd)) =
    (((ZAbs (v, va, vb)) : zterm) = (ZConst (vc, vd)))
  | aconv_zterm (ZAbs (v, va, vb)) (ZApp (vc, vd)) =
    (((ZAbs (v, va, vb)) : zterm) = (ZApp (vc, vd)))
  | aconv_zterm (ZAbs (v, va, vb)) (OFCLASS (vc, vd)) =
    (((ZAbs (v, va, vb)) : zterm) = (OFCLASS (vc, vd)))
  | aconv_zterm (OFCLASS (v, va)) a2 = (((OFCLASS (v, va)) : zterm) = a2)
  | aconv_zterm a1 (ZVar (v, va)) = ((a1 : zterm) = (ZVar (v, va)))
  | aconv_zterm a1 (ZBound v) = ((a1 : zterm) = (ZBound v))
  | aconv_zterm a1 (ZConst0 v) = ((a1 : zterm) = (ZConst0 v))
  | aconv_zterm a1 (ZConst1 (v, va)) = ((a1 : zterm) = (ZConst1 (v, va)))
  | aconv_zterm a1 (ZConst (v, va)) = ((a1 : zterm) = (ZConst (v, va)))
  | aconv_zterm (ZApp (vc, vd)) (ZAbs (v, va, vb)) =
    (((ZApp (vc, vd)) : zterm) = (ZAbs (v, va, vb)))
  | aconv_zterm a1 (OFCLASS (v, va)) = ((a1 : zterm) = (OFCLASS (v, va)));

fun zv_insert_list [] t = SOME t
  | zv_insert_list ((k, x) :: xs) t =
    (case ZVars.lookup t k of NONE => zv_insert_list xs (ZVars.update (k, x) t)
      | SOME y => (if aconv_zterm y x then zv_insert_list xs t else NONE));

fun make_inst xs =
  (case zv_insert_list xs ZVars.empty of NONE => raiseZ (BAD_INST xs)
    | SOME a => returnZ a);

fun map_insts typ term insts =
  let
    val (instT, inst) = insts;
  in
    bindZ (mapZ (fn (a, b) =>
                  let
                    val (x, t) = a;
                  in
                    (fn ta =>
                      bindZ (term ta) (fn taa => returnZ ((x, typ t), taa)))
                  end
                    b)
            (ZVars.dest inst))
      (fn xs =>
        bindZ (make_inst xs)
          (fn insta => returnZ ((fn f => ZTVars.map (K f)) typ instT, insta)))
  end;

fun zcombound t n Zero_nat = t
  | zcombound t n (Suc k) =
    ZApp (zcombound t (IntInf.+ (n, (1 : IntInf.int))) k, ZBound n);

fun zsubst_type tvar (ZTVar (v, s)) =
  (case tvar (v, s) of NONE => ZTVar (v, s) | SOME t => t)
  | zsubst_type tvar (ZFun (t, u)) =
    ZFun (zsubst_type tvar t, zsubst_type tvar u)
  | zsubst_type tvar ZProp = ZProp
  | zsubst_type tvar (ZType0 a) = ZType0 a
  | zsubst_type tvar (ZType1 (a, t)) = ZType1 (a, zsubst_type tvar t)
  | zsubst_type tvar (ZType (a, ts)) = ZType (a, map (zsubst_type tvar) ts);

fun zincr_tvar inc t =
  (if ((inc : IntInf.int) = (0 : IntInf.int)) then t
    else zsubst_type
           (fn (a, b) =>
             let
               val (aa, i) = a;
             in
               (fn s =>
                 (if IntInf.<= ((0 : IntInf.int), i)
                   then SOME (ZTVar ((aa, IntInf.+ (i, inc)), s)) else NONE))
             end
               b)
           t);

fun zlift_term inc ts lev (ZVar ((x, i), t)) =
  (if IntInf.<= ((0 : IntInf.int), i)
    then zcombound (ZVar ((x, IntInf.+ (i, inc)), zFuns ts (zincr_tvar inc t)))
           lev (size_list ts)
    else ZVar ((x, i), zincr_tvar inc t))
  | zlift_term inc ts lev (ZBound i) = ZBound i
  | zlift_term inc ts lev (ZConst0 c) = ZConst0 c
  | zlift_term inc ts lev (ZConst1 (c, t)) = ZConst1 (c, zincr_tvar inc t)
  | zlift_term inc ts lev (ZConst (c, us)) = ZConst (c, map (zincr_tvar inc) us)
  | zlift_term inc ts lev (ZAbs (x, ta, t)) =
    ZAbs (x, zincr_tvar inc ta,
      zlift_term inc ts (IntInf.+ (lev, (1 : IntInf.int))) t)
  | zlift_term inc ts lev (ZApp (t, u)) =
    ZApp (zlift_term inc ts lev t, zlift_term inc ts lev u)
  | zlift_term inc ts lev (OFCLASS (t, c)) = OFCLASS (zincr_tvar inc t, c);

fun zlift_terma inc ts lev t =
  (if null ts andalso ((inc : IntInf.int) = (0 : IntInf.int)) then t
    else zlift_term inc ts lev t);

fun zlift_prf inc ts lev (ZAbst (a, t, p)) =
  bindZ (zlift_prf inc ts (IntInf.+ (lev, (1 : IntInf.int))) p)
    (fn pa => returnZ (ZAbst (a, zincr_tvar inc t, pa)))
  | zlift_prf inc ts lev (ZAbsp (a, t, p)) =
    bindZ (zlift_prf inc ts lev p)
      (fn pa => returnZ (ZAbsp (a, zlift_terma inc ts lev t, pa)))
  | zlift_prf inc ts lev (ZAppt (p, t)) =
    bindZ (zlift_prf inc ts lev p)
      (fn pa => returnZ (ZAppt (pa, zlift_terma inc ts lev t)))
  | zlift_prf inc ts lev (ZAppp (p, q)) =
    bindZ (zlift_prf inc ts lev p)
      (fn pa =>
        bindZ (zlift_prf inc ts lev q) (fn qa => returnZ (ZAppp (pa, qa))))
  | zlift_prf inc ts lev (ZConstp (a, insts)) =
    bindZ (map_insts (zincr_tvar inc)
            (fn t => returnZ (zlift_terma inc ts lev t)) insts)
      (fn instsa => returnZ (ZConstp (a, instsa)))
  | zlift_prf inc ts lev (OFCLASSp (t, c)) =
    returnZ (OFCLASSp (zincr_tvar inc t, c))
  | zlift_prf inc ts lev ZNop = returnZ ZNop
  | zlift_prf inc ts lev (ZBoundp v) = returnZ (ZBoundp v)
  | zlift_prf inc ts lev (ZHyp v) = returnZ (ZHyp v);

fun brc_trace (BRCtx (x1, x2, x3, x4, x5, x6, x7)) = x1;

fun brc_Hs (BRCtx (x1, x2, x3, x4, x5, x6, x7)) = x7;

fun could_reshyp hs (a1 :: uu) = list_ex (could_unify a1) hs
  | could_reshyp hs [] = false;

fun th_prop (Thm_rep_ext (th_maxidx, th_tpairs, th_prop, more)) = th_prop;

fun strip_imp_prems t =
  (case dest_imp t of NONE => [] | SOME (a, b) => a :: strip_imp_prems b);

fun prems_of th = strip_imp_prems (th_prop th);

fun strip_imp_concl t =
  (case dest_imp t of NONE => t | SOME (_, a) => strip_imp_concl a);

fun concl_of th = strip_imp_concl (th_prop th);

fun could_bires hs b eres_flg rule =
  could_unify (concl_of rule) b andalso
    (not eres_flg orelse could_reshyp hs (prems_of rule));

fun brc_B (BRCtx (x1, x2, x3, x4, x5, x6, x7)) = x6;

fun res rep ctx [] = RQ_Empty
  | res rep ctx ((eres_flg, rule) :: brules) =
    (if brc_trace ctx orelse
          could_bires (brc_Hs ctx) (brc_B ctx) eres_flg (rep rule)
      then RQ_Make (ctx, (eres_flg, rule), brules) else res rep ctx brules);

fun type_unify alg t u st = unify_aux alg t u st;

fun downto a b =
  (if IntInf.< (a, b) then []
    else a :: downto (IntInf.- (a, (1 : IntInf.int))) b);

val dummyT : typ = Type ("dummy", []);

fun liftMP m = map_option (fn a => ([], a)) m;

fun mk_app b x =
  let
    val (i, (j, p)) = x;
  in
    (if b then (IntInf.- (i, (1 : IntInf.int)), (j, p %% Proofterm.PBound i))
      else (i, (IntInf.- (j, (1 : IntInf.int)), p % SOME (Bound j))))
  end;

fun raiseP e = SOME ([], Err e);

fun var_eq v w =
  equal_proda equal_literal equal_integer (fst v) (fst w) andalso
    (((snd v) : typ) = (snd w));

fun map_res f (Ok x1) = Ok (f x1)
  | map_res f (Err x2) = Err x2;

fun map_zproof typ term (ZConstp (a, insts)) =
  bindZ (map_insts typ term insts) (fn instsa => returnZ (ZConstp (a, instsa)))
  | map_zproof typ term (ZAbst (a, t, p)) =
    bindZ (map_zproof typ term p) (fn pa => returnZ (ZAbst (a, typ t, pa)))
  | map_zproof typ term (ZAbsp (a, t, p)) =
    bindZ (term t)
      (fn ta =>
        bindZ (map_zproof typ term p) (fn pa => returnZ (ZAbsp (a, ta, pa))))
  | map_zproof typ term (ZAppt (p, t)) =
    bindZ (map_zproof typ term p)
      (fn pa => bindZ (term t) (fn ta => returnZ (ZAppt (pa, ta))))
  | map_zproof typ term (ZAppp (p, q)) =
    bindZ (map_zproof typ term p)
      (fn pa =>
        bindZ (map_zproof typ term q) (fn qa => returnZ (ZAppp (pa, qa))))
  | map_zproof typ term ZNop = returnZ ZNop
  | map_zproof typ term (ZBoundp v) = returnZ (ZBoundp v)
  | map_zproof typ term (ZHyp v) = returnZ (ZHyp v)
  | map_zproof typ term (OFCLASSp (v, va)) = returnZ (OFCLASSp (v, va));

fun zincr_boundvars inc t =
  (if ((inc : IntInf.int) = (0 : IntInf.int)) then t
    else zincr_bv inc (0 : IntInf.int) t);

fun zsubst_bound arg lev (ZBound i) =
  (if IntInf.< (i, lev) then ZBound i
    else (if ((i : IntInf.int) = lev) then zincr_boundvars lev arg
           else ZBound (IntInf.- (i, (1 : IntInf.int)))))
  | zsubst_bound arg lev (ZAbs (a, ta, t)) =
    ZAbs (a, ta, zsubst_bound arg (IntInf.+ (lev, (1 : IntInf.int))) t)
  | zsubst_bound arg lev (ZApp (t, u)) =
    ZApp (zsubst_bound arg lev t, zsubst_bound arg lev u)
  | zsubst_bound arg lev (ZVar (v, va)) = ZVar (v, va)
  | zsubst_bound arg lev (ZConst0 v) = ZConst0 v
  | zsubst_bound arg lev (ZConst1 (v, va)) = ZConst1 (v, va)
  | zsubst_bound arg lev (ZConst (v, va)) = ZConst (v, va)
  | zsubst_bound arg lev (OFCLASS (v, va)) = OFCLASS (v, va);

fun subst_term_bound arg body = zsubst_bound arg (0 : IntInf.int) body;

fun znorm_type_aux tye t =
  (case t
    of ZTVar (v, s) =>
      bindZ (liftMZ (type_lookup tye v s))
        (fn a =>
          (case a of NONE => returnZ t
            | SOME u => znorm_type_aux tye (ztyp_of u)))
    | ZFun (u, v) =>
      bindZ (znorm_type_aux tye u)
        (fn ua =>
          bindZ (znorm_type_aux tye v) (fn va => returnZ (ZFun (ua, va))))
    | ZProp => returnZ t | ZType0 _ => returnZ t
    | ZType1 (a, u) =>
      bindZ (znorm_type_aux tye u) (fn ua => returnZ (ZType1 (a, ua)))
    | ZType (a, us) =>
      bindZ (mapZ (znorm_type_aux tye) us)
        (fn usa => returnZ (ZType (a, usa))));

fun znorm_type tye t =
  (if Vartab.is_empty tye then returnZ t else znorm_type_aux tye t);

fun znorm_term_aux x =
  (case snd x
    of ZVar (xi, t) =>
      bindZ (zlookup (fst (fst x)) (snd (fst x)) xi t)
        (fn a =>
          (case a
            of NONE =>
              bindZ (znorm_type (Envir.type_env (snd (fst x))) t)
                (fn ta => returnZ (ZVar (xi, ta)))
            | SOME u => znorm_term_aux (fst x, u)))
    | ZBound integer => returnZ (ZBound integer)
    | ZConst0 literal => returnZ (ZConst0 literal)
    | ZConst1 (a, t) =>
      bindZ (znorm_type (Envir.type_env (snd (fst x))) t)
        (fn ta => returnZ (ZConst1 (a, ta)))
    | ZConst (a, ts) =>
      bindZ (mapZ (znorm_type (Envir.type_env (snd (fst x)))) ts)
        (fn tsa => returnZ (ZConst (a, tsa)))
    | ZAbs (a, t, b) =>
      bindZ (znorm_type (Envir.type_env (snd (fst x))) t)
        (fn ta =>
          bindZ (znorm_term_aux (fst x, b))
            (fn ba => returnZ (ZAbs (a, ta, ba))))
    | ZApp (g, u) =>
      (case g
        of ZVar (_, _) =>
          bindZ (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZBound _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))))
        | ZBound _ =>
          bindZ (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZBound _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))))
        | ZConst0 _ =>
          bindZ (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZBound _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))))
        | ZConst1 (_, _) =>
          bindZ (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZBound _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))))
        | ZConst (_, _) =>
          bindZ (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZBound _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))))
        | ZAbs (_, _, body) => znorm_term_aux (fst x, subst_term_bound u body)
        | ZApp (_, _) =>
          bindZ (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZBound _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))))
        | OFCLASS (_, _) =>
          bindZ (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZBound _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindZ (znorm_term_aux (fst x, u))
                    (fn nu => returnZ (ZApp (nf, nu))))))
    | OFCLASS (ztyp, literal) => returnZ (OFCLASS (ztyp, literal)));

fun beta_norm_term t =
  (case t of ZVar (_, _) => SOME t | ZBound _ => SOME t | ZConst0 _ => SOME t
    | ZConst1 (_, _) => SOME t | ZConst (_, _) => SOME t
    | ZAbs (a, ta, b) =>
      bind (beta_norm_term b) (fn ba => SOME (ZAbs (a, ta, ba)))
    | ZApp (f, u) =>
      (case f
        of ZVar (_, _) =>
          bind (beta_norm_term f)
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZBound _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZAbs (_, _, body) => beta_norm_term (subst_term_bound u body)
                | ZApp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))))
        | ZBound _ =>
          bind (beta_norm_term f)
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZBound _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZAbs (_, _, body) => beta_norm_term (subst_term_bound u body)
                | ZApp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))))
        | ZConst0 _ =>
          bind (beta_norm_term f)
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZBound _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZAbs (_, _, body) => beta_norm_term (subst_term_bound u body)
                | ZApp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))))
        | ZConst1 (_, _) =>
          bind (beta_norm_term f)
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZBound _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZAbs (_, _, body) => beta_norm_term (subst_term_bound u body)
                | ZApp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))))
        | ZConst (_, _) =>
          bind (beta_norm_term f)
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZBound _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZAbs (_, _, body) => beta_norm_term (subst_term_bound u body)
                | ZApp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))))
        | ZAbs (_, _, body) => beta_norm_term (subst_term_bound u body)
        | ZApp (_, _) =>
          bind (beta_norm_term f)
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZBound _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZAbs (_, _, body) => beta_norm_term (subst_term_bound u body)
                | ZApp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))))
        | OFCLASS (_, _) =>
          bind (beta_norm_term f)
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZBound _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | ZAbs (_, _, body) => beta_norm_term (subst_term_bound u body)
                | ZApp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZApp (nf, nu))))))
    | OFCLASS (_, _) => SOME t);

fun znorm_term ta env t =
  (if env_is_empty env then liftOZ (beta_norm_term t)
    else znorm_term_aux ((ta, env), t));

fun imp_prf (Const (c, u) $ a $ b) i m =
  (if ((m : IntInf.int) = (0 : IntInf.int)) then Proofterm.PBound i
    else (if ((c : string) = "Pure.imp")
           then Proofterm.AbsP ("H", NONE,
                  imp_prf b (IntInf.+ (i, (1 : IntInf.int)))
                    (IntInf.- (m, (1 : IntInf.int))))
           else Proofterm.PBound i))
  | imp_prf (Const (v, va)) i m = Proofterm.PBound i
  | imp_prf (Free (v, va)) i m = Proofterm.PBound i
  | imp_prf (Var (v, va)) i m = Proofterm.PBound i
  | imp_prf (Bound v) i m = Proofterm.PBound i
  | imp_prf (Abs (v, va, vb)) i m = Proofterm.PBound i
  | imp_prf (Const (vb, vc) $ va) i m = Proofterm.PBound i
  | imp_prf (Free (vb, vc) $ va) i m = Proofterm.PBound i
  | imp_prf (Var (vb, vc) $ va) i m = Proofterm.PBound i
  | imp_prf (Bound vb $ va) i m = Proofterm.PBound i
  | imp_prf (Abs (vb, vc, vd) $ va) i m = Proofterm.PBound i
  | imp_prf (Free (vd, ve) $ vc $ va) i m = Proofterm.PBound i
  | imp_prf (Var (vd, ve) $ vc $ va) i m = Proofterm.PBound i
  | imp_prf (Bound vd $ vc $ va) i m = Proofterm.PBound i
  | imp_prf (Abs (vd, ve, vf) $ vc $ va) i m = Proofterm.PBound i
  | imp_prf (vd $ ve $ vc $ va) i m = Proofterm.PBound i;

fun all_prf i m (Const (c, u) $ Abs (a, ta, t)) =
  (if ((c : string) = "Pure.all") then Proofterm.Abst (a, NONE, all_prf i m t)
    else imp_prf (Const (c, u) $ Abs (a, ta, t)) (IntInf.~ i) m)
  | all_prf i m (Const (v, va)) = imp_prf (Const (v, va)) (IntInf.~ i) m
  | all_prf i m (Free (v, va)) = imp_prf (Free (v, va)) (IntInf.~ i) m
  | all_prf i m (Var (v, va)) = imp_prf (Var (v, va)) (IntInf.~ i) m
  | all_prf i m (Bound v) = imp_prf (Bound v) (IntInf.~ i) m
  | all_prf i m (Abs (v, va, vb)) = imp_prf (Abs (v, va, vb)) (IntInf.~ i) m
  | all_prf i m (Free (vb, vc) $ va) =
    imp_prf (Free (vb, vc) $ va) (IntInf.~ i) m
  | all_prf i m (Var (vb, vc) $ va) = imp_prf (Var (vb, vc) $ va) (IntInf.~ i) m
  | all_prf i m (Bound vb $ va) = imp_prf (Bound vb $ va) (IntInf.~ i) m
  | all_prf i m (Abs (vb, vc, vd) $ va) =
    imp_prf (Abs (vb, vc, vd) $ va) (IntInf.~ i) m
  | all_prf i m (vb $ vc $ va) = imp_prf (vb $ vc $ va) (IntInf.~ i) m
  | all_prf i m (v $ Const (vb, vc)) =
    imp_prf (v $ Const (vb, vc)) (IntInf.~ i) m
  | all_prf i m (v $ Free (vb, vc)) = imp_prf (v $ Free (vb, vc)) (IntInf.~ i) m
  | all_prf i m (v $ Var (vb, vc)) = imp_prf (v $ Var (vb, vc)) (IntInf.~ i) m
  | all_prf i m (v $ Bound vb) = imp_prf (v $ Bound vb) (IntInf.~ i) m
  | all_prf i m (v $ (vb $ vc)) = imp_prf (v $ (vb $ vc)) (IntInf.~ i) m;

fun handleP m h =
  (case m of NONE => m | SOME (_, Ok _) => m
    | SOME (ws, Err e) => map_option (fn (wsa, a) => (ws @ wsa, a)) (h e));

fun mk_AbsP xs p = foldr (fn _ => (fn a => Proofterm.AbsP ("H", NONE, a))) xs p;

fun returnP x = SOME ([], Ok x);

fun zdedup_vars [] = []
  | zdedup_vars (v :: vs) =
    v :: zdedup_vars (filter (fn w => not (zvar_eq w v)) vs);

fun zlift_prems ta inc k prf ts bs i j (Const (c, u) $ a $ b) =
  (if ((c : string) = "Pure.imp")
    then bindZ (zterm_of ta a)
           (fn aa =>
             bindZ (zlift_prems ta inc k prf ts (true :: bs)
                     (IntInf.+ (i, (1 : IntInf.int))) j b)
               (fn p => returnZ (ZAbsp ("H", aa, p))))
    else bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
           (fn p =>
             returnZ
               (zAppps p
                 (map (fn ka =>
                        snd (snd (foldr zmk_app bs
                                   (IntInf.- (i, (1 : IntInf.int)),
                                     (IntInf.- (j, (1 : IntInf.int)),
                                       ZBoundp ka)))))
                   (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i)))))
  | zlift_prems taa inc k prf ts bs i j (Const (c, u) $ Abs (a, ta, t)) =
    (if ((c : string) = "Pure.all")
      then bindZ (zlift_prems taa inc k prf (ztyp_of ta :: ts) (false :: bs) i
                   (IntInf.+ (j, (1 : IntInf.int))) t)
             (fn p => returnZ (ZAbst (a, ztyp_of ta, p)))
      else bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
             (fn p =>
               returnZ
                 (zAppps p
                   (map (fn ka =>
                          snd (snd (foldr zmk_app bs
                                     (IntInf.- (i, (1 : IntInf.int)),
                                       (IntInf.- (j, (1 : IntInf.int)),
 ZBoundp ka)))))
                     (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int)))
                       i)))))
  | zlift_prems ta inc k prf ts bs i j (Const (v, va)) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Free (v, va)) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Var (v, va)) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Bound v) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Abs (v, va, vb)) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ Const (v, vd)) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ Free (v, vd)) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ Var (v, vd)) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ Bound v) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ (v $ vd)) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Free (vb, vc) $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Var (vb, vc) $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Bound vb $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Abs (vb, vc, vd) $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Free (vd, ve) $ vc $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Var (vd, ve) $ vc $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Bound vd $ vc $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Abs (vd, ve, vf) $ vc $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (vd $ ve $ vc $ va) =
    bindZ (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        returnZ
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))));

fun of_nat_aux A_ inc Zero_nat i = i
  | of_nat_aux A_ inc (Suc n) i = of_nat_aux A_ inc n (inc i);

fun of_nat A_ n =
  of_nat_aux A_
    (fn i =>
      plus ((plus_semigroup_add o semigroup_add_numeral o
              numeral_semiring_numeral o semiring_numeral_semiring_1)
             A_)
        i (one ((one_numeral o numeral_semiring_numeral o
                  semiring_numeral_semiring_1)
                 A_)))
    n (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
              A_));

fun integer_of_nat x = of_nat semiring_1_integer x;

fun zlift_proof ta gprop inc prems prf =
  bindZ (mapZ (zterm_of ta) prems)
    (fn asa =>
      bindZ (zlift_prems ta inc (integer_of_nat (size_list prems)) prf [] []
              (0 : IntInf.int) (0 : IntInf.int) gprop)
        (fn p => returnZ (zAbsps asa p)));

fun zlookup_var [] v = NONE
  | zlookup_var ((w, x) :: xs) v =
    (if zvar_eq w v then SOME x else zlookup_var xs v);

fun zmk_asm_prf c i m = zall_prf i m c;

fun zsubst_proof_bound arg lev (ZAbsp (a, t, p)) =
  ZAbsp (a, zsubst_bound arg lev t, zsubst_proof_bound arg lev p)
  | zsubst_proof_bound arg lev (ZAbst (a, t, p)) =
    ZAbst (a, t, zsubst_proof_bound arg (IntInf.+ (lev, (1 : IntInf.int))) p)
  | zsubst_proof_bound arg lev (ZAppp (p, q)) =
    ZAppp (zsubst_proof_bound arg lev p, zsubst_proof_bound arg lev q)
  | zsubst_proof_bound arg lev (ZAppt (p, t)) =
    ZAppt (zsubst_proof_bound arg lev p, zsubst_bound arg lev t)
  | zsubst_proof_bound arg lev ZNop = ZNop
  | zsubst_proof_bound arg lev (ZConstp v) = ZConstp v
  | zsubst_proof_bound arg lev (ZBoundp v) = ZBoundp v
  | zsubst_proof_bound arg lev (ZHyp v) = ZHyp v
  | zsubst_proof_bound arg lev (OFCLASSp (v, va)) = OFCLASSp (v, va);

fun subst_proof_bound arg body = zsubst_proof_bound arg (0 : IntInf.int) body;

fun beta_norm_prooft p =
  (case p of ZNop => SOME p | ZConstp _ => SOME p | ZBoundp _ => SOME p
    | ZAbst (a, t, q) =>
      bind (beta_norm_prooft q) (fn qa => SOME (ZAbst (a, t, qa)))
    | ZAbsp (_, _, _) => SOME p
    | ZAppt (f, u) =>
      (case f
        of ZNop =>
          bind (beta_norm_prooft f)
            (fn nf =>
              (case nf
                of ZNop =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZConstp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZBoundp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAbst (_, _, body) =>
                  beta_norm_prooft (subst_proof_bound u body)
                | ZAbsp (_, _, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppt (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZHyp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | OFCLASSp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))))
        | ZConstp _ =>
          bind (beta_norm_prooft f)
            (fn nf =>
              (case nf
                of ZNop =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZConstp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZBoundp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAbst (_, _, body) =>
                  beta_norm_prooft (subst_proof_bound u body)
                | ZAbsp (_, _, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppt (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZHyp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | OFCLASSp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))))
        | ZBoundp _ =>
          bind (beta_norm_prooft f)
            (fn nf =>
              (case nf
                of ZNop =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZConstp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZBoundp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAbst (_, _, body) =>
                  beta_norm_prooft (subst_proof_bound u body)
                | ZAbsp (_, _, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppt (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZHyp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | OFCLASSp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))))
        | ZAbst (_, _, body) => beta_norm_prooft (subst_proof_bound u body)
        | ZAbsp (_, _, _) =>
          bind (beta_norm_prooft f)
            (fn nf =>
              (case nf
                of ZNop =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZConstp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZBoundp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAbst (_, _, body) =>
                  beta_norm_prooft (subst_proof_bound u body)
                | ZAbsp (_, _, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppt (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZHyp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | OFCLASSp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))))
        | ZAppt (_, _) =>
          bind (beta_norm_prooft f)
            (fn nf =>
              (case nf
                of ZNop =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZConstp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZBoundp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAbst (_, _, body) =>
                  beta_norm_prooft (subst_proof_bound u body)
                | ZAbsp (_, _, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppt (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZHyp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | OFCLASSp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))))
        | ZAppp (_, _) =>
          bind (beta_norm_prooft f)
            (fn nf =>
              (case nf
                of ZNop =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZConstp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZBoundp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAbst (_, _, body) =>
                  beta_norm_prooft (subst_proof_bound u body)
                | ZAbsp (_, _, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppt (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZHyp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | OFCLASSp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))))
        | ZHyp _ =>
          bind (beta_norm_prooft f)
            (fn nf =>
              (case nf
                of ZNop =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZConstp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZBoundp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAbst (_, _, body) =>
                  beta_norm_prooft (subst_proof_bound u body)
                | ZAbsp (_, _, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppt (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZHyp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | OFCLASSp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))))
        | OFCLASSp (_, _) =>
          bind (beta_norm_prooft f)
            (fn nf =>
              (case nf
                of ZNop =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZConstp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZBoundp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAbst (_, _, body) =>
                  beta_norm_prooft (subst_proof_bound u body)
                | ZAbsp (_, _, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppt (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZAppp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | ZHyp _ =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu)))
                | OFCLASSp (_, _) =>
                  bind (beta_norm_term u) (fn nu => SOME (ZAppt (nf, nu))))))
    | ZAppp (_, _) => SOME p | ZHyp _ => SOME p | OFCLASSp (_, _) => SOME p);

fun term_types (Const (c, t)) = [t]
  | term_types (Free (x, t)) = [t]
  | term_types (Var (xi, t)) = [t]
  | term_types (Bound i) = []
  | term_types (Abs (x, ta, t)) = ta :: term_types t
  | term_types (t $ u) = term_types t @ term_types u;

fun typ_tvars (Type (a, ts)) = maps typ_tvars ts
  | typ_tvars (TFree (a, s)) = []
  | typ_tvars (TVar (xi, s)) = [(xi, s)];

fun visible_tvars ts =
  dedup (equal_prod (equal_prod equal_literal equal_integer)
          (equal_list equal_literal))
    (maps (fn t => maps typ_tvars (term_types t)) ts);

fun term_vars (Var (xi, t)) = [(xi, t)]
  | term_vars (Abs (x, ta, t)) = term_vars t
  | term_vars (t $ u) = term_vars t @ term_vars u
  | term_vars (Const (v, va)) = []
  | term_vars (Free (v, va)) = []
  | term_vars (Bound v) = [];

fun visible_vars ts = maps term_vars ts;

fun zsubst_term typ var (ZVar (x, t)) =
  (case var (x, typ t) of NONE => ZVar (x, typ t) | SOME ta => ta)
  | zsubst_term typ var (ZBound i) = ZBound i
  | zsubst_term typ var (ZConst0 a) = ZConst0 a
  | zsubst_term typ var (ZConst1 (a, t)) = ZConst1 (a, typ t)
  | zsubst_term typ var (ZConst (a, ts)) = ZConst (a, map typ ts)
  | zsubst_term typ var (ZAbs (a, ta, t)) =
    ZAbs (a, typ ta, zsubst_term typ var t)
  | zsubst_term typ var (ZApp (t, u)) =
    ZApp (zsubst_term typ var t, zsubst_term typ var u)
  | zsubst_term typ var (OFCLASS (t, c)) = OFCLASS (typ t, c);

fun znorm_proof ta env visible prf =
  (if env_is_empty env orelse null visible then liftOZ (beta_norm_prooft prf)
    else bindZ (if Vartab.is_empty (Envir.type_env env) then returnZ NONE
                 else bindZ (mapZ (fn (v, s) =>
                                    znorm_type (Envir.type_env env)
                                      (ZTVar (v, s)))
                              (visible_tvars visible))
                        (fn us =>
                          returnZ (SOME (zip (visible_tvars visible) us))))
           (fn instT =>
             let
               val inst_typ =
                 (case instT of NONE => id
                   | SOME xs =>
                     (if null xs then id
                       else zsubst_type
                              (map_of
                                (equal_prod
                                  (equal_prod equal_literal equal_integer)
                                  (equal_list equal_literal))
                                xs)));
               val vs =
                 zdedup_vars
                   (map (fn (a, t) => (a, inst_typ (ztyp_of t)))
                     (visible_vars visible));
             in
               bindZ (mapZ (fn (a, t) => znorm_term ta env (ZVar (a, t))) vs)
                 (fn us =>
                   let
                     val inst_term =
                       zsubst_term inst_typ (zlookup_var (zip vs us));
                   in
                     bindZ (map_zproof inst_typ
                             (fn t => liftOZ (beta_norm_term (inst_term t)))
                             prf)
                       (fn p => liftOZ (beta_norm_prooft p))
                   end)
             end));

fun max A_ a b = (if less_eq A_ a b then b else a);

fun insert_list (xi, t) [] = [(xi, [t])]
  | insert_list (xi, t) ((yj, ts) :: tab) =
    (if equal_proda equal_literal equal_integer xi yj
      then (yj, (if list_ex (fn a => ((t : typ) = a)) ts then ts
                  else t :: ts)) ::
             tab
      else (yj, ts) :: insert_list (xi, t) tab);

fun add_vars (Var (xi, t)) tab = insert_list (xi, t) tab
  | add_vars (Abs (uu, uv, t)) tab = add_vars t tab
  | add_vars (t $ u) tab = add_vars u (add_vars t tab)
  | add_vars (Const (v, va)) tab = tab
  | add_vars (Free (v, va)) tab = tab
  | add_vars (Bound v) tab = tab;

fun inst_typ iT (Type (a, ts)) = Type (a, map (inst_typ iT) ts)
  | inst_typ iT (TFree (a, s)) = TFree (a, s)
  | inst_typ iT (TVar (xi, s)) =
    (case map_of
            (equal_prod (equal_prod equal_literal equal_integer)
              (equal_list equal_literal))
            iT (xi, s)
      of NONE => TVar (xi, s) | SOME t => t);

fun incr_tvar inc (Type (a, ts)) = Type (a, map (incr_tvar inc) ts)
  | incr_tvar inc (TFree (a, s)) = TFree (a, s)
  | incr_tvar inc (TVar ((a, i), s)) = TVar ((a, IntInf.+ (i, inc)), s);

fun incr_idx ts inc lev (Var ((x, i), t)) =
  combound
    (Var ((x, IntInf.+ (i, inc)),
      foldr (fn ta => fn u => Type ("fun", [ta, u])) ts (incr_tvar inc t)))
    lev (size_list ts)
  | incr_idx ts inc lev (Free (x, t)) = Free (x, incr_tvar inc t)
  | incr_idx ts inc lev (Abs (x, ta, t)) =
    Abs (x, incr_tvar inc ta,
      incr_idx ts inc (IntInf.+ (lev, (1 : IntInf.int))) t)
  | incr_idx ts inc lev (t $ u) = incr_idx ts inc lev t $ incr_idx ts inc lev u
  | incr_idx ts inc lev (Const (c, t)) = Const (c, incr_tvar inc t)
  | incr_idx ts inc lev (Bound i) = Bound i;

fun lift_prf inc ts lev (Proofterm.Abst (a, t, p)) =
  Proofterm.Abst (a, map_option (incr_tvar inc) t,
    lift_prf inc ts (IntInf.+ (lev, (1 : IntInf.int))) p)
  | lift_prf inc ts lev (Proofterm.AbsP (a, t, p)) =
    Proofterm.AbsP (a, map_option (incr_idx ts inc lev) t,
      lift_prf inc ts lev p)
  | lift_prf inc ts lev (p % t) =
    lift_prf inc ts lev p % map_option (incr_idx ts inc lev) t
  | lift_prf inc ts lev (p %% q) =
    lift_prf inc ts lev p %% lift_prf inc ts lev q
  | lift_prf inc ts lev (Proofterm.PAxm (aa, a, us)) =
    Proofterm.PAxm (aa, a, map_option (map (incr_tvar inc)) us)
  | lift_prf inc ts lev (Proofterm.PClass (t, c)) =
    Proofterm.PClass (incr_tvar inc t, c)
  | lift_prf inc ts lev (Proofterm.Oracle (aa, a, us)) =
    Proofterm.Oracle (aa, a, map_option (map (incr_tvar inc)) us)
  | lift_prf inc ts lev (Proofterm.PThm (h, b)) =
    Proofterm.PThm
      ((fn {serial, command_pos, theory_name, thm_name, prop, ...} : Proofterm.thm_header =>
      fn types => Proofterm.thm_header serial command_pos theory_name thm_name prop types)
         h (map_option (map (incr_tvar inc))
             ((fn h : Proofterm.thm_header => #types h) h)),
        b)
  | lift_prf inc ts lev Proofterm.MinProof = Proofterm.MinProof
  | lift_prf inc ts lev (Proofterm.PBound v) = Proofterm.PBound v
  | lift_prf inc ts lev (Proofterm.Hyp v) = Proofterm.Hyp v;

fun empty_env m =
  Envir.Envir {maxidx = m, tenv = Vartab.empty, tyenv = Vartab.empty};

fun mk_equals tu =
  let
    val (t, u) = tu;
  in
    bindM (fastype_of t)
      (fn ta =>
        return
          (Const ("Pure.eq", Type ("fun", [ta, Type ("fun", [ta, propT])])) $
             t $
            u))
  end;

fun fast_indexname_less xi yj =
  IntInf.< (snd xi, snd yj) orelse
    (((snd xi) : IntInf.int) = (snd yj)) andalso
      (IntInf.< (IntInf.fromInt (String.size (fst
       xi)), IntInf.fromInt (String.size (fst yj))) orelse
        (((IntInf.fromInt (String.size (fst
 xi))) : IntInf.int) = (IntInf.fromInt (String.size (fst yj)))) andalso
          (((fst xi) : string) < (fst yj)));

fun insert_key p [] = [p]
  | insert_key p (q :: qs) =
    (if fast_indexname_less (fst q) (fst p) then q :: insert_key p qs
      else p :: q :: qs);

fun sort_keys tab = foldr insert_key tab [];

fun brrule RQ_Empty = NONE
  | brrule (RQ_Make (uu, r, uv)) = SOME r
  | brrule (RQ_App (r, uw, ux)) = SOME r;

fun th_maxidx (Thm_rep_ext (th_maxidx, th_tpairs, th_prop, more)) = th_maxidx;

fun brc_state (BRCtx (x1, x2, x3, x4, x5, x6, x7)) = x3;

fun brc_match (BRCtx (x1, x2, x3, x4, x5, x6, x7)) = x2;

fun brc_goal (BRCtx (x1, x2, x3, x4, x5, x6, x7)) = x5;

fun brc_dst (BRCtx (x1, x2, x3, x4, x5, x6, x7)) = x4;

fun full_prop_of tpairs prop =
  bindM (mapM mk_equals tpairs) (fn eqs => return (list_implies eqs prop));

fun unify_types alg t u env =
  (if ((t : typ) = u) then return env
    else handlea
           (bindM (type_unify alg u t (Envir.type_env env, Envir.maxidx_of env))
             (fn (tye, maxidx) =>
               return
                 (Envir.Envir {maxidx = maxidx, tenv = (Envir.term_env env),
                   tyenv = tye})))
           (fn e =>
             (case e of Unif _ => raisea e | Pattern => raisea e
               | Match => raisea e
               | TUnify => raisea (Unif (Typ_Clash (Envir.type_env env, t, u)))
               | Type_Match => raisea e | Class_Error _ => raisea e
               | Type_Error (_, _, _) => raisea e
               | Term_Error (_, _) => raisea e | Failure _ => raisea e
               | Subscript => raisea e | Unequal_Lengths => raisea e
               | Dup _ => raisea e)));

fun unify_vars alg (t :: us) env = foldM (unify_types alg t) us env
  | unify_vars alg [] env = return env;

fun unify_var_types alg th1 th2 env =
  (case bindM (full_prop_of (fst th1) (snd th1))
          (fn p1 =>
            bindM (full_prop_of (fst th2) (snd th2))
              (fn p2 => let
                          val vars = sort_keys (add_vars p2 (add_vars p1 []));
                        in
                          foldM (fn (_, a) => unify_vars alg a) vars env
                        end))
    of NONE => liftMT (map_option (map_res SOME) NONE)
    | SOME (Ok aa) => liftMT (map_option (map_res SOME) (SOME (Ok aa)))
    | SOME (Err (Unif tr)) => bindT (emitT (Ev_Unif tr)) (fn _ => returnT NONE)
    | SOME (Err Pattern) =>
      liftMT (map_option (map_res SOME) (SOME (Err Pattern)))
    | SOME (Err Match) => liftMT (map_option (map_res SOME) (SOME (Err Match)))
    | SOME (Err TUnify) =>
      liftMT (map_option (map_res SOME) (SOME (Err TUnify)))
    | SOME (Err Type_Match) =>
      liftMT (map_option (map_res SOME) (SOME (Err Type_Match)))
    | SOME (Err (Class_Error class_error)) =>
      liftMT (map_option (map_res SOME) (SOME (Err (Class_Error class_error))))
    | SOME (Err (Type_Error (literal, list1, list2))) =>
      liftMT
        (map_option (map_res SOME)
          (SOME (Err (Type_Error (literal, list1, list2)))))
    | SOME (Err (Term_Error (literal, lista))) =>
      liftMT
        (map_option (map_res SOME) (SOME (Err (Term_Error (literal, lista)))))
    | SOME (Err (Failure literal)) =>
      liftMT (map_option (map_res SOME) (SOME (Err (Failure literal))))
    | SOME (Err Subscript) =>
      liftMT (map_option (map_res SOME) (SOME (Err Subscript)))
    | SOME (Err Unequal_Lengths) =>
      liftMT (map_option (map_res SOME) (SOME (Err Unequal_Lengths)))
    | SOME (Err (Dup prod)) =>
      liftMT (map_option (map_res SOME) (SOME (Err (Dup prod)))));

fun strip_all_body t =
  (case dest_all t of NONE => t | SOME (_, (_, a)) => strip_all_body a);

fun strip_assums_imp nasms hs b =
  (if ((nasms : IntInf.int) = (0 : IntInf.int)) then (hs, b)
    else (case dest_imp b of NONE => (hs, b)
           | SOME (h, a) =>
             strip_assums_imp (IntInf.- (nasms, (1 : IntInf.int))) (h :: hs)
               a));

fun strip_assums_all params t =
  (case dest_all t of NONE => (params, t)
    | SOME (a, (ta, b)) => strip_assums_all ((a, ta) :: params) b);

fun assum_problems nasms a = let
                               val (params, aa) = strip_assums_all [] a;
                               val (hs, b) = strip_assums_imp nasms [] aa;
                             in
                               (params, (rev hs, b))
                             end;

fun bicompose_body ops ctx env eres_flg rAs =
  (if eres_flg
    then (case rev rAs
           of [] =>
             raiseT
               (THM ("bicompose: no premises", (0 : IntInf.int), Orule_State))
           | a1 :: asa =>
             let
               val (params, (asms, concl)) =
                 assum_problems (IntInf.+ (bc_nlift ctx, (1 : IntInf.int))) a1;
             in
               tryasms ops ctx
                 (ER (env, params, concl, rlist_abs params concl, a1, asa)) asms
                 (1 : IntInf.int)
             end)
    else bindT (bo_unifiers ops env (bc_dpairs ctx))
           (fn us =>
             bindT (bo_pull ops us)
               (fn a =>
                 (case a of NONE => returnT BS_Empty
                   | SOME ((enva, tpairs), usa) =>
                     bindT (newAs (bo_variants ops) ctx (rev rAs)
                             (0 : IntInf.int) [bc_BBi ctx] tpairs)
                       (fn na =>
                         returnT
                           (BS_Its
                             (ctx, NONE, na, UQ_Cell ((enva, tpairs), usa),
                               BS_Empty)))))));

fun strip_assums2 b bi =
  (case (dest_imp b, dest_imp bi)
    of (NONE, _) =>
      (case (dest_all b, dest_all bi) of (NONE, _) => (b, bi)
        | (SOME (_, (_, _)), NONE) => (b, bi)
        | (SOME (a, (t, t1)), SOME (_, (_, t2))) =>
          let
            val (b1, b2) = strip_assums2 t1 t2;
          in
            (Abs (a, t, b1), Abs (a, t, b2))
          end)
    | (SOME (_, _), NONE) =>
      (case (dest_all b, dest_all bi) of (NONE, _) => (b, bi)
        | (SOME (_, (_, _)), NONE) => (b, bi)
        | (SOME (a, (t, t1)), SOME (_, (_, t2))) =>
          let
            val (b1, b2) = strip_assums2 t1 t2;
          in
            (Abs (a, t, b1), Abs (a, t, b2))
          end)
    | (SOME (_, b1), SOME (_, a)) => strip_assums2 b1 a);

fun strip_prems i asa b =
  (if ((i : IntInf.int) = (0 : IntInf.int)) then return (asa, b)
    else (case dest_imp b
           of NONE => raisea (Term_Error ("strip_prems", b :: asa))
           | SOME (a, ba) =>
             strip_prems (IntInf.- (i, (1 : IntInf.int))) (a :: asa) ba));

fun count_prems t =
  (case dest_imp t of NONE => (0 : IntInf.int)
    | SOME (_, b) => IntInf.+ ((1 : IntInf.int), count_prems b));

fun bicompose_aux ops alg flatten match_flg incremented state dst lifted
  eres_flg orule nsubgoal =
  let
    val (smax, (_, _)) = state;
    val (stpairs, (bs, (bi, c))) = dst;
    val (rmax, (rtpairs, rprop)) = orule;
    val nlift =
      IntInf.+ (count_prems
                  (strip_all_body
                    bi), (if eres_flg then (~1 : IntInf.int)
                           else (0 : IntInf.int)));
  in
    bindT (handleT (liftMT (strip_prems nsubgoal [] rprop))
            (fn e =>
              (case e of UExn (PExn (Unif _)) => raiseT e
                | UExn (PExn Pattern) => raiseT e
                | UExn (PExn Match) => raiseT e | UExn (PExn TUnify) => raiseT e
                | UExn (PExn Type_Match) => raiseT e
                | UExn (PExn (Class_Error _)) => raiseT e
                | UExn (PExn (Type_Error (_, _, _))) => raiseT e
                | UExn (PExn (Term_Error (_, _))) =>
                  raiseT
                    (THM ("bicompose: rule", (0 : IntInf.int), Orule_State))
                | UExn (PExn (Failure _)) => raiseT e
                | UExn (PExn Subscript) => raiseT e
                | UExn (PExn Unequal_Lengths) => raiseT e
                | UExn (PExn (Dup _)) => raiseT e | UExn CANTUNIFY => raiseT e
                | UExn ASSIGN => raiseT e | UExn CHANGE_FAIL => raiseT e
                | UExn Bind => raiseT e | THM (_, _, _) => raiseT e
                | ERROR _ => raiseT e | COMPOSE => raiseT e)))
      (fn (rAs, b) =>
        let
          val bBi = (if lifted then strip_assums2 b bi else (b, bi));
          val ctx =
            BCtx (flatten, match_flg, lifted, smax, bs, bi, c, rtpairs, nlift,
                   bBi, bBi :: rtpairs @ stpairs);
        in
          bindT (if incremented
                  then returnT (SOME (empty_env (max ord_integer rmax smax)))
                  else unify_var_types alg (snd state) (snd orule)
                         (empty_env (max ord_integer rmax smax)))
            (fn a =>
              (case a of NONE => returnT BS_Empty
                | SOME env => bicompose_body ops ctx env eres_flg rAs))
        end)
  end;

fun nprems_of th = count_prems (th_prop th);

fun th_tpairs (Thm_rep_ext (th_maxidx, th_tpairs, th_prop, more)) = th_tpairs;

fun incr_indexes ts inc t =
  (if null ts andalso ((inc : IntInf.int) = (0 : IntInf.int)) then t
    else incr_idx ts inc (0 : IntInf.int) t);

fun lift_all_aux inc ts (Const (c, u) $ h $ b) t =
  (if ((c : string) = "Pure.imp")
    then Const (c, u) $ h $ lift_all_aux inc ts b t
    else incr_indexes (rev ts) inc t)
  | lift_all_aux inc ts (Const (c, u) $ Abs (a, ta, b)) t =
    (if ((c : string) = "Pure.all")
      then Const (c, u) $ Abs (a, ta, lift_all_aux inc (ta :: ts) b t)
      else incr_indexes (rev ts) inc t)
  | lift_all_aux inc ts (Const (v, va)) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Free (v, va)) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Var (v, va)) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Bound v) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Abs (v, va, vb)) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Const (vb, vc) $ Const (v, vd)) t =
    incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Const (vb, vc) $ Free (v, vd)) t =
    incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Const (vb, vc) $ Var (v, vd)) t =
    incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Const (vb, vc) $ Bound v) t =
    incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Const (vb, vc) $ (v $ vd)) t =
    incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Free (vb, vc) $ va) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Var (vb, vc) $ va) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Bound vb $ va) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Abs (vb, vc, vd) $ va) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Free (vd, ve) $ vc $ va) t =
    incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Var (vd, ve) $ vc $ va) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Bound vd $ vc $ va) t = incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (Abs (vd, ve, vf) $ vc $ va) t =
    incr_indexes (rev ts) inc t
  | lift_all_aux inc ts (vd $ ve $ vc $ va) t = incr_indexes (rev ts) inc t;

fun lift_all inc gprop t = lift_all_aux inc [] gprop t;

fun lift_abs_aux inc ts (Const (c, u) $ h $ b) t =
  (if ((c : string) = "Pure.imp") then lift_abs_aux inc ts b t
    else incr_indexes (rev ts) inc t)
  | lift_abs_aux inc ts (Const (c, u) $ Abs (a, ta, b)) t =
    (if ((c : string) = "Pure.all")
      then Abs (a, ta, lift_abs_aux inc (ta :: ts) b t)
      else incr_indexes (rev ts) inc t)
  | lift_abs_aux inc ts (Const (v, va)) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Free (v, va)) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Var (v, va)) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Bound v) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Abs (v, va, vb)) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Const (vb, vc) $ Const (v, vd)) t =
    incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Const (vb, vc) $ Free (v, vd)) t =
    incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Const (vb, vc) $ Var (v, vd)) t =
    incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Const (vb, vc) $ Bound v) t =
    incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Const (vb, vc) $ (v $ vd)) t =
    incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Free (vb, vc) $ va) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Var (vb, vc) $ va) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Bound vb $ va) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Abs (vb, vc, vd) $ va) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Free (vd, ve) $ vc $ va) t =
    incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Var (vd, ve) $ vc $ va) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Bound vd $ vc $ va) t = incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (Abs (vd, ve, vf) $ vc $ va) t =
    incr_indexes (rev ts) inc t
  | lift_abs_aux inc ts (vd $ ve $ vc $ va) t = incr_indexes (rev ts) inc t;

fun lift_abs inc gprop t = lift_abs_aux inc [] gprop t;

fun lift_rule gprop gmax orule =
  let
    val inc = IntInf.+ (gmax, (1 : IntInf.int));
    val asa = strip_imp_prems (th_prop orule);
    val b = strip_imp_concl (th_prop orule);
  in
    Thm_rep_ext
      (IntInf.+ (th_maxidx orule, inc),
        map (fn (t, u) => (lift_abs inc gprop t, lift_abs inc gprop u))
          (th_tpairs orule),
        list_implies (map (lift_all inc gprop) asa) (lift_all inc gprop b), ())
  end;

fun pthm_of th = (th_maxidx th, (th_tpairs th, th_prop th));

fun compose ops alg ctx eres_flg rule =
  bicompose_aux ops alg true (brc_match ctx) true (pthm_of (brc_state ctx))
    (brc_dst ctx) true eres_flg
    (pthm_of (lift_rule (brc_goal ctx) (th_maxidx (brc_state ctx)) rule))
    (nprems_of rule);

fun brstep ops alg rep RQ_Empty = returnT RS_Done
  | brstep ops alg rep (RQ_Make (ctx, (eres_flg, rule), brules)) =
    bindT (compose ops alg ctx eres_flg (rep rule))
      (fn xq =>
        returnT (RS_Skip (RQ_App ((eres_flg, rule), xq, res rep ctx brules))))
  | brstep ops alg rep (RQ_App (r, xq, xqq)) =
    bindT (bpull ops xq)
      (fn a =>
        (case a of NONE => returnT (RS_Skip xqq)
          | SOME (th, xqa) =>
            returnT (RS_Result ((th, r), RQ_App (r, xqa, xqq)))));

fun lookup_var [] v = NONE
  | lookup_var ((w, x) :: xs) v =
    (if var_eq w v then SOME x else lookup_var xs v);

fun inst_term iT it (Const (c, t)) = Const (c, inst_typ iT t)
  | inst_term iT it (Free (x, t)) = Free (x, inst_typ iT t)
  | inst_term iT it (Var (xi, t)) =
    (case lookup_var it (xi, inst_typ iT t) of NONE => Var (xi, inst_typ iT t)
      | SOME ta => ta)
  | inst_term iT it (Bound i) = Bound i
  | inst_term iT it (Abs (x, ta, t)) =
    Abs (x, inst_typ iT ta, inst_term iT it t)
  | inst_term iT it (t $ u) = inst_term iT it t $ inst_term iT it u;

fun norm_same env ta t =
  not (could_beta_contract ta) andalso
    (list_all (fn v => is_none (Vartab.lookup (Envir.term_env env) (fst v)))
       (term_vars ta) andalso
      ((t : term) = ta));

fun can_lookup env v =
  (case lookup env (fst v) (snd v) of NONE => NONE | SOME (Ok _) => return true
    | SOME (Err _) => return false);

fun proof_combP p qs = foldl (fn a => fn b => a %% b) p qs;

fun lift_prems inc k prf ts bs i j (Const (c, u) $ a $ b) =
  (if ((c : string) = "Pure.imp")
    then Proofterm.AbsP ("H", NONE,
           lift_prems inc k prf ts (true :: bs) (IntInf.+ (i, (1 : IntInf.int)))
             j b)
    else proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
           (map (fn ka =>
                  snd (snd (foldr mk_app bs
                             (IntInf.- (i, (1 : IntInf.int)),
                               (IntInf.- (j, (1 : IntInf.int)),
                                 Proofterm.PBound ka)))))
             (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i)))
  | lift_prems inc k prf ts bs i j (Const (c, u) $ Abs (a, ta, t)) =
    (if ((c : string) = "Pure.all")
      then Proofterm.Abst (a, NONE,
             lift_prems inc k prf (ta :: ts) (false :: bs) i
               (IntInf.+ (j, (1 : IntInf.int))) t)
      else proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
             (map (fn ka =>
                    snd (snd (foldr mk_app bs
                               (IntInf.- (i, (1 : IntInf.int)),
                                 (IntInf.- (j, (1 : IntInf.int)),
                                   Proofterm.PBound ka)))))
               (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i)))
  | lift_prems inc k prf ts bs i j (Const (v, va)) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Free (v, va)) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Var (v, va)) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Bound v) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Abs (v, va, vb)) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Const (vb, vc) $ Const (v, vd)) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Const (vb, vc) $ Free (v, vd)) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Const (vb, vc) $ Var (v, vd)) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Const (vb, vc) $ Bound v) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Const (vb, vc) $ (v $ vd)) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Free (vb, vc) $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Var (vb, vc) $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Bound vb $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Abs (vb, vc, vd) $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Free (vd, ve) $ vc $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Var (vd, ve) $ vc $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Bound vd $ vc $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (Abs (vd, ve, vf) $ vc $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))
  | lift_prems inc k prf ts bs i j (vd $ ve $ vc $ va) =
    proof_combP (lift_prf inc (rev ts) (0 : IntInf.int) prf)
      (map (fn ka =>
             snd (snd (foldr mk_app bs
                        (IntInf.- (i, (1 : IntInf.int)),
                          (IntInf.- (j, (1 : IntInf.int)),
                            Proofterm.PBound ka)))))
        (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i));

fun lift_proof gprop inc prems prf =
  mk_AbsP prems
    (lift_prems inc (integer_of_nat (size_list prems)) prf [] []
      (0 : IntInf.int) (0 : IntInf.int) gprop);

fun mk_asm_prf c i m = all_prf i m c;

fun tvar_conflict tye v =
  (case Vartab.lookup tye (fst v) of NONE => false
    | SOME (s, _) => not (equal_lista equal_literal (snd v) s));

fun dummy_tfree s = TFree ("'" ^ "dummy", s);

fun conflicting_tvars tye ts =
  map (fn v => (v, dummy_tfree (snd v)))
    (remdups
      (equal_prod (equal_prod equal_literal equal_integer)
        (equal_list equal_literal))
      (filter (tvar_conflict tye) (maps typ_tvars ts)));

fun del_conflicting_tvars tye t = inst_typ (conflicting_tvars tye [t]) t;

fun norm_type_same tye ta t =
  list_all (fn v => is_none (Vartab.lookup tye (fst v))) (typ_tvars ta) andalso
    ((t : typ) = ta);

fun norm_types_P tye ts =
  handleP
    (liftMP
      (if Vartab.is_empty tye then return ts else mapM (norm_type_aux tye) ts))
    (fn e =>
      (case e of Unif _ => raiseP e | Pattern => raiseP e | Match => raiseP e
        | TUnify => raiseP e | Type_Match => raiseP e
        | Class_Error _ => raiseP e
        | Type_Error (s, _, _) =>
          bindP (warnP s)
            (fn _ =>
              let
                val tsa = map (del_conflicting_tvars tye) ts;
              in
                bindP (liftMP
                        (if Vartab.is_empty tye then return tsa
                          else mapM (norm_type_aux tye) tsa))
                  (fn tsb =>
                    returnP
                      (if Vartab.is_empty tye orelse
                            list_all2 (norm_type_same tye) tsa tsb
                        then ts else tsb))
              end)
        | Term_Error (_, _) => raiseP e | Failure _ => raiseP e
        | Subscript => raiseP e | Unequal_Lengths => raiseP e
        | Dup _ => raiseP e));

fun norm_type_P tye t =
  handleP (liftMP (norm_type tye t))
    (fn e =>
      (case e of Unif _ => raiseP e | Pattern => raiseP e | Match => raiseP e
        | TUnify => raiseP e | Type_Match => raiseP e
        | Class_Error _ => raiseP e
        | Type_Error (s, _, _) =>
          bindP (warnP s)
            (fn _ =>
              let
                val ta = del_conflicting_tvars tye t;
              in
                bindP (liftMP (norm_type tye ta))
                  (fn tb =>
                    returnP (if norm_type_same tye ta tb then t else tb))
              end)
        | Term_Error (_, _) => raiseP e | Failure _ => raiseP e
        | Subscript => raiseP e | Unequal_Lengths => raiseP e
        | Dup _ => raiseP e));

fun remdups_vars [] = []
  | remdups_vars (v :: vs) =
    (if list_ex (var_eq v) vs then remdups_vars vs else v :: remdups_vars vs);

fun filter_outM p [] = return []
  | filter_outM p (x :: xs) =
    bindM (p x)
      (fn b =>
        bindM (filter_outM p xs) (fn ys => return (if b then ys else x :: ys)));

fun del_conflicting_vars env t =
  bindM (filter_outM (can_lookup env) (remdups_vars (term_vars t)))
    (fn vs =>
      return
        (inst_term (conflicting_tvars (Envir.type_env env) (term_types t))
          (map (fn v => (v, Free ("dummy", snd v))) vs) t));

fun norm_term_P env t =
  handleP (liftMP (norm_term env t))
    (fn e =>
      (case e of Unif _ => raiseP e | Pattern => raiseP e | Match => raiseP e
        | TUnify => raiseP e | Type_Match => raiseP e
        | Class_Error _ => raiseP e
        | Type_Error (s, _, _) =>
          bindP (warnP s)
            (fn _ =>
              bindP (liftMP (del_conflicting_vars env t))
                (fn ta =>
                  bindP (liftMP (norm_term env ta))
                    (fn tb => returnP (if norm_same env ta tb then t else tb))))
        | Term_Error (_, _) => raiseP e | Failure _ => raiseP e
        | Subscript => raiseP e | Unequal_Lengths => raiseP e
        | Dup _ => raiseP e));

fun map_optionP f x =
  (case x of NONE => returnP NONE
    | SOME y => bindP (f y) (fn z => returnP (SOME z)));

fun norm_proof env (Proofterm.Abst (a, t, p)) =
  bindP (map_optionP (norm_type_P (Envir.type_env env)) t)
    (fn ta =>
      bindP (norm_proof env p) (fn pa => returnP (Proofterm.Abst (a, ta, pa))))
  | norm_proof env (Proofterm.AbsP (a, t, p)) =
    bindP (map_optionP (norm_term_P env) t)
      (fn ta =>
        bindP (norm_proof env p)
          (fn pa => returnP (Proofterm.AbsP (a, ta, pa))))
  | norm_proof env (p % t) =
    bindP (norm_proof env p)
      (fn pa =>
        bindP (map_optionP (norm_term_P env) t) (fn ta => returnP (pa % ta)))
  | norm_proof env (p %% q) =
    bindP (norm_proof env p)
      (fn pa => bindP (norm_proof env q) (fn qa => returnP (pa %% qa)))
  | norm_proof env (Proofterm.PAxm (aa, a, ts)) =
    bindP (map_optionP (norm_types_P (Envir.type_env env)) ts)
      (fn tsa => returnP (Proofterm.PAxm (aa, a, tsa)))
  | norm_proof env (Proofterm.PClass (t, c)) =
    bindP (norm_type_P (Envir.type_env env) t)
      (fn ta => returnP (Proofterm.PClass (ta, c)))
  | norm_proof env (Proofterm.Oracle (aa, a, ts)) =
    bindP (map_optionP (norm_types_P (Envir.type_env env)) ts)
      (fn tsa => returnP (Proofterm.Oracle (aa, a, tsa)))
  | norm_proof env (Proofterm.PThm (h, b)) =
    bindP (map_optionP (norm_types_P (Envir.type_env env))
            ((fn h : Proofterm.thm_header => #types h) h))
      (fn ts =>
        returnP
          (Proofterm.PThm
            ((fn {serial, command_pos, theory_name, thm_name, prop, ...} : Proofterm.thm_header =>
      fn types => Proofterm.thm_header serial command_pos theory_name thm_name prop types)
               h ts,
              b)))
  | norm_proof env Proofterm.MinProof = returnP Proofterm.MinProof
  | norm_proof env (Proofterm.PBound v) = returnP (Proofterm.PBound v)
  | norm_proof env (Proofterm.Hyp v) = returnP (Proofterm.Hyp v);

fun nth_prem i t =
  (case dest_imp t of NONE => raisea (Term_Error ("nth_prem", [t]))
    | SOME (a, b) =>
      (if ((i : IntInf.int) = (1 : IntInf.int)) then return a
        else nth_prem (IntInf.- (i, (1 : IntInf.int))) b));

fun cprem_of th i =
  handleT (liftMT (nth_prem i (th_prop th)))
    (fn e =>
      (case e of UExn (PExn (Unif _)) => raiseT e
        | UExn (PExn Pattern) => raiseT e | UExn (PExn Match) => raiseT e
        | UExn (PExn TUnify) => raiseT e | UExn (PExn Type_Match) => raiseT e
        | UExn (PExn (Class_Error _)) => raiseT e
        | UExn (PExn (Type_Error (_, _, _))) => raiseT e
        | UExn (PExn (Term_Error (_, _))) => raiseT (THM ("cprem_of", i, State))
        | UExn (PExn (Failure _)) => raiseT e
        | UExn (PExn Subscript) => raiseT e
        | UExn (PExn Unequal_Lengths) => raiseT e
        | UExn (PExn (Dup _)) => raiseT e | UExn CANTUNIFY => raiseT e
        | UExn ASSIGN => raiseT e | UExn CHANGE_FAIL => raiseT e
        | UExn Bind => raiseT e | THM (_, _, _) => raiseT e
        | ERROR _ => raiseT e | COMPOSE => raiseT e));

fun proof_combt p ts = foldl (fn pa => fn t => pa % SOME t) p ts;

fun zflatten_params_proof i j n (ZApp (ZApp (ZConst0 c, a), b), k) =
  (if ((c : string) = "Pure.imp")
    then ZAbsp ("H", a,
           zflatten_params_proof (IntInf.+ (i, (1 : IntInf.int))) j n (b, k))
    else zAppps
           (zAppts (ZBoundp (IntInf.+ (k, i)))
             (map ZBound
               (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
           (map ZBoundp
             (removeAll equal_integer (IntInf.- (i, n))
               (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int)))))
  | zflatten_params_proof i j n (ZApp (ZConst1 (c, u), ZAbs (a, ta, t)), k) =
    (if ((c : string) = "Pure.all")
      then ZAbst (a, ta,
             zflatten_params_proof i (IntInf.+ (j, (1 : IntInf.int))) n (t, k))
      else zAppps
             (zAppts (ZBoundp (IntInf.+ (k, i)))
               (map ZBound
                 (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
             (map ZBoundp
               (removeAll equal_integer (IntInf.- (i, n))
                 (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int)))))
  | zflatten_params_proof i j n (ZVar (v, va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZBound v, k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZConst0 v, k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZConst1 (v, va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZConst (v, va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZAbs (v, va, vb), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZVar (vb, vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZBound vb, va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst0 vb, va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst1 (vb, vc), ZVar (v, vd)), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst1 (vb, vc), ZBound v), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst1 (vb, vc), ZConst0 v), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst1 (vb, vc), ZConst1 (v, vd)), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst1 (vb, vc), ZConst (v, vd)), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst1 (vb, vc), ZApp (v, vd)), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst1 (vb, vc), OFCLASS (v, vd)), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZConst (vb, vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZAbs (vb, vc, vd), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZApp (ZVar (vd, ve), vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZApp (ZBound vd, vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZApp (ZConst1 (vd, ve), vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZApp (ZConst (vd, ve), vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZApp (ZAbs (vd, ve, vf), vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZApp (ZApp (vd, ve), vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (ZApp (OFCLASS (vd, ve), vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (ZApp (OFCLASS (vb, vc), va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | zflatten_params_proof i j n (OFCLASS (v, va), k) =
    zAppps
      (zAppts (ZBoundp (IntInf.+ (k, i)))
        (map ZBound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map ZBoundp
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))));

fun zbicompose_core ta env flatten bs asa a oldAs n m p q =
  let
    val normt = (fn t => bindZ (zterm_of ta t) (znorm_term ta env));
  in
    bindZ (mapZ normt (bs @ asa))
      (fn ns =>
        let
          val lb = integer_of_nat (size_list bs);
          val la = integer_of_nat (size_list asa);
          val qa =
            zAppps q
              (map ZBoundp
                (downto (IntInf.- (IntInf.+ (lb, la), (1 : IntInf.int))) la));
        in
          bindZ (if IntInf.< ((0 : IntInf.int), n)
                  then (case a of NONE => raiseZ ZOption
                         | SOME c =>
                           bindZ (normt c)
                             (fn ca => returnZ [zmk_asm_prf ca n m]))
                  else returnZ [])
            (fn asm =>
              bindZ (mapZ normt oldAs)
                (fn os =>
                  bindZ (liftMZ
                          (zip_eq os
                            (downto (IntInf.- (la, (1 : IntInf.int)))
                              (0 : IntInf.int))))
                    (fn ks =>
                      returnZ
                        (zAbsps ns
                          (ZAppp (qa,
                            zAppps p
                              (asm @
                                map (if flatten
                                      then zflatten_params_proof
     (0 : IntInf.int) (0 : IntInf.int) n
                                      else (fn x => ZBoundp (snd x)))
                                  ks)))))))
        end)
  end;

fun remove_types (Abs (s, ta, t)) = Abs (s, dummyT, remove_types t)
  | remove_types (t $ u) = remove_types t $ remove_types u
  | remove_types (Const (s, t)) = Const (s, dummyT)
  | remove_types (Free (v, va)) = Free (v, va)
  | remove_types (Var (v, va)) = Var (v, va)
  | remove_types (Bound v) = Bound v;

fun zbicompose_proof ta env smax flatten bs asa a oldAs n m visible rprf sprf =
  (if env_is_empty env
    then zbicompose_core ta env flatten bs asa a oldAs n m rprf sprf
    else bindZ (znorm_proof ta env visible rprf)
           (fn rprfa =>
             bindZ (if above env smax then returnZ sprf
                     else znorm_proof ta env visible sprf)
               (zbicompose_core ta env flatten bs asa a oldAs n m rprfa)));

fun dest_state state i =
  handleT
    (bindT (liftMT (strip_prems i [] (th_prop state)))
      (fn a =>
        (case a of ([], _) => raiseT (THM ("dest_state", i, State))
          | (b :: rBs, c) => returnT (th_tpairs state, (rev rBs, (b, c))))))
    (fn e =>
      (case e of UExn (PExn (Unif _)) => raiseT e
        | UExn (PExn Pattern) => raiseT e | UExn (PExn Match) => raiseT e
        | UExn (PExn TUnify) => raiseT e | UExn (PExn Type_Match) => raiseT e
        | UExn (PExn (Class_Error _)) => raiseT e
        | UExn (PExn (Type_Error (_, _, _))) => raiseT e
        | UExn (PExn (Term_Error (_, _))) =>
          raiseT (THM ("dest_state", i, State))
        | UExn (PExn (Failure _)) => raiseT e
        | UExn (PExn Subscript) => raiseT e
        | UExn (PExn Unequal_Lengths) => raiseT e
        | UExn (PExn (Dup _)) => raiseT e | UExn CANTUNIFY => raiseT e
        | UExn ASSIGN => raiseT e | UExn CHANGE_FAIL => raiseT e
        | UExn Bind => raiseT e | THM (_, _, _) => raiseT e
        | ERROR _ => raiseT e | COMPOSE => raiseT e));

fun flatten_params_proof i j n (Const (c, u) $ a $ b, k) =
  (if ((c : string) = "Pure.imp")
    then Proofterm.AbsP ("H", NONE,
           flatten_params_proof (IntInf.+ (i, (1 : IntInf.int))) j n (b, k))
    else proof_combP
           (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
             (map Bound
               (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
           (map Proofterm.PBound
             (removeAll equal_integer (IntInf.- (i, n))
               (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int)))))
  | flatten_params_proof i j n (Const (c, u) $ Abs (a, ta, t), k) =
    (if ((c : string) = "Pure.all")
      then Proofterm.Abst (a, NONE,
             flatten_params_proof i (IntInf.+ (j, (1 : IntInf.int))) n (t, k))
      else proof_combP
             (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
               (map Bound
                 (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
             (map Proofterm.PBound
               (removeAll equal_integer (IntInf.- (i, n))
                 (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int)))))
  | flatten_params_proof i j n (Const (v, va), k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Free (v, va), k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Var (v, va), k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Bound v, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Abs (v, va, vb), k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Const (vb, vc) $ Const (v, vd), k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Const (vb, vc) $ Free (v, vd), k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Const (vb, vc) $ Var (v, vd), k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Const (vb, vc) $ Bound v, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Const (vb, vc) $ (v $ vd), k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Free (vb, vc) $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Var (vb, vc) $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Bound vb $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Abs (vb, vc, vd) $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Free (vd, ve) $ vc $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Var (vd, ve) $ vc $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Bound vd $ vc $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (Abs (vd, ve, vf) $ vc $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))))
  | flatten_params_proof i j n (vd $ ve $ vc $ va, k) =
    proof_combP
      (proof_combt (Proofterm.PBound (IntInf.+ (k, i)))
        (map Bound (downto (IntInf.- (j, (1 : IntInf.int))) (0 : IntInf.int))))
      (map Proofterm.PBound
        (removeAll equal_integer (IntInf.- (i, n))
          (downto (IntInf.- (i, (1 : IntInf.int))) (0 : IntInf.int))));

fun bicompose_core env flatten bs asa a oldAs n m sprf p =
  bindP (liftMP (mapM (norm_term env) (bs @ asa)))
    (fn ns =>
      let
        val lb = integer_of_nat (size_list bs);
        val la = integer_of_nat (size_list asa);
        val q =
          proof_combP sprf
            (map Proofterm.PBound
              (downto (IntInf.- (IntInf.+ (lb, la), (1 : IntInf.int))) la));
      in
        bindP (if IntInf.< ((0 : IntInf.int), n)
                then (case a of NONE => raiseP (Failure "Option")
                       | SOME c => returnP [mk_asm_prf c n m])
                else returnP [])
          (fn asm =>
            bindP (liftMP
                    (zip_eq oldAs
                      (downto (IntInf.- (la, (1 : IntInf.int)))
                        (0 : IntInf.int))))
              (fn ks =>
                returnP
                  (mk_AbsP ns
                    (q %% proof_combP p
                            (asm @
                              map (if flatten
                                    then flatten_params_proof (0 : IntInf.int)
   (0 : IntInf.int) n
                                    else (fn x => Proofterm.PBound (snd x)))
                                ks)))))
      end);

fun strip_assums_concl t =
  (case dest_imp t
    of NONE =>
      (case dest_all t of NONE => t | SOME (_, (_, a)) => strip_assums_concl a)
    | SOME (_, a) => strip_assums_concl a);

fun strip_assums_hyp_aux hs t =
  (case dest_imp t
    of NONE =>
      (case dest_all t of NONE => rev hs
        | SOME (_, (_, a)) =>
          strip_assums_hyp_aux (map (incr_boundvars (1 : IntInf.int)) hs) a)
    | SOME (h, a) => strip_assums_hyp_aux (h :: hs) a);

fun strip_assums_hyp b = strip_assums_hyp_aux [] b;

fun biresolution trace match_flg rep brules i state =
  bindT (dest_state state i)
    (fn dst =>
      bindT (cprem_of state i)
        (fn goal =>
          let
            val (_, (_, (bi, _))) = dst;
          in
            returnT
              (res rep
                (BRCtx
                  (trace, match_flg, state, dst, goal, strip_assums_concl bi,
                    strip_assums_hyp bi))
                brules)
          end));

fun make th_maxidx th_tpairs th_prop =
  Thm_rep_ext (th_maxidx, th_tpairs, th_prop, ());

fun remove_types_env env =
  Envir.Envir {maxidx = (Envir.maxidx_of env),
    tenv = ((fn f => Vartab.map (K f)) (fn (t, ta) => (t, remove_types ta))
             (Envir.term_env env)),
    tyenv = (Envir.type_env env)};

fun norm_proof_remove_types env p = norm_proof (remove_types_env env) p;

fun bicompose_proof env smax flatten bs asa a oldAs n m rprf sprf =
  (if env_is_empty env
    then bicompose_core env flatten bs asa a oldAs n m sprf rprf
    else (if above env smax
           then bindP (norm_proof_remove_types env rprf)
                  (bicompose_core env flatten bs asa a oldAs n m sprf)
           else bindP (bicompose_core env flatten bs asa a oldAs n m sprf rprf)
                  (norm_proof_remove_types env)));

fun map_proof_terms f g (Proofterm.Abst (a, t, p)) =
  Proofterm.Abst (a, map_option g t, map_proof_terms f g p)
  | map_proof_terms f g (Proofterm.AbsP (a, t, p)) =
    Proofterm.AbsP (a, map_option f t, map_proof_terms f g p)
  | map_proof_terms f g (p % t) = map_proof_terms f g p % map_option f t
  | map_proof_terms f g (p %% q) =
    map_proof_terms f g p %% map_proof_terms f g q
  | map_proof_terms f g (Proofterm.PAxm (aa, a, ts)) =
    Proofterm.PAxm (aa, a, map_option (map g) ts)
  | map_proof_terms f g (Proofterm.PClass (t, c)) = Proofterm.PClass (g t, c)
  | map_proof_terms f g (Proofterm.Oracle (aa, a, ts)) =
    Proofterm.Oracle (aa, a, map_option (map g) ts)
  | map_proof_terms f g (Proofterm.PThm (h, b)) =
    Proofterm.PThm
      ((fn {serial, command_pos, theory_name, thm_name, prop, ...} : Proofterm.thm_header =>
      fn types => Proofterm.thm_header serial command_pos theory_name thm_name prop types)
         h (map_option (map g) ((fn h : Proofterm.thm_header => #types h) h)),
        b)
  | map_proof_terms f g Proofterm.MinProof = Proofterm.MinProof
  | map_proof_terms f g (Proofterm.PBound v) = Proofterm.PBound v
  | map_proof_terms f g (Proofterm.Hyp v) = Proofterm.Hyp v;

end; (*struct Bicompose_Generated*)


structure Thm: THM =
struct

(*** Certified terms and types ***)

(** certified types **)

datatype ctyp = Ctyp of {cert: Context.certificate, T: typ, maxidx: int, sorts: sort Ord_List.T};

fun typ_of (Ctyp {T, ...}) = T;

fun maxidx_of_ctyp (Ctyp {maxidx, ...}) = maxidx;

fun global_ctyp_of thy raw_T =
  let
    val T = Sign.certify_typ thy raw_T;
    val maxidx = Term.maxidx_of_typ T;
    val sorts = Sorts.insert_typ T [];
  in Ctyp {cert = Context.Certificate thy, T = T, maxidx = maxidx, sorts = sorts} end;

val ctyp_of = global_ctyp_of o Proof_Context.theory_of;

fun dest_ctyp (Ctyp {cert, T = Type (_, Ts), maxidx, sorts}) =
      map (fn T => Ctyp {cert = cert, T = T, maxidx = maxidx, sorts = sorts}) Ts
  | dest_ctyp cT = raise TYPE ("dest_ctyp", [typ_of cT], []);

fun dest_ctypN n (Ctyp {cert, T, maxidx, sorts}) =
  let fun err () = raise TYPE ("dest_ctypN", [T], []) in
    (case T of
      Type (_, Ts) =>
        Ctyp {cert = cert, T = nth Ts n handle General.Subscript => err (),
          maxidx = maxidx, sorts = sorts}
    | _ => err ())
  end;

fun join_certificate_ctyp (Ctyp {cert, ...}) cert0 = Context.join_certificate (cert0, cert);
fun union_sorts_ctyp (Ctyp {sorts, ...}) sorts0 = Sorts.union sorts0 sorts;
fun maxidx_ctyp (Ctyp {maxidx, ...}) maxidx0 = Int.max (maxidx0, maxidx);

fun make_ctyp (Ctyp {cert, T, maxidx = _, sorts = _}) cargs =
  let
    val As = map typ_of cargs;
    fun err () = raise TYPE ("make_ctyp", T :: As, []);
  in
    (case T of
      Type (a, args) =>
        Ctyp {
          cert = fold join_certificate_ctyp cargs cert,
          maxidx = fold maxidx_ctyp cargs ~1,
          sorts = fold union_sorts_ctyp cargs [],
          T = if length args = length cargs then Type (a, As) else err ()}
    | _ => err ())
  end;



(** certified terms **)

(*certified terms with checked typ, maxidx, and sorts*)
datatype cterm =
  Cterm of {cert: Context.certificate, t: term, T: typ, maxidx: int, sorts: sort Ord_List.T};

exception CTERM of string * cterm list;

fun term_of (Cterm {t, ...}) = t;

fun typ_of_cterm (Cterm {T, ...}) = T;

fun ctyp_of_cterm (Cterm {cert, T, maxidx, sorts, ...}) =
  Ctyp {cert = cert, T = T, maxidx = maxidx, sorts = sorts};

fun maxidx_of_cterm (Cterm {maxidx, ...}) = maxidx;

fun global_cterm_of thy tm =
  let
    val (t, T) = Sign.certify_term thy tm;
    val maxidx = Term.maxidx_of_term t;
    val sorts = Sorts.insert_term t [];
  in Cterm {cert = Context.Certificate thy, t = t, T = T, maxidx = maxidx, sorts = sorts} end;

val cterm_of = global_cterm_of o Proof_Context.theory_of;

fun join_certificate0 (Cterm {cert = cert1, ...}, Cterm {cert = cert2, ...}) =
  Context.join_certificate (cert1, cert2);

fun renamed_term t' (Cterm {cert, t, T, maxidx, sorts}) =
  if t aconv t' then Cterm {cert = cert, t = t', T = T, maxidx = maxidx, sorts = sorts}
  else raise TERM ("renamed_term: terms disagree", [t, t']);

val fast_term_ord = Term_Ord.fast_term_ord o apply2 term_of;
val term_ord = Term_Ord.term_ord o apply2 term_of;


(* destructors *)

fun dest_comb (Cterm {t = c $ a, T, cert, maxidx, sorts}) =
      let val A = Term.argument_type_of c 0 in
        (Cterm {t = c, T = A --> T, cert = cert, maxidx = maxidx, sorts = sorts},
         Cterm {t = a, T = A, cert = cert, maxidx = maxidx, sorts = sorts})
      end
  | dest_comb ct = raise CTERM ("dest_comb", [ct]);

fun dest_fun (Cterm {t = c $ _, T, cert, maxidx, sorts}) =
      let val A = Term.argument_type_of c 0
      in Cterm {t = c, T = A --> T, cert = cert, maxidx = maxidx, sorts = sorts} end
  | dest_fun ct = raise CTERM ("dest_fun", [ct]);

fun dest_arg (Cterm {t = c $ a, T = _, cert, maxidx, sorts}) =
      let val A = Term.argument_type_of c 0
      in Cterm {t = a, T = A, cert = cert, maxidx = maxidx, sorts = sorts} end
  | dest_arg ct = raise CTERM ("dest_arg", [ct]);


fun dest_fun2 (Cterm {t = c $ _ $ _, T, cert, maxidx, sorts}) =
      let
        val A = Term.argument_type_of c 0;
        val B = Term.argument_type_of c 1;
      in Cterm {t = c, T = A --> B --> T, cert = cert, maxidx = maxidx, sorts = sorts} end
  | dest_fun2 ct = raise CTERM ("dest_fun2", [ct]);

fun dest_arg1 (Cterm {t = c $ a $ _, T = _, cert, maxidx, sorts}) =
      let val A = Term.argument_type_of c 0
      in Cterm {t = a, T = A, cert = cert, maxidx = maxidx, sorts = sorts} end
  | dest_arg1 ct = raise CTERM ("dest_arg1", [ct]);

fun gen_dest_abs dest ct =
  (case ct of
    Cterm {t = t as Abs _, T = Type ("fun", [_, U]), cert, maxidx, sorts} =>
      let
        val ((x', T), t') = dest t;
        val v = Cterm {t = Free (x', T), T = T, cert = cert, maxidx = maxidx, sorts = sorts};
        val body = Cterm {t = t', T = U, cert = cert, maxidx = maxidx, sorts = sorts};
      in (v, body) end
  | _ => raise CTERM ("dest_abs", [ct]));

val dest_abs_fresh = gen_dest_abs o Term.dest_abs_fresh;
val dest_abs_global = gen_dest_abs Term.dest_abs_global;


(* constructors *)

fun rename_tvar (a, i) (Ctyp {cert, T, maxidx = _, sorts = _}) =
  let
    val S =
      (case T of
        TFree (_, S) => S
      | TVar (_, S) => S
      | _ => raise TYPE ("rename_tvar: no variable", [T], []));
    val _ = if i < 0 then raise TYPE ("rename_tvar: bad index", [TVar ((a, i), S)], []) else ();
  in Ctyp {cert = cert, T = TVar ((a, i), S), maxidx = i, sorts = [S]} end;

fun free (x, Ctyp {cert, T, maxidx, sorts}) =
  Cterm {cert = cert, t = Free (x, T), T = T, maxidx = maxidx, sorts = sorts};

fun var ((x, i), Ctyp {cert, T, maxidx, sorts}) =
  if i < 0 then raise TERM ("var: bad index", [Var ((x, i), T)])
  else Cterm {cert = cert, t = Var ((x, i), T), T = T, maxidx = Int.max (i, maxidx), sorts = sorts};

fun apply
  (cf as Cterm {t = f, T = Type ("fun", [dty, rty]), maxidx = maxidx1, sorts = sorts1, ...})
  (cx as Cterm {t = x, T, maxidx = maxidx2, sorts = sorts2, ...}) =
    if T = dty then
      Cterm {cert = join_certificate0 (cf, cx),
        t = f $ x,
        T = rty,
        maxidx = Int.max (maxidx1, maxidx2),
        sorts = Sorts.union sorts1 sorts2}
      else raise CTERM ("apply: types don't agree", [cf, cx])
  | apply cf cx = raise CTERM ("apply: first arg is not a function", [cf, cx]);

fun lambda_name
  (x, ct1 as Cterm {t = t1, T = T1, maxidx = maxidx1, sorts = sorts1, ...})
  (ct2 as Cterm {t = t2, T = T2, maxidx = maxidx2, sorts = sorts2, ...}) =
    let val t = Term.lambda_name (x, t1) t2 in
      Cterm {cert = join_certificate0 (ct1, ct2),
        t = t, T = T1 --> T2,
        maxidx = Int.max (maxidx1, maxidx2),
        sorts = Sorts.union sorts1 sorts2}
    end;

fun lambda t u = lambda_name ("", t) u;


(* indexes *)

fun adjust_maxidx_cterm i (ct as Cterm {cert, t, T, maxidx, sorts}) =
  if maxidx = i then ct
  else if maxidx < i then
    Cterm {maxidx = i, cert = cert, t = t, T = T, sorts = sorts}
  else
    Cterm {maxidx = Int.max (maxidx_of_term t, i), cert = cert, t = t, T = T, sorts = sorts};

fun incr_indexes_cterm i (ct as Cterm {cert, t, T, maxidx, sorts}) =
  if i < 0 then raise CTERM ("negative increment", [ct])
  else if i = 0 then ct
  else Cterm {cert = cert, t = Logic.incr_indexes ([], i) t,
    T = Logic.incr_tvar i T, maxidx = maxidx + i, sorts = sorts};



(*** Derivations and Theorems ***)

(* sort constraints *)

type constraint = {theory: theory, typ: typ, sort: sort};

local

val constraint_ord : constraint ord =
  Context.theory_id_ord o apply2 (Context.theory_id o #theory)
  ||| Term_Ord.typ_ord o apply2 #typ
  ||| Term_Ord.sort_ord o apply2 #sort;

val smash_atyps =
  map_atyps (fn TVar (_, S) => Term.aT S | TFree (_, S) => Term.aT S | T => T);

in

val union_constraints = Ord_List.union constraint_ord;

fun insert_constraints _ (_, []) = I
  | insert_constraints thy (T, S) =
      let
        val ignored =
          (case T of
            TFree (_, S') => S = S'
          | TVar (_, S') => S = S'
          | _ => false);
      in
        if ignored then I
        else Ord_List.insert constraint_ord {theory = thy, typ = smash_atyps T, sort = S}
      end;

fun insert_constraints_env thy env =
  let
    val tyenv = Envir.type_env env;
    val normT = Envir.norm_type tyenv;
    fun insert ([], _) = I
      | insert (S, T) = insert_constraints thy (normT T, S);
  in tyenv |> Vartab.fold (insert o #2) end;

end;


(* datatype thm *)

datatype thm = Thm of
 deriv *                        (*derivation*)
 {cert: Context.certificate,    (*background theory certificate*)
  tags: Properties.T,           (*additional annotations/comments*)
  maxidx: int,                  (*maximum index of any Var or TVar*)
  constraints: constraint Ord_List.T,  (*implicit proof obligations for sort constraints*)
  shyps: sort Ord_List.T,       (*sort hypotheses*)
  hyps: term Ord_List.T,        (*hypotheses*)
  tpairs: (term * term) list,   (*flex-flex pairs*)
  prop: term}                   (*conclusion*)
and deriv = Deriv of
 {promises: (serial * thm future) Ord_List.T,
  body: Proofterm.proof_body};

type conv = cterm -> thm;

(*errors involving theorems*)
exception THM of string * int * thm list;

fun rep_thm (Thm (_, args)) = args;

fun fold_terms h f (Thm (_, {tpairs, prop, hyps, ...})) =
  fold (fn (t, u) => f t #> f u) tpairs #> f prop #> #hyps h ? fold f hyps;

fun fold_atomic_ctyps h g f (th as Thm (_, {cert, maxidx, shyps, ...})) =
  let
    fun ctyp T = Ctyp {cert = cert, T = T, maxidx = maxidx, sorts = shyps};
    fun apply T a = if g a T then f (ctyp T) a else a;
  in (fold_terms h o fold_types o fold_atyps) apply th end;

fun fold_atomic_cterms h g f (th as Thm (_, {cert, maxidx, shyps, ...})) =
  let
    fun cterm t T = Cterm {cert = cert, t = t, T = T, maxidx = maxidx, sorts = shyps};
    fun apply t T a = if g a t then f (cterm t T) a else a;
  in
    (fold_terms h o fold_aterms)
      (fn t as Const (_, T) => apply t T
        | t as Free (_, T) => apply t T
        | t as Var (_, T) => apply t T
        | _ => I) th
  end;


fun terms_of_tpairs tpairs = fold_rev (fn (t, u) => cons t o cons u) tpairs [];

fun eq_tpairs ((t, u), (t', u')) = t aconv t' andalso u aconv u';
fun union_tpairs ts us = Library.merge eq_tpairs (ts, us);
val maxidx_tpairs = fold (fn (t, u) => Term.maxidx_term t #> Term.maxidx_term u);

fun attach_tpairs tpairs prop =
  Logic.list_implies (map Logic.mk_equals tpairs, prop);

fun full_prop_of (Thm (_, {tpairs, prop, ...})) = attach_tpairs tpairs prop;


val union_hyps = Ord_List.union Term_Ord.fast_term_ord;
val insert_hyps = Ord_List.insert Term_Ord.fast_term_ord;
val remove_hyps = Ord_List.remove Term_Ord.fast_term_ord;

fun join_certificate1 (Cterm {cert = cert1, ...}, Thm (_, {cert = cert2, ...})) =
  Context.join_certificate (cert1, cert2);

fun join_certificate2 (Thm (_, {cert = cert1, ...}), Thm (_, {cert = cert2, ...})) =
  Context.join_certificate (cert1, cert2);


(* basic components *)

val cert_of = #cert o rep_thm;
val theory_id = Context.certificate_theory_id o cert_of;

fun theory_name long = Context.theory_id_name long o theory_id;
val theory_long_name = theory_name {long = true};
val theory_base_name = theory_name {long = false};

val maxidx_of = #maxidx o rep_thm;
fun maxidx_thm th i = Int.max (maxidx_of th, i);
val shyps_of = #shyps o rep_thm;
val hyps_of = #hyps o rep_thm;
val prop_of = #prop o rep_thm;
val tpairs_of = #tpairs o rep_thm;

val concl_of = Logic.strip_imp_concl o prop_of;
val prems_of = Logic.strip_imp_prems o prop_of;
fun take_prems_of n = Logic.take_imp_prems n o prop_of;
val nprems_of = Logic.count_prems o prop_of;
val no_prems = Logic.no_prems o prop_of;
val one_prem = Logic.one_prem o prop_of;

fun prem_of th i =
  Logic.nth_prem (i, prop_of th) handle TERM _ => raise THM ("prem_of", i, [th]);

fun major_prem_of th =
  (case take_prems_of 1 th of
    prem :: _ => Logic.strip_assums_concl prem
  | [] => raise THM ("major_prem_of: rule with no premises", 0, [th]));

fun cprop_of (Thm (_, {cert, maxidx, shyps, prop, ...})) =
  Cterm {cert = cert, maxidx = maxidx, T = propT, t = prop, sorts = shyps};

fun cprem_of (th as Thm (_, {cert, maxidx, shyps, prop, ...})) i =
  Cterm {cert = cert, maxidx = maxidx, T = propT, sorts = shyps,
    t = Logic.nth_prem (i, prop) handle TERM _ => raise THM ("cprem_of", i, [th])};

fun cconcl_of (th as Thm (_, {cert, maxidx, shyps, ...})) =
  Cterm {cert = cert, maxidx = maxidx, T = propT, sorts = shyps, t = concl_of th};

fun cprems_of (th as Thm (_, {cert, maxidx, shyps, ...})) =
  map (fn t => Cterm {cert = cert, maxidx = maxidx, T = propT, sorts = shyps, t = t})
    (prems_of th);

fun take_cprems_of n (th as Thm (_, {cert, maxidx, shyps, ...})) =
  map (fn t => Cterm {cert = cert, maxidx = maxidx, T = propT, sorts = shyps, t = t})
    (take_prems_of n th);

fun chyps_of (Thm (_, {cert, shyps, hyps, ...})) =
  map (fn t => Cterm {cert = cert, maxidx = ~1, T = propT, sorts = shyps, t = t}) hyps;


(* thm order: ignores theory context! *)

val thm_ord =
  pointer_eq_ord
    (Term_Ord.fast_term_ord o apply2 prop_of
      ||| list_ord (prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord) o apply2 tpairs_of
      ||| list_ord Term_Ord.fast_term_ord o apply2 hyps_of
      ||| list_ord Term_Ord.sort_ord o apply2 shyps_of);


(* implicit theory context *)

exception CONTEXT of string * ctyp list * cterm list * thm list * Context.generic option;

fun theory_of_cterm (ct as Cterm {cert, ...}) =
  Context.certificate_theory cert
    handle ERROR msg => raise CONTEXT (msg, [], [ct], [], NONE);

fun theory_of_thm th =
  Context.certificate_theory (cert_of th)
    handle ERROR msg => raise CONTEXT (msg, [], [], [th], NONE);

fun trim_context_ctyp cT =
  (case cT of
    Ctyp {cert = Context.Certificate_Id _, ...} => cT
  | Ctyp {cert = Context.Certificate thy, T, maxidx, sorts} =>
      Ctyp {cert = Context.Certificate_Id (Context.theory_id thy),
        T = T, maxidx = maxidx, sorts = sorts});

fun trim_context_cterm ct =
  (case ct of
    Cterm {cert = Context.Certificate_Id _, ...} => ct
  | Cterm {cert = Context.Certificate thy, t, T, maxidx, sorts} =>
      Cterm {cert = Context.Certificate_Id (Context.theory_id thy),
        t = t, T = T, maxidx = maxidx, sorts = sorts});

fun trim_context_thm th =
  (case th of
    Thm (_, {constraints = _ :: _, ...}) =>
      raise THM ("trim_context: pending sort constraints", 0, [th])
  | Thm (_, {cert = Context.Certificate_Id _, ...}) => th
  | Thm (der,
      {cert = Context.Certificate thy, tags, maxidx, constraints = [], shyps, hyps,
        tpairs, prop}) =>
      Thm (der,
       {cert = Context.Certificate_Id (Context.theory_id thy),
        tags = tags, maxidx = maxidx, constraints = [], shyps = shyps, hyps = hyps,
        tpairs = tpairs, prop = prop}));

fun transfer_ctyp thy' cT =
  let
    val Ctyp {cert, T, maxidx, sorts} = cT;
    val _ =
      Context.subthy_id (Context.certificate_theory_id cert, Context.theory_id thy') orelse
        raise CONTEXT ("Cannot transfer: not a super theory", [cT], [], [],
          SOME (Context.Theory thy'));
    val cert' = Context.join_certificate (Context.Certificate thy', cert);
  in
    if Context.eq_certificate (cert, cert') then cT
    else Ctyp {cert = cert', T = T, maxidx = maxidx, sorts = sorts}
  end;

val transfer_ctyp' = transfer_ctyp o Proof_Context.theory_of;
val transfer_ctyp'' = transfer_ctyp o Context.theory_of;

fun transfer_cterm thy' ct =
  let
    val Cterm {cert, t, T, maxidx, sorts} = ct;
    val _ =
      Context.subthy_id (Context.certificate_theory_id cert, Context.theory_id thy') orelse
        raise CONTEXT ("Cannot transfer: not a super theory", [], [ct], [],
          SOME (Context.Theory thy'));
    val cert' = Context.join_certificate (Context.Certificate thy', cert);
  in
    if Context.eq_certificate (cert, cert') then ct
    else Cterm {cert = cert', t = t, T = T, maxidx = maxidx, sorts = sorts}
  end;

val transfer_cterm' = transfer_cterm o Proof_Context.theory_of;
val transfer_cterm'' = transfer_cterm o Context.theory_of;

fun transfer thy' th =
  let
    val Thm (der, {cert, tags, maxidx, constraints, shyps, hyps, tpairs, prop}) = th;
    val _ =
      Context.subthy_id (Context.certificate_theory_id cert, Context.theory_id thy') orelse
        raise CONTEXT ("Cannot transfer: not a super theory", [], [], [th],
          SOME (Context.Theory thy'));
    val cert' = Context.join_certificate (Context.Certificate thy', cert);
  in
    if Context.eq_certificate (cert, cert') then th
    else
      Thm (der,
       {cert = cert',
        tags = tags,
        maxidx = maxidx,
        constraints = constraints,
        shyps = shyps,
        hyps = hyps,
        tpairs = tpairs,
        prop = prop})
  end;

val transfer' = transfer o Proof_Context.theory_of;
val transfer'' = transfer o Context.theory_of;

fun join_transfer thy th =
  (Context.subthy_id (theory_id th, Context.theory_id thy) ? transfer thy) th;

fun join_transfer_context (ctxt, th) =
  if Context.subthy_id (theory_id th, Context.theory_id (Proof_Context.theory_of ctxt))
  then (ctxt, transfer' ctxt th)
  else (Context.raw_transfer (theory_of_thm th) ctxt, th);


(* matching *)

local

fun gen_match match
    (ct1 as Cterm {t = t1, sorts = sorts1, ...},
     ct2 as Cterm {t = t2, sorts = sorts2, maxidx = maxidx2, ...}) =
  let
    val cert = join_certificate0 (ct1, ct2);
    val thy = Context.certificate_theory cert
      handle ERROR msg => raise CONTEXT (msg, [], [ct1, ct2], [], NONE);
    val (Tinsts, tinsts) = match thy (t1, t2) (Vartab.empty, Vartab.empty);
    val sorts = Sorts.union sorts1 sorts2;
    fun mk_cTinst ((a, i), (S, T)) =
      (((a, i), S), Ctyp {T = T, cert = cert, maxidx = maxidx2, sorts = sorts});
    fun mk_ctinst ((x, i), (U, t)) =
      let val T = Envir.subst_type Tinsts U in
        (((x, i), T), Cterm {t = t, T = T, cert = cert, maxidx = maxidx2, sorts = sorts})
      end;
  in
    (TVars.build (Vartab.fold (TVars.add o mk_cTinst) Tinsts),
     Vars.build (Vartab.fold (Vars.add o mk_ctinst) tinsts))
  end;

in

val match = gen_match Pattern.match;
val first_order_match = gen_match Pattern.first_order_match;

end;


(*implicit alpha-conversion*)
fun renamed_prop prop' (Thm (der, {cert, tags, maxidx, constraints, shyps, hyps, tpairs, prop})) =
  if prop aconv prop' then
    Thm (der, {cert = cert, tags = tags, maxidx = maxidx, constraints = constraints, shyps = shyps,
      hyps = hyps, tpairs = tpairs, prop = prop'})
  else raise TERM ("renamed_prop: props disagree", [prop, prop']);

fun make_context ths NONE cert =
      (Context.Theory (Context.certificate_theory cert)
        handle ERROR msg => raise CONTEXT (msg, [], [], ths, NONE))
  | make_context ths (SOME ctxt) cert =
      let
        val thy_id = Context.certificate_theory_id cert;
        val thy_id' = Context.theory_id (Proof_Context.theory_of ctxt);
      in
        if Context.subthy_id (thy_id, thy_id') then Context.Proof ctxt
        else raise CONTEXT ("Bad context", [], [], ths, SOME (Context.Proof ctxt))
      end;

fun make_context_certificate ths opt_ctxt cert =
  let
    val context = make_context ths opt_ctxt cert;
    val cert' = Context.Certificate (Context.theory_of context);
  in (context, cert') end;

(*explicit weakening: maps |- B to A |- B*)
fun weaken raw_ct th =
  let
    val ct as Cterm {t = A, T, sorts, maxidx = maxidxA, ...} = adjust_maxidx_cterm ~1 raw_ct;
    val Thm (der, {tags, maxidx, constraints, shyps, hyps, tpairs, prop, ...}) = th;
  in
    if T <> propT then
      raise THM ("weaken: assumptions must have type prop", 0, [])
    else if maxidxA <> ~1 then
      raise THM ("weaken: assumptions may not contain schematic variables", maxidxA, [])
    else
      Thm (der,
       {cert = join_certificate1 (ct, th),
        tags = tags,
        maxidx = maxidx,
        constraints = constraints,
        shyps = Sorts.union sorts shyps,
        hyps = insert_hyps A hyps,
        tpairs = tpairs,
        prop = prop})
  end;

fun weaken_sorts raw_sorts ct =
  let
    val Cterm {cert, t, T, maxidx, sorts} = ct;
    val thy = theory_of_cterm ct;
    val more_sorts = Sorts.make (map (Sign.certify_sort thy) raw_sorts);
    val sorts' = Sorts.union sorts more_sorts;
  in Cterm {cert = cert, t = t, T = T, maxidx = maxidx, sorts = sorts'} end;



(** derivations and promised proofs **)

fun make_deriv0 promises body = Deriv {promises = promises, body = body};

fun make_deriv promises oracles thms zboxes zproof proof =
  make_deriv0 promises
    (PBody {oracles = oracles, thms = thms, zboxes = zboxes, zproof = zproof, proof = proof});

val empty_deriv = make_deriv [] [] [] [] ZNop MinProof;


(* inference rules *)

val promise_ord: (serial * thm future) ord = fn ((i, _), (j, _)) => int_ord (j, i);

fun deriv_rule2 zproof proof
    (Deriv {promises = ps1, body = PBody body1})
    (Deriv {promises = ps2, body = PBody body2}) =
  let
    val ps' = Ord_List.union promise_ord ps1 ps2;

    val {oracles = oracles1, thms = thms1, zboxes = zboxes1, zproof = zprf1, proof = prf1} = body1;
    val {oracles = oracles2, thms = thms2, zboxes = zboxes2, zproof = zprf2, proof = prf2} = body2;

    val oracles' = Proofterm.union_oracles oracles1 oracles2;
    val thms' = Proofterm.union_thms thms1 thms2;
    val zboxes' = ZTerm.union_zboxes zboxes1 zboxes2;

    val proofs = Proofterm.get_proofs_level ();
    val zproof' = if Proofterm.zproof_enabled proofs then zproof zprf1 zprf2 else ZNop;
    val proof' = if Proofterm.proof_enabled proofs then proof prf1 prf2 else MinProof;
  in make_deriv ps' oracles' thms' zboxes' zproof' proof' end;

fun deriv_rule1 zproof proof = deriv_rule2 (K zproof) (K proof) empty_deriv;

fun deriv_rule0 zproof proof =
  let val proofs = Proofterm.get_proofs_level () in
    if Proofterm.proof_enabled proofs orelse Proofterm.zproof_enabled proofs then
      deriv_rule1 I I (make_deriv [] [] [] []
       (if Proofterm.zproof_enabled proofs then zproof () else ZNop)
       (if Proofterm.proof_enabled proofs then proof () else MinProof))
    else empty_deriv
  end;


(* fulfilled proofs *)

fun raw_promises_of (Thm (Deriv {promises, ...}, _)) = promises;

fun join_promises [] = ()
  | join_promises promises = join_promises_of (Future.joins (map snd promises))
and join_promises_of thms = join_promises (Ord_List.make promise_ord (maps raw_promises_of thms));

fun fulfill_body (th as Thm (Deriv {promises, body}, _)) =
  let val fulfilled_promises = map #1 promises ~~ map fulfill_body (Future.joins (map #2 promises))
  in Proofterm.fulfill_norm_proof (theory_of_thm th) fulfilled_promises body end;

fun proof_bodies_of thms = (join_promises_of thms; map fulfill_body thms);
val proof_body_of = singleton proof_bodies_of;

val zproof_of = Proofterm.zproof_of o proof_body_of;
val proof_of = Proofterm.proof_of o proof_body_of;

fun reconstruct_proof_of thm =
  Proofterm.reconstruct_proof (theory_of_thm thm) (prop_of thm) (proof_of thm);

val consolidate = ignore o proof_bodies_of;

fun expose_proofs thy thms =
  if Proofterm.export_proof_boxes_required thy then
    Proofterm.export_proof_boxes (proof_bodies_of (map (transfer thy) thms))
  else ();

fun expose_proof thy = expose_proofs thy o single;


(* future rule *)

fun future_result i orig_cert orig_shyps orig_prop thm =
  let
    fun err msg = raise THM ("future_result: " ^ msg, 0, [thm]);
    val Thm (Deriv {promises, ...}, {cert, constraints, shyps, hyps, tpairs, prop, ...}) = thm;

    val _ = Context.eq_certificate (cert, orig_cert) orelse err "bad theory";
    val _ = prop aconv orig_prop orelse err "bad prop";
    val _ = null constraints orelse err "bad sort constraints";
    val _ = null tpairs orelse err "bad flex-flex constraints";
    val _ = null hyps orelse err "bad hyps";
    val _ = Sorts.subset (shyps, orig_shyps) orelse err "bad shyps";
    val _ = forall (fn (j, _) => i <> j) promises orelse err "bad dependencies";
    val _ = join_promises promises;
  in thm end;

fun future future_thm ct =
  let
    val Cterm {cert = cert, t = prop, T, maxidx, sorts} = ct;
    val _ = T <> propT andalso raise CTERM ("future: prop expected", [ct]);
    val _ =
      if Proofterm.any_proofs_enabled ()
      then raise CTERM ("future: proof terms enabled", [ct]) else ();

    val i = serial ();
    val future = future_thm |> Future.map (future_result i cert sorts prop);
  in
    Thm (make_deriv [(i, future)] [] [] [] ZNop MinProof,
     {cert = cert,
      tags = [],
      maxidx = maxidx,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = prop})
  end;



(** Axioms **)

fun axiom thy name =
  (case Name_Space.lookup (Theory.axiom_table thy) name of
    SOME prop =>
      let
        fun zproof () = ZTerm.axiom_proof thy name prop;
        fun proof () = Proofterm.axiom_proof name prop;
        val cert = Context.Certificate thy;
        val maxidx = maxidx_of_term prop;
        val shyps = Sorts.insert_term prop [];
      in
        Thm (deriv_rule0 zproof proof,
          {cert = cert, tags = [], maxidx = maxidx,
            constraints = [], shyps = shyps, hyps = [], tpairs = [], prop = prop})
      end
  | NONE => raise THEORY ("No axiom " ^ quote name, [thy]));

fun all_axioms_of thy =
  map (fn (name, _) => (name, axiom thy name)) (Theory.all_axioms_of thy);


(* tags *)

val get_tags = #tags o rep_thm;

fun map_tags f (Thm (der, {cert, tags, maxidx, constraints, shyps, hyps, tpairs, prop})) =
  Thm (der, {cert = cert, tags = f tags, maxidx = maxidx, constraints = constraints,
    shyps = shyps, hyps = hyps, tpairs = tpairs, prop = prop});


(* technical adjustments *)

fun norm_proof (th as Thm (der, args)) =
  Thm (deriv_rule1 I (Proofterm.rew_proof (theory_of_thm th)) der, args);

fun adjust_maxidx_thm i
    (th as Thm (der, {cert, tags, maxidx, constraints, shyps, hyps, tpairs, prop})) =
  if maxidx = i then th
  else if maxidx < i then
    Thm (der, {maxidx = i, cert = cert, tags = tags, constraints = constraints, shyps = shyps,
      hyps = hyps, tpairs = tpairs, prop = prop})
  else
    Thm (der, {maxidx = Int.max (maxidx_tpairs tpairs (maxidx_of_term prop), i),
      cert = cert, tags = tags, constraints = constraints, shyps = shyps,
      hyps = hyps, tpairs = tpairs, prop = prop});



(*** Theory data ***)

(* type classes *)

structure Aritytab =
  Table(
    type key = string * sort list * class;
    val ord =
      fast_string_ord o apply2 #1
      ||| fast_string_ord o apply2 #3
      ||| list_ord Term_Ord.sort_ord o apply2 #2;
  );

datatype classes = Classes of
 {classrels: thm Symreltab.table,
  arities: (thm * string * serial) Aritytab.table};

fun make_classes (classrels, arities) = Classes {classrels = classrels, arities = arities};

val empty_classes = make_classes (Symreltab.empty, Aritytab.empty);

(*see Theory.at_begin hook for transitive closure of classrels and arity completion*)
fun merge_classes
   (Classes {classrels = classrels1, arities = arities1},
    Classes {classrels = classrels2, arities = arities2}) =
  let
    val classrels' = Symreltab.merge (K true) (classrels1, classrels2);
    val arities' = Aritytab.merge (K true) (arities1, arities2);
  in make_classes (classrels', arities') end;


(* data *)

type data =
 {proofs: thm list lazy Inttab.table,  (*forked proofs*)
  zproofs: {name: Thm_Name.P, thm: thm} Inttab.table,  (*stored zproof thms*)
  oracles: unit Name_Space.table,  (*oracles: authentic derivation names*)
  classes: classes};  (*type classes within the logic*)

fun make_data (proofs, zproofs, oracles, classes) : data =
  {proofs = proofs, zproofs = zproofs, oracles = oracles, classes = classes};

structure Data = Theory_Data
(
  type T = data;
  val empty =
    make_data (Inttab.empty, Inttab.empty, Name_Space.empty_table Markup.oracleN, empty_classes);
  fun merge
    ({proofs = proofs1, oracles = oracles1, classes = classes1, ...},
     {proofs = proofs2, oracles = oracles2, classes = classes2, ...}) =
    make_data
     (Inttab.merge (K true) (proofs1, proofs2),
      Inttab.empty,
      Name_Space.merge_tables (oracles1, oracles2),
      merge_classes (classes1, classes2));
);

val _ =
  (Theory.setup o Theory.at_begin) (fn thy =>
    let val {proofs, zproofs, oracles, classes} = Data.get thy in
      if Inttab.is_empty proofs andalso Inttab.is_empty zproofs then NONE
      else SOME (Data.put (make_data (Inttab.empty, Inttab.empty, oracles, classes)) thy)
    end);

fun map_data f =
  Data.map (fn {proofs, zproofs, oracles, classes} =>
    make_data (f (proofs, zproofs, oracles, classes)));

val get_proofs = #proofs o Data.get;
fun map_proofs f = map_data (fn (a, b, c, d) => (f a, b, c, d));

val get_zproofs = #zproofs o Data.get;
fun map_zproofs f = map_data (fn (a, b, c, d) => (a, f b, c, d));

val get_oracles = #oracles o Data.get;
fun map_oracles f = map_data (fn (a, b, c, d) => (a, b, f c, d));

val get_classes = (fn {classes = Classes args, ...} => args) o Data.get;
val get_classrels = #classrels o get_classes;
val get_arities = #arities o get_classes;

fun map_classes f =
  map_data (fn (a, b, c, Classes {classrels, arities}) =>
    (a, b, c, make_classes (f (classrels, arities))));
fun map_classrels f = map_classes (fn (classrels, arities) => (f classrels, arities));
fun map_arities f = map_classes (fn (classrels, arities) => (classrels, f arities));


(* type classes *)

fun the_classrel thy (c1, c2) =
  (case Symreltab.lookup (get_classrels thy) (c1, c2) of
    SOME thm => transfer thy thm
  | NONE => error ("Unproven class relation " ^
      Syntax.string_of_classrel (Proof_Context.init_global thy) [c1, c2]));

fun the_arity thy (a, Ss, c) =
  (case Aritytab.lookup (get_arities thy) (a, Ss, c) of
    SOME (thm, _, _) => transfer thy thm
  | NONE => error ("Unproven type arity " ^
      Syntax.string_of_arity (Proof_Context.init_global thy) (a, Ss, [c])));

fun sorts_zproof thy = (zproof_of o the_classrel thy, zproof_of o the_arity thy);
fun sorts_proof thy = (proof_of o the_classrel thy, proof_of o the_arity thy);


(* solve sort constraints by pro-forma proof *)

local

fun union_digest (oracles1, thms1) (oracles2, thms2) =
  (Proofterm.union_oracles oracles1 oracles2, Proofterm.union_thms thms1 thms2);

fun thm_digest (Thm (Deriv {body = PBody {oracles, thms, ...}, ...}, _)) = (oracles, thms);

fun constraint_digest ({theory = thy, typ, sort, ...}: constraint) =
  Sorts.of_sort_derivation (Sign.classes_of thy)
   {class_relation = fn _ => fn _ => fn (digest, c1) => fn c2 =>
      if c1 = c2 then digest else union_digest digest (thm_digest (the_classrel thy (c1, c2))),
    type_constructor = fn (a, _) => fn dom => fn c =>
      let val arity_digest = thm_digest (the_arity thy (a, (map o map) #2 dom, c))
      in (fold o fold) (union_digest o #1) dom arity_digest end,
    type_variable = fn T => map (pair ([], [])) (Type.sort_of_atyp T)}
   (typ, sort);

fun bad_constraint_theory cert ({theory = thy, ...}: constraint) =
  if Context.eq_thy_id (Context.certificate_theory_id cert, Context.theory_id thy)
  then NONE else SOME thy;

in

fun solve_constraints (thm as Thm (der, args)) =
  let
    val {cert, tags, maxidx, constraints, shyps, hyps, tpairs, prop} = args;

    val bad_thys = map_filter (bad_constraint_theory cert) constraints;
    val _ =
      if null bad_thys then ()
      else
        raise THEORY ("solve_constraints: bad theories for theorem\n" ^
          Syntax.string_of_term_global (hd bad_thys) (prop_of thm), bad_thys);

    val Deriv {promises, body = PBody {oracles, thms, zboxes, zproof, proof}} = der;
    val (oracles', thms') = (oracles, thms)
      |> fold (fold union_digest o constraint_digest) constraints;
    val zproof' = ZTerm.beta_norm_prooft zproof;
  in
    Thm (make_deriv promises oracles' thms' zboxes zproof' proof,
      {constraints = [], cert = cert, tags = tags, maxidx = maxidx,
        shyps = shyps, hyps = hyps, tpairs = tpairs, prop = prop})
  end;

end;

(*Dangling sort constraints of a thm*)
fun extra_shyps (th as Thm (_, {shyps, ...})) =
  Sorts.subtract (fold_terms {hyps = true} Sorts.insert_term th []) shyps;

(*Remove extra sorts that are witnessed by type signature information*)
fun strip_shyps thm =
  (case thm of
    Thm (_, {shyps = [], ...}) => thm
  | Thm (der, {cert, tags, maxidx, constraints, shyps, hyps, tpairs, prop}) =>
      let
        val Deriv {promises, body = PBody {oracles, thms, zboxes, zproof, proof}} = der;

        val thy = theory_of_thm thm;
        val algebra = Sign.classes_of thy;
        val le = Sorts.sort_le algebra;
        fun lt (S1, S2) = le (S1, S2) andalso not (le (S2, S1));
        fun rel (S1, S2) = if S1 = S2 then [] else [(Term.aT S1, S2)];

        val present_set = Types.build (thm |> fold_terms {hyps = true} Types.add_atyps);
        val {present, extra} = Logic.present_sorts shyps present_set;

        val (witnessed, non_witnessed) =
          Sign.witness_sorts thy present extra ||> map (`(Sorts.minimize_sort algebra));

        val extra' =
          non_witnessed |> map_filter (fn (S, _) =>
            if non_witnessed |> exists (fn (S', _) => lt (S', S)) then NONE else SOME S)
          |> Sorts.make;

        val non_witnessed_constraints =
          non_witnessed |> maps (fn (S1, S2) =>
            let val S0 = the (find_first (fn S => le (S, S1)) extra')
            in rel (S0, S1) @ rel (S1, S2) end);

        val constraints' = constraints
          |> fold (insert_constraints thy) witnessed
          |> fold (insert_constraints thy) non_witnessed_constraints;

        val shyps' = fold (Sorts.insert_sort o #2) present extra';

        val types = present @ witnessed @ map (`Logic.dummy_tfree) extra';
        fun get_type S = types |> get_first (fn (T', S') => if le (S', S) then SOME T' else NONE);
        val map_atyp =
          Same.function_eq (op =) (fn T =>
            if Types.defined present_set T then raise Same.SAME
            else
              (case get_type (Type.sort_of_atyp T) of
                SOME T' => T'
              | NONE => raise Fail "strip_shyps: bad type variable in proof term"));
        val map_ztyp =
          ZTypes.apply_unsynchronized_cache
            (ZTerm.subst_type_same (ZTerm.ztyp_of o map_atyp o ZTerm.typ_of o ZTVar));

        val zproof' = ZTerm.map_proof_types {hyps = true} map_ztyp zproof;
        val proof' = Proofterm.map_proof_types (Term.map_atyps_same map_atyp) proof;
      in
        Thm (make_deriv promises oracles thms zboxes zproof' proof',
         {cert = cert, tags = tags, maxidx = maxidx, constraints = constraints',
          shyps = shyps', hyps = hyps, tpairs = tpairs, prop = prop})
      end)
  |> solve_constraints;



(*** Closed theorems with official name ***)

(*non-deterministic, depends on unknown promises*)
fun derivation_closed (Thm (Deriv {body, ...}, _)) =
  Proofterm.compact_proof (Proofterm.proof_of body);

(*non-deterministic, depends on unknown promises*)
fun raw_derivation_name (Thm (Deriv {body, ...}, {shyps, hyps, prop, ...})) =
  Proofterm.get_approximative_name shyps hyps prop (Proofterm.proof_of body);

fun expand_name (Thm (Deriv {body, ...}, {shyps, hyps, prop, ...})) =
  let
    val self_id =
      (case Proofterm.get_identity shyps hyps prop (Proofterm.proof_of body) of
        NONE => K false
      | SOME {serial, ...} => fn (header: Proofterm.thm_header) => serial = #serial header);
    fun expand header =
      if self_id header orelse Thm_Name.is_empty (#1 (#thm_name header))
      then SOME Thm_Name.none else NONE;
  in expand end;

(*deterministic name of finished proof*)
fun derivation_name (thm as Thm (_, {shyps, hyps, prop, ...})) =
  #1 (Proofterm.get_approximative_name shyps hyps prop (proof_of thm));

(*identified PThm node*)
fun derivation_id (thm as Thm (_, {shyps, hyps, prop, ...})) =
  Proofterm.get_id shyps hyps prop (proof_of thm);

(*dependencies of PThm node*)
fun thm_deps (thm as Thm (Deriv {promises = [], body = PBody {thms, ...}, ...}, _)) =
      (case (derivation_id thm, thms) of
        (SOME {serial = i, ...}, [(j, thm_node)]) =>
          if i = j then Proofterm.thm_node_thms thm_node else thms
      | _ => thms)
  | thm_deps thm = raise THM ("thm_deps: bad promises", 0, [thm]);

fun name_derivation name_pos =
  strip_shyps #> (fn thm as Thm (der, args) =>
    let
      val thy = theory_of_thm thm;

      val Deriv {promises, body} = der;
      val {shyps, hyps, prop, tpairs, ...} = args;

      val _ = null tpairs orelse raise THM ("name_derivation: bad flex-flex constraints", 0, [thm]);

      val ps = map (apsnd (Future.map fulfill_body)) promises;
      val body' = Proofterm.thm_proof thy (sorts_proof thy) name_pos shyps hyps prop ps body;
    in Thm (make_deriv0 [] body', args) end);

fun close_derivation pos =
  solve_constraints #> (fn thm =>
    if not (null (tpairs_of thm)) orelse derivation_closed thm then thm
    else name_derivation (Thm_Name.empty, pos) thm);

val trim_context = solve_constraints #> trim_context_thm;


(* forked proofs *)

fun register_proofs ths thy =
  let val entry = (serial (), Lazy.map_finished (map trim_context) ths)
  in (map_proofs o Inttab.update) entry thy end;

fun force_proofs thy =
  get_proofs thy |> Inttab.dest |> maps (map (transfer thy) o Lazy.force o #2);

val consolidate_theory = consolidate o force_proofs;

fun expose_theory thy =
  if Proofterm.export_enabled ()
  then expose_proofs thy (force_proofs thy) else ();


(*** Oracles ***)

fun add_oracle (b, oracle_fn) thy1 =
  let
    val (name, oracles') = Name_Space.define (Context.Theory thy1) true (b, ()) (get_oracles thy1);
    val thy2 = map_oracles (K oracles') thy1;
    val cert2 = Context.Certificate_Id (Context.theory_id thy2);
    fun invoke_oracle arg =
      let val ct as Cterm {cert = cert3, t = prop, T, maxidx, sorts} = oracle_fn arg in
        if T <> propT then
          raise THM ("Oracle's result must have type prop: " ^ name, 0, [])
        else
          let
            val cert = Context.join_certificate (cert2, cert3);
            val proofs = Proofterm.get_proofs_level ();
            val oracle =
              if Proofterm.oracle_enabled proofs
              then ((name, Position.thread_data ()), SOME prop)
              else ((name, Position.none), NONE);
            val proof =
              if Proofterm.proof_enabled proofs
              then Proofterm.oracle_proof name prop
              else MinProof;
            val zproof =
              if Proofterm.zproof_enabled proofs then
                let
                  val thy = Context.certificate_theory cert handle ERROR msg =>
                    raise CONTEXT (msg, [], [ct], [], NONE);
                in ZTerm.oracle_proof thy name prop end
              else ZNop;
          in
            Thm (make_deriv [] [oracle] [] [] zproof proof,
             {cert = cert,
              tags = [],
              maxidx = maxidx,
              constraints = [],
              shyps = sorts,
              hyps = [],
              tpairs = [],
              prop = prop})
          end
      end;
  in ((name, invoke_oracle), thy2) end;

val oracle_space = Name_Space.space_of_table o get_oracles;

fun pretty_oracle ctxt =
  Name_Space.pretty ctxt (oracle_space (Proof_Context.theory_of ctxt));

fun extern_oracles verbose ctxt =
  map #1 (Name_Space.markups_table verbose ctxt (get_oracles (Proof_Context.theory_of ctxt)));

fun check_oracle ctxt =
  Name_Space.check (Context.Proof ctxt) (get_oracles (Proof_Context.theory_of ctxt)) #> #1;



(*** Meta rules ***)

(** primitive rules **)

(*The assumption rule A |- A*)
fun assume raw_ct =
  let val ct as Cterm {cert, t = prop, T, maxidx, sorts} = adjust_maxidx_cterm ~1 raw_ct in
    if T <> propT then
      raise THM ("assume: prop", 0, [])
    else if maxidx <> ~1 then
      raise THM ("assume: variables", maxidx, [])
    else
      let
        fun zproof () =
          let
            val thy = Context.certificate_theory cert handle ERROR msg =>
              raise CONTEXT (msg, [], [ct], [], NONE);
          in ZTerm.assume_proof thy prop end;
        fun proof () = Proofterm.Hyp prop;
      in
        Thm (deriv_rule0 zproof proof,
         {cert = cert,
          tags = [],
          maxidx = ~1,
          constraints = [],
          shyps = sorts,
          hyps = [prop],
          tpairs = [],
          prop = prop})
      end
  end;

fun assume_cterm A = assume A
  handle THM (msg, _, _) => raise CTERM (msg, [A]);


(*Implication introduction
    [A]
     :
     B
  -------
  A \<Longrightarrow> B
*)
fun implies_intr
    (ct as Cterm {t = A, T, maxidx = maxidx1, sorts, ...})
    (th as Thm (der, {maxidx = maxidx2, hyps, constraints, shyps, tpairs, prop, ...})) =
  if T <> propT then
    raise THM ("implies_intr: assumptions must have type prop", 0, [th])
  else
    let
      val cert = join_certificate1 (ct, th);
      fun zproof p =
        let
          val thy = Context.certificate_theory cert handle ERROR msg =>
            raise CONTEXT (msg, [], [ct], [th], NONE);
        in ZTerm.implies_intr_proof thy A p end
      fun proof p = Proofterm.implies_intr_proof A p;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert,
        tags = [],
        maxidx = Int.max (maxidx1, maxidx2),
        constraints = constraints,
        shyps = Sorts.union sorts shyps,
        hyps = remove_hyps A hyps,
        tpairs = tpairs,
        prop = Logic.mk_implies (A, prop)})
    end;


(*Implication elimination
  A \<Longrightarrow> B    A
  ------------
        B
*)
fun implies_elim thAB thA =
  let
    val Thm (derA,
      {maxidx = maxidx1, hyps = hypsA, constraints = constraintsA, shyps = shypsA,
        tpairs = tpairsA, prop = propA, ...}) = thA
    and Thm (der, {maxidx = maxidx2, hyps, constraints, shyps, tpairs, prop, ...}) = thAB;
    fun err () = raise THM ("implies_elim: major premise", 0, [thAB, thA]);
  in
    (case prop of
      Const ("Pure.imp", _) $ A $ B =>
        if A aconv propA then
          Thm (deriv_rule2 (curry ZAppp) (curry Proofterm.%%) der derA,
           {cert = join_certificate2 (thAB, thA),
            tags = [],
            maxidx = Int.max (maxidx1, maxidx2),
            constraints = union_constraints constraintsA constraints,
            shyps = Sorts.union shypsA shyps,
            hyps = union_hyps hypsA hyps,
            tpairs = union_tpairs tpairsA tpairs,
            prop = B})
        else err ()
    | _ => err ())
  end;

(*Forall introduction.  The Free or Var x must not be free in the hypotheses.
    [x]
     :
     A
  ------
  \<And>x. A
*)
fun occs x ts tpairs =
  let fun occs t = Logic.occs (x, t)
  in exists occs ts orelse exists (occs o fst) tpairs orelse exists (occs o snd) tpairs end;

fun forall_intr
    (ct as Cterm {maxidx = maxidx1, t = x, T, sorts, ...})
    (th as Thm (der, {maxidx = maxidx2, constraints, shyps, hyps, tpairs, prop, ...})) =
  let
    fun check_result a ts =
      if occs x ts tpairs then
        raise THM ("forall_intr: variable " ^ quote a ^ " free in assumptions", 0, [th])
      else
        let
          val cert = join_certificate1 (ct, th);
          fun zproof p =
            let
              val thy = Context.certificate_theory cert handle ERROR msg =>
                raise CONTEXT (msg, [], [ct], [th], NONE);
            in ZTerm.forall_intr_proof thy T (a, x) p end;
          fun proof p = Proofterm.forall_intr_proof (a, x) NONE p;
        in
          Thm (deriv_rule1 zproof proof der,
           {cert = cert,
            tags = [],
            maxidx = Int.max (maxidx1, maxidx2),
            constraints = constraints,
            shyps = Sorts.union sorts shyps,
            hyps = hyps,
            tpairs = tpairs,
            prop = Logic.all_const T $ Abs (a, T, abstract_over (x, prop))})
        end;
  in
    (case x of
      Free (a, _) => check_result a hyps
    | Var ((a, _), _) => check_result a []
    | _ => raise THM ("forall_intr: not a variable", 0, [th]))
  end;

(*Forall elimination
  \<And>x. A
  ------
  A[t/x]
*)
fun forall_elim
    (ct as Cterm {t, T, maxidx = maxidx1, sorts, ...})
    (th as Thm (der, {maxidx = maxidx2, constraints, shyps, hyps, tpairs, prop, ...})) =
  (case prop of
    Const ("Pure.all", Type ("fun", [Type ("fun", [qary, _]), _])) $ A =>
      if T <> qary then
        raise THM ("forall_elim: type mismatch", 0, [th])
      else
        let
          val cert = join_certificate1 (ct, th);
          fun zproof p =
            let
              val thy = Context.certificate_theory cert handle ERROR msg =>
                raise CONTEXT (msg, [], [ct], [th], NONE);
            in ZTerm.forall_elim_proof thy t p end;
          fun proof p = p % SOME t;
        in
          Thm (deriv_rule1 zproof proof der,
           {cert = cert,
            tags = [],
            maxidx = Int.max (maxidx1, maxidx2),
            constraints = constraints,
            shyps = Sorts.union sorts shyps,
            hyps = hyps,
            tpairs = tpairs,
            prop = Term.betapply (A, t)})
        end
  | _ => raise THM ("forall_elim: not quantified", 0, [th]));


(* Equality *)

(*Reflexivity
  t \<equiv> t
*)
fun reflexive (ct as Cterm {cert, t, T, maxidx, sorts}) =
  let
    fun zproof () =
      let
        val thy = Context.certificate_theory cert handle ERROR msg =>
          raise CONTEXT (msg, [], [ct], [], NONE);
      in ZTerm.reflexive_proof thy T t end;
    fun proof () = Proofterm.reflexive_proof;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = maxidx,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = Logic.mk_equals (t, t)})
  end;

(*Symmetry
  t \<equiv> u
  ------
  u \<equiv> t
*)
fun symmetric (th as Thm (der, {cert, maxidx, constraints, shyps, hyps, tpairs, prop, ...})) =
  (case prop of
    (eq as Const ("Pure.eq", Type ("fun", [T, _]))) $ t $ u =>
      let
        fun zproof p =
          let
            val thy = Context.certificate_theory cert handle ERROR msg =>
              raise CONTEXT (msg, [], [], [th], NONE);
          in ZTerm.symmetric_proof thy T t u p end;
      in
        Thm (deriv_rule1 zproof Proofterm.symmetric_proof der,
         {cert = cert,
          tags = [],
          maxidx = maxidx,
          constraints = constraints,
          shyps = shyps,
          hyps = hyps,
          tpairs = tpairs,
          prop = eq $ u $ t})
      end
    | _ => raise THM ("symmetric", 0, [th]));

(*Transitivity
  t1 \<equiv> u    u \<equiv> t2
  ------------------
       t1 \<equiv> t2
*)
fun transitive th1 th2 =
  let
    val Thm (der1, {maxidx = maxidx1, hyps = hyps1, constraints = constraints1, shyps = shyps1,
        tpairs = tpairs1, prop = prop1, ...}) = th1
    and Thm (der2, {maxidx = maxidx2, hyps = hyps2, constraints = constraints2, shyps = shyps2,
        tpairs = tpairs2, prop = prop2, ...}) = th2;
    fun err msg = raise THM ("transitive: " ^ msg, 0, [th1, th2]);
  in
    case (prop1, prop2) of
      ((eq as Const ("Pure.eq", Type (_, [T, _]))) $ t1 $ u, Const ("Pure.eq", _) $ u' $ t2) =>
        if not (u aconv u') then err "middle term"
        else
          let
            val cert = join_certificate2 (th1, th2);
            fun zproof p q =
              let
                val thy = Context.certificate_theory cert handle ERROR msg =>
                  raise CONTEXT (msg, [], [], [th1, th2], NONE);
              in ZTerm.transitive_proof thy T t1 u t2 p q end;
            fun proof p = Proofterm.transitive_proof T u p;
          in
            Thm (deriv_rule2 zproof proof der1 der2,
             {cert = cert,
              tags = [],
              maxidx = Int.max (maxidx1, maxidx2),
              constraints = union_constraints constraints1 constraints2,
              shyps = Sorts.union shyps1 shyps2,
              hyps = union_hyps hyps1 hyps2,
              tpairs = union_tpairs tpairs1 tpairs2,
              prop = eq $ t1 $ t2})
          end
     | _ => err "premises"
  end;

(*Beta-conversion
  (\<lambda>x. t) u \<equiv> t[u/x]
  fully beta-reduces the term if full = true
*)
fun beta_conversion full (ct as Cterm {cert, t, T, maxidx, sorts}) =
  let
    val t' =
      if full then Envir.beta_norm t
      else
        (case t of Abs (_, _, bodt) $ u => subst_bound (u, bodt)
        | _ => raise THM ("beta_conversion: not a redex", 0, []));
    fun zproof () =
      let
        val thy = Context.certificate_theory cert handle ERROR msg =>
          raise CONTEXT (msg, [], [ct], [], NONE);
      in ZTerm.reflexive_proof thy T t end;
    fun proof () = Proofterm.reflexive_proof;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = maxidx,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = Logic.mk_equals (t, t')})
  end;

fun eta_conversion (ct as Cterm {cert, t, T, maxidx, sorts}) =
  let
    fun zproof () =
      let
        val thy = Context.certificate_theory cert handle ERROR msg =>
          raise CONTEXT (msg, [], [ct], [], NONE);
      in ZTerm.reflexive_proof thy T t end;
    fun proof () = Proofterm.reflexive_proof;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = maxidx,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = Logic.mk_equals (t, Envir.eta_contract t)})
  end;

fun eta_long_conversion (ct as Cterm {cert, t, T, maxidx, sorts}) =
  let
    fun zproof () =
      let
        val thy = Context.certificate_theory cert handle ERROR msg =>
          raise CONTEXT (msg, [], [ct], [], NONE);
      in ZTerm.reflexive_proof thy T t end;
    fun proof () = Proofterm.reflexive_proof;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = maxidx,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = [],
      prop = Logic.mk_equals (t, Envir.eta_long [] t)})
  end;

(*The abstraction rule.  The Free or Var x must not be free in the hypotheses.
  The bound variable will be named "a" (since x will be something like x320)
      t \<equiv> u
  --------------
  \<lambda>x. t \<equiv> \<lambda>x. u
*)
fun abstract_rule b
    (ct as Cterm {t = x, T, sorts, ...})
    (th as Thm (der, {maxidx, hyps, constraints, shyps, tpairs, prop, ...})) =
  let
    val (U, t, u) =
      (case prop of
        Const ("Pure.eq", Type ("fun", [U, _])) $ t $ u => (U, t, u)
      | _ => raise THM ("abstract_rule: premise not an equality", 0, [th]));
    fun check_result a ts =
      if occs x ts tpairs then
        raise THM ("abstract_rule: variable " ^ quote a ^ " free in assumptions", 0, [th])
      else
        let
          val cert = join_certificate1 (ct, th);
          val f = Abs (b, T, abstract_over (x, t));
          val g = Abs (b, T, abstract_over (x, u));
          fun zproof p =
            let
              val thy = Context.certificate_theory cert handle ERROR msg =>
                raise CONTEXT (msg, [], [ct], [th], NONE);
            in ZTerm.abstract_rule_proof thy T U (b, x) f g p end;
          fun proof p = Proofterm.abstract_rule_proof (b, x) p
        in
          Thm (deriv_rule1 zproof proof der,
           {cert = cert,
            tags = [],
            maxidx = Term.maxidx_typ T maxidx,
            constraints = constraints,
            shyps = Sorts.union sorts shyps,
            hyps = hyps,
            tpairs = tpairs,
            prop = Logic.mk_equals (f, g)})
        end;
  in
    (case x of
      Free (a, _) => check_result a hyps
    | Var ((a, _), _) => check_result a []
    | _ => raise THM ("abstract_rule: not a variable", 0, [th]))
  end;

(*The combination rule
  f \<equiv> g  t \<equiv> u
  -------------
    f t \<equiv> g u
*)
fun combination th1 th2 =
  let
    val Thm (der1, {maxidx = maxidx1, constraints = constraints1, shyps = shyps1,
        hyps = hyps1, tpairs = tpairs1, prop = prop1, ...}) = th1
    and Thm (der2, {maxidx = maxidx2, constraints = constraints2, shyps = shyps2,
        hyps = hyps2, tpairs = tpairs2, prop = prop2, ...}) = th2;
  in
    (case (prop1, prop2) of
      (Const ("Pure.eq", Type ("fun", [fT, _])) $ f $ g,
       Const ("Pure.eq", Type ("fun", [tT, _])) $ t $ u) =>
        let
          val U =
            (case fT of
              Type ("fun", [T1, U]) =>
                if T1 = tT then U
                else raise THM ("combination: types", 0, [th1, th2])
            | _ => raise THM ("combination: not function type", 0, [th1, th2]));
          val cert = join_certificate2 (th1, th2);
          fun zproof p q =
            let
              val thy = Context.certificate_theory cert handle ERROR msg =>
                raise CONTEXT (msg, [], [], [th1, th2], NONE);
            in ZTerm.combination_proof thy fT U f g t u p q end;
          fun proof p q = Proofterm.combination_proof f g t u p q;
        in
          Thm (deriv_rule2 zproof proof der1 der2,
           {cert = cert,
            tags = [],
            maxidx = Int.max (maxidx1, maxidx2),
            constraints = union_constraints constraints1 constraints2,
            shyps = Sorts.union shyps1 shyps2,
            hyps = union_hyps hyps1 hyps2,
            tpairs = union_tpairs tpairs1 tpairs2,
            prop = Logic.mk_equals (f $ t, g $ u)})
        end
     | _ => raise THM ("combination: premises", 0, [th1, th2]))
  end;

(*Equality introduction
  A \<Longrightarrow> B  B \<Longrightarrow> A
  ----------------
       A \<equiv> B
*)
fun equal_intr th1 th2 =
  let
    val Thm (der1, {maxidx = maxidx1, constraints = constraints1, shyps = shyps1,
      hyps = hyps1, tpairs = tpairs1, prop = prop1, ...}) = th1
    and Thm (der2, {maxidx = maxidx2, constraints = constraints2, shyps = shyps2,
      hyps = hyps2, tpairs = tpairs2, prop = prop2, ...}) = th2;
    fun err msg = raise THM ("equal_intr: " ^ msg, 0, [th1, th2]);
  in
    (case (prop1, prop2) of
      (Const("Pure.imp", _) $ A $ B, Const("Pure.imp", _) $ B' $ A') =>
        if A aconv A' andalso B aconv B' then
          let
            val cert = join_certificate2 (th1, th2);
            fun proof p q = Proofterm.equal_intr_proof A B p q;
            fun zproof p q =
              let
                val thy = Context.certificate_theory cert handle ERROR msg =>
                  raise CONTEXT (msg, [], [], [th1, th2], NONE);
              in ZTerm.equal_intr_proof thy A B p q end;
          in
            Thm (deriv_rule2 zproof proof der1 der2,
             {cert = cert,
              tags = [],
              maxidx = Int.max (maxidx1, maxidx2),
              constraints = union_constraints constraints1 constraints2,
              shyps = Sorts.union shyps1 shyps2,
              hyps = union_hyps hyps1 hyps2,
              tpairs = union_tpairs tpairs1 tpairs2,
              prop = Logic.mk_equals (A, B)})
          end
        else err "not equal"
    | _ =>  err "premises")
  end;

(*The equal propositions rule
  A \<equiv> B  A
  ---------
      B
*)
fun equal_elim th1 th2 =
  let
    val Thm (der1, {maxidx = maxidx1, constraints = constraints1, shyps = shyps1,
      hyps = hyps1, tpairs = tpairs1, prop = prop1, ...}) = th1
    and Thm (der2, {maxidx = maxidx2, constraints = constraints2, shyps = shyps2,
      hyps = hyps2, tpairs = tpairs2, prop = prop2, ...}) = th2;
    fun err msg = raise THM ("equal_elim: " ^ msg, 0, [th1, th2]);
  in
    (case prop1 of
      Const ("Pure.eq", _) $ A $ B =>
        if prop2 aconv A then
          let
            val cert = join_certificate2 (th1, th2);
            fun proof p q = Proofterm.equal_elim_proof A B p q;
            fun zproof p q =
              let
                val thy = Context.certificate_theory cert handle ERROR msg =>
                  raise CONTEXT (msg, [], [], [th1, th2], NONE);
              in ZTerm.equal_elim_proof thy A B p q end;
          in
            Thm (deriv_rule2 zproof proof der1 der2,
             {cert = cert,
              tags = [],
              maxidx = Int.max (maxidx1, maxidx2),
              constraints = union_constraints constraints1 constraints2,
              shyps = Sorts.union shyps1 shyps2,
              hyps = union_hyps hyps1 hyps2,
              tpairs = union_tpairs tpairs1 tpairs2,
              prop = B})
          end
        else err "not equal"
     | _ =>  err "major premise")
  end;



(**** Derived rules ****)

(*Smash unifies the list of term pairs leaving no flex-flex pairs.
  Instantiates the theorem and deletes trivial tpairs.  Resulting
  sequence may contain multiple elements if the tpairs are not all
  flex-flex.*)
fun flexflex_rule opt_ctxt =
  solve_constraints #> (fn th =>
    let
      val Thm (der, {cert, maxidx, constraints, shyps, hyps, tpairs, prop, ...}) = th;
      val (context, cert') = make_context_certificate [th] opt_ctxt cert;
    in
      Unify.smash_unifiers context tpairs (Envir.empty maxidx)
      |> Seq.map (fn env =>
          if Envir.is_empty env then th
          else
            let
              val tpairs' = tpairs |> map (apply2 (Envir.norm_term env))
                (*remove trivial tpairs, of the form t \<equiv> t*)
                |> filter_out (op aconv);
              val prop' = Envir.norm_term env prop;
              val thy' = Context.certificate_theory cert' handle ERROR msg =>
                raise CONTEXT (msg, [], [], [th], Option.map Context.Proof opt_ctxt);

              fun zproof p = ZTerm.norm_proof thy' env [full_prop_of th] p;
              fun proof p = Proofterm.norm_proof_remove_types env p;
            in
              Thm (deriv_rule1 zproof proof der,
               {cert = cert',
                tags = [],
                maxidx = maxidx_tpairs tpairs' (maxidx_of_term prop'),
                constraints = insert_constraints_env thy' env constraints,
                shyps = Envir.insert_sorts env shyps,
                hyps = hyps,
                tpairs = tpairs',
                prop = prop'})
            end)
    end);


(*Generalization of fixed variables
           A
  --------------------
  A[?'a/'a, ?x/x, ...]
*)

fun generalize (tfrees, frees) idx th =
  if Names.is_empty tfrees andalso Names.is_empty frees then th
  else
    let
      val Thm (der, {cert, maxidx, constraints, shyps, hyps, tpairs, prop, ...}) = th;
      val _ = idx <= maxidx andalso raise THM ("generalize: bad index", idx, [th]);

      val bad_type =
        if Names.is_empty tfrees then K false
        else Term.exists_subtype (fn TFree (a, _) => Names.defined tfrees a | _ => false);
      fun bad_term (Free (x, T)) = bad_type T orelse Names.defined frees x
        | bad_term (Var (_, T)) = bad_type T
        | bad_term (Const (_, T)) = bad_type T
        | bad_term (Abs (_, T, t)) = bad_type T orelse bad_term t
        | bad_term (t $ u) = bad_term t orelse bad_term u
        | bad_term (Bound _) = false;
      val _ = exists bad_term hyps andalso
        raise THM ("generalize: variable free in assumptions", 0, [th]);

      val generalize = Term_Subst.generalize (tfrees, frees) idx;
      val prop' = generalize prop;
      val tpairs' = map (apply2 generalize) tpairs;
      val maxidx' = maxidx_tpairs tpairs' (maxidx_of_term prop');

      val zproof = ZTerm.generalize_proof (tfrees, frees) idx;
      val proof = Proofterm.generalize_proof (tfrees, frees) idx prop;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert,
        tags = [],
        maxidx = maxidx',
        constraints = constraints,
        shyps = shyps,
        hyps = hyps,
        tpairs = tpairs',
        prop = prop'})
    end;

fun generalize_cterm (tfrees, frees) idx (ct as Cterm {cert, t, T, maxidx, sorts}) =
  if Names.is_empty tfrees andalso Names.is_empty frees then ct
  else if idx <= maxidx then raise CTERM ("generalize_cterm: bad index", [ct])
  else
    let
      val T' = Term_Subst.generalizeT tfrees idx T;
      val t' = Term_Subst.generalize (tfrees, frees) idx t;
      val maxidx' = maxidx_of_term t';
    in Cterm {cert = cert, sorts = sorts, T = T', t = t', maxidx = maxidx'} end;

fun generalize_ctyp tfrees idx (cT as Ctyp {cert, T, maxidx, sorts}) =
  if Names.is_empty tfrees then cT
  else if idx <= maxidx then raise CTERM ("generalize_ctyp: bad index", [])
  else
    let val T' = Term_Subst.generalizeT tfrees idx T
    in Ctyp {cert = cert, sorts = sorts, T = T', maxidx = Int.max (maxidx, idx)} end;


(*Instantiation of schematic variables
           A
  --------------------
  A[t1/v1, ..., tn/vn]
*)

local

fun add_cert cert_of (_, c) cert = Context.join_certificate (cert, cert_of c);
val add_instT_cert = add_cert (fn Ctyp {cert, ...} => cert);
val add_inst_cert = add_cert (fn Cterm {cert, ...} => cert);

fun add_sorts sorts_of (_, c) sorts = Sorts.union (sorts_of c) sorts;
val add_instT_sorts = add_sorts (fn Ctyp {sorts, ...} => sorts);
val add_inst_sorts = add_sorts (fn Cterm {sorts, ...} => sorts);

fun make_instT thy (_: indexname, S) (Ctyp {T = U, maxidx, ...}) =
  if Sign.of_sort thy (U, S) then (U, maxidx)
  else raise TYPE ("Type not of sort " ^ Syntax.string_of_sort_global thy S, [U], []);

fun make_inst thy (v as (_, T)) (Cterm {t = u, T = U, maxidx, ...}) =
  if T = U then (u, maxidx)
  else
    let
      fun pretty_typing t ty =
        Pretty.block [Syntax.pretty_term_global thy t, Pretty.str " ::",
          Pretty.brk 1, Syntax.pretty_typ_global thy ty];
      val msg =
        Pretty.string_of (Pretty.big_list "instantiate: type conflict"
         [Pretty.item [pretty_typing (Var v) T],
          Pretty.item [pretty_typing u U]]);
    in raise TYPE (msg, [T, U], [Var v, u]) end;

fun prep_insts (instT, inst) (cert, sorts) =
  let
    val cert' = cert
      |> TVars.fold add_instT_cert instT
      |> Vars.fold add_inst_cert inst;
    val thy' =
      Context.certificate_theory cert' handle ERROR msg =>
        raise CONTEXT (msg, TVars.dest instT |> map #2, Vars.dest inst |> map #2, [], NONE);

    val sorts' = sorts
      |> TVars.fold add_instT_sorts instT
      |> Vars.fold add_inst_sorts inst;

    val instT' = TVars.map (make_instT thy') instT;
    val inst' = Vars.map (make_inst thy') inst;
  in ((instT', inst'), (cert', sorts')) end;

in

(*Left-to-right replacements: ctpairs = [..., (vi, ti), ...].
  Instantiates distinct Vars by terms of same type.
  Does NOT normalize the resulting theorem!*)
fun gen_instantiate inst_fn (instT, inst) th =
  if TVars.is_empty instT andalso Vars.is_empty inst then th
  else
    let
      val Thm (der, {cert, hyps, constraints, shyps, tpairs, prop, ...}) = th;
      val ((instT', inst'), (cert', shyps')) = prep_insts (instT, inst) (cert, shyps)
        handle CONTEXT (msg, cTs, cts, ths, context) =>
          raise CONTEXT (msg, cTs, cts, th :: ths, context);

      val subst = inst_fn (instT', inst');
      val (prop', maxidx1) = subst prop ~1;
      val (tpairs', maxidx') =
        fold_map (fn (t, u) => fn i => subst t i ||>> subst u) tpairs maxidx1;

      val thy' = Context.certificate_theory cert'
        handle ERROR msg => raise CONTEXT (msg, [], [], [th], NONE);
      val constraints' =
        TVars.fold (fn ((_, S), (T, _)) => insert_constraints thy' (T, S))
          instT' constraints;

      fun zproof p =
        ZTerm.instantiate_proof thy'
          (TVars.fold (fn (v, (T, _)) => cons (v, T)) instT' [],
           Vars.fold (fn (v, (t, _)) => cons (v, t)) inst' []) p;
      fun proof p =
        Proofterm.instantiate (TVars.map (K #1) instT', Vars.map (K #1) inst') p;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert',
        tags = [],
        maxidx = maxidx',
        constraints = constraints',
        shyps = shyps',
        hyps = hyps,
        tpairs = tpairs',
        prop = prop'})
      |> solve_constraints
    end
    handle TYPE (msg, _, _) => raise THM (msg, 0, [th]);

val instantiate = gen_instantiate Term_Subst.instantiate_maxidx;
val instantiate_beta = gen_instantiate Term_Subst.instantiate_beta_maxidx;

fun gen_instantiate_cterm inst_fn (instT, inst) ct =
  if TVars.is_empty instT andalso Vars.is_empty inst then ct
  else
    let
      val Cterm {cert, t, T, sorts, ...} = ct;
      val ((instT', inst'), (cert', sorts')) = prep_insts (instT, inst) (cert, sorts);
      val subst = inst_fn (instT', inst');
      val substT = Term_Subst.instantiateT_maxidx instT';
      val (t', maxidx1) = subst t ~1;
      val (T', maxidx') = substT T maxidx1;
    in Cterm {cert = cert', t = t', T = T', sorts = sorts', maxidx = maxidx'} end
    handle TYPE (msg, _, _) => raise CTERM (msg, [ct]);

val instantiate_cterm = gen_instantiate_cterm Term_Subst.instantiate_maxidx;
val instantiate_beta_cterm = gen_instantiate_cterm Term_Subst.instantiate_beta_maxidx;

end;


(*The trivial implication A \<Longrightarrow> A, justified by assume and forall rules.
  A can contain Vars, not so for assume!*)
fun trivial (ct as Cterm {cert, t = A, T, maxidx, sorts}) =
  if T <> propT then
    raise THM ("trivial: the term must have type prop", 0, [])
  else
    let
      fun zproof () =
        let
          val thy = Context.certificate_theory cert handle ERROR msg =>
            raise CONTEXT (msg, [], [ct], [], NONE);
        in ZTerm.trivial_proof thy A end;
      fun proof () = Proofterm.trivial_proof;
    in
      Thm (deriv_rule0 zproof proof,
       {cert = cert,
        tags = [],
        maxidx = maxidx,
        constraints = [],
        shyps = sorts,
        hyps = [],
        tpairs = [],
        prop = Logic.mk_implies (A, A)})
    end;

(*Axiom-scheme reflecting signature contents
        T :: c
  -------------------
  OFCLASS(T, c_class)
*)
fun of_class (cT, raw_c) =
  let
    val Ctyp {cert, T, ...} = cT;
    val thy = Context.certificate_theory cert
      handle ERROR msg => raise CONTEXT (msg, [cT], [], [], NONE);
    val c = Sign.certify_class thy raw_c;

    val prop = Logic.mk_of_class (T, c);
    val Cterm {t = prop', maxidx, sorts, ...} = global_cterm_of thy prop;

    fun zproof () = ZTerm.of_class_proof (T, c);
    fun proof () = Proofterm.PClass (T, c);
  in
    if prop <> prop' then raise THM ("of_class: bad proposition via cterm_of", 0, [])
    else if Sign.of_sort thy (T, [c]) then
      Thm (deriv_rule0 zproof proof,
       {cert = cert,
        tags = [],
        maxidx = maxidx,
        constraints = insert_constraints thy (T, [c]) [],
        shyps = sorts,
        hyps = [],
        tpairs = [],
        prop = prop})
    else raise THM ("of_class: type not of class " ^ Syntax.string_of_sort_global thy [c], 0, [])
  end |> solve_constraints;

(*Sort constraints within the logic*)
val unconstrainT =
  strip_shyps #> (fn thm as Thm (der, args) =>
    let
      val Deriv {promises, body} = der;
      val {cert, shyps, hyps, tpairs, prop, ...} = args;
      val thy = theory_of_thm thm;

      fun err msg = raise THM ("unconstrainT: " ^ msg, 0, [thm]);
      val _ = null hyps orelse err "bad hyps";
      val _ = null tpairs orelse err "bad flex-flex constraints";
      val tfrees = build_rev (Term.add_tfree_names prop);
      val _ = null tfrees orelse err ("illegal free type variables " ^ commas_quote tfrees);

      val ps = map (apsnd (Future.map fulfill_body)) promises;
      val (prop', body') = Proofterm.unconstrain_thm_proof thy (sorts_proof thy) shyps prop ps body;
    in
      Thm (make_deriv0 [] body',
       {cert = cert,
        tags = [],
        maxidx = maxidx_of_term prop',
        constraints = [],
        shyps = [[]],  (*potentially redundant*)
        hyps = [],
        tpairs = [],
        prop = prop'})
    end);

(*Replace all TFrees not fixed or in the hyps by new TVars*)
fun varifyT_global' fixed (Thm (der, {cert, maxidx, constraints, shyps, hyps, tpairs, prop, ...})) =
  let
    val tfrees = fold TFrees.add_tfrees hyps fixed;
    val prop1 = attach_tpairs tpairs prop;
    val (al, prop2) = Type.varify_global tfrees prop1;
    val (ts, prop3) = Logic.strip_prems (length tpairs, [], prop2);
    fun zproof p = ZTerm.varifyT_proof al p;
    fun proof p = Proofterm.varifyT_proof al p;
  in
    (al, Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = Int.max (0, maxidx),
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = rev (map Logic.dest_equals ts),
      prop = prop3}))
  end;

val varifyT_global = #2 o varifyT_global' TFrees.empty;

(*Replace all TVars by TFrees that are often new*)
fun legacy_freezeT (Thm (der, {cert, constraints, shyps, hyps, tpairs, prop, ...})) =
  let
    val prop1 = attach_tpairs tpairs prop;
    val prop2 = Type.legacy_freeze prop1;
    val (ts, prop3) = Logic.strip_prems (length tpairs, [], prop2);
    fun zproof p = ZTerm.legacy_freezeT_proof prop1 p;
    fun proof p = Proofterm.legacy_freezeT prop1 p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = maxidx_of_term prop2,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = rev (map Logic.dest_equals ts),
      prop = prop3})
  end;

fun plain_prop_of raw_thm =
  let
    val thm = strip_shyps raw_thm;
    fun err msg = raise THM ("plain_prop_of: " ^ msg, 0, [thm]);
  in
    if not (null (hyps_of thm)) then
      err "theorem may not contain hypotheses"
    else if not (null (extra_shyps thm)) then
      err "theorem may not contain sort hypotheses"
    else if not (null (tpairs_of thm)) then
      err "theorem may not contain flex-flex pairs"
    else prop_of thm
  end;


(* stored thms: zproof *)

val get_zproof_serials = Inttab.keys o get_zproofs;

fun get_zproof thy =
  Inttab.lookup (get_zproofs thy) #> Option.map (fn {name, thm} =>
    let
      val thm' = transfer thy thm;
      val PBody {zboxes, zproof, ...} = proof_body_of thm';
    in {name = name, thm = thm', zboxes = zboxes, zproof = zproof} end);

fun store_zproof name thm thy =
  let
    val Thm (Deriv {promises, body = PBody body}, args as {hyps, prop, ...}) = thm;
    val {oracles, thms, zboxes, zproof, proof} = body;
    fun deriv a b = make_deriv promises oracles thms a b proof;

    val _ = null promises orelse
      raise THM ("store_zproof: theorem may not use promises", 0, [thm]);

    val ((i, (_, zproof1)), zproof2) = ZTerm.thm_proof thy name hyps prop zproof;
    val der1 = if Options.default_bool "prune_proofs" then deriv [] ZNop else deriv zboxes zproof1;
    val der2 = deriv [] zproof2;

    val thm' = trim_context (Thm (der1, args));
    val thy' = thy |> (map_zproofs o Inttab.update) (i, {name = name, thm = thm'});
  in (Thm (der2, args), thy') end;



(*** Inference rules for tactics ***)

(*Destruct proof state into constraints, other goals, goal(i), rest *)
fun dest_state (state as Thm (_, {prop,tpairs,...}), i) =
  (case  Logic.strip_prems(i, [], prop) of
      (B::rBs, C) => (tpairs, rev rBs, B, C)
    | _ => raise THM("dest_state", i, [state]))
  handle TERM _ => raise THM("dest_state", i, [state]);

(*** tight proofs: type arguments of constants, exceptions ***)

local

structure G = Bicompose_Generated;

in

(*Consts.typargs as a computation of the model*)
fun ztypargs thy =
  let val consts = Sign.consts_of thy in
    fn c => fn T =>
      (SOME (G.Ok (Consts.typargs consts (c, T)))
        handle TYPE (msg, Ts, ts) => SOME (G.Err (G.Type_Error (msg, Ts, ts)))
          | Subscript => SOME (G.Err G.Subscript))
  end;

(*the exceptions of session Pure_Pattern*)
fun raise_pexn exn =
  (case exn of
    G.Unif _ => raise Pattern.Unif
  | G.Pattern => raise Pattern.Pattern
  | G.Match => raise Pattern.MATCH
  | G.TUnify => raise Type.TUNIFY
  | G.Type_Match => raise Type.TYPE_MATCH
  | G.Class_Error _ => raise Fail "bicompose: unexpected CLASS_ERROR"
  | G.Type_Error (msg, Ts, ts) => raise TYPE (msg, Ts, ts)
  | G.Term_Error (msg, ts) => raise TERM (msg, ts)
  | G.Failure msg => raise Fail msg
  | G.Subscript => raise Subscript
  | G.Unequal_Lengths => raise ListPair.UnequalLengths
  | G.Dup xi => raise Vartab.DUP xi);

fun run_zproof r =
  (case r of
    SOME (G.ZOk p) => p
  | SOME (G.ZErr (G.ZExn exn)) => raise_pexn exn
  | SOME (G.ZErr (G.BAD_INST inst)) => raise ZTerm.BAD_INST inst
  | SOME (G.ZErr G.ZOption) => raise Option.Option
  | NONE => raise Fail "zproof: undefined result");

end;


(*** lift_rule ***)

(*Prepare orule for resolution by lifting it over the parameters and
assumptions of goal.  The logical part of the lifted rule is computed by the generated code.*)
fun lift_rule goal orule =
  let
    val Cterm {t = gprop, T, maxidx = gmax, sorts, ...} = goal;
    val inc = gmax + 1;
    val Thm (der, {maxidx, constraints, shyps, hyps, tpairs, prop, ...}) = orule;
    val (As, _) = Logic.strip_horn prop;
  in
    if T <> propT then raise THM ("lift_rule: the term must have type prop", 0, [])
    else
      let
        val cert = join_certificate1 (goal, orule);
        val prems = map (Logic.lift_all inc gprop) As;
        fun zproof p =
          let
            val thy = Context.certificate_theory cert
              handle ERROR msg => raise CONTEXT (msg, [], [goal], [orule], NONE);
          in
            run_zproof (Bicompose_Generated.zlift_proof (ztypargs thy) gprop inc prems p)
          end;
        fun proof p = Bicompose_Generated.lift_proof gprop inc prems p;
        val lifted =
          Bicompose_Generated.lift_rule gprop gmax (Bicompose_Generated.make maxidx tpairs prop);
      in
        Thm (deriv_rule1 zproof proof der,
         {cert = cert,
          tags = [],
          maxidx = Bicompose_Generated.th_maxidx lifted,
          constraints = constraints,
          shyps = Sorts.union shyps sorts,  (*sic!*)
          hyps = hyps,
          tpairs = Bicompose_Generated.th_tpairs lifted,
          prop = Bicompose_Generated.th_prop lifted})
      end
  end;


fun incr_indexes i (thm as Thm (der, {cert, maxidx, constraints, shyps, hyps, tpairs, prop, ...})) =
  if i < 0 then raise THM ("negative increment", 0, [thm])
  else if i = 0 then thm
  else
    let
      fun zproof p = ZTerm.incr_indexes_proof i p;
      fun proof p = Proofterm.incr_indexes i p;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert,
        tags = [],
        maxidx = maxidx + i,
        constraints = constraints,
        shyps = shyps,
        hyps = hyps,
        tpairs = map (apply2 (Logic.incr_indexes ([], i))) tpairs,
        prop = Logic.incr_indexes ([], i) prop})
    end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption. *)
fun assumption opt_ctxt i state =
  let
    val Thm (der, {cert, maxidx, constraints, shyps, hyps, ...}) = state;
    val (context, cert') = make_context_certificate [state] opt_ctxt cert;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    fun newth n (env, tpairs) =
      let
        val thy' = Context.certificate_theory cert' handle ERROR msg =>
          raise CONTEXT (msg, [], [], [state], Option.map Context.Proof opt_ctxt);
        val normt = Envir.norm_term env;
        fun zproof p = ZTerm.assumption_proof thy' env Bs Bi n [full_prop_of state] p;
        fun proof p =
          Proofterm.assumption_proof (map normt Bs) (normt Bi) n p
          |> not (Envir.is_empty env) ? Proofterm.norm_proof_remove_types env;
      in
        Thm (deriv_rule1 zproof proof der,
         {tags = [],
          maxidx = Envir.maxidx_of env,
          constraints = insert_constraints_env thy' env constraints,
          shyps = Envir.insert_sorts env shyps,
          hyps = hyps,
          tpairs = if Envir.is_empty env then tpairs else map (apply2 normt) tpairs,
          prop =
            if Envir.is_empty env
            then Logic.list_implies (Bs, C) (*avoid wasted normalizations*)
            else normt (Logic.list_implies (Bs, C)) (*normalize the new rule fully*),
          cert = cert'})
      end;

    val (close, asms, concl) = Logic.assum_problems (~1, Bi);
    val concl' = close concl;
    fun addprfs [] _ = Seq.empty
      | addprfs (asm :: rest) n = Seq.make (fn () => Seq.pull
          (Seq.mapp (newth n)
            (if Term.could_unify (asm, concl) then
              (Unify.unifiers (context, Envir.empty maxidx, (close asm, concl') :: tpairs))
             else Seq.empty)
            (addprfs rest (n + 1))))
  in addprfs asms 1 end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  Checks if Bi's conclusion is alpha/eta-convertible to one of its assumptions*)
fun eq_assumption i state =
  let
    val Thm (der, {cert, maxidx, constraints, shyps, hyps, ...}) = state;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    val (_, asms, concl) = Logic.assum_problems (~1, Bi);
  in
    (case find_index (fn asm => Envir.aeconv (asm, concl)) asms of
      ~1 => raise THM ("eq_assumption", 0, [state])
    | n =>
        let
          fun zproof p =
            let
              val thy = Context.certificate_theory cert
                handle ERROR msg => raise CONTEXT (msg, [], [], [state], NONE);
            in ZTerm.assumption_proof thy Envir.init Bs Bi (n + 1) [] p end;
          fun proof p = Proofterm.assumption_proof Bs Bi (n + 1) p;
        in
          Thm (deriv_rule1 zproof proof der,
           {cert = cert,
            tags = [],
            maxidx = maxidx,
            constraints = constraints,
            shyps = shyps,
            hyps = hyps,
            tpairs = tpairs,
            prop = Logic.list_implies (Bs, C)})
        end)
  end;


(*For rotate_tac: fast rotation of assumptions of subgoal i*)
fun rotate_rule k i state =
  let
    val Thm (der, {cert, maxidx, constraints, shyps, hyps, ...}) = state;
    val (tpairs, Bs, Bi, C) = dest_state (state, i);
    val params = Term.strip_all_vars Bi;
    val rest = Term.strip_all_body Bi;
    val asms = Logic.strip_imp_prems rest
    val concl = Logic.strip_imp_concl rest;
    val n = length asms;
    val m = if k < 0 then n + k else k;
    val Bi' =
      if 0 = m orelse m = n then Bi
      else if 0 < m andalso m < n then
        let val (ps, qs) = chop m asms
        in Logic.list_all (params, Logic.list_implies (qs @ ps, concl)) end
      else raise THM ("rotate_rule", k, [state]);

    fun zproof p =
      let
        val thy = Context.certificate_theory cert
          handle ERROR msg => raise CONTEXT (msg, [], [], [state], NONE);
      in ZTerm.rotate_proof thy Bs Bi' params asms m p end;
    fun proof p = Proofterm.rotate_proof Bs Bi' params asms m p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = maxidx,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = tpairs,
      prop = Logic.list_implies (Bs @ [Bi'], C)})
  end;


(*Rotates a rule's premises to the left by k, leaving the first j premises
  unchanged.  Does nothing if k=0 or if k equals n-j, where n is the
  number of premises.  Useful with eresolve_tac and underlies defer_tac*)
fun permute_prems j k rl =
  let
    val Thm (der, {cert, maxidx, constraints, shyps, hyps, tpairs, prop, ...}) = rl;
    val prems = Logic.strip_imp_prems prop
    and concl = Logic.strip_imp_concl prop;
    val moved_prems = List.drop (prems, j)
    and fixed_prems = List.take (prems, j)
      handle General.Subscript => raise THM ("permute_prems: j", j, [rl]);
    val n_j = length moved_prems;
    val m = if k < 0 then n_j + k else k;
    val (prems', prop') =
      if 0 = m orelse m = n_j then (prems, prop)
      else if 0 < m andalso m < n_j then
        let
          val (ps, qs) = chop m moved_prems;
          val prems' = fixed_prems @ qs @ ps;
        in (prems', Logic.list_implies (prems', concl)) end
      else raise THM ("permute_prems: k", k, [rl]);

    fun zproof p =
      let
        val thy = Context.certificate_theory cert
          handle ERROR msg => raise CONTEXT (msg, [], [], [rl], NONE);
      in ZTerm.permute_prems_proof thy prems' j m p end;
    fun proof p = Proofterm.permute_prems_proof prems' j m p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = maxidx,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = tpairs,
      prop = prop'})
  end;


(*** RESOLUTION ***)

(*Composition of object rule r=(A1...Am/B) with proof state s=(B1...Bn/C)
  Unifies B with Bi, replacing subgoal i    (1 <= i <= n)
  If match then forbid instantiations in proof state
  If lifted then shorten the dpair using strip_assums2.
  If eres_flg then simultaneously proves A1 by assumption.
  nsubgoal is the number of new subgoals (written m above).
  Curried so that resolution calls dest_state only once.
*)
local

structure G = Bicompose_Generated;

fun typ_clash context (tye, T, U) =
  if Config.get_generic context Pattern.unify_trace_failure then
    let
      val ctxt = Context.proof_of context;
      val t = Syntax.string_of_typ ctxt (Envir.norm_type tye T);
      val u = Syntax.string_of_typ ctxt (Envir.norm_type tye U);
    in tracing ("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ();

(*the model only emits failures of type unification; the unifier traces itself*)
fun event context ev =
  (case ev of
    G.Ev_Unif (G.Typ_Clash (tye, T, U)) => typ_clash context (tye, T, U)
  | _ => ());

(*Sorts.class_error is abstract, so CLASS_ERROR cannot be reconstructed here;
  thms () are the proof state and the rule*)
fun raise_exn thms exn =
  (case exn of
    G.UExn (G.PExn (G.Unif _)) => raise Pattern.Unif
  | G.UExn (G.PExn G.Pattern) => raise Pattern.Pattern
  | G.UExn (G.PExn G.Match) => raise Pattern.MATCH
  | G.UExn (G.PExn G.TUnify) => raise Type.TUNIFY
  | G.UExn (G.PExn G.Type_Match) => raise Type.TYPE_MATCH
  | G.UExn (G.PExn (G.Class_Error _)) => raise Fail "bicompose: unexpected CLASS_ERROR"
  | G.UExn (G.PExn (G.Type_Error (msg, Ts, ts))) => raise TYPE (msg, Ts, ts)
  | G.UExn (G.PExn (G.Term_Error (msg, ts))) => raise TERM (msg, ts)
  | G.UExn (G.PExn (G.Failure msg)) => raise Fail msg
  | G.UExn (G.PExn G.Subscript) => raise Subscript
  | G.UExn (G.PExn G.Unequal_Lengths) => raise ListPair.UnequalLengths
  | G.UExn (G.PExn (G.Dup xi)) => raise Vartab.DUP xi
  | G.UExn G.Bind => raise Bind
  | G.UExn _ => raise Fail "bicompose: unexpected exception of the unifier"
  | G.THM (msg, i, G.Orule) => raise THM (msg, i, [#2 (thms ())])
  | G.THM (msg, i, G.Orule_State) => raise THM (msg, i, [#2 (thms ()), #1 (thms ())])
  | G.THM (msg, i, G.State) => raise THM (msg, i, [#1 (thms ())])
  | G.ERROR msg => error msg
  | G.COMPOSE => raise Fail "bicompose: COMPOSE");

(*the messages of a computation are printed when it is finished*)
fun run context thms r =
  (case r of
    SOME (evs, res) =>
      (List.app (event context) evs;
        (case res of
          G.TOk x => x
        | G.TErr exn => raise_exn thms exn))
  | NONE => raise Fail "bicompose: undefined result");

(*the warnings of the normalisation of a proof are printed when it is finished*)
fun run_proof thms r =
  (case r of
    SOME (ws, res) =>
      (List.app (fn s => warning ("type conflict in norm_proof:\n" ^ s)) ws;
        (case res of
          G.Ok p => p
        | G.Err exn => raise_exn thms (G.UExn (G.PExn exn))))
  | NONE => raise Fail "bicompose_proof: undefined result");

(*Pure's operations as computations of the model; they raise their exceptions directly*)
fun ops context =
  G.BOps
    (fn env => fn tus => SOME ([], G.TOk (Unify.unifiers (context, env, tus))),
     fn xq => SOME ([], G.TOk (Seq.pull xq)),
     Name.variant_list []);

(*the new theorem with prop = "\<lbrakk>Bs; As\<rbrakk> \<Longrightarrow> C"*)
fun mk_thm opt_ctxt cert flatten (state, Bs, nlift) orule
    (G.BRes (env, ntpairs, prop, A, G.NewAs (As, oldAs, ren, n))) =
  let
    val Thm (sder, {maxidx=smax, constraints = constraints2, shyps = shyps2, hyps = hyps2, ...}) =
      state
    and Thm (rder, {constraints = constraints1, shyps = shyps1, hyps = hyps1, ...}) = orule;
    val rder' =
      (case ren of
        NONE => rder
      | SOME r =>
          let fun proof p = G.map_proof_terms (G.ren_term r) I p
          in deriv_rule1 I proof rder end);
    val thy' = Context.certificate_theory cert handle ERROR msg =>
      raise CONTEXT (msg, [], [], [state, orule], Option.map Context.Proof opt_ctxt);
    val constraints' =
      union_constraints constraints1 constraints2
      |> insert_constraints_env thy' env;
    fun zproof p q =
      run_zproof (G.zbicompose_proof (ztypargs thy') env smax flatten Bs As A oldAs n (nlift + 1)
        [full_prop_of state, full_prop_of orule] p q);
    fun proof p q =
      run_proof (fn () => (state, orule))
        (G.bicompose_proof env smax flatten Bs As A oldAs n (nlift + 1) p q);
  in
    Thm (deriv_rule2 zproof proof rder' sder,
     {tags = [],
      maxidx = Envir.maxidx_of env,
      constraints = constraints',
      shyps = Envir.insert_sorts env (Sorts.union shyps1 shyps2),
      hyps = union_hyps hyps1 hyps2,
      tpairs = ntpairs,
      prop = prop,
      cert = cert})
  end;

fun rep_of (Thm (_, {maxidx, tpairs, prop, ...})) = G.make maxidx tpairs prop;

in

fun bicompose_aux opt_ctxt {flatten, match, incremented} (state, (stpairs, Bs, Bi, C), lifted)
    (eres_flg, orule, nsubgoal) =
  let
    val Thm (_, {maxidx=smax, tpairs = stpairs0, prop = sprop, ...}) = state
    and Thm (_, {maxidx=rmax, tpairs = rtpairs, prop = rprop, ...}) = orule
    (*How many hyps to skip over during normalization*)
    and nlift = Logic.count_prems (strip_all_body Bi) + (if eres_flg then ~1 else 0);
    val (context, cert) =
      make_context_certificate [state, orule] opt_ctxt (join_certificate2 (state, orule));
    val ops = ops context;
    fun eval r = run context (fn () => (state, orule)) r;
    fun to_seq s =
      Seq.make (fn () =>
        (case eval (G.bpull ops s) of
          NONE => NONE
        | SOME (res, s') => SOME (mk_thm opt_ctxt cert flatten (state, Bs, nlift) orule res, to_seq s')));
    val alg = Sign.classes_of (Context.theory_of context);
  in
    to_seq (eval (G.bicompose_aux ops alg flatten match incremented (smax, (stpairs0, sprop))
      (stpairs, (Bs, (Bi, C))) lifted eres_flg (rmax, (rtpairs, rprop)) nsubgoal))
  end;

(*Bi-resolution of a state with a list of (flag,rule) pairs.
  Puts the rule above:  rule/state.  Renames vars in the rules.
  A step of pulling the result sequence evaluates the computation of one rule, whose
  lifted form is the rule of the exceptions of the step.*)
fun biresolution opt_ctxt match brules i state =
  let
    val context0 = make_context [state] opt_ctxt (cert_of state);
    val trace = Config.get_generic context0 Pattern.unify_trace_failure;
    val s0 =
      run context0 (fn () => (state, state))
        (G.biresolution trace match rep_of brules i (rep_of state));
    val (_, Bs, Bi, _) = dest_state (state, i);
    val lift = lift_rule (cprem_of state i);
    fun pull s =
      let
        val orule = Lazy.lazy (fn () =>
          (case G.brrule s of SOME (_, rule) => lift rule | NONE => state));
        val (context, cert) =
          (case G.brrule s of
            SOME _ =>
              make_context_certificate [state, Lazy.force orule] opt_ctxt
                (join_certificate2 (state, Lazy.force orule))
          | NONE => (context0, cert_of state));
        val alg = Sign.classes_of (Context.theory_of context);
      in
        (case run context (fn () => (state, Lazy.force orule)) (G.brstep (ops context) alg rep_of s) of
          G.RS_Done => NONE
        | G.RS_Skip s' => pull s'
        | G.RS_Result ((res, (eres_flg, _)), s') =>
            let val nlift = Logic.count_prems (strip_all_body Bi) + (if eres_flg then ~1 else 0)
            in SOME (mk_thm opt_ctxt cert true (state, Bs, nlift) (Lazy.force orule) res, to_seq s') end)
      end
    and to_seq s = Seq.make (fn () => pull s);
  in to_seq s0 end;

end;

fun bicompose opt_ctxt flags arg i state =
  bicompose_aux opt_ctxt flags (state, dest_state (state,i), false) arg;

(*Resolution: exactly one resolvent must be produced*)
fun tha RSN (i, thb) =
  (case Seq.chop 2 (biresolution NONE false [(false, tha)] i thb) of
    ([th], _) => solve_constraints th
  | ([], _) => raise THM ("RSN: no unifiers", i, [tha, thb])
  | _ => raise THM ("RSN: multiple unifiers", i, [tha, thb]));

(*Resolution: P \<Longrightarrow> Q, Q \<Longrightarrow> R gives P \<Longrightarrow> R*)
fun tha RS thb = tha RSN (1,thb);



(**** Type classes ****)

fun standard_tvars thm =
  let
    val thy = theory_of_thm thm;
    val tvars = build_rev (Term.add_tvars (prop_of thm));
    val names = Name.invent_global_types (length tvars);
    val tinst =
      map2 (fn (ai, S) => fn b => ((ai, S), global_ctyp_of thy (TVar ((b, 0), S)))) tvars names;
  in instantiate (TVars.make tinst, Vars.empty) thm end


(* class relations *)

val is_classrel = Symreltab.defined o get_classrels;

fun complete_classrels thy =
  let
    fun complete (c, (_, (all_preds, all_succs))) (finished1, thy1) =
      let
        fun compl c1 c2 (finished2, thy2) =
          if is_classrel thy2 (c1, c2) then (finished2, thy2)
          else
            (false,
              thy2
              |> (map_classrels o Symreltab.update) ((c1, c2),
                (the_classrel thy2 (c1, c) RS the_classrel thy2 (c, c2))
                |> standard_tvars
                |> close_derivation \<^here>
                |> tap (expose_proof thy2)
                |> trim_context));

        val proven = is_classrel thy1;
        val preds = Graph.Keys.fold (fn c1 => proven (c1, c) ? cons c1) all_preds [];
        val succs = Graph.Keys.fold (fn c2 => proven (c, c2) ? cons c2) all_succs [];
      in
        fold_product compl preds succs (finished1, thy1)
      end;
  in
    (case Graph.fold complete (Sorts.classes_of (Sign.classes_of thy)) (true, thy) of
      (true, _) => NONE
    | (_, thy') => SOME thy')
  end;


(* type arities *)

fun theory_names_of_arity {long} thy (a, c) =
  build (get_arities thy |> Aritytab.fold
    (fn ((a', _, c'), (_, name, ser)) => (a = a' andalso c = c') ? cons (name, ser)))
  |> sort (int_ord o apply2 #2) |> map (if long then #1 else Long_Name.base_name o #1);

fun insert_arity_completions thy ((t, Ss, c), (th, thy_name, ser)) (finished, arities) =
  let
    val completions =
      Sign.super_classes thy c |> map_filter (fn c1 =>
        if Aritytab.defined arities (t, Ss, c1) then NONE
        else
          let
            val th1 =
              (th RS the_classrel thy (c, c1))
              |> standard_tvars
              |> close_derivation \<^here>
              |> tap (expose_proof thy)
              |> trim_context;
          in SOME ((t, Ss, c1), (th1, thy_name, ser)) end);
    val finished' = finished andalso null completions;
    val arities' = fold Aritytab.update completions arities;
  in (finished', arities') end;

fun complete_arities thy =
  let
    val arities = get_arities thy;
    val (finished, arities') =
      Aritytab.fold (insert_arity_completions thy) arities (true, get_arities thy);
  in
    if finished then NONE
    else SOME (map_arities (K arities') thy)
  end;

val _ =
  Theory.setup
   (Theory.at_begin complete_classrels #>
    Theory.at_begin complete_arities);


(* primitive rules *)

fun add_classrel raw_th thy =
  let
    val th = strip_shyps (transfer thy raw_th);
    val th' = th |> unconstrainT |> tap (expose_proof thy) |> trim_context;
    val prop = plain_prop_of th;
    val (c1, c2) = Logic.dest_classrel prop;
  in
    thy
    |> Sign.primitive_classrel (c1, c2)
    |> register_proofs (Lazy.value [th'])
    |> map_classrels (Symreltab.update ((c1, c2), th'))
    |> perhaps complete_classrels
    |> perhaps complete_arities
  end;

fun add_arity raw_th thy =
  let
    val th = strip_shyps (transfer thy raw_th);
    val th' = th |> unconstrainT |> tap (expose_proof thy) |> trim_context;
    val prop = plain_prop_of th;
    val (t, Ss, c) = Logic.dest_arity prop;
    val ar = ((t, Ss, c), (th', Context.theory_long_name thy, serial ()));
  in
    thy
    |> Sign.primitive_arity (t, Ss, [c])
    |> register_proofs (Lazy.value [th'])
    |> map_arities (Aritytab.update ar #> curry (insert_arity_completions thy ar) true #> #2)
  end;

end;

structure Basic_Thm: BASIC_THM = Thm;
open Basic_Thm;
