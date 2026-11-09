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

(** the inference rules of Thm: generated code **)

(*Generated from the Isabelle/HOL formalization in session Pure_Thm (theories
  Pure_Bicompose, Pure_Biresolution, Pure_Assumption, Pure_Rules, Pure_Subst_Rules,
  Pure_Bicompose_Code), on top of the formalization of Pure's terms, environments and type
  unification in session Pure_Pattern and of unify.ML in session Pure_Unify.  The inference
  rules of structure Thm below are the wrappers of bicompose_wrapper.ML around this code.

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
  type nat
  type num
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
  datatype ('a, 'b) xres = Ok of 'a | Err of 'b
  datatype zexn = ZExn of exn |
    BAD_INST of (((string * IntInf.int) * ztyp) * zterm) list | ZOption
  datatype uexn = PExn of exn | CANTUNIFY | ASSIGN | CHANGE_FAIL | Bind
  datatype event = Ev_Unif of unif_trace | Ev_Loss of typ * typ |
    Ev_Dpairs of string * Envir.env * ((string * typ) list * (term * term)) list
    | Ev_Failure_Node | Ev_Bound_Exceeded
  type 'a uq
  type bctx
  datatype thm_args = Orule | Orule_State | State | No_Thm
  datatype texn = UExn of uexn | THM of string * IntInf.int * thm_args |
    ERROR of string | COMPOSE | NOT_OF_SORT of typ * string list |
    INST_CONFLICT of ((string * IntInf.int) * typ) * term * typ
  datatype 'a bops =
    BOps of
      (Envir.env ->
        (term * term) list -> (event list * ('a, texn) xres) option) *
        ('a ->
          (event list *
            ((((Envir.env * (term * term) list) * 'a) option), texn)
              xres) option) *
        (string list -> string list)
  datatype newas =
    NewAs of
      term list * term list *
        ((string * string) list * (string * string) list) option * IntInf.int
  datatype bres =
    BRes of Envir.env * (term * term) list * term * term option * newas
  type eres_data
  type 'a bseq
  type actx
  type 'a thm_rep_ext
  datatype ares = ARes of Envir.env * IntInf.int * unit thm_rep_ext
  type 'a aseq
  type 'a fseq
  datatype cterm_rep = CTerm of term * typ * IntInf.int
  type brctx
  type ('a, 'b) rseq
  datatype ('a, 'b) rstep = RS_Done | RS_Skip of ('a, 'b) rseq |
    RS_Result of (bres * (bool * 'b)) * ('a, 'b) rseq
  val weaken :
    cterm_rep ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val dest_eq : term -> (typ * (term * term)) option
  val trivial : cterm_rep -> (event list * (unit thm_rep_ext, texn) xres) option
  val ren_term : (string * string) list * (string * string) list -> term -> term
  val bpull :
    'a bops ->
      'a bseq -> (event list * (((bres * 'a bseq) option), texn) xres) option
  val reflexive :
    cterm_rep -> (event list * (unit thm_rep_ext, texn) xres) option
  val th_tpairs : 'a thm_rep_ext -> (term * term) list
  val th_maxidx : 'a thm_rep_ext -> IntInf.int
  val th_prop : 'a thm_rep_ext -> term
  val symmetric :
    unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val apull :
    'a bops ->
      'a aseq -> (event list * (((ares * 'a aseq) option), texn) xres) option
  val fpull :
    'a bops ->
      (Envir.env * (term * term) list ->
        (event list * (Envir.env, texn) xres) option) ->
        unit thm_rep_ext ->
          'a fseq ->
            (event list *
              ((((Envir.env * unit thm_rep_ext) * 'a fseq) option), texn)
                xres) option
  val equal_elim :
    unit thm_rep_ext ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val equal_intr :
    unit thm_rep_ext ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val transitive :
    unit thm_rep_ext ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val bres_nlift : term -> bool -> IntInf.int
  val map_proof_terms :
    (term -> term) -> (typ -> typ) -> Proofterm.proof -> Proofterm.proof
  val norm_proof_remove_types :
    Envir.env ->
      Proofterm.proof -> (string list * (Proofterm.proof, exn) xres) option
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
                          (string list * (Proofterm.proof, exn) xres) option
  val bres_proof :
    unit thm_rep_ext ->
      term list ->
        IntInf.int ->
          bool ->
            bres ->
              Proofterm.proof ->
                Proofterm.proof ->
                  (string list * (Proofterm.proof, exn) xres) option
  val zren_proof :
    (string * string) list * (string * string) list ->
      IntInf.int -> zproof -> (zproof, zexn) xres option
  val assume_rule :
    cterm_rep -> (event list * (unit thm_rep_ext, texn) xres) option
  val combination_data :
    unit thm_rep_ext ->
      unit thm_rep_ext ->
        (event list *
          ((typ * (typ * (term * (term * (term * term))))), texn) xres) option
  val combination :
    unit thm_rep_ext ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val forall_elim :
    cterm_rep ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val forall_intr :
    term list ->
      cterm_rep ->
        unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val zbicompose_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      Envir.env ->
        IntInf.int ->
          bool ->
            term list ->
              term list ->
                term option ->
                  term list ->
                    IntInf.int ->
                      IntInf.int ->
                        term list ->
                          zproof -> zproof -> (zproof, zexn) xres option
  val full_prop_of : (term * term) list -> term -> (term, exn) xres option
  val bres_zproof :
    (string -> typ -> ((typ list), exn) xres option) ->
      unit thm_rep_ext ->
        term list ->
          IntInf.int ->
            bool ->
              unit thm_rep_ext ->
                bres -> zproof -> zproof -> (zproof, zexn) xres option
  val zlift_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term -> IntInf.int -> term list -> zproof -> (zproof, zexn) xres option
  val implies_elim :
    unit thm_rep_ext ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val implies_intr :
    cterm_rep ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val renamed_prop :
    term ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val aseq_ctx : 'a aseq -> actx
  val brrule : ('a, 'b) rseq -> (bool * 'b) option
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
                        IntInf.int -> (event list * ('a bseq, texn) xres) option
  val lift_rule : term -> IntInf.int -> unit thm_rep_ext -> unit thm_rep_ext
  val brstep :
    'a bops ->
      Sorts.algebra ->
        ('b -> unit thm_rep_ext) ->
          ('a, 'b) rseq -> (event list * (('a, 'b) rstep, texn) xres) option
  val abstract_rule_data :
    string ->
      term list ->
        cterm_rep ->
          unit thm_rep_ext ->
            (event list * ((typ * (term * term)), texn) xres) option
  val abstract_rule :
    string ->
      term list ->
        cterm_rep ->
          unit thm_rep_ext ->
            (event list * (unit thm_rep_ext, texn) xres) option
  val trivial_proof : Proofterm.proof
  val zassume_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term -> (zproof, zexn) xres option
  val lift_proof :
    term -> IntInf.int -> term list -> Proofterm.proof -> Proofterm.proof
  val eta_conversion :
    cterm_rep -> (event list * (unit thm_rep_ext, texn) xres) option
  val ztrivial_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term -> (zproof, zexn) xres option
  val of_class :
    Sorts.algebra ->
      typ -> string -> (event list * (unit thm_rep_ext, texn) xres) option
  val assumption_proof :
    term list -> term -> IntInf.int -> Proofterm.proof -> Proofterm.proof
  val ares_proof :
    actx ->
      ares ->
        Proofterm.proof -> (string list * (Proofterm.proof, exn) xres) option
  val assumption :
    IntInf.int -> unit thm_rep_ext -> (event list * ('a aseq, texn) xres) option
  val beta_conversion :
    bool -> cterm_rep -> (event list * (unit thm_rep_ext, texn) xres) option
  val combination_res :
    unit thm_rep_ext ->
      unit thm_rep_ext ->
        (event list *
          ((unit thm_rep_ext * (typ * (typ * (term * (term * (term * term)))))),
            texn)
            xres) option
  val reflexive_proof : Proofterm.proof
  val symmetric_proof : Proofterm.proof -> Proofterm.proof
  val lift_rule_proof :
    term -> IntInf.int -> unit thm_rep_ext -> Proofterm.proof -> Proofterm.proof
  val ares_zproof :
    (string -> typ -> ((typ list), exn) xres option) ->
      unit thm_rep_ext -> actx -> ares -> zproof -> (zproof, zexn) xres option
  val equal_elim_proof :
    term -> term -> Proofterm.proof -> Proofterm.proof -> Proofterm.proof
  val equal_intr_proof :
    term -> term -> Proofterm.proof -> Proofterm.proof -> Proofterm.proof
  val transitive_proof :
    typ -> term -> Proofterm.proof -> Proofterm.proof -> Proofterm.proof
  val zreflexive_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      typ -> term -> (zproof, zexn) xres option
  val zsymmetric_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      typ -> term -> term -> zproof -> (zproof, zexn) xres option
  val generalize :
    string list ->
      string list ->
        IntInf.int ->
          term list ->
            unit thm_rep_ext ->
              (event list * (unit thm_rep_ext, texn) xres) option
  val lift_rule_zproof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term ->
        IntInf.int -> unit thm_rep_ext -> zproof -> (zproof, zexn) xres option
  val abstract_rule_res :
    string ->
      term list ->
        cterm_rep ->
          unit thm_rep_ext ->
            (event list *
              ((unit thm_rep_ext * (typ * (term * term))), texn) xres) option
  val adjust_maxidx_thm : IntInf.int -> unit thm_rep_ext -> unit thm_rep_ext
  val combination_proof :
    term ->
      term ->
        term ->
          term ->
            Proofterm.proof ->
              Proofterm.proof ->
                (string list * (Proofterm.proof, exn) xres) option
  val forall_intr_proof : string -> term -> Proofterm.proof -> Proofterm.proof
  val zequal_elim_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term -> term -> zproof -> zproof -> (zproof, zexn) xres option
  val zequal_intr_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term -> term -> zproof -> zproof -> (zproof, zexn) xres option
  val ztransitive_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      typ ->
        term -> term -> term -> zproof -> zproof -> (zproof, zexn) xres option
  val instantiate :
    Sorts.algebra ->
      bool ->
        (((string * IntInf.int) * string list) * (typ * IntInf.int)) list ->
          (((string * IntInf.int) * typ) * (term * (typ * IntInf.int))) list ->
            unit thm_rep_ext ->
              (event list * (unit thm_rep_ext, texn) xres) option
  val rotate_data :
    IntInf.int ->
      IntInf.int ->
        unit thm_rep_ext ->
          (event list *
            ((unit thm_rep_ext *
               (term list *
                 (term * ((string * typ) list * (term list * IntInf.int))))),
              texn)
              xres) option
  val rotate_rule :
    IntInf.int ->
      IntInf.int ->
        unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val eq_assumption :
    IntInf.int ->
      unit thm_rep_ext ->
        (event list * ((IntInf.int * unit thm_rep_ext), texn) xres) option
  val flexflex_rule :
    'a bops -> unit thm_rep_ext -> (event list * ('a fseq, texn) xres) option
  val implies_intr_proof : term -> Proofterm.proof -> Proofterm.proof
  val zcombination_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      typ ->
        typ ->
          term ->
            term ->
              term -> term -> zproof -> zproof -> (zproof, zexn) xres option
  val zforall_elim_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term -> zproof -> (zproof, zexn) xres option
  val zforall_intr_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      typ -> string -> term -> zproof -> (zproof, zexn) xres option
  val permute_data :
    IntInf.int ->
      IntInf.int ->
        unit thm_rep_ext ->
          (event list *
            ((unit thm_rep_ext * (term list * IntInf.int)), texn) xres) option
  val rotate_proof :
    term list ->
      term ->
        (string * typ) list ->
          term list -> IntInf.int -> Proofterm.proof -> Proofterm.proof
  val biresolution :
    bool ->
      bool ->
        ('a -> unit thm_rep_ext) ->
          (bool * 'a) list ->
            IntInf.int ->
              unit thm_rep_ext ->
                (event list * (('b, 'a) rseq, texn) xres) option
  val make : IntInf.int -> (term * term) list -> term -> unit thm_rep_ext
  val abstract_rule_proof : string -> term -> Proofterm.proof -> Proofterm.proof
  val eta_long_conversion :
    cterm_rep -> (event list * (unit thm_rep_ext, texn) xres) option
  val zimplies_intr_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term -> zproof -> (zproof, zexn) xres option
  val permute_prems :
    IntInf.int ->
      IntInf.int ->
        unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val varifyT_proof :
    ((string * string list) * ((string * IntInf.int) * string list)) list ->
      Proofterm.proof -> Proofterm.proof
  val zrotate_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term list ->
        term ->
          (string * typ) list ->
            term list -> IntInf.int -> zproof -> (zproof, zexn) xres option
  val flexflex_zproof :
    (string -> typ -> ((typ list), exn) xres option) ->
      unit thm_rep_ext -> Envir.env -> zproof -> (zproof, zexn) xres option
  val zabstract_rule_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      typ ->
        typ ->
          string -> term -> term -> term -> zproof -> (zproof, zexn) xres option
  val legacy_freezeT :
    (string list -> string list -> string list) ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val varifyT_global :
    (string list -> string list -> string list) ->
      (string * string list) list ->
        term list ->
          unit thm_rep_ext ->
            (event list *
              ((((string * string list) *
                  ((string * IntInf.int) * string list)) list *
                 unit thm_rep_ext),
                texn)
                xres) option
  val zvarifyT_proof :
    ((string * string list) * ((string * IntInf.int) * string list)) list ->
      zproof -> (zproof, zexn) xres option
  val generalize_proof :
    string list ->
      string list -> IntInf.int -> term -> Proofterm.proof -> Proofterm.proof
  val incr_indexes_thm :
    IntInf.int ->
      unit thm_rep_ext -> (event list * (unit thm_rep_ext, texn) xres) option
  val instantiate_proof :
    (((string * IntInf.int) * string list) * typ) list ->
      (((string * IntInf.int) * typ) * term) list ->
        Proofterm.proof -> Proofterm.proof
  val zgeneralize_proof :
    string list ->
      string list -> IntInf.int -> zproof -> (zproof, zexn) xres option
  val incr_indexes_proof : IntInf.int -> Proofterm.proof -> Proofterm.proof
  val zinstantiate_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      (((string * IntInf.int) * string list) * typ) list ->
        (((string * IntInf.int) * typ) * term) list ->
          zproof -> (zproof, zexn) xres option
  val eq_assumption_zproof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term list -> term -> IntInf.int -> zproof -> (zproof, zexn) xres option
  val permute_prems_proof :
    term list -> IntInf.int -> IntInf.int -> Proofterm.proof -> Proofterm.proof
  val zincr_indexes_proof : IntInf.int -> zproof -> (zproof, zexn) xres option
  val legacy_freezeT_proof :
    (string list -> string list -> string list) ->
      term -> Proofterm.proof -> Proofterm.proof
  val zpermute_prems_proof :
    (string -> typ -> ((typ list), exn) xres option) ->
      term list ->
        IntInf.int -> IntInf.int -> zproof -> (zproof, zexn) xres option
  val zlegacy_freezeT_proof :
    (string list -> string list -> string list) ->
      term -> zproof -> (zproof, zexn) xres option
end = struct

datatype nat = Zero_nat | Suc of nat;

fun equal_nata Zero_nat (Suc x2) = false
  | equal_nata (Suc x2) Zero_nat = false
  | equal_nata (Suc x2) (Suc y2) = equal_nata x2 y2
  | equal_nata Zero_nat Zero_nat = true;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun plus_nata Zero_nat n = n
  | plus_nata (Suc m) n = plus_nata m (Suc n);

fun times_nata Zero_nat n = Zero_nat
  | times_nata (Suc m) n = plus_nata n (times_nata m n);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

val one_nata : nat = Suc Zero_nat;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = Zero_nat} : nat zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

fun minus_nata m Zero_nat = m
  | minus_nata Zero_nat n = Zero_nat
  | minus_nata (Suc m) (Suc n) = minus_nata m n;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = minus_nata} : nat minus;

fun less_nat n Zero_nat = false
  | less_nat m (Suc n) = less_eq_nat m n
and less_eq_nat Zero_nat n = true
  | less_eq_nat (Suc m) n = less_nat m n;

fun divmod_nat m n =
  (if equal_nata n Zero_nat orelse less_nat m n then (Zero_nat, m)
    else let
           val (q, a) = divmod_nat (minus_nata m n) n;
         in
           (Suc q, a)
         end);

fun fst (x1, x2) = x1;

fun divide_nata m n = fst (divmod_nat m n);

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

val divide_nat = {divide = divide_nata} : nat divide;

fun snd (x1, x2) = x2;

fun modulo_nata m n = snd (divmod_nat m n);

type 'a modulo =
  {divide_modulo : 'a divide, dvd_modulo : 'a dvd, modulo : 'a -> 'a -> 'a};
val divide_modulo = #divide_modulo : 'a modulo -> 'a divide;
val dvd_modulo = #dvd_modulo : 'a modulo -> 'a dvd;
val modulo = #modulo : 'a modulo -> 'a -> 'a -> 'a;

val modulo_nat =
  {divide_modulo = divide_nat, dvd_modulo = dvd_nat, modulo = modulo_nata} :
  nat modulo;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

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

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

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

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

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

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors =
  #semiring_1_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors =
  #semiring_no_zero_divisors_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

val semiring_0_nat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_nat,
    mult_zero_semiring_0 = mult_zero_nat, semiring_semiring_0 = semiring_nat}
  : nat semiring_0;

val semiring_no_zero_divisors_nat =
  {semiring_0_semiring_no_zero_divisors = semiring_0_nat} :
  nat semiring_no_zero_divisors;

val monoid_mult_nat =
  {semigroup_mult_monoid_mult = semigroup_mult_nat,
    power_monoid_mult = power_nat}
  : nat monoid_mult;

val semiring_numeral_nat =
  {monoid_mult_semiring_numeral = monoid_mult_nat,
    numeral_semiring_numeral = numeral_nat,
    semiring_semiring_numeral = semiring_nat}
  : nat semiring_numeral;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} : nat zero_neq_one;

val semiring_1_nat =
  {semiring_numeral_semiring_1 = semiring_numeral_nat,
    semiring_0_semiring_1 = semiring_0_nat,
    zero_neq_one_semiring_1 = zero_neq_one_nat}
  : nat semiring_1;

val semiring_1_no_zero_divisors_nat =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_nat,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_nat}
  : nat semiring_1_no_zero_divisors;

val cancel_semigroup_add_nat =
  {semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
  nat cancel_semigroup_add;

val cancel_ab_semigroup_add_nat =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat,
    minus_cancel_ab_semigroup_add = minus_nat}
  : nat cancel_ab_semigroup_add;

val cancel_comm_monoid_add_nat =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_nat,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
  : nat cancel_comm_monoid_add;

val semiring_0_cancel_nat =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat,
    semiring_0_semiring_0_cancel = semiring_0_nat}
  : nat semiring_0_cancel;

val ab_semigroup_mult_nat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
  nat ab_semigroup_mult;

val comm_semiring_nat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat,
    semiring_comm_semiring = semiring_nat}
  : nat comm_semiring;

val comm_semiring_0_nat =
  {comm_semiring_comm_semiring_0 = comm_semiring_nat,
    semiring_0_comm_semiring_0 = semiring_0_nat}
  : nat comm_semiring_0;

val comm_semiring_0_cancel_nat =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
  : nat comm_semiring_0_cancel;

val semiring_1_cancel_nat =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat,
    semiring_1_semiring_1_cancel = semiring_1_nat}
  : nat semiring_1_cancel;

val comm_monoid_mult_nat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat,
    monoid_mult_comm_monoid_mult = monoid_mult_nat,
    dvd_comm_monoid_mult = dvd_nat}
  : nat comm_monoid_mult;

val comm_semiring_1_nat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat,
    semiring_1_comm_semiring_1 = semiring_1_nat}
  : nat comm_semiring_1;

val comm_semiring_1_cancel_nat =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
  : nat comm_semiring_1_cancel;

val semidom_nat =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_nat,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_nat}
  : nat semidom;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

type 'a semiring_char_0 = {semiring_1_semiring_char_0 : 'a semiring_1};
val semiring_1_semiring_char_0 = #semiring_1_semiring_char_0 :
  'a semiring_char_0 -> 'a semiring_1;

val semiring_char_0_nat = {semiring_1_semiring_char_0 = semiring_1_nat} :
  nat semiring_char_0;

type 'a zero_less_one =
  {order_zero_less_one : 'a order,
    zero_neq_one_zero_less_one : 'a zero_neq_one};
val order_zero_less_one = #order_zero_less_one : 'a zero_less_one -> 'a order;
val zero_neq_one_zero_less_one = #zero_neq_one_zero_less_one :
  'a zero_less_one -> 'a zero_neq_one;

val zero_less_one_nat =
  {order_zero_less_one = order_nat,
    zero_neq_one_zero_less_one = zero_neq_one_nat}
  : nat zero_less_one;

type 'a divide_trivial =
  {one_divide_trivial : 'a one, zero_divide_trivial : 'a zero,
    divide_divide_trivial : 'a divide};
val one_divide_trivial = #one_divide_trivial : 'a divide_trivial -> 'a one;
val zero_divide_trivial = #zero_divide_trivial : 'a divide_trivial -> 'a zero;
val divide_divide_trivial = #divide_divide_trivial :
  'a divide_trivial -> 'a divide;

val divide_trivial_nat =
  {one_divide_trivial = one_nat, zero_divide_trivial = zero_nat,
    divide_divide_trivial = divide_nat}
  : nat divide_trivial;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a semidom_divide =
  {divide_trivial_semidom_divide : 'a divide_trivial,
    semidom_semidom_divide : 'a semidom,
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};
val divide_trivial_semidom_divide = #divide_trivial_semidom_divide :
  'a semidom_divide -> 'a divide_trivial;
val semidom_semidom_divide = #semidom_semidom_divide :
  'a semidom_divide -> 'a semidom;
val semiring_no_zero_divisors_cancel_semidom_divide =
  #semiring_no_zero_divisors_cancel_semidom_divide :
  'a semidom_divide -> 'a semiring_no_zero_divisors_cancel;

val semiring_no_zero_divisors_cancel_nat =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_nat}
  : nat semiring_no_zero_divisors_cancel;

val semidom_divide_nat =
  {divide_trivial_semidom_divide = divide_trivial_nat,
    semidom_semidom_divide = semidom_nat,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_nat}
  : nat semidom_divide;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel,
    modulo_semiring_modulo : 'a modulo};
val comm_semiring_1_cancel_semiring_modulo =
  #comm_semiring_1_cancel_semiring_modulo :
  'a semiring_modulo -> 'a comm_semiring_1_cancel;
val modulo_semiring_modulo = #modulo_semiring_modulo :
  'a semiring_modulo -> 'a modulo;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial,
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};
val divide_trivial_semiring_modulo_trivial =
  #divide_trivial_semiring_modulo_trivial :
  'a semiring_modulo_trivial -> 'a divide_trivial;
val semiring_modulo_semiring_modulo_trivial =
  #semiring_modulo_semiring_modulo_trivial :
  'a semiring_modulo_trivial -> 'a semiring_modulo;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};
val semidom_divide_algebraic_semidom = #semidom_divide_algebraic_semidom :
  'a algebraic_semidom -> 'a semidom_divide;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom,
    semiring_modulo_trivial_semidom_modulo : 'a semiring_modulo_trivial};
val algebraic_semidom_semidom_modulo = #algebraic_semidom_semidom_modulo :
  'a semidom_modulo -> 'a algebraic_semidom;
val semiring_modulo_trivial_semidom_modulo =
  #semiring_modulo_trivial_semidom_modulo :
  'a semidom_modulo -> 'a semiring_modulo_trivial;

val semiring_modulo_nat =
  {comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_nat,
    modulo_semiring_modulo = modulo_nat}
  : nat semiring_modulo;

val semiring_modulo_trivial_nat =
  {divide_trivial_semiring_modulo_trivial = divide_trivial_nat,
    semiring_modulo_semiring_modulo_trivial = semiring_modulo_nat}
  : nat semiring_modulo_trivial;

val algebraic_semidom_nat =
  {semidom_divide_algebraic_semidom = semidom_divide_nat} :
  nat algebraic_semidom;

val semidom_modulo_nat =
  {algebraic_semidom_semidom_modulo = algebraic_semidom_nat,
    semiring_modulo_trivial_semidom_modulo = semiring_modulo_trivial_nat}
  : nat semidom_modulo;

type 'a semiring_parity =
  {semiring_modulo_semiring_parity : 'a semiring_modulo};
val semiring_modulo_semiring_parity = #semiring_modulo_semiring_parity :
  'a semiring_parity -> 'a semiring_modulo;

val semiring_parity_nat =
  {semiring_modulo_semiring_parity = semiring_modulo_nat} : nat semiring_parity;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add,
    order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add =
  #ab_semigroup_add_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a order;

type 'a ordered_comm_monoid_add =
  {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add,
    ordered_ab_semigroup_add_ordered_comm_monoid_add :
      'a ordered_ab_semigroup_add};
val comm_monoid_add_ordered_comm_monoid_add =
  #comm_monoid_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_ordered_comm_monoid_add =
  #ordered_ab_semigroup_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_semiring =
  {ordered_comm_monoid_add_ordered_semiring : 'a ordered_comm_monoid_add,
    semiring_ordered_semiring : 'a semiring};
val ordered_comm_monoid_add_ordered_semiring =
  #ordered_comm_monoid_add_ordered_semiring :
  'a ordered_semiring -> 'a ordered_comm_monoid_add;
val semiring_ordered_semiring = #semiring_ordered_semiring :
  'a ordered_semiring -> 'a semiring;

val ordered_ab_semigroup_add_nat =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_nat,
    order_ordered_ab_semigroup_add = order_nat}
  : nat ordered_ab_semigroup_add;

val ordered_comm_monoid_add_nat =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_nat,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_nat}
  : nat ordered_comm_monoid_add;

val ordered_semiring_nat =
  {ordered_comm_monoid_add_ordered_semiring = ordered_comm_monoid_add_nat,
    semiring_ordered_semiring = semiring_nat}
  : nat ordered_semiring;

type 'a strict_ordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add};
val ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
  'a strict_ordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_ab_semigroup_add =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
     'a cancel_ab_semigroup_add,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
      'a strict_ordered_ab_semigroup_add};
val cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a cancel_ab_semigroup_add;
val strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_semiring_0 =
  {ordered_semiring_ordered_semiring_0 : 'a ordered_semiring,
    semiring_0_ordered_semiring_0 : 'a semiring_0};
val ordered_semiring_ordered_semiring_0 = #ordered_semiring_ordered_semiring_0 :
  'a ordered_semiring_0 -> 'a ordered_semiring;
val semiring_0_ordered_semiring_0 = #semiring_0_ordered_semiring_0 :
  'a ordered_semiring_0 -> 'a semiring_0;

type 'a ordered_cancel_semiring =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_semiring :
     'a ordered_cancel_ab_semigroup_add,
    ordered_semiring_0_ordered_cancel_semiring : 'a ordered_semiring_0,
    semiring_0_cancel_ordered_cancel_semiring : 'a semiring_0_cancel};
val ordered_cancel_ab_semigroup_add_ordered_cancel_semiring =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a ordered_cancel_ab_semigroup_add;
val ordered_semiring_0_ordered_cancel_semiring =
  #ordered_semiring_0_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a ordered_semiring_0;
val semiring_0_cancel_ordered_cancel_semiring =
  #semiring_0_cancel_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a semiring_0_cancel;

type 'a ordered_comm_semiring =
  {comm_semiring_0_ordered_comm_semiring : 'a comm_semiring_0,
    ordered_semiring_ordered_comm_semiring : 'a ordered_semiring};
val comm_semiring_0_ordered_comm_semiring =
  #comm_semiring_0_ordered_comm_semiring :
  'a ordered_comm_semiring -> 'a comm_semiring_0;
val ordered_semiring_ordered_comm_semiring =
  #ordered_semiring_ordered_comm_semiring :
  'a ordered_comm_semiring -> 'a ordered_semiring;

type 'a ordered_cancel_comm_semiring =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring :
     'a comm_semiring_0_cancel,
    ordered_cancel_semiring_ordered_cancel_comm_semiring :
      'a ordered_cancel_semiring,
    ordered_comm_semiring_ordered_cancel_comm_semiring :
      'a ordered_comm_semiring};
val comm_semiring_0_cancel_ordered_cancel_comm_semiring =
  #comm_semiring_0_cancel_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a comm_semiring_0_cancel;
val ordered_cancel_semiring_ordered_cancel_comm_semiring =
  #ordered_cancel_semiring_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a ordered_cancel_semiring;
val ordered_comm_semiring_ordered_cancel_comm_semiring =
  #ordered_comm_semiring_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a ordered_comm_semiring;

type 'a ordered_semiring_strict =
  {ordered_cancel_ab_semigroup_add_ordered_semiring_strict :
     'a ordered_cancel_ab_semigroup_add,
    ordered_semiring_ordered_semiring_strict : 'a ordered_semiring,
    semiring_0_cancel_ordered_semiring_strict : 'a semiring_0_cancel};
val ordered_cancel_ab_semigroup_add_ordered_semiring_strict =
  #ordered_cancel_ab_semigroup_add_ordered_semiring_strict :
  'a ordered_semiring_strict -> 'a ordered_cancel_ab_semigroup_add;
val ordered_semiring_ordered_semiring_strict =
  #ordered_semiring_ordered_semiring_strict :
  'a ordered_semiring_strict -> 'a ordered_semiring;
val semiring_0_cancel_ordered_semiring_strict =
  #semiring_0_cancel_ordered_semiring_strict :
  'a ordered_semiring_strict -> 'a semiring_0_cancel;

type 'a ordered_comm_semiring_strict =
  {ordered_cancel_comm_semiring_ordered_comm_semiring_strict :
     'a ordered_cancel_comm_semiring,
    ordered_semiring_strict_ordered_comm_semiring_strict :
      'a ordered_semiring_strict};
val ordered_cancel_comm_semiring_ordered_comm_semiring_strict =
  #ordered_cancel_comm_semiring_ordered_comm_semiring_strict :
  'a ordered_comm_semiring_strict -> 'a ordered_cancel_comm_semiring;
val ordered_semiring_strict_ordered_comm_semiring_strict =
  #ordered_semiring_strict_ordered_comm_semiring_strict :
  'a ordered_comm_semiring_strict -> 'a ordered_semiring_strict;

type 'a ordered_ab_semigroup_add_imp_le =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
     'a ordered_cancel_ab_semigroup_add};
val ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
  #ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
  'a ordered_ab_semigroup_add_imp_le -> 'a ordered_cancel_ab_semigroup_add;

type 'a strict_ordered_comm_monoid_add =
  {comm_monoid_add_strict_ordered_comm_monoid_add : 'a comm_monoid_add,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
      'a strict_ordered_ab_semigroup_add};
val comm_monoid_add_strict_ordered_comm_monoid_add =
  #comm_monoid_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a comm_monoid_add;
val strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
  #strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_cancel_comm_monoid_add =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
     'a ordered_cancel_ab_semigroup_add,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a ordered_comm_monoid_add,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a strict_ordered_comm_monoid_add};
val ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_cancel_ab_semigroup_add;
val ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_comm_monoid_add;
val strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a strict_ordered_comm_monoid_add;

type 'a ordered_ab_semigroup_monoid_add_imp_le =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
     'a cancel_comm_monoid_add,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_ab_semigroup_add_imp_le,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_cancel_comm_monoid_add};
val cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le -> 'a cancel_comm_monoid_add;
val ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_ab_semigroup_add_imp_le;
val ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_cancel_comm_monoid_add;

type 'a linordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add,
    linorder_linordered_ab_semigroup_add : 'a linorder};
val ordered_ab_semigroup_add_linordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_linordered_ab_semigroup_add :
  'a linordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;
val linorder_linordered_ab_semigroup_add = #linorder_linordered_ab_semigroup_add
  : 'a linordered_ab_semigroup_add -> 'a linorder;

type 'a linordered_cancel_ab_semigroup_add =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
     'a linordered_ab_semigroup_add,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add_imp_le};
val linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
  #linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a linordered_ab_semigroup_add;
val ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
  #ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a ordered_ab_semigroup_add_imp_le;

type 'a linordered_semiring =
  {linordered_cancel_ab_semigroup_add_linordered_semiring :
     'a linordered_cancel_ab_semigroup_add,
    ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring :
      'a ordered_ab_semigroup_monoid_add_imp_le,
    ordered_cancel_semiring_linordered_semiring : 'a ordered_cancel_semiring};
val linordered_cancel_ab_semigroup_add_linordered_semiring =
  #linordered_cancel_ab_semigroup_add_linordered_semiring :
  'a linordered_semiring -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring =
  #ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring :
  'a linordered_semiring -> 'a ordered_ab_semigroup_monoid_add_imp_le;
val ordered_cancel_semiring_linordered_semiring =
  #ordered_cancel_semiring_linordered_semiring :
  'a linordered_semiring -> 'a ordered_cancel_semiring;

type 'a linordered_semiring_strict =
  {linordered_semiring_linordered_semiring_strict : 'a linordered_semiring,
    ordered_semiring_strict_linordered_semiring_strict :
      'a ordered_semiring_strict};
val linordered_semiring_linordered_semiring_strict =
  #linordered_semiring_linordered_semiring_strict :
  'a linordered_semiring_strict -> 'a linordered_semiring;
val ordered_semiring_strict_linordered_semiring_strict =
  #ordered_semiring_strict_linordered_semiring_strict :
  'a linordered_semiring_strict -> 'a ordered_semiring_strict;

type 'a linordered_comm_semiring_strict =
  {linordered_semiring_strict_linordered_comm_semiring_strict :
     'a linordered_semiring_strict,
    ordered_comm_semiring_strict_linordered_comm_semiring_strict :
      'a ordered_comm_semiring_strict};
val linordered_semiring_strict_linordered_comm_semiring_strict =
  #linordered_semiring_strict_linordered_comm_semiring_strict :
  'a linordered_comm_semiring_strict -> 'a linordered_semiring_strict;
val ordered_comm_semiring_strict_linordered_comm_semiring_strict =
  #ordered_comm_semiring_strict_linordered_comm_semiring_strict :
  'a linordered_comm_semiring_strict -> 'a ordered_comm_semiring_strict;

type 'a ordered_semiring_1 =
  {ordered_semiring_0_ordered_semiring_1 : 'a ordered_semiring_0,
    semiring_1_ordered_semiring_1 : 'a semiring_1,
    zero_less_one_ordered_semiring_1 : 'a zero_less_one};
val ordered_semiring_0_ordered_semiring_1 =
  #ordered_semiring_0_ordered_semiring_1 :
  'a ordered_semiring_1 -> 'a ordered_semiring_0;
val semiring_1_ordered_semiring_1 = #semiring_1_ordered_semiring_1 :
  'a ordered_semiring_1 -> 'a semiring_1;
val zero_less_one_ordered_semiring_1 = #zero_less_one_ordered_semiring_1 :
  'a ordered_semiring_1 -> 'a zero_less_one;

type 'a linordered_nonzero_semiring =
  {semiring_char_0_linordered_nonzero_semiring : 'a semiring_char_0,
    linorder_linordered_nonzero_semiring : 'a linorder,
    comm_semiring_1_linordered_nonzero_semiring : 'a comm_semiring_1,
    ordered_comm_semiring_linordered_nonzero_semiring :
      'a ordered_comm_semiring,
    ordered_semiring_1_linordered_nonzero_semiring : 'a ordered_semiring_1};
val semiring_char_0_linordered_nonzero_semiring =
  #semiring_char_0_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a semiring_char_0;
val linorder_linordered_nonzero_semiring = #linorder_linordered_nonzero_semiring
  : 'a linordered_nonzero_semiring -> 'a linorder;
val comm_semiring_1_linordered_nonzero_semiring =
  #comm_semiring_1_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a comm_semiring_1;
val ordered_comm_semiring_linordered_nonzero_semiring =
  #ordered_comm_semiring_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a ordered_comm_semiring;
val ordered_semiring_1_linordered_nonzero_semiring =
  #ordered_semiring_1_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a ordered_semiring_1;

type 'a linordered_semidom =
  {linordered_comm_semiring_strict_linordered_semidom :
     'a linordered_comm_semiring_strict,
    linordered_nonzero_semiring_linordered_semidom :
      'a linordered_nonzero_semiring,
    semidom_linordered_semidom : 'a semidom};
val linordered_comm_semiring_strict_linordered_semidom =
  #linordered_comm_semiring_strict_linordered_semidom :
  'a linordered_semidom -> 'a linordered_comm_semiring_strict;
val linordered_nonzero_semiring_linordered_semidom =
  #linordered_nonzero_semiring_linordered_semidom :
  'a linordered_semidom -> 'a linordered_nonzero_semiring;
val semidom_linordered_semidom = #semidom_linordered_semidom :
  'a linordered_semidom -> 'a semidom;

val strict_ordered_ab_semigroup_add_nat =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
     ordered_ab_semigroup_add_nat}
  : nat strict_ordered_ab_semigroup_add;

val ordered_cancel_ab_semigroup_add_nat =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
     cancel_ab_semigroup_add_nat,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      strict_ordered_ab_semigroup_add_nat}
  : nat ordered_cancel_ab_semigroup_add;

val ordered_semiring_0_nat =
  {ordered_semiring_ordered_semiring_0 = ordered_semiring_nat,
    semiring_0_ordered_semiring_0 = semiring_0_nat}
  : nat ordered_semiring_0;

val ordered_cancel_semiring_nat =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_semiring =
     ordered_cancel_ab_semigroup_add_nat,
    ordered_semiring_0_ordered_cancel_semiring = ordered_semiring_0_nat,
    semiring_0_cancel_ordered_cancel_semiring = semiring_0_cancel_nat}
  : nat ordered_cancel_semiring;

val ordered_comm_semiring_nat =
  {comm_semiring_0_ordered_comm_semiring = comm_semiring_0_nat,
    ordered_semiring_ordered_comm_semiring = ordered_semiring_nat}
  : nat ordered_comm_semiring;

val ordered_cancel_comm_semiring_nat =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring =
     comm_semiring_0_cancel_nat,
    ordered_cancel_semiring_ordered_cancel_comm_semiring =
      ordered_cancel_semiring_nat,
    ordered_comm_semiring_ordered_cancel_comm_semiring =
      ordered_comm_semiring_nat}
  : nat ordered_cancel_comm_semiring;

val ordered_semiring_strict_nat =
  {ordered_cancel_ab_semigroup_add_ordered_semiring_strict =
     ordered_cancel_ab_semigroup_add_nat,
    ordered_semiring_ordered_semiring_strict = ordered_semiring_nat,
    semiring_0_cancel_ordered_semiring_strict = semiring_0_cancel_nat}
  : nat ordered_semiring_strict;

val ordered_comm_semiring_strict_nat =
  {ordered_cancel_comm_semiring_ordered_comm_semiring_strict =
     ordered_cancel_comm_semiring_nat,
    ordered_semiring_strict_ordered_comm_semiring_strict =
      ordered_semiring_strict_nat}
  : nat ordered_comm_semiring_strict;

val ordered_ab_semigroup_add_imp_le_nat =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
     ordered_cancel_ab_semigroup_add_nat}
  : nat ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_nat =
  {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_nat,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
      strict_ordered_ab_semigroup_add_nat}
  : nat strict_ordered_comm_monoid_add;

val ordered_cancel_comm_monoid_add_nat =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
     ordered_cancel_ab_semigroup_add_nat,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      ordered_comm_monoid_add_nat,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      strict_ordered_comm_monoid_add_nat}
  : nat ordered_cancel_comm_monoid_add;

val ordered_ab_semigroup_monoid_add_imp_le_nat =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
     cancel_comm_monoid_add_nat,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_ab_semigroup_add_imp_le_nat,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_cancel_comm_monoid_add_nat}
  : nat ordered_ab_semigroup_monoid_add_imp_le;

val linordered_ab_semigroup_add_nat =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add =
     ordered_ab_semigroup_add_nat,
    linorder_linordered_ab_semigroup_add = linorder_nat}
  : nat linordered_ab_semigroup_add;

val linordered_cancel_ab_semigroup_add_nat =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
     linordered_ab_semigroup_add_nat,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
      ordered_ab_semigroup_add_imp_le_nat}
  : nat linordered_cancel_ab_semigroup_add;

val linordered_semiring_nat =
  {linordered_cancel_ab_semigroup_add_linordered_semiring =
     linordered_cancel_ab_semigroup_add_nat,
    ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring =
      ordered_ab_semigroup_monoid_add_imp_le_nat,
    ordered_cancel_semiring_linordered_semiring = ordered_cancel_semiring_nat}
  : nat linordered_semiring;

val linordered_semiring_strict_nat =
  {linordered_semiring_linordered_semiring_strict = linordered_semiring_nat,
    ordered_semiring_strict_linordered_semiring_strict =
      ordered_semiring_strict_nat}
  : nat linordered_semiring_strict;

val linordered_comm_semiring_strict_nat =
  {linordered_semiring_strict_linordered_comm_semiring_strict =
     linordered_semiring_strict_nat,
    ordered_comm_semiring_strict_linordered_comm_semiring_strict =
      ordered_comm_semiring_strict_nat}
  : nat linordered_comm_semiring_strict;

val ordered_semiring_1_nat =
  {ordered_semiring_0_ordered_semiring_1 = ordered_semiring_0_nat,
    semiring_1_ordered_semiring_1 = semiring_1_nat,
    zero_less_one_ordered_semiring_1 = zero_less_one_nat}
  : nat ordered_semiring_1;

val linordered_nonzero_semiring_nat =
  {semiring_char_0_linordered_nonzero_semiring = semiring_char_0_nat,
    linorder_linordered_nonzero_semiring = linorder_nat,
    comm_semiring_1_linordered_nonzero_semiring = comm_semiring_1_nat,
    ordered_comm_semiring_linordered_nonzero_semiring =
      ordered_comm_semiring_nat,
    ordered_semiring_1_linordered_nonzero_semiring = ordered_semiring_1_nat}
  : nat linordered_nonzero_semiring;

val linordered_semidom_nat =
  {linordered_comm_semiring_strict_linordered_semidom =
     linordered_comm_semiring_strict_nat,
    linordered_nonzero_semiring_linordered_semidom =
      linordered_nonzero_semiring_nat,
    semidom_linordered_semidom = semidom_nat}
  : nat linordered_semidom;

fun power A_ a Zero_nat = one (one_power A_)
  | power A_ a (Suc n) = times (times_power A_) a (power A_ a n);

fun eq A_ a b = equal A_ a b;

fun dvd (A1_, A2_) a b =
  eq A1_
    (modulo
      ((modulo_semiring_modulo o semiring_modulo_semiring_modulo_trivial o
         semiring_modulo_trivial_semidom_modulo)
        A2_)
      b a)
    (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semidom o semidom_semidom_divide o
             semidom_divide_algebraic_semidom o
             algebraic_semidom_semidom_modulo)
            A2_));

datatype num = One | Bit0 of num | Bit1 of num;

fun nat_of_num One = one_nata
  | nat_of_num (Bit0 n) = let
                            val m = nat_of_num n;
                          in
                            plus_nata m m
                          end
  | nat_of_num (Bit1 n) = let
                            val m = nat_of_num n;
                          in
                            Suc (plus_nata m m)
                          end;

fun bit_nat m n =
  not (dvd (equal_nat, semidom_modulo_nat) (nat_of_num (Bit0 One))
        (divide_nata m (power power_nat (nat_of_num (Bit0 One)) n)));

type 'a semiring_bits =
  {semiring_parity_semiring_bits : 'a semiring_parity,
    semiring_modulo_trivial_semiring_bits : 'a semiring_modulo_trivial,
    bit : 'a -> nat -> bool};
val semiring_parity_semiring_bits = #semiring_parity_semiring_bits :
  'a semiring_bits -> 'a semiring_parity;
val semiring_modulo_trivial_semiring_bits =
  #semiring_modulo_trivial_semiring_bits :
  'a semiring_bits -> 'a semiring_modulo_trivial;
val bit = #bit : 'a semiring_bits -> 'a -> nat -> bool;

val semiring_bits_nat =
  {semiring_parity_semiring_bits = semiring_parity_nat,
    semiring_modulo_trivial_semiring_bits = semiring_modulo_trivial_nat,
    bit = bit_nat}
  : nat semiring_bits;

type 'a discrete_linordered_semidom =
  {linordered_semidom_discrete_linordered_semidom : 'a linordered_semidom};
val linordered_semidom_discrete_linordered_semidom =
  #linordered_semidom_discrete_linordered_semidom :
  'a discrete_linordered_semidom -> 'a linordered_semidom;

val discrete_linordered_semidom_nat =
  {linordered_semidom_discrete_linordered_semidom = linordered_semidom_nat} :
  nat discrete_linordered_semidom;

fun id x = (fn xa => xa) x;

fun euclidean_size_nat x = id x;

type 'a euclidean_semiring =
  {semidom_modulo_euclidean_semiring : 'a semidom_modulo,
    euclidean_size : 'a -> nat};
val semidom_modulo_euclidean_semiring = #semidom_modulo_euclidean_semiring :
  'a euclidean_semiring -> 'a semidom_modulo;
val euclidean_size = #euclidean_size : 'a euclidean_semiring -> 'a -> nat;

val euclidean_semiring_nat =
  {semidom_modulo_euclidean_semiring = semidom_modulo_nat,
    euclidean_size = euclidean_size_nat}
  : nat euclidean_semiring;

fun division_segment_nat n = one_nata;

type 'a euclidean_semiring_cancel =
  {euclidean_semiring_euclidean_semiring_cancel : 'a euclidean_semiring};
val euclidean_semiring_euclidean_semiring_cancel =
  #euclidean_semiring_euclidean_semiring_cancel :
  'a euclidean_semiring_cancel -> 'a euclidean_semiring;

type 'a unique_euclidean_semiring =
  {euclidean_semiring_cancel_unique_euclidean_semiring :
     'a euclidean_semiring_cancel,
    division_segment : 'a -> 'a};
val euclidean_semiring_cancel_unique_euclidean_semiring =
  #euclidean_semiring_cancel_unique_euclidean_semiring :
  'a unique_euclidean_semiring -> 'a euclidean_semiring_cancel;
val division_segment = #division_segment :
  'a unique_euclidean_semiring -> 'a -> 'a;

type 'a linordered_euclidean_semiring =
  {unique_euclidean_semiring_linordered_euclidean_semiring :
     'a unique_euclidean_semiring,
    semiring_parity_linordered_euclidean_semiring : 'a semiring_parity,
    discrete_linordered_semidom_linordered_euclidean_semiring :
      'a discrete_linordered_semidom};
val unique_euclidean_semiring_linordered_euclidean_semiring =
  #unique_euclidean_semiring_linordered_euclidean_semiring :
  'a linordered_euclidean_semiring -> 'a unique_euclidean_semiring;
val semiring_parity_linordered_euclidean_semiring =
  #semiring_parity_linordered_euclidean_semiring :
  'a linordered_euclidean_semiring -> 'a semiring_parity;
val discrete_linordered_semidom_linordered_euclidean_semiring =
  #discrete_linordered_semidom_linordered_euclidean_semiring :
  'a linordered_euclidean_semiring -> 'a discrete_linordered_semidom;

val euclidean_semiring_cancel_nat =
  {euclidean_semiring_euclidean_semiring_cancel = euclidean_semiring_nat} :
  nat euclidean_semiring_cancel;

val unique_euclidean_semiring_nat =
  {euclidean_semiring_cancel_unique_euclidean_semiring =
     euclidean_semiring_cancel_nat,
    division_segment = division_segment_nat}
  : nat unique_euclidean_semiring;

val linordered_euclidean_semiring_nat =
  {unique_euclidean_semiring_linordered_euclidean_semiring =
     unique_euclidean_semiring_nat,
    semiring_parity_linordered_euclidean_semiring = semiring_parity_nat,
    discrete_linordered_semidom_linordered_euclidean_semiring =
      discrete_linordered_semidom_nat}
  : nat linordered_euclidean_semiring;

fun unset_bit_nat Zero_nat m =
  times_nata (nat_of_num (Bit0 One)) (divide_nata m (nat_of_num (Bit0 One)))
  | unset_bit_nat (Suc n) m =
    plus_nata (modulo_nata m (nat_of_num (Bit0 One)))
      (times_nata (nat_of_num (Bit0 One))
        (unset_bit_nat n (divide_nata m (nat_of_num (Bit0 One)))));

fun take_bit_nat n m =
  modulo_nata m (power power_nat (nat_of_num (Bit0 One)) n);

fun push_bit_nat n m = times_nata m (power power_nat (nat_of_num (Bit0 One)) n);

fun xor_nat m n =
  (if equal_nata m Zero_nat then n
    else (if equal_nata n Zero_nat then m
           else plus_nata
                  (modulo_nata
                    (plus_nata (modulo_nata m (nat_of_num (Bit0 One)))
                      (modulo_nata n (nat_of_num (Bit0 One))))
                    (nat_of_num (Bit0 One)))
                  (times_nata (nat_of_num (Bit0 One))
                    (xor_nat (divide_nata m (nat_of_num (Bit0 One)))
                      (divide_nata n (nat_of_num (Bit0 One)))))));

fun flip_bit_nat m n = xor_nat n (push_bit_nat m one_nata);

fun drop_bit_nat n m =
  divide_nata m (power power_nat (nat_of_num (Bit0 One)) n);

fun max A_ a b = (if less_eq A_ a b then b else a);

fun or_nat m n =
  (if equal_nata m Zero_nat then n
    else (if equal_nata n Zero_nat then m
           else plus_nata
                  (max ord_nat (modulo_nata m (nat_of_num (Bit0 One)))
                    (modulo_nata n (nat_of_num (Bit0 One))))
                  (times_nata (nat_of_num (Bit0 One))
                    (or_nat (divide_nata m (nat_of_num (Bit0 One)))
                      (divide_nata n (nat_of_num (Bit0 One)))))));

fun set_bit_nat m n = or_nat n (push_bit_nat m one_nata);

fun mask_nat n =
  minus_nata (power power_nat (nat_of_num (Bit0 One)) n) one_nata;

fun and_nat m n =
  (if equal_nata m Zero_nat orelse equal_nata n Zero_nat then Zero_nat
    else plus_nata
           (times_nata (modulo_nata m (nat_of_num (Bit0 One)))
             (modulo_nata n (nat_of_num (Bit0 One))))
           (times_nata (nat_of_num (Bit0 One))
             (and_nat (divide_nata m (nat_of_num (Bit0 One)))
               (divide_nata n (nat_of_num (Bit0 One))))));

type 'a semiring_bit_operations =
  {semiring_bits_semiring_bit_operations : 'a semiring_bits,
    anda : 'a -> 'a -> 'a, or : 'a -> 'a -> 'a, xor : 'a -> 'a -> 'a,
    mask : nat -> 'a, set_bit : nat -> 'a -> 'a, unset_bit : nat -> 'a -> 'a,
    flip_bit : nat -> 'a -> 'a, push_bit : nat -> 'a -> 'a,
    drop_bit : nat -> 'a -> 'a, take_bit : nat -> 'a -> 'a};
val semiring_bits_semiring_bit_operations =
  #semiring_bits_semiring_bit_operations :
  'a semiring_bit_operations -> 'a semiring_bits;
val anda = #anda : 'a semiring_bit_operations -> 'a -> 'a -> 'a;
val or = #or : 'a semiring_bit_operations -> 'a -> 'a -> 'a;
val xor = #xor : 'a semiring_bit_operations -> 'a -> 'a -> 'a;
val mask = #mask : 'a semiring_bit_operations -> nat -> 'a;
val set_bit = #set_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a;
val unset_bit = #unset_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a;
val flip_bit = #flip_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a;
val push_bit = #push_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a;
val drop_bit = #drop_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a;
val take_bit = #take_bit : 'a semiring_bit_operations -> nat -> 'a -> 'a;

val semiring_bit_operations_nat =
  {semiring_bits_semiring_bit_operations = semiring_bits_nat, anda = and_nat,
    or = or_nat, xor = xor_nat, mask = mask_nat, set_bit = set_bit_nat,
    unset_bit = unset_bit_nat, flip_bit = flip_bit_nat, push_bit = push_bit_nat,
    drop_bit = drop_bit_nat, take_bit = take_bit_nat}
  : nat semiring_bit_operations;

type 'a linordered_euclidean_semiring_bit_operations =
  {semiring_bit_operations_linordered_euclidean_semiring_bit_operations :
     'a semiring_bit_operations,
    linordered_euclidean_semiring_linordered_euclidean_semiring_bit_operations :
      'a linordered_euclidean_semiring};
val semiring_bit_operations_linordered_euclidean_semiring_bit_operations =
  #semiring_bit_operations_linordered_euclidean_semiring_bit_operations :
  'a linordered_euclidean_semiring_bit_operations -> 'a semiring_bit_operations;
val linordered_euclidean_semiring_linordered_euclidean_semiring_bit_operations =
  #linordered_euclidean_semiring_linordered_euclidean_semiring_bit_operations :
  'a linordered_euclidean_semiring_bit_operations ->
    'a linordered_euclidean_semiring;

val linordered_euclidean_semiring_bit_operations_nat =
  {semiring_bit_operations_linordered_euclidean_semiring_bit_operations =
     semiring_bit_operations_nat,
    linordered_euclidean_semiring_linordered_euclidean_semiring_bit_operations =
      linordered_euclidean_semiring_nat}
  : nat linordered_euclidean_semiring_bit_operations;

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

val ord_literal =
  {less_eq = (fn a => fn b => ((a : string) <= b)),
    less = (fn a => fn b => ((a : string) < b))}
  : string ord;

val preorder_literal = {ord_preorder = ord_literal} : string preorder;

val order_literal = {preorder_order = preorder_literal} : string order;

val linorder_literal = {order_linorder = order_literal} : string linorder;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

val equal_integer = {equal = (fn a => fn b => ((a : IntInf.int) = b))} :
  IntInf.int equal;

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

val plus_integer = {plus = (fn a => fn b => IntInf.+ (a, b))} : IntInf.int plus;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val semigroup_add_integer = {plus_semigroup_add = plus_integer} :
  IntInf.int semigroup_add;

val numeral_integer =
  {one_numeral = one_integer, semigroup_add_numeral = semigroup_add_integer} :
  IntInf.int numeral;

val times_integer = {times = (fn a => fn b => IntInf.* (a, b))} :
  IntInf.int times;

val power_integer = {one_power = one_integer, times_power = times_integer} :
  IntInf.int power;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

val ab_semigroup_add_integer =
  {semigroup_add_ab_semigroup_add = semigroup_add_integer} :
  IntInf.int ab_semigroup_add;

val semigroup_mult_integer = {times_semigroup_mult = times_integer} :
  IntInf.int semigroup_mult;

val semiring_integer =
  {ab_semigroup_add_semiring = ab_semigroup_add_integer,
    semigroup_mult_semiring = semigroup_mult_integer}
  : IntInf.int semiring;

val mult_zero_integer =
  {times_mult_zero = times_integer, zero_mult_zero = zero_integer} :
  IntInf.int mult_zero;

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

datatype ('a, 'b) xres = Ok of 'a | Err of 'b;

datatype zexn = ZExn of exn |
  BAD_INST of (((string * IntInf.int) * ztyp) * zterm) list | ZOption;

datatype uexn = PExn of exn | CANTUNIFY | ASSIGN | CHANGE_FAIL | Bind;

datatype event = Ev_Unif of unif_trace | Ev_Loss of typ * typ |
  Ev_Dpairs of string * Envir.env * ((string * typ) list * (term * term)) list |
  Ev_Failure_Node | Ev_Bound_Exceeded;

datatype 'a uq = UQ_Cell of ((Envir.env * (term * term) list) * 'a) |
  UQ_Seq of 'a;

datatype bctx =
  BCtx of
    bool * bool * bool * IntInf.int * term list * term * term *
      (term * term) list * IntInf.int * (term * term) * (term * term) list;

datatype thm_args = Orule | Orule_State | State | No_Thm;

datatype texn = UExn of uexn | THM of string * IntInf.int * thm_args |
  ERROR of string | COMPOSE | NOT_OF_SORT of typ * string list |
  INST_CONFLICT of ((string * IntInf.int) * typ) * term * typ;

datatype 'a bops =
  BOps of
    (Envir.env -> (term * term) list -> (event list * ('a, texn) xres) option) *
      ('a ->
        (event list *
          ((((Envir.env * (term * term) list) * 'a) option), texn)
            xres) option) *
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

datatype actx =
  ACtx of
    IntInf.int * (term * term) list * term list * term * term *
      (string * typ) list * term;

datatype 'a thm_rep_ext =
  Thm_rep_ext of IntInf.int * (term * term) list * term * 'a;

datatype ares = ARes of Envir.env * IntInf.int * unit thm_rep_ext;

datatype 'a aseq = AQ_Try of actx * term list * IntInf.int |
  AQ_Map of actx * IntInf.int * 'a * term list * IntInf.int;

datatype 'a fseq = FQ of 'a;

datatype cterm_rep = CTerm of term * typ * IntInf.int;

datatype brctx =
  BRCtx of
    bool * bool * unit thm_rep_ext *
      ((term * term) list * (term list * (term * term))) * term * term *
      term list * bool;

datatype ('a, 'b) rseq = RQ_Empty |
  RQ_Make of brctx * (bool * 'b) * (bool * 'b) list |
  RQ_App of (bool * 'b) * 'a bseq * ('a, 'b) rseq;

datatype ('a, 'b) rstep = RS_Done | RS_Skip of ('a, 'b) rseq |
  RS_Result of (bres * (bool * 'b)) * ('a, 'b) rseq;

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun drop n [] = []
  | drop n (x :: xs) = (case n of Zero_nat => x :: xs | Suc m => drop m xs);

fun null [] = true
  | null (x :: xs) = false;

fun last (x :: xs) = (if null xs then x else last xs);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

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

fun insert A_ x xs = (if member A_ xs x then xs else x :: xs);

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun butlast [] = []
  | butlast (x :: xs) = (if null xs then [] else x :: butlast xs);

fun hd (x21 :: x22) = x21;

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

fun decr lev (Bound i) =
  (if IntInf.<= (lev, i) then Bound (IntInf.- (i, (1 : IntInf.int)))
    else Bound i)
  | decr lev (Abs (a, t, body)) =
    Abs (a, t, decr (IntInf.+ (lev, (1 : IntInf.int))) body)
  | decr lev (t $ u) = decr lev t $ decr lev u
  | decr lev (Const (v, va)) = Const (v, va)
  | decr lev (Free (v, va)) = Free (v, va)
  | decr lev (Var (v, va)) = Var (v, va);

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

fun exists_subterm p (t $ u) =
  p (t $ u) orelse (exists_subterm p t orelse exists_subterm p u)
  | exists_subterm p (Abs (a, ta, t)) =
    p (Abs (a, ta, t)) orelse exists_subterm p t
  | exists_subterm p (Const (v, va)) = p (Const (v, va))
  | exists_subterm p (Free (v, va)) = p (Free (v, va))
  | exists_subterm p (Var (v, va)) = p (Var (v, va))
  | exists_subterm p (Bound v) = p (Bound v);

fun aconv_term (t1 $ u1) (t2 $ u2) = aconv_term t1 t2 andalso aconv_term u1 u2
  | aconv_term (Abs (uu, t1a, t1)) (Abs (uv, t2a, t2)) =
    aconv_term t1 t2 andalso ((t1a : typ) = t2a)
  | aconv_term (Const (v, va)) a2 = (((Const (v, va)) : term) = a2)
  | aconv_term (Free (v, va)) a2 = (((Free (v, va)) : term) = a2)
  | aconv_term (Var (v, va)) a2 = (((Var (v, va)) : term) = a2)
  | aconv_term (Bound v) a2 = (((Bound v) : term) = a2)
  | aconv_term (Abs (v, va, vb)) (Const (vc, vd)) =
    (((Abs (v, va, vb)) : term) = (Const (vc, vd)))
  | aconv_term (Abs (v, va, vb)) (Free (vc, vd)) =
    (((Abs (v, va, vb)) : term) = (Free (vc, vd)))
  | aconv_term (Abs (v, va, vb)) (Var (vc, vd)) =
    (((Abs (v, va, vb)) : term) = (Var (vc, vd)))
  | aconv_term (Abs (v, va, vb)) (Bound vc) =
    (((Abs (v, va, vb)) : term) = (Bound vc))
  | aconv_term (Abs (v, va, vb)) (vc $ vd) =
    (((Abs (v, va, vb)) : term) = (vc $ vd))
  | aconv_term a1 (Const (v, va)) = ((a1 : term) = (Const (v, va)))
  | aconv_term a1 (Free (v, va)) = ((a1 : term) = (Free (v, va)))
  | aconv_term a1 (Var (v, va)) = ((a1 : term) = (Var (v, va)))
  | aconv_term a1 (Bound v) = ((a1 : term) = (Bound v))
  | aconv_term (vc $ vd) (Abs (v, va, vb)) =
    (((vc $ vd) : term) = (Abs (v, va, vb)));

fun occs t u = exists_subterm (aconv_term t) u;

fun emit ev = SOME ([ev], Ok ());

fun returnW x = SOME ([], Ok x);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun bindW m f =
  (case m of NONE => NONE
    | SOME (evs, Ok x) =>
      (case evs of [] => f x
        | _ :: _ => map_option (fn (evsa, a) => (evs @ evsa, a)) (f x))
    | SOME (evs, Err e) => SOME (evs, Err e));

fun mapW f [] = returnW []
  | mapW f (x :: xs) =
    bindW (f x) (fn y => bindW (mapW f xs) (fn ys => returnW (y :: ys)));

val tvar_a : string =
  implode
    [Chara (true, true, true, false, false, true, false, false),
      Chara (true, false, false, false, false, true, true, false)];

val ax_aT : typ = TVar ((tvar_a, (0 : IntInf.int)), []);

val tvar_b : string =
  implode
    [Chara (true, true, true, false, false, true, false, false),
      Chara (false, true, false, false, false, true, true, false)];

val ax_bT : typ = TVar ((tvar_b, (0 : IntInf.int)), []);

val propT : typ = Type ("prop", []);

fun ax_eq ta t u =
  Const ("Pure.eq", Type ("fun", [ta, Type ("fun", [ta, propT])])) $ t $ u;

fun loose_bvar1 (Bound i) k = ((i : IntInf.int) = k)
  | loose_bvar1 (f $ t) k = loose_bvar1 f k orelse loose_bvar1 t k
  | loose_bvar1 (Abs (uu, uv, t)) k =
    loose_bvar1 t (IntInf.+ (k, (1 : IntInf.int)))
  | loose_bvar1 (Const (v, va)) ux = false
  | loose_bvar1 (Free (v, va)) ux = false
  | loose_bvar1 (Var (v, va)) ux = false;

fun is_dependent t = loose_bvar1 t (0 : IntInf.int);

fun eta_contract (Abs (a, t, body)) =
  let
    val bodya = eta_contract body;
  in
    (case bodya of Const (_, _) => Abs (a, t, bodya)
      | Free (_, _) => Abs (a, t, bodya) | Var (_, _) => Abs (a, t, bodya)
      | Bound _ => Abs (a, t, bodya) | Abs (_, _, _) => Abs (a, t, bodya)
      | _ $ Const (_, _) => Abs (a, t, bodya)
      | _ $ Free (_, _) => Abs (a, t, bodya)
      | _ $ Var (_, _) => Abs (a, t, bodya)
      | f $ Bound i =>
        (if ((i : IntInf.int) = (0 : IntInf.int)) andalso not (is_dependent f)
          then decr (0 : IntInf.int) f else Abs (a, t, bodya))
      | _ $ Abs (_, _, _) => Abs (a, t, bodya)
      | _ $ (_ $ _) => Abs (a, t, bodya))
  end
  | eta_contract (t $ u) = eta_contract t $ eta_contract u
  | eta_contract (Const (v, va)) = Const (v, va)
  | eta_contract (Free (v, va)) = Free (v, va)
  | eta_contract (Var (v, va)) = Var (v, va)
  | eta_contract (Bound v) = Bound v;

fun aeconv t u =
  aconv_term t u orelse aconv_term (eta_contract t) (eta_contract u);

fun is_Abs (Abs (uu, uv, uw)) = true
  | is_Abs (Const (v, va)) = false
  | is_Abs (Free (v, va)) = false
  | is_Abs (Var (v, va)) = false
  | is_Abs (Bound v) = false
  | is_Abs (v $ va) = false;

fun zip_eq [] [] = return []
  | zip_eq (x :: xs) (y :: ys) =
    bindM (zip_eq xs ys) (fn zs => return ((x, y) :: zs))
  | zip_eq (v :: va) [] = raisea Unequal_Lengths
  | zip_eq [] (v :: va) = raisea Unequal_Lengths;

fun zFuns ts t = foldr (fn a => fn b => ZFun (a, b)) ts t;

fun dedup A_ [] = []
  | dedup A_ (x :: xs) = x :: dedup A_ (filter (fn y => not (eq A_ y x)) xs);

fun liftM m =
  (case m of NONE => NONE | SOME (Ok x) => SOME ([], Ok x)
    | SOME (Err e) => SOME ([], Err (PExn e)));

fun var_clash xi ta t =
  raisea
    (Type_Error
      ("Variable has two distinct types", [], [Var (xi, t), Var (xi, ta)]));

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (Suc n);

fun size_list xs = length_tailrec xs Zero_nat;

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
                           (b andalso
                             equal_nata (size_list ts) (size_list tsa)))
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

fun abshyp h i (Proofterm.Hyp t) =
  (if aconv_term h t then Proofterm.PBound i else Proofterm.Hyp t)
  | abshyp h i (Proofterm.Abst (s, t, p)) = Proofterm.Abst (s, t, abshyp h i p)
  | abshyp h i (Proofterm.AbsP (s, t, p)) =
    Proofterm.AbsP (s, t, abshyp h (IntInf.+ (i, (1 : IntInf.int))) p)
  | abshyp h i (p % t) = abshyp h i p % t
  | abshyp h i (p %% q) = abshyp h i p %% abshyp h i q
  | abshyp h i Proofterm.MinProof = Proofterm.MinProof
  | abshyp h i (Proofterm.PBound v) = Proofterm.PBound v
  | abshyp h i (Proofterm.PAxm (v, va, vb)) = Proofterm.PAxm (v, va, vb)
  | abshyp h i (Proofterm.PClass (v, va)) = Proofterm.PClass (v, va)
  | abshyp h i (Proofterm.Oracle (v, va, vb)) = Proofterm.Oracle (v, va, vb)
  | abshyp h i (Proofterm.PThm v) = Proofterm.PThm v;

fun ax_var x t = Var ((x, (0 : IntInf.int)), t);

fun mk_rep m tps p = Thm_rep_ext (m, tps, p, ());

fun ct_maxidx (CTerm (x1, x2, x3)) = x3;

fun maxidx_typ (TVar ((uu, j), uv)) i = max ord_integer i j
  | maxidx_typ (Type (uw, ts)) i = fold maxidx_typ ts i
  | maxidx_typ (TFree (ux, uy)) i = i;

fun maxidx_term (Var ((uu, j), t)) i = maxidx_typ t (max ord_integer i j)
  | maxidx_term (Const (uv, t)) i = maxidx_typ t i
  | maxidx_term (Free (uw, t)) i = maxidx_typ t i
  | maxidx_term (Bound ux) i = i
  | maxidx_term (Abs (uy, ta, t)) i = maxidx_term t (maxidx_typ ta i)
  | maxidx_term (t $ u) i = maxidx_term u (maxidx_term t i);

fun maxidx_of_term t = maxidx_term t (~1 : IntInf.int);

fun ct_t (CTerm (x1, x2, x3)) = x1;

fun ct_T (CTerm (x1, x2, x3)) = x2;

fun adjust_maxidx_cterm i ct =
  (if (((ct_maxidx ct) : IntInf.int) = i) then ct
    else (if IntInf.< (ct_maxidx ct, i) then CTerm (ct_t ct, ct_T ct, i)
           else CTerm (ct_t ct, ct_T ct,
                        max ord_integer (maxidx_of_term (ct_t ct)) i)));

fun raiseW e = SOME ([], Err e);

fun weaken raw_ct th =
  let
    val ct = adjust_maxidx_cterm (~1 : IntInf.int) raw_ct;
  in
    (if not (((ct_T ct) : typ) = propT)
      then raiseW
             (THM ("weaken: assumptions must have type prop", (0 : IntInf.int),
                    No_Thm))
      else (if not (((ct_maxidx ct) : IntInf.int) = (~1 : IntInf.int))
             then raiseW
                    (THM ("weaken: assumptions may not contain schematic variables",
                           ct_maxidx ct, No_Thm))
             else returnW th))
  end;

val zax_aT : ztyp = ZTVar ((tvar_a, (~1 : IntInf.int)), []);

val zax_bT : ztyp = ZTVar ((tvar_b, (~1 : IntInf.int)), []);

fun zax_eq ta t u = ZApp (ZApp (ZConst1 ("Pure.eq", ta), t), u);

fun head_of (f $ uu) = head_of f
  | head_of (Const (v, va)) = Const (v, va)
  | head_of (Free (v, va)) = Free (v, va)
  | head_of (Var (v, va)) = Var (v, va)
  | head_of (Bound v) = Bound v
  | head_of (Abs (v, va, vb)) = Abs (v, va, vb);

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
  (case m of NONE => NONE | SOME (Ok x) => SOME (Ok x)
    | SOME (Err e) => SOME (Err (ZExn e)));

fun liftOZ m = map_option Ok m;

fun typ_of (ZTVar (v, s)) =
  (if (((snd v) : IntInf.int) = (~1 : IntInf.int)) then TFree (fst v, s)
    else TVar (v, s))
  | typ_of (ZFun (t, u)) = Type ("fun", [typ_of t, typ_of u])
  | typ_of ZProp = propT
  | typ_of (ZType0 c) = Type (c, [])
  | typ_of (ZType1 (c, t)) = Type (c, [typ_of t])
  | typ_of (ZType (c, ts)) = Type (c, map typ_of ts);

fun apsnd f (x, y) = (x, f y);

fun existsM p [] = return false
  | existsM p (x :: xs) =
    bindM (p x) (fn b => (if b then return true else existsM p xs));

fun lookup1 te xi t =
  (case Vartab.lookup te xi of NONE => return NONE
    | SOME (u, ta) =>
      (if ((t : typ) = u) then return (SOME ta) else var_clash xi t u));

fun of_sort alg t s =
  (if null s then return true
    else (case t
           of Type (a, ts) =>
             handlea
               (bindM (mg_domain alg a s)
                 (fn ss => allM (fn (aa, b) => of_sort alg aa b) (zip ts ss)))
               (fn e =>
                 (case e of Unif _ => raisea e | Pattern => raisea e
                   | Match => raisea e | TUnify => raisea e
                   | Type_Match => raisea e | Class_Error _ => return false
                   | Type_Error (_, _, _) => raisea e
                   | Term_Error (_, _) => raisea e | Failure _ => raisea e
                   | Subscript => raisea e | Unequal_Lengths => raisea e
                   | Dup _ => raisea e))
           | TFree (_, sa) => return (sort_le alg sa s)
           | TVar (_, sa) => return (sort_le alg sa s)));

fun dest_eq (Const (c, Type (n, [ta, uu])) $ t $ u) =
  (if ((c : string) = "Pure.eq") then SOME (ta, (t, u)) else NONE)
  | dest_eq (Const (v, va)) = NONE
  | dest_eq (Free (v, va)) = NONE
  | dest_eq (Var (v, va)) = NONE
  | dest_eq (Bound v) = NONE
  | dest_eq (Abs (v, va, vb)) = NONE
  | dest_eq (Const (vb, vc) $ va) = NONE
  | dest_eq (Free (vb, vc) $ va) = NONE
  | dest_eq (Var (vb, vc) $ va) = NONE
  | dest_eq (Bound vb $ va) = NONE
  | dest_eq (Abs (vb, vc, vd) $ va) = NONE
  | dest_eq (Const (vd, Type (vf, [])) $ vc $ va) = NONE
  | dest_eq (Const (vd, Type (vf, [vh])) $ vc $ va) = NONE
  | dest_eq (Const (vd, Type (vf, vh :: vj :: vl :: vm)) $ vc $ va) = NONE
  | dest_eq (Const (vd, TFree (vf, vg)) $ vc $ va) = NONE
  | dest_eq (Const (vd, TVar (vf, vg)) $ vc $ va) = NONE
  | dest_eq (Free (vd, ve) $ vc $ va) = NONE
  | dest_eq (Var (vd, ve) $ vc $ va) = NONE
  | dest_eq (Bound vd $ vc $ va) = NONE
  | dest_eq (Abs (vd, ve, vf) $ vc $ va) = NONE
  | dest_eq (vd $ ve $ vc $ va) = NONE;

val implies : term =
  Const ("Pure.imp", Type ("fun", [propT, Type ("fun", [propT, propT])]));

fun mk_implies a b = implies $ a $ b;

fun trivial ct =
  (if not (((ct_T ct) : typ) = propT)
    then raiseW
           (THM ("trivial: the term must have type prop", (0 : IntInf.int),
                  No_Thm))
    else returnW (mk_rep (ct_maxidx ct) [] (mk_implies (ct_t ct) (ct_t ct))));

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

fun zabshyp h lev (ZHyp t) = (if aconv_zterm h t then ZBoundp lev else ZHyp t)
  | zabshyp h lev (ZAbst (x, t, p)) = ZAbst (x, t, zabshyp h lev p)
  | zabshyp h lev (ZAbsp (x, t, p)) =
    ZAbsp (x, t, zabshyp h (IntInf.+ (lev, (1 : IntInf.int))) p)
  | zabshyp h lev (ZAppt (p, t)) = ZAppt (zabshyp h lev p, t)
  | zabshyp h lev (ZAppp (p, q)) = ZAppp (zabshyp h lev p, zabshyp h lev q)
  | zabshyp h lev ZNop = ZNop
  | zabshyp h lev (ZConstp v) = ZConstp v
  | zabshyp h lev (ZBoundp v) = ZBoundp v
  | zabshyp h lev (OFCLASSp (v, va)) = OFCLASSp (v, va);

fun zax_imp a b = ZApp (ZApp (ZConst0 "Pure.imp", a), b);

fun zax_var x t = ZVar ((x, (~1 : IntInf.int)), t);

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
                    (drop (minus_nata (size_list cs) (size_list s)) cs) s))
          then SOME (ta, implode
                           (take (minus_nata (size_list cs) (size_list s)) cs))
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
  return (ZVar ((x, (~1 : IntInf.int)), ztyp_of t))
  | zterm_of ta (Var (xi, t)) = return (ZVar (xi, ztyp_of t))
  | zterm_of ta (Bound i) = return (ZBound i)
  | zterm_of ta (Const (c, t)) =
    bindM (liftMZ (ta c t))
      (fn ts =>
        return
          (case ts of [] => ZConst0 c | [u] => ZConst1 (c, ztyp_of u)
            | _ :: _ :: _ => ZConst (c, map ztyp_of ts)))
  | zterm_of ta (Abs (a, t, b)) =
    bindM (zterm_of ta b) (fn ba => return (ZAbs (a, ztyp_of t, ba)))
  | zterm_of ta (t $ u) =
    (case match_of_class (t $ u)
      of NONE =>
        bindM (zterm_of ta t)
          (fn tb => bindM (zterm_of ta u) (fn ua => return (ZApp (tb, ua))))
      | SOME tc =>
        (if (((t $ u) : term) = (mk_of_class (fst tc) (snd tc)))
          then return (OFCLASS (ztyp_of (fst tc), snd tc))
          else bindM (zterm_of ta t)
                 (fn tb =>
                   bindM (zterm_of ta u) (fn ua => return (ZApp (tb, ua))))));

fun zlookup ta env xi t =
  (if Vartab.is_empty (Envir.term_env env) then return NONE
    else bindM (liftMZ (lookup env xi (typ_of t)))
           (fn a =>
             (case a of NONE => return NONE
               | SOME u => bindM (zterm_of ta u) (fn ua => return (SOME ua)))));

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

fun handleW m h =
  (case m of NONE => m | SOME (_, Ok _) => m
    | SOME (evs, Err e) =>
      (case evs of [] => h e
        | _ :: _ => map_option (fn (evsa, a) => (evs @ evsa, a)) (h e)));

fun list_all2 p [] ys = null ys
  | list_all2 p xs [] = null xs
  | list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys;

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

fun betapply (Abs (uu, uv, t)) u = subst_bound u t
  | betapply (Const (v, va)) u = Const (v, va) $ u
  | betapply (Free (v, va)) u = Free (v, va) $ u
  | betapply (Var (v, va)) u = Var (v, va) $ u
  | betapply (Bound v) u = Bound v $ u
  | betapply (v $ va) u = v $ va $ u;

val dummyT : typ = Type ("dummy", []);

fun remove_types (Abs (s, ta, t)) = Abs (s, dummyT, remove_types t)
  | remove_types (t $ u) = remove_types t $ remove_types u
  | remove_types (Const (s, t)) = Const (s, dummyT)
  | remove_types (Free (v, va)) = Free (v, va)
  | remove_types (Var (v, va)) = Var (v, va)
  | remove_types (Bound v) = Bound v;

fun comb_arg f t =
  (case head_of f of Const (_, _) => NONE | Free (_, _) => NONE
    | Var (_, _) => SOME (remove_types t) | Bound _ => NONE
    | Abs (_, _, _) => SOME (remove_types t) | _ $ _ => NONE);

fun dest_Abs (Abs (s, t, b)) = SOME (s, (t, b))
  | dest_Abs (Const (v, va)) = NONE
  | dest_Abs (Free (v, va)) = NONE
  | dest_Abs (Var (v, va)) = NONE
  | dest_Abs (Bound v) = NONE
  | dest_Abs (v $ va) = NONE;

fun eq_tpair tua tu =
  aconv_term (fst tua) (fst tu) andalso aconv_term (snd tua) (snd tu);

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

fun binder_types (Type (n, [t, u])) =
  (if ((n : string) = "fun") then t :: binder_types u else [])
  | binder_types (Type (v, [])) = []
  | binder_types (Type (v, [vb])) = []
  | binder_types (Type (v, vb :: vd :: vf :: vg)) = []
  | binder_types (TFree (v, va)) = []
  | binder_types (TVar (v, va)) = [];

fun downto a b =
  (if IntInf.< (a, b) then []
    else a :: downto (IntInf.- (a, (1 : IntInf.int))) b);

fun strip_comb_acc (f $ t) ts = strip_comb_acc f (t :: ts)
  | strip_comb_acc (Const (v, va)) ts = (Const (v, va), ts)
  | strip_comb_acc (Free (v, va)) ts = (Free (v, va), ts)
  | strip_comb_acc (Var (v, va)) ts = (Var (v, va), ts)
  | strip_comb_acc (Bound v) ts = (Bound v, ts)
  | strip_comb_acc (Abs (v, va, vb)) ts = (Abs (v, va, vb), ts);

fun strip_comb t = strip_comb_acc t [];

fun empty_env m =
  Envir.Envir {maxidx = m, tenv = Vartab.empty, tyenv = Vartab.empty};

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

fun beta_norm t = norm_term (empty_env (~1 : IntInf.int)) t;

fun list_comb t ts = foldl (fn a => fn b => a $ b) t ts;

fun eta_long ts t =
  (case dest_Abs t
    of NONE =>
      let
        val (u, tsa) = strip_comb t;
      in
        (if is_Abs u then bindM (beta_norm t) (eta_long ts)
          else bindM (fastype_of_term ts t)
                 (fn ta =>
                   bindM (mapM (fn s =>
                                 eta_long (rev (binder_types ta) @ ts)
                                   (incr_boundvars
                                     (integer_of_nat
                                       (size_list (binder_types ta)))
                                     s))
                           tsa)
                     (fn tsaa =>
                       bindM (mapM (fn j =>
                                     eta_long (rev (binder_types ta) @ ts)
                                       (Bound j))
                               (downto
                                 (IntInf.- (integer_of_nat
      (size_list (binder_types ta)), (1 : IntInf.int)))
                                 (0 : IntInf.int)))
                         (fn bs =>
                           return
                             (foldr (fn a => fn b => Abs ("x", a, b))
                               (binder_types ta)
                               (list_comb
                                 (incr_boundvars
                                   (integer_of_nat
                                     (size_list (binder_types ta)))
                                   u)
                                 (tsaa @ bs)))))))
      end
    | SOME (s, (ta, b)) =>
      bindM (eta_long (ta :: ts) b) (fn ba => return (Abs (s, ta, ba))));

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

fun liftWT m =
  (case m of NONE => NONE | SOME (evs, Ok x) => SOME (evs, Ok x)
    | SOME (evs, Err e) => SOME (evs, Err (UExn e)));

fun liftMT m = liftWT (liftM m);

fun norm_type tye t =
  (if Vartab.is_empty tye then return t else norm_type_aux tye t);

fun norm_term_skip env n t =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then liftMT (norm_term env t)
    else (case dest_all t
           of NONE =>
             (case dest_imp t
               of NONE => raiseW (ERROR "norm_term_skip: too few assumptions??")
               | SOME (a, b) =>
                 bindW (norm_term_skip env (IntInf.- (n, (1 : IntInf.int))) b)
                   (fn ba => returnW (mk_implies a ba)))
           | SOME (a, (ta, b)) =>
             bindW (liftMT (norm_type (Envir.type_env env) ta))
               (fn tb =>
                 bindW (norm_term_skip env n b)
                   (fn ba => returnW (all_const tb $ Abs (a, tb, ba))))));

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
    bindW (if env_is_empty env
            then returnW (tpairs, (bc_Bs ctx @ na_As na, bc_C ctx))
            else bindW (liftMT (mapM (norm_tpair env) tpairs))
                   (fn ntps =>
                     (if above env (bc_smax ctx)
                       then (if bc_lifted ctx
                              then bindW (mapW
   (norm_term_skip env (bc_nlift ctx)) (na_As na))
                                     (fn asa =>
                                       returnW
 (ntps, (bc_Bs ctx @ asa, bc_C ctx)))
                              else bindW (liftMT
   (mapM (norm_term env) (na_As na)))
                                     (fn asa =>
                                       returnW
 (ntps, (bc_Bs ctx @ asa, bc_C ctx))))
                       else (if bc_match ctx then raiseW COMPOSE
                              else bindW (liftMT
   (mapM (norm_term env) (bc_Bs ctx @ na_As na)))
                                     (fn hs =>
                                       bindW (liftMT (norm_term env (bc_C ctx)))
 (fn c => returnW (ntps, (hs, c))))))))
      (fn (ntpairs, (hs, c)) =>
        returnW (BRes (env, ntpairs, list_implies hs c, a, na)))
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
    handleW
      (bindW
        (if bc_flatten ctx then liftMT (mapM (flatten_params variants n) as1)
          else returnW as1)
        (fn as2 => returnW (NewAs (as2, as1, r, n))))
      (fn e =>
        (case e of UExn (PExn (Unif _)) => raiseW e
          | UExn (PExn Pattern) => raiseW e | UExn (PExn Match) => raiseW e
          | UExn (PExn TUnify) => raiseW e | UExn (PExn Type_Match) => raiseW e
          | UExn (PExn (Class_Error _)) => raiseW e
          | UExn (PExn (Type_Error (_, _, _))) => raiseW e
          | UExn (PExn (Term_Error (_, _))) =>
            raiseW (THM ("bicompose: 1st premise", (0 : IntInf.int), Orule))
          | UExn (PExn (Failure _)) => raiseW e
          | UExn (PExn Subscript) => raiseW e
          | UExn (PExn Unequal_Lengths) => raiseW e
          | UExn (PExn (Dup _)) => raiseW e | UExn CANTUNIFY => raiseW e
          | UExn ASSIGN => raiseW e | UExn CHANGE_FAIL => raiseW e
          | UExn Bind => raiseW e | THM (_, _, _) => raiseW e
          | ERROR _ => raiseW e | COMPOSE => raiseW e
          | NOT_OF_SORT (_, _) => raiseW e
          | INST_CONFLICT (_, _, _) => raiseW e))
  end;

fun tryasms ops ctx er [] n = returnW BS_Empty
  | tryasms ops ctx er (asm :: rest) n =
    (if could_unify asm (er_concl er)
      then let
             val asma = rlist_abs (er_params er) asm;
           in
             bindW (bo_unifiers ops (er_env er)
                     ((asma, er_concla er) :: bc_dpairs ctx))
               (fn us =>
                 bindW (bo_pull ops us)
                   (fn a =>
                     (case a
                       of NONE =>
                         tryasms ops ctx er rest
                           (IntInf.+ (n, (1 : IntInf.int)))
                       | SOME ((env, tpairs), usa) =>
                         bindW (newAs (bo_variants ops) ctx (er_As er) n
                                 [bc_BBi ctx, (er_concla er, asma)] tpairs)
                           (fn na =>
                             returnW
                               (BS_Its
                                 (ctx, SOME (er_A1 er), na,
                                   UQ_Cell ((env, tpairs), usa),
                                   BS_Tryasms
                                     (ctx, er, rest,
                                       IntInf.+ (n, (1 : IntInf.int)))))))))
           end
      else tryasms ops ctx er rest (IntInf.+ (n, (1 : IntInf.int))));

fun bpull ops s =
  (case s of BS_Empty => returnW NONE
    | BS_Its (ctx, a, na, xq, yq) =>
      bindW (case xq of UQ_Cell c => returnW (SOME c)
              | UQ_Seq aa => bo_pull ops aa)
        (fn b =>
          (case b of NONE => bpull ops yq
            | SOME (et, us) =>
              handleW
                (bindW (addth ctx a na et)
                  (fn th =>
                    returnW (SOME (th, BS_Its (ctx, a, na, UQ_Seq us, yq)))))
                (fn e =>
                  (case e of UExn _ => raiseW e | THM (_, _, _) => raiseW e
                    | ERROR _ => raiseW e
                    | COMPOSE => bpull ops (BS_Its (ctx, a, na, UQ_Seq us, yq))
                    | NOT_OF_SORT (_, _) => raiseW e
                    | INST_CONFLICT (_, _, _) => raiseW e))))
    | BS_Tryasms (ctx, er, asms, n) =>
      bindW (tryasms ops ctx er asms n) (bpull ops));

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

fun occs_hyps x ts tpairs =
  list_ex (occs x) ts orelse
    (list_ex (fn (t, _) => occs x t) tpairs orelse
      list_ex (fn (_, a) => occs x a) tpairs);

fun quote_lit s = "\"" ^ s ^ "\"";

fun fastype_of t = fastype_of_term [] t;

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

fun reflexive ct =
  liftMT
    (bindM (mk_equals (ct_t ct, ct_t ct))
      (fn p => return (mk_rep (ct_maxidx ct) [] p)));

fun th_tpairs (Thm_rep_ext (th_maxidx, th_tpairs, th_prop, more)) = th_tpairs;

fun th_maxidx (Thm_rep_ext (th_maxidx, th_tpairs, th_prop, more)) = th_maxidx;

fun th_prop (Thm_rep_ext (th_maxidx, th_tpairs, th_prop, more)) = th_prop;

fun dest_eq_fun (Const (c, Type (n, [ta, ua])) $ t $ u) =
  (if ((c : string) = "Pure.eq") andalso ((n : string) = "fun")
    then SOME (ta, (t, u)) else NONE)
  | dest_eq_fun (Const (v, va)) = NONE
  | dest_eq_fun (Free (v, va)) = NONE
  | dest_eq_fun (Var (v, va)) = NONE
  | dest_eq_fun (Bound v) = NONE
  | dest_eq_fun (Abs (v, va, vb)) = NONE
  | dest_eq_fun (Const (vb, vc) $ va) = NONE
  | dest_eq_fun (Free (vb, vc) $ va) = NONE
  | dest_eq_fun (Var (vb, vc) $ va) = NONE
  | dest_eq_fun (Bound vb $ va) = NONE
  | dest_eq_fun (Abs (vb, vc, vd) $ va) = NONE
  | dest_eq_fun (Const (vd, Type (vf, [])) $ vc $ va) = NONE
  | dest_eq_fun (Const (vd, Type (vf, [vh])) $ vc $ va) = NONE
  | dest_eq_fun (Const (vd, Type (vf, vh :: vj :: vl :: vm)) $ vc $ va) = NONE
  | dest_eq_fun (Const (vd, TFree (vf, vg)) $ vc $ va) = NONE
  | dest_eq_fun (Const (vd, TVar (vf, vg)) $ vc $ va) = NONE
  | dest_eq_fun (Free (vd, ve) $ vc $ va) = NONE
  | dest_eq_fun (Var (vd, ve) $ vc $ va) = NONE
  | dest_eq_fun (Bound vd $ vc $ va) = NONE
  | dest_eq_fun (Abs (vd, ve, vf) $ vc $ va) = NONE
  | dest_eq_fun (vd $ ve $ vc $ va) = NONE;

fun symmetric th =
  (case th_prop th
    of Const (_, _) => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Free (_, _) => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Var (_, _) => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Bound _ => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Abs (_, _, _) => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Const (_, _) $ _ => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Free (_, _) $ _ => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Var (_, _) $ _ => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Bound _ $ _ => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | Abs (_, _, _) $ _ => raiseW (THM ("symmetric", (0 : IntInf.int), State))
    | eq $ t $ u =>
      (case dest_eq_fun (th_prop th)
        of NONE => raiseW (THM ("symmetric", (0 : IntInf.int), State))
        | SOME _ =>
          returnW (mk_rep (th_maxidx th) (th_tpairs th) (eq $ u $ t))));

fun zv_insert_list [] t = SOME t
  | zv_insert_list ((k, x) :: xs) t =
    (case ZVars.lookup t k of NONE => zv_insert_list xs (ZVars.update (k, x) t)
      | SOME y => (if aconv_zterm y x then zv_insert_list xs t else NONE));

fun make_inst xs =
  (case zv_insert_list xs ZVars.empty of NONE => raisea (BAD_INST xs)
    | SOME a => return a);

fun map_insts typ term insts =
  let
    val (instT, inst) = insts;
  in
    bindM (mapM (fn (a, b) =>
                  let
                    val (x, t) = a;
                  in
                    (fn ta =>
                      bindM (term ta) (fn taa => return ((x, typ t), taa)))
                  end
                    b)
            (ZVars.dest inst))
      (fn xs =>
        bindM (make_inst xs)
          (fn insta => return ((fn f => ZTVars.map (K f)) typ instT, insta)))
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
  bindM (zlift_prf inc ts (IntInf.+ (lev, (1 : IntInf.int))) p)
    (fn pa => return (ZAbst (a, zincr_tvar inc t, pa)))
  | zlift_prf inc ts lev (ZAbsp (a, t, p)) =
    bindM (zlift_prf inc ts lev p)
      (fn pa => return (ZAbsp (a, zlift_terma inc ts lev t, pa)))
  | zlift_prf inc ts lev (ZAppt (p, t)) =
    bindM (zlift_prf inc ts lev p)
      (fn pa => return (ZAppt (pa, zlift_terma inc ts lev t)))
  | zlift_prf inc ts lev (ZAppp (p, q)) =
    bindM (zlift_prf inc ts lev p)
      (fn pa =>
        bindM (zlift_prf inc ts lev q) (fn qa => return (ZAppp (pa, qa))))
  | zlift_prf inc ts lev (ZConstp (a, insts)) =
    bindM (map_insts (zincr_tvar inc)
            (fn t => return (zlift_terma inc ts lev t)) insts)
      (fn instsa => return (ZConstp (a, instsa)))
  | zlift_prf inc ts lev (OFCLASSp (t, c)) =
    return (OFCLASSp (zincr_tvar inc t, c))
  | zlift_prf inc ts lev ZNop = return ZNop
  | zlift_prf inc ts lev (ZBoundp v) = return (ZBoundp v)
  | zlift_prf inc ts lev (ZHyp v) = return (ZHyp v);

fun zren_term r m (ZVar ((x, i), t)) =
  ZVar (((if IntInf.< (m, i) then ren_name (fst r) x else x), i), t)
  | zren_term r m (ZAbs (a, ta, t)) = ZAbs (a, ta, zren_term r m t)
  | zren_term r m (ZApp (t, u)) = ZApp (zren_term r m t, zren_term r m u)
  | zren_term r m (ZBound v) = ZBound v
  | zren_term r m (ZConst0 v) = ZConst0 v
  | zren_term r m (ZConst1 (v, va)) = ZConst1 (v, va)
  | zren_term r m (ZConst (v, va)) = ZConst (v, va)
  | zren_term r m (OFCLASS (v, va)) = OFCLASS (v, va);

fun zvars_all p (ZVar (x, t)) = p (x, t)
  | zvars_all p (ZAbs (a, ta, t)) = zvars_all p t
  | zvars_all p (ZApp (t, u)) = zvars_all p t andalso zvars_all p u
  | zvars_all p (ZBound v) = true
  | zvars_all p (ZConst0 v) = true
  | zvars_all p (ZConst1 (v, va)) = true
  | zvars_all p (ZConst (v, va)) = true
  | zvars_all p (OFCLASS (v, va)) = true;

fun ac_tpairs (ACtx (x1, x2, x3, x4, x5, x6, x7)) = x2;

fun ac_params (ACtx (x1, x2, x3, x4, x5, x6, x7)) = x6;

fun ac_maxidx (ACtx (x1, x2, x3, x4, x5, x6, x7)) = x1;

fun ac_concl (ACtx (x1, x2, x3, x4, x5, x6, x7)) = x7;

fun ac_Bs (ACtx (x1, x2, x3, x4, x5, x6, x7)) = x3;

fun ac_C (ACtx (x1, x2, x3, x4, x5, x6, x7)) = x5;

fun newth ctx n et =
  let
    val (env, tpairs) = et;
  in
    (if env_is_empty env
      then returnW
             (ARes (env, n,
                     Thm_rep_ext
                       (Envir.maxidx_of env, tpairs,
                         list_implies (ac_Bs ctx) (ac_C ctx), ())))
      else liftMT
             (bindM (mapM (norm_tpair env) tpairs)
               (fn tps =>
                 bindM (norm_term env (list_implies (ac_Bs ctx) (ac_C ctx)))
                   (fn p =>
                     return
                       (ARes (env, n,
                               Thm_rep_ext
                                 (Envir.maxidx_of env, tps, p, ())))))))
  end;

fun apull ops s =
  (case s of AQ_Try (_, [], _) => returnW NONE
    | AQ_Try (ctx, asm :: rest, n) =>
      (if could_unify asm (ac_concl ctx)
        then bindW (bo_unifiers ops (empty_env (ac_maxidx ctx))
                     ((rlist_abs (ac_params ctx) asm,
                        rlist_abs (ac_params ctx) (ac_concl ctx)) ::
                       ac_tpairs ctx))
               (fn us =>
                 apull ops
                   (AQ_Map (ctx, n, us, rest, IntInf.+ (n, (1 : IntInf.int)))))
        else apull ops (AQ_Try (ctx, rest, IntInf.+ (n, (1 : IntInf.int)))))
    | AQ_Map (ctx, n, us, rest, m) =>
      bindW (bo_pull ops us)
        (fn a =>
          (case a of NONE => apull ops (AQ_Try (ctx, rest, m))
            | SOME (et, usa) =>
              bindW (newth ctx n et)
                (fn th =>
                  returnW (SOME (th, AQ_Map (ctx, n, usa, rest, m)))))));

fun maxidx_tpairs tpairs =
  fold (fn (t, u) => fn i => maxidx_term u (maxidx_term t i)) tpairs;

fun fnewth th env =
  (if env_is_empty env then return th
    else bindM (mapM (norm_tpair env) (th_tpairs th))
           (fn tps =>
             let
               val tpsa = filter (fn (t, u) => not (aconv_term t u)) tps;
             in
               bindM (norm_term env (th_prop th))
                 (fn p =>
                   return
                     (Thm_rep_ext
                       (maxidx_tpairs tpsa (maxidx_of_term p), tpsa, p, ())))
             end));

fun fpull ops smash th s =
  let
    val FQ us = s;
  in
    bindW (bo_pull ops us)
      (fn a =>
        (case a of NONE => returnW NONE
          | SOME (et, usa) =>
            bindW (smash et)
              (fn env =>
                bindW (liftMT (fnewth th env))
                  (fn tha => returnW (SOME ((env, tha), FQ usa))))))
  end;

fun brc_test_hyps (BRCtx (x1, x2, x3, x4, x5, x6, x7, x8)) = x8;

fun brc_trace (BRCtx (x1, x2, x3, x4, x5, x6, x7, x8)) = x1;

fun brc_Hs (BRCtx (x1, x2, x3, x4, x5, x6, x7, x8)) = x7;

fun could_reshyp th hs (a1 :: uu) = not th orelse list_ex (could_unify a1) hs
  | could_reshyp th hs [] = false;

fun strip_imp_prems t =
  (case dest_imp t of NONE => [] | SOME (a, b) => a :: strip_imp_prems b);

fun prems_of th = strip_imp_prems (th_prop th);

fun strip_imp_concl t =
  (case dest_imp t of NONE => t | SOME (_, a) => strip_imp_concl a);

fun concl_of th = strip_imp_concl (th_prop th);

fun could_bires th hs b eres_flg rule =
  could_unify (concl_of rule) b andalso
    (not eres_flg orelse could_reshyp th hs (prems_of rule));

fun brc_B (BRCtx (x1, x2, x3, x4, x5, x6, x7, x8)) = x6;

fun res rep ctx [] = RQ_Empty
  | res rep ctx ((eres_flg, rule) :: brules) =
    (if brc_trace ctx orelse
          could_bires (brc_test_hyps ctx) (brc_Hs ctx) (brc_B ctx) eres_flg
            (rep rule)
      then RQ_Make (ctx, (eres_flg, rule), brules) else res rep ctx brules);

fun type_unify alg t u st = unify_aux alg t u st;

fun liftMP m = map_option (fn a => ([], a)) m;

fun mk_app b x =
  let
    val (i, (j, p)) = x;
  in
    (if b then (IntInf.- (i, (1 : IntInf.int)), (j, p %% Proofterm.PBound i))
      else (i, (IntInf.- (j, (1 : IntInf.int)), p % SOME (Bound j))))
  end;

fun var_eq v w =
  equal_proda equal_literal equal_integer (fst v) (fst w) andalso
    (((snd v) : typ) = (snd w));

fun check_comb (Proofterm.PAxm (a, uu, uv) % f % uw % ux % uy %% p %% uz) =
  ((a : string) = "Pure.combination") andalso
    (not (is_none f) orelse check_comb p)
  | check_comb (Proofterm.PAxm (a, va, vb) % vc % vd % ve %% p %% q) =
    ((a : string) = "Pure.transitive") andalso
      (check_comb p andalso check_comb q)
  | check_comb (Proofterm.PAxm (a, vf, vg) % vh % vi %% p) =
    ((a : string) = "Pure.symmetric") andalso check_comb p
  | check_comb Proofterm.MinProof = false
  | check_comb (Proofterm.PBound v) = false
  | check_comb (Proofterm.Abst (v, va, vb)) = false
  | check_comb (Proofterm.AbsP (v, va, vb)) = false
  | check_comb (v % va) = false
  | check_comb (Proofterm.MinProof %% va) = false
  | check_comb (Proofterm.PBound vb %% va) = false
  | check_comb (Proofterm.Abst (vb, vc, vd) %% va) = false
  | check_comb (Proofterm.AbsP (vb, vc, vd) %% va) = false
  | check_comb (Proofterm.MinProof % vc %% va) = false
  | check_comb (Proofterm.PBound v % vc %% va) = false
  | check_comb (Proofterm.Abst (v, vd, ve) % vc %% va) = false
  | check_comb (Proofterm.AbsP (v, vd, ve) % vc %% va) = false
  | check_comb (Proofterm.MinProof % vd % vc %% va) = false
  | check_comb (Proofterm.PBound ve % vd % vc %% va) = false
  | check_comb (Proofterm.Abst (ve, vf, vg) % vd % vc %% va) = false
  | check_comb (Proofterm.AbsP (ve, vf, vg) % vd % vc %% va) = false
  | check_comb (ve % vf % vd % vc %% va) = false
  | check_comb (ve %% vf % vd % vc %% va) = false
  | check_comb (Proofterm.Hyp ve % vd % vc %% va) = false
  | check_comb (Proofterm.PClass (ve, vf) % vd % vc %% va) = false
  | check_comb (Proofterm.Oracle (ve, vf, vg) % vd % vc %% va) = false
  | check_comb (Proofterm.PThm ve % vd % vc %% va) = false
  | check_comb (v %% vd % vc %% va) = false
  | check_comb (Proofterm.Hyp v % vc %% va) = false
  | check_comb (Proofterm.PAxm (v, vd, ve) % vc %% va) = false
  | check_comb (Proofterm.PClass (v, vd) % vc %% va) = false
  | check_comb (Proofterm.Oracle (v, vd, ve) % vc %% va) = false
  | check_comb (Proofterm.PThm v % vc %% va) = false
  | check_comb (Proofterm.MinProof %% vc %% va) = false
  | check_comb (Proofterm.PBound vd %% vc %% va) = false
  | check_comb (Proofterm.Abst (vd, ve, vf) %% vc %% va) = false
  | check_comb (Proofterm.AbsP (vd, ve, vf) %% vc %% va) = false
  | check_comb (Proofterm.MinProof % ve %% vc %% va) = false
  | check_comb (Proofterm.PBound vf % ve %% vc %% va) = false
  | check_comb (Proofterm.Abst (vf, vg, vh) % ve %% vc %% va) = false
  | check_comb (Proofterm.AbsP (vf, vg, vh) % ve %% vc %% va) = false
  | check_comb (Proofterm.MinProof % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.PBound vh % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Abst (vh, vi, vk) % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.AbsP (vh, vi, vk) % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.MinProof % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.PBound vk % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Abst (vk, vl, vm) % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.AbsP (vk, vl, vm) % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.MinProof % vl % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.PBound vm % vl % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Abst (vm, vn, vo) % vl % vi % vg % ve %% vc %% va) =
    false
  | check_comb (Proofterm.AbsP (vm, vn, vo) % vl % vi % vg % ve %% vc %% va) =
    false
  | check_comb (vm % vn % vl % vi % vg % ve %% vc %% va) = false
  | check_comb (vm %% vn % vl % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Hyp vm % vl % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.PClass (vm, vn) % vl % vi % vg % ve %% vc %% va) =
    false
  | check_comb (Proofterm.Oracle (vm, vn, vo) % vl % vi % vg % ve %% vc %% va) =
    false
  | check_comb (Proofterm.PThm vm % vl % vi % vg % ve %% vc %% va) = false
  | check_comb (vk %% vl % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Hyp vk % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.PClass (vk, vl) % vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Oracle (vk, vl, vm) % vi % vg % ve %% vc %% va) =
    false
  | check_comb (Proofterm.PThm vk % vi % vg % ve %% vc %% va) = false
  | check_comb (vh %% vi % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Hyp vh % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.PAxm (vh, vi, vk) % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.PClass (vh, vi) % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Oracle (vh, vi, vk) % vg % ve %% vc %% va) = false
  | check_comb (Proofterm.PThm vh % vg % ve %% vc %% va) = false
  | check_comb (vf %% vg % ve %% vc %% va) = false
  | check_comb (Proofterm.Hyp vf % ve %% vc %% va) = false
  | check_comb (Proofterm.PAxm (vf, vg, vh) % ve %% vc %% va) = false
  | check_comb (Proofterm.PClass (vf, vg) % ve %% vc %% va) = false
  | check_comb (Proofterm.Oracle (vf, vg, vh) % ve %% vc %% va) = false
  | check_comb (Proofterm.PThm vf % ve %% vc %% va) = false
  | check_comb (vd %% ve %% vc %% va) = false
  | check_comb (Proofterm.Hyp vd %% vc %% va) = false
  | check_comb (Proofterm.PAxm (vd, ve, vf) %% vc %% va) = false
  | check_comb (Proofterm.PClass (vd, ve) %% vc %% va) = false
  | check_comb (Proofterm.Oracle (vd, ve, vf) %% vc %% va) = false
  | check_comb (Proofterm.PThm vd %% vc %% va) = false
  | check_comb (Proofterm.Hyp vb %% va) = false
  | check_comb (Proofterm.PAxm (vb, vc, vd) %% va) = false
  | check_comb (Proofterm.PClass (vb, vc) %% va) = false
  | check_comb (Proofterm.Oracle (vb, vc, vd) %% va) = false
  | check_comb (Proofterm.PThm vb %% va) = false
  | check_comb (Proofterm.Hyp v) = false
  | check_comb (Proofterm.PAxm (v, va, vb)) = false
  | check_comb (Proofterm.PClass (v, va)) = false
  | check_comb (Proofterm.Oracle (v, va, vb)) = false
  | check_comb (Proofterm.PThm v) = false;

fun insert_tpair x xs = (if list_ex (eq_tpair x) xs then xs else x :: xs);

fun union_tpairs ts us = (if null ts then us else foldr insert_tpair us ts);

fun dest_eq_any (Const (c, uu) $ t $ u) =
  (if ((c : string) = "Pure.eq") then SOME (t, u) else NONE)
  | dest_eq_any (Const (v, va)) = NONE
  | dest_eq_any (Free (v, va)) = NONE
  | dest_eq_any (Var (v, va)) = NONE
  | dest_eq_any (Bound v) = NONE
  | dest_eq_any (Abs (v, va, vb)) = NONE
  | dest_eq_any (Const (vb, vc) $ va) = NONE
  | dest_eq_any (Free (vb, vc) $ va) = NONE
  | dest_eq_any (Var (vb, vc) $ va) = NONE
  | dest_eq_any (Bound vb $ va) = NONE
  | dest_eq_any (Abs (vb, vc, vd) $ va) = NONE
  | dest_eq_any (Free (vd, ve) $ vc $ va) = NONE
  | dest_eq_any (Var (vd, ve) $ vc $ va) = NONE
  | dest_eq_any (Bound vd $ vc $ va) = NONE
  | dest_eq_any (Abs (vd, ve, vf) $ vc $ va) = NONE
  | dest_eq_any (vd $ ve $ vc $ va) = NONE;

fun equal_elim th1 th2 =
  (case dest_eq_any (th_prop th1)
    of NONE =>
      raiseW (THM ("equal_elim: major premise", (0 : IntInf.int), Orule_State))
    | SOME (a, b) =>
      (if aconv_term (th_prop th2) a
        then returnW
               (mk_rep (max ord_integer (th_maxidx th1) (th_maxidx th2))
                 (union_tpairs (th_tpairs th1) (th_tpairs th2)) b)
        else raiseW
               (THM ("equal_elim: not equal", (0 : IntInf.int), Orule_State))));

fun equal_intr th1 th2 =
  (case (dest_imp (th_prop th1), dest_imp (th_prop th2))
    of (NONE, _) =>
      raiseW (THM ("equal_intr: premises", (0 : IntInf.int), Orule_State))
    | (SOME (_, _), NONE) =>
      raiseW (THM ("equal_intr: premises", (0 : IntInf.int), Orule_State))
    | (SOME (a, ba), SOME (b, aa)) =>
      (if aconv_term a aa andalso aconv_term ba b
        then liftMT
               (bindM (mk_equals (a, ba))
                 (fn p =>
                   return
                     (mk_rep (max ord_integer (th_maxidx th1) (th_maxidx th2))
                       (union_tpairs (th_tpairs th1) (th_tpairs th2)) p)))
        else raiseW
               (THM ("equal_intr: not equal", (0 : IntInf.int), Orule_State))));

fun transitive th1 th2 =
  (case (th_prop th1, (dest_eq (th_prop th1), dest_eq_any (th_prop th2)))
    of (Const (_, _), _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Free (_, _), _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Var (_, _), _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Bound _, _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Abs (_, _, _), _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Const (_, _) $ _, _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Free (_, _) $ _, _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Var (_, _) $ _, _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Bound _ $ _, _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (Abs (_, _, _) $ _, _) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (_ $ _ $ _, (NONE, _)) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (_ $ _ $ _, (SOME (_, (_, _)), NONE)) =>
      raiseW (THM ("transitive: premises", (0 : IntInf.int), Orule_State))
    | (eq $ _ $ _, (SOME (_, (t1, u)), SOME (ua, t2))) =>
      (if not (aconv_term u ua)
        then raiseW
               (THM ("transitive: middle term", (0 : IntInf.int), Orule_State))
        else returnW
               (mk_rep (max ord_integer (th_maxidx th1) (th_maxidx th2))
                 (union_tpairs (th_tpairs th1) (th_tpairs th2))
                 (eq $ t1 $ t2))));

fun strip_all_body t =
  (case dest_all t of NONE => t | SOME (_, (_, a)) => strip_all_body a);

fun count_prems t =
  (case dest_imp t of NONE => (0 : IntInf.int)
    | SOME (_, b) => IntInf.+ ((1 : IntInf.int), count_prems b));

fun bres_nlift bi eres_flg =
  IntInf.+ (count_prems
              (strip_all_body
                bi), (if eres_flg then (~1 : IntInf.int)
                       else (0 : IntInf.int)));

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

fun remove_types_env env =
  Envir.Envir {maxidx = (Envir.maxidx_of env),
    tenv = ((fn f => Vartab.map (K f)) (fn (t, ta) => (t, remove_types ta))
             (Envir.term_env env)),
    tyenv = (Envir.type_env env)};

fun tvar_conflict tye v =
  (case Vartab.lookup tye (fst v) of NONE => false
    | SOME (s, _) => not (equal_lista equal_literal (snd v) s));

fun dummy_tfree s = TFree ("'" ^ "dummy", s);

fun typ_tvars (Type (a, ts)) = maps typ_tvars ts
  | typ_tvars (TFree (a, s)) = []
  | typ_tvars (TVar (xi, s)) = [(xi, s)];

fun conflicting_tvars tye ts =
  map (fn v => (v, dummy_tfree (snd v)))
    (remdups
      (equal_prod (equal_prod equal_literal equal_integer)
        (equal_list equal_literal))
      (filter (tvar_conflict tye) (maps typ_tvars ts)));

fun inst_typ iT (Type (a, ts)) = Type (a, map (inst_typ iT) ts)
  | inst_typ iT (TFree (a, s)) = TFree (a, s)
  | inst_typ iT (TVar (xi, s)) =
    (case map_of
            (equal_prod (equal_prod equal_literal equal_integer)
              (equal_list equal_literal))
            iT (xi, s)
      of NONE => TVar (xi, s) | SOME t => t);

fun del_conflicting_tvars tye t = inst_typ (conflicting_tvars tye [t]) t;

fun norm_type_same tye ta t =
  list_all (fn v => is_none (Vartab.lookup tye (fst v))) (typ_tvars ta) andalso
    ((t : typ) = ta);

fun norm_types_P tye ts =
  handleW
    (liftMP
      (if Vartab.is_empty tye then return ts else mapM (norm_type_aux tye) ts))
    (fn e =>
      (case e of Unif _ => raiseW e | Pattern => raiseW e | Match => raiseW e
        | TUnify => raiseW e | Type_Match => raiseW e
        | Class_Error _ => raiseW e
        | Type_Error (s, _, _) =>
          bindW (emit s)
            (fn _ =>
              let
                val tsa = map (del_conflicting_tvars tye) ts;
              in
                bindW (liftMP
                        (if Vartab.is_empty tye then return tsa
                          else mapM (norm_type_aux tye) tsa))
                  (fn tsb =>
                    returnW
                      (if Vartab.is_empty tye orelse
                            list_all2 (norm_type_same tye) tsa tsb
                        then ts else tsb))
              end)
        | Term_Error (_, _) => raiseW e | Failure _ => raiseW e
        | Subscript => raiseW e | Unequal_Lengths => raiseW e
        | Dup _ => raiseW e));

fun norm_type_P tye t =
  handleW (liftMP (norm_type tye t))
    (fn e =>
      (case e of Unif _ => raiseW e | Pattern => raiseW e | Match => raiseW e
        | TUnify => raiseW e | Type_Match => raiseW e
        | Class_Error _ => raiseW e
        | Type_Error (s, _, _) =>
          bindW (emit s)
            (fn _ =>
              let
                val ta = del_conflicting_tvars tye t;
              in
                bindW (liftMP (norm_type tye ta))
                  (fn tb =>
                    returnW (if norm_type_same tye ta tb then t else tb))
              end)
        | Term_Error (_, _) => raiseW e | Failure _ => raiseW e
        | Subscript => raiseW e | Unequal_Lengths => raiseW e
        | Dup _ => raiseW e));

fun remdups_vars [] = []
  | remdups_vars (v :: vs) =
    (if list_ex (var_eq v) vs then remdups_vars vs else v :: remdups_vars vs);

fun filter_outM p [] = return []
  | filter_outM p (x :: xs) =
    bindM (p x)
      (fn b =>
        bindM (filter_outM p xs) (fn ys => return (if b then ys else x :: ys)));

fun term_types (Const (c, t)) = [t]
  | term_types (Free (x, t)) = [t]
  | term_types (Var (xi, t)) = [t]
  | term_types (Bound i) = []
  | term_types (Abs (x, ta, t)) = ta :: term_types t
  | term_types (t $ u) = term_types t @ term_types u;

fun can_lookup env v =
  (case lookup env (fst v) (snd v) of NONE => NONE | SOME (Ok _) => return true
    | SOME (Err _) => return false);

fun term_vars (Var (xi, t)) = [(xi, t)]
  | term_vars (Abs (x, ta, t)) = term_vars t
  | term_vars (t $ u) = term_vars t @ term_vars u
  | term_vars (Const (v, va)) = []
  | term_vars (Free (v, va)) = []
  | term_vars (Bound v) = [];

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

fun del_conflicting_vars env t =
  bindM (filter_outM (can_lookup env) (remdups_vars (term_vars t)))
    (fn vs =>
      return
        (inst_term (conflicting_tvars (Envir.type_env env) (term_types t))
          (map (fn v => (v, Free ("dummy", snd v))) vs) t));

fun norm_same env ta t =
  not (could_beta_contract ta) andalso
    (list_all (fn v => is_none (Vartab.lookup (Envir.term_env env) (fst v)))
       (term_vars ta) andalso
      ((t : term) = ta));

fun norm_term_P env t =
  handleW (liftMP (norm_term env t))
    (fn e =>
      (case e of Unif _ => raiseW e | Pattern => raiseW e | Match => raiseW e
        | TUnify => raiseW e | Type_Match => raiseW e
        | Class_Error _ => raiseW e
        | Type_Error (s, _, _) =>
          bindW (emit s)
            (fn _ =>
              bindW (liftMP (del_conflicting_vars env t))
                (fn ta =>
                  bindW (liftMP (norm_term env ta))
                    (fn tb => returnW (if norm_same env ta tb then t else tb))))
        | Term_Error (_, _) => raiseW e | Failure _ => raiseW e
        | Subscript => raiseW e | Unequal_Lengths => raiseW e
        | Dup _ => raiseW e));

fun map_optionP f x =
  (case x of NONE => returnW NONE
    | SOME y => bindW (f y) (fn z => returnW (SOME z)));

fun norm_proof env (Proofterm.Abst (a, t, p)) =
  bindW (map_optionP (norm_type_P (Envir.type_env env)) t)
    (fn ta =>
      bindW (norm_proof env p) (fn pa => returnW (Proofterm.Abst (a, ta, pa))))
  | norm_proof env (Proofterm.AbsP (a, t, p)) =
    bindW (map_optionP (norm_term_P env) t)
      (fn ta =>
        bindW (norm_proof env p)
          (fn pa => returnW (Proofterm.AbsP (a, ta, pa))))
  | norm_proof env (p % t) =
    bindW (norm_proof env p)
      (fn pa =>
        bindW (map_optionP (norm_term_P env) t) (fn ta => returnW (pa % ta)))
  | norm_proof env (p %% q) =
    bindW (norm_proof env p)
      (fn pa => bindW (norm_proof env q) (fn qa => returnW (pa %% qa)))
  | norm_proof env (Proofterm.PAxm (aa, a, ts)) =
    bindW (map_optionP (norm_types_P (Envir.type_env env)) ts)
      (fn tsa => returnW (Proofterm.PAxm (aa, a, tsa)))
  | norm_proof env (Proofterm.PClass (t, c)) =
    bindW (norm_type_P (Envir.type_env env) t)
      (fn ta => returnW (Proofterm.PClass (ta, c)))
  | norm_proof env (Proofterm.Oracle (aa, a, ts)) =
    bindW (map_optionP (norm_types_P (Envir.type_env env)) ts)
      (fn tsa => returnW (Proofterm.Oracle (aa, a, tsa)))
  | norm_proof env (Proofterm.PThm (h, b)) =
    bindW (map_optionP (norm_types_P (Envir.type_env env))
            ((fn h : Proofterm.thm_header => #types h) h))
      (fn ts =>
        returnW
          (Proofterm.PThm
            ((fn {serial, command_pos, theory_name, thm_name, prop, ...} : Proofterm.thm_header =>
      fn types => Proofterm.thm_header serial command_pos theory_name thm_name prop types)
               h ts,
              b)))
  | norm_proof env Proofterm.MinProof = returnW Proofterm.MinProof
  | norm_proof env (Proofterm.PBound v) = returnW (Proofterm.PBound v)
  | norm_proof env (Proofterm.Hyp v) = returnW (Proofterm.Hyp v);

fun norm_proof_remove_types env p = norm_proof (remove_types_env env) p;

fun proof_combt p ts = foldl (fn pa => fn t => pa % SOME t) p ts;

fun proof_combP p qs = foldl (fn a => fn b => a %% b) p qs;

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

fun mk_asm_prf c i m = all_prf i m c;

fun mk_AbsP xs p = foldr (fn _ => (fn a => Proofterm.AbsP ("H", NONE, a))) xs p;

fun bicompose_core env flatten bs asa a oldAs n m sprf p =
  bindW (liftMP (mapM (norm_term env) (bs @ asa)))
    (fn ns =>
      let
        val lb = integer_of_nat (size_list bs);
        val la = integer_of_nat (size_list asa);
        val q =
          proof_combP sprf
            (map Proofterm.PBound
              (downto (IntInf.- (IntInf.+ (lb, la), (1 : IntInf.int))) la));
      in
        bindW (if IntInf.< ((0 : IntInf.int), n)
                then (case a of NONE => raiseW (Failure "Option")
                       | SOME c => returnW [mk_asm_prf c n m])
                else returnW [])
          (fn asm =>
            bindW (liftMP
                    (zip_eq oldAs
                      (downto (IntInf.- (la, (1 : IntInf.int)))
                        (0 : IntInf.int))))
              (fn ks =>
                returnW
                  (mk_AbsP ns
                    (q %% proof_combP p
                            (asm @
                              map (if flatten
                                    then flatten_params_proof (0 : IntInf.int)
   (0 : IntInf.int) n
                                    else (fn x => Proofterm.PBound (snd x)))
                                ks)))))
      end);

fun bicompose_proof env smax flatten bs asa a oldAs n m rprf sprf =
  (if env_is_empty env
    then bicompose_core env flatten bs asa a oldAs n m sprf rprf
    else (if above env smax
           then bindW (norm_proof_remove_types env rprf)
                  (bicompose_core env flatten bs asa a oldAs n m sprf)
           else bindW (bicompose_core env flatten bs asa a oldAs n m sprf rprf)
                  (norm_proof_remove_types env)));

fun bres_proof state bs nlift flatten x rprf sprf =
  let
    val BRes (env, _, _, a, NewAs (asa, oldAs, ren, n)) = x;
  in
    bicompose_proof env (th_maxidx state) flatten bs asa a oldAs n
      (IntInf.+ (nlift, (1 : IntInf.int)))
      (case ren of NONE => rprf
        | SOME r => map_proof_terms (ren_term r) id rprf)
      sprf
  end;

fun map_zproof typ term (ZConstp (a, insts)) =
  bindM (map_insts typ term insts) (fn instsa => return (ZConstp (a, instsa)))
  | map_zproof typ term (ZAbst (a, t, p)) =
    bindM (map_zproof typ term p) (fn pa => return (ZAbst (a, typ t, pa)))
  | map_zproof typ term (ZAbsp (a, t, p)) =
    bindM (term t)
      (fn ta =>
        bindM (map_zproof typ term p) (fn pa => return (ZAbsp (a, ta, pa))))
  | map_zproof typ term (ZAppt (p, t)) =
    bindM (map_zproof typ term p)
      (fn pa => bindM (term t) (fn ta => return (ZAppt (pa, ta))))
  | map_zproof typ term (ZAppp (p, q)) =
    bindM (map_zproof typ term p)
      (fn pa =>
        bindM (map_zproof typ term q) (fn qa => return (ZAppp (pa, qa))))
  | map_zproof typ term ZNop = return ZNop
  | map_zproof typ term (ZBoundp v) = return (ZBoundp v)
  | map_zproof typ term (ZHyp v) = return (ZHyp v)
  | map_zproof typ term (OFCLASSp (v, va)) = return (OFCLASSp (v, va));

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

fun zasm_count m a =
  integer_of_nat (size_list (fst (snd (assum_problems m a))));

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
      bindM (liftMZ (type_lookup tye v s))
        (fn a =>
          (case a of NONE => return t
            | SOME u => znorm_type_aux tye (ztyp_of u)))
    | ZFun (u, v) =>
      bindM (znorm_type_aux tye u)
        (fn ua =>
          bindM (znorm_type_aux tye v) (fn va => return (ZFun (ua, va))))
    | ZProp => return t | ZType0 _ => return t
    | ZType1 (a, u) =>
      bindM (znorm_type_aux tye u) (fn ua => return (ZType1 (a, ua)))
    | ZType (a, us) =>
      bindM (mapM (znorm_type_aux tye) us) (fn usa => return (ZType (a, usa))));

fun znorm_type tye t =
  (if Vartab.is_empty tye then return t else znorm_type_aux tye t);

fun znorm_term_aux x =
  (case snd x
    of ZVar (xi, t) =>
      bindM (zlookup (fst (fst x)) (snd (fst x)) xi t)
        (fn a =>
          (case a
            of NONE =>
              bindM (znorm_type (Envir.type_env (snd (fst x))) t)
                (fn ta => return (ZVar (xi, ta)))
            | SOME u => znorm_term_aux (fst x, u)))
    | ZBound integer => return (ZBound integer)
    | ZConst0 literal => return (ZConst0 literal)
    | ZConst1 (a, t) =>
      bindM (znorm_type (Envir.type_env (snd (fst x))) t)
        (fn ta => return (ZConst1 (a, ta)))
    | ZConst (a, ts) =>
      bindM (mapM (znorm_type (Envir.type_env (snd (fst x)))) ts)
        (fn tsa => return (ZConst (a, tsa)))
    | ZAbs (a, t, b) =>
      bindM (znorm_type (Envir.type_env (snd (fst x))) t)
        (fn ta =>
          bindM (znorm_term_aux (fst x, b))
            (fn ba => return (ZAbs (a, ta, ba))))
    | ZApp (g, u) =>
      (case g
        of ZVar (_, _) =>
          bindM (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZBound _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))))
        | ZBound _ =>
          bindM (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZBound _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))))
        | ZConst0 _ =>
          bindM (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZBound _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))))
        | ZConst1 (_, _) =>
          bindM (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZBound _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))))
        | ZConst (_, _) =>
          bindM (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZBound _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))))
        | ZAbs (_, _, body) => znorm_term_aux (fst x, subst_term_bound u body)
        | ZApp (_, _) =>
          bindM (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZBound _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))))
        | OFCLASS (_, _) =>
          bindM (znorm_term_aux (fst x, g))
            (fn nf =>
              (case nf
                of ZVar (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZBound _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst0 _ =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst1 (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZConst (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | ZAbs (_, _, body) =>
                  znorm_term_aux (fst x, subst_term_bound u body)
                | ZApp (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu)))
                | OFCLASS (_, _) =>
                  bindM (znorm_term_aux (fst x, u))
                    (fn nu => return (ZApp (nf, nu))))))
    | OFCLASS (t, c) =>
      bindM (znorm_type (Envir.type_env (snd (fst x))) t)
        (fn ta => return (OFCLASS (ta, c))));

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

fun zren_proof r m p = map_zproof id (fn t => return (zren_term r m t)) p;

fun assume_rule raw_ct =
  let
    val ct = adjust_maxidx_cterm (~1 : IntInf.int) raw_ct;
  in
    (if not (((ct_T ct) : typ) = propT)
      then raiseW (THM ("assume: prop", (0 : IntInf.int), No_Thm))
      else (if not (((ct_maxidx ct) : IntInf.int) = (~1 : IntInf.int))
             then raiseW (THM ("assume: variables", ct_maxidx ct, No_Thm))
             else returnW (mk_rep (~1 : IntInf.int) [] (ct_t ct))))
  end;

fun combination_data th1 th2 =
  (case (dest_eq_fun (th_prop th1), dest_eq_fun (th_prop th2))
    of (NONE, _) =>
      raiseW (THM ("combination: premises", (0 : IntInf.int), Orule_State))
    | (SOME (_, (_, _)), NONE) =>
      raiseW (THM ("combination: premises", (0 : IntInf.int), Orule_State))
    | (SOME (fT, (f, g)), SOME (tT, (t, u))) =>
      (case fT
        of Type (_, []) =>
          raiseW
            (THM ("combination: not function type", (0 : IntInf.int),
                   Orule_State))
        | Type (_, [_]) =>
          raiseW
            (THM ("combination: not function type", (0 : IntInf.int),
                   Orule_State))
        | Type (n, [t1, ua]) =>
          (if ((n : string) = "fun")
            then (if ((t1 : typ) = tT) then returnW (fT, (ua, (f, (g, (t, u)))))
                   else raiseW
                          (THM ("combination: types", (0 : IntInf.int),
                                 Orule_State)))
            else raiseW
                   (THM ("combination: not function type", (0 : IntInf.int),
                          Orule_State)))
        | Type (_, _ :: _ :: _ :: _) =>
          raiseW
            (THM ("combination: not function type", (0 : IntInf.int),
                   Orule_State))
        | TFree (_, _) =>
          raiseW
            (THM ("combination: not function type", (0 : IntInf.int),
                   Orule_State))
        | TVar (_, _) =>
          raiseW
            (THM ("combination: not function type", (0 : IntInf.int),
                   Orule_State))));

fun combination th1 th2 =
  bindW (combination_data th1 th2)
    (fn (_, (_, (f, (g, (t, u))))) =>
      liftMT
        (bindM (mk_equals (f $ t, g $ u))
          (fn p =>
            return
              (mk_rep (max ord_integer (th_maxidx th1) (th_maxidx th2))
                (union_tpairs (th_tpairs th1) (th_tpairs th2)) p))));

fun dest_all_app (Const (c, Type (n, [Type (m, [qary, uu]), uv])) $ a) =
  (if ((c : string) = "Pure.all") andalso
        (((n : string) = "fun") andalso ((m : string) = "fun"))
    then SOME (qary, a) else NONE)
  | dest_all_app (Const (v, va)) = NONE
  | dest_all_app (Free (v, va)) = NONE
  | dest_all_app (Var (v, va)) = NONE
  | dest_all_app (Bound v) = NONE
  | dest_all_app (Abs (v, va, vb)) = NONE
  | dest_all_app (Const (vb, Type (vd, [])) $ va) = NONE
  | dest_all_app (Const (vb, Type (vd, Type (vh, []) :: vg)) $ va) = NONE
  | dest_all_app (Const (vb, Type (vd, Type (vh, [vj]) :: vg)) $ va) = NONE
  | dest_all_app
    (Const (vb, Type (vd, Type (vh, vj :: vl :: vn :: vo) :: vg)) $ va) = NONE
  | dest_all_app (Const (vb, Type (vd, TFree (vh, vi) :: vg)) $ va) = NONE
  | dest_all_app (Const (vb, Type (vd, TVar (vh, vi) :: vg)) $ va) = NONE
  | dest_all_app (Const (vb, Type (vd, [vf])) $ va) = NONE
  | dest_all_app (Const (vb, Type (vd, vf :: vh :: vj :: vk)) $ va) = NONE
  | dest_all_app (Const (vb, TFree (vd, ve)) $ va) = NONE
  | dest_all_app (Const (vb, TVar (vd, ve)) $ va) = NONE
  | dest_all_app (Free (vb, vc) $ va) = NONE
  | dest_all_app (Var (vb, vc) $ va) = NONE
  | dest_all_app (Bound vb $ va) = NONE
  | dest_all_app (Abs (vb, vc, vd) $ va) = NONE
  | dest_all_app (vb $ vc $ va) = NONE;

fun forall_elim ct th =
  (case dest_all_app (th_prop th)
    of NONE =>
      raiseW (THM ("forall_elim: not quantified", (0 : IntInf.int), State))
    | SOME (qary, a) =>
      (if not (((ct_T ct) : typ) = qary)
        then raiseW
               (THM ("forall_elim: type mismatch", (0 : IntInf.int), State))
        else returnW
               (mk_rep (max ord_integer (ct_maxidx ct) (th_maxidx th))
                 (th_tpairs th) (betapply a (ct_t ct)))));

fun abstract_over_aux v lev (Abs (a, ta, t)) =
  (if aconv_term v (Abs (a, ta, t)) then Bound lev
    else Abs (a, ta, abstract_over_aux v (IntInf.+ (lev, (1 : IntInf.int))) t))
  | abstract_over_aux v lev (t $ u) =
    (if aconv_term v (t $ u) then Bound lev
      else abstract_over_aux v lev t $ abstract_over_aux v lev u)
  | abstract_over_aux v lev (Const (va, vb)) =
    (if aconv_term v (Const (va, vb)) then Bound lev else Const (va, vb))
  | abstract_over_aux v lev (Free (va, vb)) =
    (if aconv_term v (Free (va, vb)) then Bound lev else Free (va, vb))
  | abstract_over_aux v lev (Var (va, vb)) =
    (if aconv_term v (Var (va, vb)) then Bound lev else Var (va, vb))
  | abstract_over_aux v lev (Bound va) =
    (if aconv_term v (Bound va) then Bound lev else Bound va);

fun abstract_over v body = abstract_over_aux v (0 : IntInf.int) body;

fun forall_intr hyps ct th =
  let
    val x = ct_t ct;
    val t = ct_T ct;
    val check =
      (fn a => fn ts =>
        (if occs_hyps x ts (th_tpairs th)
          then raiseW
                 (THM ("forall_intr: variable " ^ quote_lit a ^
                         " free in assumptions",
                        (0 : IntInf.int), State))
          else returnW
                 (mk_rep (max ord_integer (ct_maxidx ct) (th_maxidx th))
                   (th_tpairs th)
                   (all_const t $ Abs (a, t, abstract_over x (th_prop th))))));
  in
    (case x
      of Const (_, _) =>
        raiseW (THM ("forall_intr: not a variable", (0 : IntInf.int), State))
      | Free (a, _) => check a hyps | Var ((a, _), _) => check a []
      | Bound _ =>
        raiseW (THM ("forall_intr: not a variable", (0 : IntInf.int), State))
      | Abs (_, _, _) =>
        raiseW (THM ("forall_intr: not a variable", (0 : IntInf.int), State))
      | _ $ _ =>
        raiseW (THM ("forall_intr: not a variable", (0 : IntInf.int), State)))
  end;

fun atyps (Type (uu, ts)) = maps atyps ts
  | atyps (TFree (v, va)) = [TFree (v, va)]
  | atyps (TVar (v, va)) = [TVar (v, va)];

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

fun visible_tvars ts =
  dedup (equal_prod (equal_prod equal_literal equal_integer)
          (equal_list equal_literal))
    (maps (fn t => maps typ_tvars (term_types t)) ts);

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

fun zlookup_var [] v = NONE
  | zlookup_var ((w, x) :: xs) v =
    (if zvar_eq w v then SOME x else zlookup_var xs v);

fun zdedup_vars [] = []
  | zdedup_vars (v :: vs) =
    v :: zdedup_vars (filter (fn w => not (zvar_eq w v)) vs);

fun znorm_proof ta env visible prf =
  (if env_is_empty env orelse null visible then liftOZ (beta_norm_prooft prf)
    else bindM (if Vartab.is_empty (Envir.type_env env) then return NONE
                 else bindM (mapM (fn (v, s) =>
                                    znorm_type (Envir.type_env env)
                                      (ZTVar (v, s)))
                              (visible_tvars visible))
                        (fn us =>
                          return (SOME (zip (visible_tvars visible) us))))
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
               bindM (mapM (fn (a, t) => znorm_term ta env (ZVar (a, t))) vs)
                 (fn us =>
                   let
                     val inst_term =
                       zsubst_term inst_typ (zlookup_var (zip vs us));
                     val ok_var =
                       (fn (x, t) =>
                         not (is_none
                               (zlookup_var (zip vs us) (x, inst_typ t))) orelse
                           is_none (Vartab.lookup (Envir.term_env env) x));
                   in
                     bindM (map_zproof inst_typ
                             (fn t =>
                               (if zvars_all ok_var t
                                 then liftOZ (beta_norm_term (inst_term t))
                                 else raisea
(ZExn (Term_Error
        ("norm_proof: variable bound by the environment is not visible", [])))))
                             prf)
                       (fn p => liftOZ (beta_norm_prooft p))
                   end)
             end));

fun zmk_asm_prf c i m = zall_prf i m c;

fun zbicompose_core ta env flatten bs asa a oldAs n m visible p q =
  let
    val normt = (fn t => bindM (zterm_of ta t) (znorm_term ta env));
  in
    bindM (mapM normt (bs @ asa))
      (fn ns =>
        let
          val lb = integer_of_nat (size_list bs);
          val la = integer_of_nat (size_list asa);
          val qa =
            zAppps q
              (map ZBoundp
                (downto (IntInf.- (IntInf.+ (lb, la), (1 : IntInf.int))) la));
        in
          bindM (if IntInf.< ((0 : IntInf.int), n)
                  then (case a of NONE => raisea ZOption
                         | SOME c =>
                           bindM (normt c)
                             (fn ca =>
                               return [zmk_asm_prf ca n (zasm_count m c)]))
                  else return [])
            (fn asm =>
              bindM (mapM (zterm_of ta) oldAs)
                (fn os =>
                  bindM (liftMZ
                          (zip_eq os
                            (downto (IntInf.- (la, (1 : IntInf.int)))
                              (0 : IntInf.int))))
                    (fn ks =>
                      bindM (if flatten
                              then mapM (fn x =>
  znorm_proof ta env visible
    (zflatten_params_proof (0 : IntInf.int) (0 : IntInf.int) n x))
                                     ks
                              else return (map (fn x => ZBoundp (snd x)) ks))
                        (fn fs =>
                          return
                            (zAbsps ns (ZAppp (qa, zAppps p (asm @ fs))))))))
        end)
  end;

fun zbicompose_proof ta env smax flatten bs asa a oldAs n m visible rprf sprf =
  (if env_is_empty env
    then zbicompose_core ta env flatten bs asa a oldAs n m visible rprf sprf
    else bindM (znorm_proof ta env visible rprf)
           (fn rprfa =>
             bindM (if above env smax then return sprf
                     else znorm_proof ta env visible sprf)
               (zbicompose_core ta env flatten bs asa a oldAs n m visible
                 rprfa)));

fun full_prop_of tpairs prop =
  bindM (mapM mk_equals tpairs) (fn eqs => return (list_implies eqs prop));

fun bres_zproof ta state bs nlift flatten orule x rprf sprf =
  let
    val BRes (env, _, _, a, NewAs (asa, oldAs, ren, n)) = x;
  in
    bindM (case ren of NONE => return rprf
            | SOME r => zren_proof r (th_maxidx state) rprf)
      (fn rprfa =>
        bindM (liftMZ
                (mapM (fn th => full_prop_of (th_tpairs th) (th_prop th))
                  [state, orule]))
          (fn visible =>
            zbicompose_proof ta env (th_maxidx state) flatten bs asa a oldAs n
              (IntInf.+ (nlift, (1 : IntInf.int))) visible rprfa sprf))
  end;

fun zlift_prems ta inc k prf ts bs i j (Const (c, u) $ a $ b) =
  (if ((c : string) = "Pure.imp")
    then bindM (zterm_of ta a)
           (fn aa =>
             bindM (zlift_prems ta inc k prf ts (true :: bs)
                     (IntInf.+ (i, (1 : IntInf.int))) j b)
               (fn p => return (ZAbsp ("H", aa, p))))
    else bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
           (fn p =>
             return
               (zAppps p
                 (map (fn ka =>
                        snd (snd (foldr zmk_app bs
                                   (IntInf.- (i, (1 : IntInf.int)),
                                     (IntInf.- (j, (1 : IntInf.int)),
                                       ZBoundp ka)))))
                   (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i)))))
  | zlift_prems taa inc k prf ts bs i j (Const (c, u) $ Abs (a, ta, t)) =
    (if ((c : string) = "Pure.all")
      then bindM (zlift_prems taa inc k prf (ztyp_of ta :: ts) (false :: bs) i
                   (IntInf.+ (j, (1 : IntInf.int))) t)
             (fn p => return (ZAbst (a, ztyp_of ta, p)))
      else bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
             (fn p =>
               return
                 (zAppps p
                   (map (fn ka =>
                          snd (snd (foldr zmk_app bs
                                     (IntInf.- (i, (1 : IntInf.int)),
                                       (IntInf.- (j, (1 : IntInf.int)),
 ZBoundp ka)))))
                     (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int)))
                       i)))))
  | zlift_prems ta inc k prf ts bs i j (Const (v, va)) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Free (v, va)) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Var (v, va)) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Bound v) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Abs (v, va, vb)) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ Const (v, vd)) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ Free (v, vd)) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ Var (v, vd)) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ Bound v) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Const (vb, vc) $ (v $ vd)) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Free (vb, vc) $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Var (vb, vc) $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Bound vb $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Abs (vb, vc, vd) $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Free (vd, ve) $ vc $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Var (vd, ve) $ vc $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Bound vd $ vc $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (Abs (vd, ve, vf) $ vc $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))))
  | zlift_prems ta inc k prf ts bs i j (vd $ ve $ vc $ va) =
    bindM (zlift_prf inc (rev ts) (0 : IntInf.int) prf)
      (fn p =>
        return
          (zAppps p
            (map (fn ka =>
                   snd (snd (foldr zmk_app bs
                              (IntInf.- (i, (1 : IntInf.int)),
                                (IntInf.- (j, (1 : IntInf.int)), ZBoundp ka)))))
              (downto (IntInf.- (IntInf.+ (i, k), (1 : IntInf.int))) i))));

fun zlift_proof ta gprop inc prems prf =
  bindM (mapM (zterm_of ta) prems)
    (fn asa =>
      bindM (zlift_prems ta inc (integer_of_nat (size_list prems)) prf [] []
              (0 : IntInf.int) (0 : IntInf.int) gprop)
        (fn p => return (zAbsps asa p)));

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

fun equality_axiom a =
  let
    val aT = ax_aT;
    val bT = ax_bT;
    val x = ax_var "x" aT;
    val y = ax_var "y" aT;
    val z = ax_var "z" aT;
    val aa = ax_var "A" propT;
    val b = ax_var "B" propT;
    val f = ax_var "f" (Type ("fun", [aT, bT]));
    val g = ax_var "g" (Type ("fun", [aT, bT]));
  in
    (if ((a : string) = "reflexive") then ax_eq aT x x
      else (if ((a : string) = "symmetric")
             then mk_implies (ax_eq aT x y) (ax_eq aT y x)
             else (if ((a : string) = "transitive")
                    then list_implies [ax_eq aT x y, ax_eq aT y z]
                           (ax_eq aT x z)
                    else (if ((a : string) = "equal_intr")
                           then list_implies [mk_implies aa b, mk_implies b aa]
                                  (ax_eq propT aa b)
                           else (if ((a : string) = "equal_elim")
                                  then list_implies [ax_eq propT aa b, aa] b
                                  else (if ((a : string) = "abstract_rule")
 then mk_implies
        (all_const aT $
          Abs ("x", aT,
            ax_eq bT (f $ Bound (0 : IntInf.int)) (g $ Bound (0 : IntInf.int))))
        (ax_eq (Type ("fun", [aT, bT]))
          (Abs ("x", aT, f $ Bound (0 : IntInf.int)))
          (Abs ("x", aT, g $ Bound (0 : IntInf.int))))
 else list_implies [ax_eq (Type ("fun", [aT, bT])) f g, ax_eq aT x y]
        (ax_eq bT (f $ x) (g $ y))))))))
  end;

fun equality_axm a = Proofterm.PAxm ("Pure." ^ a, equality_axiom a, NONE);

fun implies_elim thAB thA =
  (case dest_imp (th_prop thAB)
    of NONE =>
      raiseW
        (THM ("implies_elim: major premise", (0 : IntInf.int), Orule_State))
    | SOME (a, b) =>
      (if aconv_term a (th_prop thA)
        then returnW
               (mk_rep (max ord_integer (th_maxidx thA) (th_maxidx thAB))
                 (union_tpairs (th_tpairs thA) (th_tpairs thAB)) b)
        else raiseW
               (THM ("implies_elim: major premise", (0 : IntInf.int),
                      Orule_State))));

fun implies_intr ct th =
  (if not (((ct_T ct) : typ) = propT)
    then raiseW
           (THM ("implies_intr: assumptions must have type prop",
                  (0 : IntInf.int), State))
    else returnW
           (mk_rep (max ord_integer (ct_maxidx ct) (th_maxidx th))
             (th_tpairs th) (mk_implies (ct_t ct) (th_prop th))));

fun renamed_prop p th =
  (if aconv_term (th_prop th) p
    then returnW (mk_rep (th_maxidx th) (th_tpairs th) p)
    else raiseW
           (UExn (PExn (Term_Error
                         ("renamed_prop: props disagree", [th_prop th, p])))));

fun zsubst_tvar_names f (ZTVar ((a, i), s)) =
  (case f a of NONE => ZTVar ((a, i), s) | SOME t => t)
  | zsubst_tvar_names f (ZFun (t, u)) =
    ZFun (zsubst_tvar_names f t, zsubst_tvar_names f u)
  | zsubst_tvar_names f (ZType1 (a, t)) = ZType1 (a, zsubst_tvar_names f t)
  | zsubst_tvar_names f (ZType (a, ts)) =
    ZType (a, map (zsubst_tvar_names f) ts)
  | zsubst_tvar_names f ZProp = ZProp
  | zsubst_tvar_names f (ZType0 v) = ZType0 v;

fun make_const_proof f g c =
  let
    val (a, insts) = c;
  in
    bindM (map_insts (zsubst_tvar_names f)
            (fn t =>
              return
                (case t
                  of ZVar ((x, _), _) => (case g x of NONE => t | SOME u => u)
                  | ZBound _ => t | ZConst0 _ => t | ZConst1 (_, _) => t
                  | ZConst (_, _) => t | ZAbs (_, _, _) => t | ZApp (_, _) => t
                  | OFCLASS (_, _) => t))
            insts)
      (fn instsa => return (ZConstp (a, instsa)))
  end;

fun zequality_axiom a =
  let
    val aT = zax_aT;
    val bT = zax_bT;
    val fT = ZFun (aT, bT);
    val x = zax_var "x" aT;
    val y = zax_var "y" aT;
    val z = zax_var "z" aT;
    val aa = zax_var "A" ZProp;
    val b = zax_var "B" ZProp;
    val f = zax_var "f" fT;
    val g = zax_var "g" fT;
    val va = ((tvar_a, (~1 : IntInf.int)), []);
    val vb = ((tvar_b, (~1 : IntInf.int)), []);
    val vx = (("x", (~1 : IntInf.int)), aT);
    val vy = (("y", (~1 : IntInf.int)), aT);
    val vz = (("z", (~1 : IntInf.int)), aT);
    val vA = (("A", (~1 : IntInf.int)), ZProp);
    val vB = (("B", (~1 : IntInf.int)), ZProp);
    val vf = (("f", (~1 : IntInf.int)), fT);
    val vg = (("g", (~1 : IntInf.int)), fT);
  in
    (if ((a : string) = "reflexive") then (zax_eq aT x x, ([va], [vx]))
      else (if ((a : string) = "symmetric")
             then (zax_imp (zax_eq aT x y) (zax_eq aT y x), ([va], [vx, vy]))
             else (if ((a : string) = "transitive")
                    then (zax_imp (zax_eq aT x y)
                            (zax_imp (zax_eq aT y z) (zax_eq aT x z)),
                           ([va], [vx, vy, vz]))
                    else (if ((a : string) = "equal_intr")
                           then (zax_imp (zax_imp aa b)
                                   (zax_imp (zax_imp b aa) (zax_eq ZProp aa b)),
                                  ([], [vA, vB]))
                           else (if ((a : string) = "equal_elim")
                                  then (zax_imp (zax_eq ZProp aa b)
  (zax_imp aa b),
 ([], [vA, vB]))
                                  else (if ((a : string) = "abstract_rule")
 then (zax_imp
         (ZApp (ZConst1 ("Pure.all", aT),
           ZAbs ("x", aT,
             zax_eq bT (ZApp (f, ZBound (0 : IntInf.int)))
               (ZApp (g, ZBound (0 : IntInf.int))))))
         (zax_eq fT (ZAbs ("x", aT, ZApp (f, ZBound (0 : IntInf.int))))
           (ZAbs ("x", aT, ZApp (g, ZBound (0 : IntInf.int))))),
        ([va, vb], [vf, vg]))
 else (zax_imp (zax_eq fT f g)
         (zax_imp (zax_eq aT x y) (zax_eq bT (ZApp (f, x)) (ZApp (g, y)))),
        ([va, vb], [vf, vg, vx, vy]))))))))
  end;

fun zequality_axm a =
  let
    val (aa, (tvs, vs)) = zequality_axiom a;
  in
    ((ZAxiom ("Pure." ^ a), aa),
      (fold (fn v => ZTVars.update (v, ZTVar (fst v, snd v))) tvs ZTVars.empty,
        fold (fn v => ZVars.update (v, ZVar (fst v, snd v))) vs ZVars.empty))
  end;

fun zaxiom_proof a tsa ts =
  make_const_proof (map_of equal_literal tsa) (map_of equal_literal ts)
    (zequality_axm a);

fun zAbsts xs prf = foldr (fn (a, b) => (fn c => ZAbst (a, b, c))) xs prf;

fun aterms (t $ u) = aterms t @ aterms u
  | aterms (Abs (uu, uv, b)) = aterms b
  | aterms (Const (v, va)) = [Const (v, va)]
  | aterms (Free (v, va)) = [Free (v, va)]
  | aterms (Var (v, va)) = [Var (v, va)]
  | aterms (Bound v) = [Bound v];

fun char_of A_ n =
  Chara (bit ((semiring_bits_semiring_bit_operations o
                semiring_bit_operations_linordered_euclidean_semiring_bit_operations)
               A_)
           n Zero_nat,
          bit ((semiring_bits_semiring_bit_operations o
                 semiring_bit_operations_linordered_euclidean_semiring_bit_operations)
                A_)
            n one_nata,
          bit ((semiring_bits_semiring_bit_operations o
                 semiring_bit_operations_linordered_euclidean_semiring_bit_operations)
                A_)
            n (nat_of_num (Bit0 One)),
          bit ((semiring_bits_semiring_bit_operations o
                 semiring_bit_operations_linordered_euclidean_semiring_bit_operations)
                A_)
            n (nat_of_num (Bit1 One)),
          bit ((semiring_bits_semiring_bit_operations o
                 semiring_bit_operations_linordered_euclidean_semiring_bit_operations)
                A_)
            n (nat_of_num (Bit0 (Bit0 One))),
          bit ((semiring_bits_semiring_bit_operations o
                 semiring_bit_operations_linordered_euclidean_semiring_bit_operations)
                A_)
            n (nat_of_num (Bit1 (Bit0 One))),
          bit ((semiring_bits_semiring_bit_operations o
                 semiring_bit_operations_linordered_euclidean_semiring_bit_operations)
                A_)
            n (nat_of_num (Bit0 (Bit1 One))),
          bit ((semiring_bits_semiring_bit_operations o
                 semiring_bit_operations_linordered_euclidean_semiring_bit_operations)
                A_)
            n (nat_of_num (Bit1 (Bit1 One))));

fun digits n =
  (if less_nat n (nat_of_num (Bit0 (Bit1 (Bit0 One))))
    then [char_of linordered_euclidean_semiring_bit_operations_nat
            (plus_nata (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))) n)]
    else digits (divide_nata n (nat_of_num (Bit0 (Bit1 (Bit0 One))))) @
           [char_of linordered_euclidean_semiring_bit_operations_nat
              (plus_nata (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
                (modulo_nata n (nat_of_num (Bit0 (Bit1 (Bit0 One))))))]);

fun lookup_vara [] v = NONE
  | lookup_vara (((xi, t), x) :: xs) v =
    (if equal_proda equal_literal equal_integer xi (fst v) andalso
          ((t : typ) = (snd v))
      then SOME x else lookup_vara xs v);

fun instT_m tab (Type (a, ts)) m = let
                                     val (tsa, b) = instTs_m tab ts m;
                                   in
                                     (Type (a, tsa), b)
                                   end
  | instT_m tab (TVar ((a, i), s)) m =
    (case map_of
            (equal_prod (equal_prod equal_literal equal_integer)
              (equal_list equal_literal))
            tab ((a, i), s)
      of NONE => (TVar ((a, i), s), max ord_integer m i)
      | SOME (t, j) => (t, max ord_integer m j))
  | instT_m tab (TFree (a, s)) m = (TFree (a, s), m)
and instTs_m tab [] m = ([], m)
  | instTs_m tab (t :: ts) m = let
                                 val (ta, m1) = instT_m tab t m;
                                 val (tsa, a) = instTs_m tab ts m1;
                               in
                                 (ta :: tsa, a)
                               end;

fun inst_m tT tt (Const (c, t)) m = let
                                      val (ta, a) = instT_m tT t m;
                                    in
                                      (Const (c, ta), a)
                                    end
  | inst_m tT tt (Free (x, t)) m = let
                                     val (ta, a) = instT_m tT t m;
                                   in
                                     (Free (x, ta), a)
                                   end
  | inst_m tT tt (Var ((x, i), t)) m =
    let
      val (ta, m1) = instT_m tT t m;
    in
      (case lookup_vara tt ((x, i), ta)
        of NONE => (Var ((x, i), ta), max ord_integer m1 i)
        | SOME (tb, j) => (tb, max ord_integer m1 j))
    end
  | inst_m tT tt (Bound i) m = (Bound i, m)
  | inst_m tT tt (Abs (x, t, b)) m = let
                                       val (ta, m1) = instT_m tT t m;
                                       val (ba, a) = inst_m tT tt b m1;
                                     in
                                       (Abs (x, ta, ba), a)
                                     end
  | inst_m tT tt (t $ u) m = let
                               val (ta, m1) = inst_m tT tt t m;
                               val (ua, a) = inst_m tT tt u m1;
                             in
                               (ta $ ua, a)
                             end;

fun map_xres f1 f2 (Ok x1) = Ok (f1 x1)
  | map_xres f1 f2 (Err x2) = Err (f2 x2);

fun aseq_ctx (AQ_Try (ctx, uu, uv)) = ctx
  | aseq_ctx (AQ_Map (ctx, uw, ux, uy, uz)) = ctx;

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

fun brc_state (BRCtx (x1, x2, x3, x4, x5, x6, x7, x8)) = x3;

fun brc_match (BRCtx (x1, x2, x3, x4, x5, x6, x7, x8)) = x2;

fun brc_goal (BRCtx (x1, x2, x3, x4, x5, x6, x7, x8)) = x5;

fun brc_dst (BRCtx (x1, x2, x3, x4, x5, x6, x7, x8)) = x4;

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
    of NONE => liftMT (map_option (map_xres SOME id) NONE)
    | SOME (Ok aa) => liftMT (map_option (map_xres SOME id) (SOME (Ok aa)))
    | SOME (Err (Unif tr)) => bindW (emit (Ev_Unif tr)) (fn _ => returnW NONE)
    | SOME (Err Pattern) =>
      liftMT (map_option (map_xres SOME id) (SOME (Err Pattern)))
    | SOME (Err Match) =>
      liftMT (map_option (map_xres SOME id) (SOME (Err Match)))
    | SOME (Err TUnify) =>
      liftMT (map_option (map_xres SOME id) (SOME (Err TUnify)))
    | SOME (Err Type_Match) =>
      liftMT (map_option (map_xres SOME id) (SOME (Err Type_Match)))
    | SOME (Err (Class_Error class_error)) =>
      liftMT
        (map_option (map_xres SOME id) (SOME (Err (Class_Error class_error))))
    | SOME (Err (Type_Error (literal, list1, list2))) =>
      liftMT
        (map_option (map_xres SOME id)
          (SOME (Err (Type_Error (literal, list1, list2)))))
    | SOME (Err (Term_Error (literal, lista))) =>
      liftMT
        (map_option (map_xres SOME id)
          (SOME (Err (Term_Error (literal, lista)))))
    | SOME (Err (Failure literal)) =>
      liftMT (map_option (map_xres SOME id) (SOME (Err (Failure literal))))
    | SOME (Err Subscript) =>
      liftMT (map_option (map_xres SOME id) (SOME (Err Subscript)))
    | SOME (Err Unequal_Lengths) =>
      liftMT (map_option (map_xres SOME id) (SOME (Err Unequal_Lengths)))
    | SOME (Err (Dup prod)) =>
      liftMT (map_option (map_xres SOME id) (SOME (Err (Dup prod)))));

fun bicompose_body ops ctx env eres_flg rAs =
  (if eres_flg
    then (case rev rAs
           of [] =>
             raiseW
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
    else bindW (bo_unifiers ops env (bc_dpairs ctx))
           (fn us =>
             bindW (bo_pull ops us)
               (fn a =>
                 (case a of NONE => returnW BS_Empty
                   | SOME ((enva, tpairs), usa) =>
                     bindW (newAs (bo_variants ops) ctx (rev rAs)
                             (0 : IntInf.int) [bc_BBi ctx] tpairs)
                       (fn na =>
                         returnW
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
    bindW (handleW (liftMT (strip_prems nsubgoal [] rprop))
            (fn e =>
              (case e of UExn (PExn (Unif _)) => raiseW e
                | UExn (PExn Pattern) => raiseW e
                | UExn (PExn Match) => raiseW e | UExn (PExn TUnify) => raiseW e
                | UExn (PExn Type_Match) => raiseW e
                | UExn (PExn (Class_Error _)) => raiseW e
                | UExn (PExn (Type_Error (_, _, _))) => raiseW e
                | UExn (PExn (Term_Error (_, _))) =>
                  raiseW
                    (THM ("bicompose: rule", (0 : IntInf.int), Orule_State))
                | UExn (PExn (Failure _)) => raiseW e
                | UExn (PExn Subscript) => raiseW e
                | UExn (PExn Unequal_Lengths) => raiseW e
                | UExn (PExn (Dup _)) => raiseW e | UExn CANTUNIFY => raiseW e
                | UExn ASSIGN => raiseW e | UExn CHANGE_FAIL => raiseW e
                | UExn Bind => raiseW e | THM (_, _, _) => raiseW e
                | ERROR _ => raiseW e | COMPOSE => raiseW e
                | NOT_OF_SORT (_, _) => raiseW e
                | INST_CONFLICT (_, _, _) => raiseW e)))
      (fn (rAs, b) =>
        let
          val bBi = (if lifted then strip_assums2 b bi else (b, bi));
          val ctx =
            BCtx (flatten, match_flg, lifted, smax, bs, bi, c, rtpairs, nlift,
                   bBi, bBi :: rtpairs @ stpairs);
        in
          bindW (if incremented
                  then returnW (SOME (empty_env (max ord_integer rmax smax)))
                  else unify_var_types alg (snd state) (snd orule)
                         (empty_env (max ord_integer rmax smax)))
            (fn a =>
              (case a of NONE => returnW BS_Empty
                | SOME env => bicompose_body ops ctx env eres_flg rAs))
        end)
  end;

fun nprems_of th = count_prems (th_prop th);

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

fun brstep ops alg rep RQ_Empty = returnW RS_Done
  | brstep ops alg rep (RQ_Make (ctx, (eres_flg, rule), brules)) =
    bindW (compose ops alg ctx eres_flg (rep rule))
      (fn xq =>
        returnW (RS_Skip (RQ_App ((eres_flg, rule), xq, res rep ctx brules))))
  | brstep ops alg rep (RQ_App (r, xq, xqq)) =
    bindW (bpull ops xq)
      (fn a =>
        (case a of NONE => returnW (RS_Skip xqq)
          | SOME (th, xqa) =>
            returnW (RS_Result ((th, r), RQ_App (r, xqa, xqq)))));

fun abstract_rule_data b hyps ct th =
  (case dest_eq_fun (th_prop th)
    of NONE =>
      raiseW
        (THM ("abstract_rule: premise not an equality", (0 : IntInf.int),
               State))
    | SOME (u, (t, ua)) =>
      let
        val x = ct_t ct;
        val ta = ct_T ct;
        val check =
          (fn a => fn ts =>
            (if occs_hyps x ts (th_tpairs th)
              then raiseW
                     (THM ("abstract_rule: variable " ^ quote_lit a ^
                             " free in assumptions",
                            (0 : IntInf.int), State))
              else returnW
                     (u, (Abs (b, ta, abstract_over x t),
                           Abs (b, ta, abstract_over x ua)))));
      in
        (case x
          of Const (_, _) =>
            raiseW
              (THM ("abstract_rule: not a variable", (0 : IntInf.int), State))
          | Free (a, _) => check a hyps | Var ((a, _), _) => check a []
          | Bound _ =>
            raiseW
              (THM ("abstract_rule: not a variable", (0 : IntInf.int), State))
          | Abs (_, _, _) =>
            raiseW
              (THM ("abstract_rule: not a variable", (0 : IntInf.int), State))
          | _ $ _ =>
            raiseW
              (THM ("abstract_rule: not a variable", (0 : IntInf.int), State)))
      end);

fun abstract_rule b hyps ct th =
  bindW (abstract_rule_data b hyps ct th)
    (fn (_, (f, g)) =>
      liftMT
        (bindM (mk_equals (f, g))
          (fn p =>
            return
              (mk_rep (maxidx_typ (ct_T ct) (th_maxidx th)) (th_tpairs th)
                p))));

val trivial_proof : Proofterm.proof =
  Proofterm.AbsP ("H", NONE, Proofterm.PBound (0 : IntInf.int));

fun zassume_proof ta a = bindM (zterm_of ta a) (fn aa => return (ZHyp aa));

fun mk_Abst params prf =
  foldr (fn (s, _) => (fn a => Proofterm.Abst (s, NONE, a))) params prf;

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

fun eta_conversion ct =
  liftMT
    (bindM (mk_equals (ct_t ct, eta_contract (ct_t ct)))
      (fn p => return (mk_rep (ct_maxidx ct) [] p)));

fun zabstract_term z i (ZAbs (x, ta, t)) =
  (if aconv_zterm (ZAbs (x, ta, t)) z then ZBound i
    else ZAbs (x, ta, zabstract_term z (IntInf.+ (i, (1 : IntInf.int))) t))
  | zabstract_term z i (ZApp (t, u)) =
    (if aconv_zterm (ZApp (t, u)) z then ZBound i
      else ZApp (zabstract_term z i t, zabstract_term z i u))
  | zabstract_term z i (ZVar (v, va)) =
    (if aconv_zterm (ZVar (v, va)) z then ZBound i else ZVar (v, va))
  | zabstract_term z i (ZBound v) =
    (if aconv_zterm (ZBound v) z then ZBound i else ZBound v)
  | zabstract_term z i (ZConst0 v) =
    (if aconv_zterm (ZConst0 v) z then ZBound i else ZConst0 v)
  | zabstract_term z i (ZConst1 (v, va)) =
    (if aconv_zterm (ZConst1 (v, va)) z then ZBound i else ZConst1 (v, va))
  | zabstract_term z i (ZConst (v, va)) =
    (if aconv_zterm (ZConst (v, va)) z then ZBound i else ZConst (v, va))
  | zabstract_term z i (OFCLASS (v, va)) =
    (if aconv_zterm (OFCLASS (v, va)) z then ZBound i else OFCLASS (v, va));

fun ztrivial_proof ta a =
  bindM (zterm_of ta a)
    (fn aa => return (ZAbsp ("H", aa, ZBoundp (0 : IntInf.int))));

fun has_tfree tfrees (TFree (a, uu)) = member equal_literal tfrees a
  | has_tfree tfrees (Type (uv, ts)) = list_ex (has_tfree tfrees) ts
  | has_tfree tfrees (TVar (v, va)) = false;

fun bad_term tfrees frees (Free (x, t)) =
  has_tfree tfrees t orelse member equal_literal frees x
  | bad_term tfrees frees (Var (uu, t)) = has_tfree tfrees t
  | bad_term tfrees frees (Const (uv, t)) = has_tfree tfrees t
  | bad_term tfrees frees (Abs (uw, ta, t)) =
    has_tfree tfrees ta orelse bad_term tfrees frees t
  | bad_term tfrees frees (t $ u) =
    bad_term tfrees frees t orelse bad_term tfrees frees u
  | bad_term tfrees frees (Bound ux) = false;

fun of_class alg t c =
  let
    val p = mk_of_class t c;
  in
    bindW (liftMT (of_sort alg t [c]))
      (fn ok =>
        (if ok then returnW (mk_rep (maxidx_of_term p) [] p)
          else raiseW (NOT_OF_SORT (t, [c]))))
  end;

fun ac_Bi (ACtx (x1, x2, x3, x4, x5, x6, x7)) = x4;

fun assumption_proof bs bi n prf =
  mk_AbsP bs
    (proof_combP prf
      (map Proofterm.PBound
         (downto (IntInf.- (integer_of_nat (size_list bs), (1 : IntInf.int)))
           (0 : IntInf.int)) @
        [mk_asm_prf bi n (~1 : IntInf.int)]));

fun ares_proof ctx x prf =
  let
    val ARes (env, n, _) = x;
  in
    bindW (liftMP (mapM (norm_term env) (ac_Bs ctx)))
      (fn ns =>
        bindW (liftMP (norm_term env (ac_Bi ctx)))
          (fn na =>
            let
              val p = assumption_proof ns na n prf;
            in
              (if env_is_empty env then returnW p
                else norm_proof_remove_types env p)
            end))
  end;

fun dest_state state i =
  handleW
    (bindW (liftMT (strip_prems i [] (th_prop state)))
      (fn a =>
        (case a of ([], _) => raiseW (THM ("dest_state", i, State))
          | (b :: rBs, c) => returnW (th_tpairs state, (rev rBs, (b, c))))))
    (fn e =>
      (case e of UExn (PExn (Unif _)) => raiseW e
        | UExn (PExn Pattern) => raiseW e | UExn (PExn Match) => raiseW e
        | UExn (PExn TUnify) => raiseW e | UExn (PExn Type_Match) => raiseW e
        | UExn (PExn (Class_Error _)) => raiseW e
        | UExn (PExn (Type_Error (_, _, _))) => raiseW e
        | UExn (PExn (Term_Error (_, _))) =>
          raiseW (THM ("dest_state", i, State))
        | UExn (PExn (Failure _)) => raiseW e
        | UExn (PExn Subscript) => raiseW e
        | UExn (PExn Unequal_Lengths) => raiseW e
        | UExn (PExn (Dup _)) => raiseW e | UExn CANTUNIFY => raiseW e
        | UExn ASSIGN => raiseW e | UExn CHANGE_FAIL => raiseW e
        | UExn Bind => raiseW e | THM (_, _, _) => raiseW e
        | ERROR _ => raiseW e | COMPOSE => raiseW e
        | NOT_OF_SORT (_, _) => raiseW e
        | INST_CONFLICT (_, _, _) => raiseW e));

fun assumption i state =
  bindW (dest_state state i)
    (fn (tpairs, (bs, (bi, c))) =>
      let
        val (params, (asms, concl)) = assum_problems (~1 : IntInf.int) bi;
      in
        returnW
          (AQ_Try
            (ACtx (th_maxidx state, tpairs, bs, bi, c, params, concl), asms,
              (1 : IntInf.int)))
      end);

fun nth_prem i t =
  (case dest_imp t of NONE => raisea (Term_Error ("nth_prem", [t]))
    | SOME (a, b) =>
      (if ((i : IntInf.int) = (1 : IntInf.int)) then return a
        else nth_prem (IntInf.- (i, (1 : IntInf.int))) b));

fun cprem_of th i =
  handleW (liftMT (nth_prem i (th_prop th)))
    (fn e =>
      (case e of UExn (PExn (Unif _)) => raiseW e
        | UExn (PExn Pattern) => raiseW e | UExn (PExn Match) => raiseW e
        | UExn (PExn TUnify) => raiseW e | UExn (PExn Type_Match) => raiseW e
        | UExn (PExn (Class_Error _)) => raiseW e
        | UExn (PExn (Type_Error (_, _, _))) => raiseW e
        | UExn (PExn (Term_Error (_, _))) => raiseW (THM ("cprem_of", i, State))
        | UExn (PExn (Failure _)) => raiseW e
        | UExn (PExn Subscript) => raiseW e
        | UExn (PExn Unequal_Lengths) => raiseW e
        | UExn (PExn (Dup _)) => raiseW e | UExn CANTUNIFY => raiseW e
        | UExn ASSIGN => raiseW e | UExn CHANGE_FAIL => raiseW e
        | UExn Bind => raiseW e | THM (_, _, _) => raiseW e
        | ERROR _ => raiseW e | COMPOSE => raiseW e
        | NOT_OF_SORT (_, _) => raiseW e
        | INST_CONFLICT (_, _, _) => raiseW e));

fun beta_conversion full ct =
  let
    val t = ct_t ct;
  in
    bindW (if full then liftMT (beta_norm t)
            else (case t
                   of Const (_, _) =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Free (_, _) =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Var (_, _) =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Bound _ =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Abs (_, _, _) =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Const (_, _) $ _ =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Free (_, _) $ _ =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Var (_, _) $ _ =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Bound _ $ _ =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))
                   | Abs (_, _, bodt) $ u => returnW (subst_bound u bodt)
                   | _ $ _ $ _ =>
                     raiseW
                       (THM ("beta_conversion: not a redex", (0 : IntInf.int),
                              No_Thm))))
      (fn ta =>
        liftMT
          (bindM (mk_equals (t, ta))
            (fn p => return (mk_rep (ct_maxidx ct) [] p))))
  end;

fun combination_res th1 th2 =
  bindW (combination_data th1 th2)
    (fn (fT, (u, (f, (g, (t, ua))))) =>
      bindW (liftMT (mk_equals (f $ t, g $ ua)))
        (fn p =>
          returnW
            (mk_rep (max ord_integer (th_maxidx th1) (th_maxidx th2))
               (union_tpairs (th_tpairs th1) (th_tpairs th2)) p,
              (fT, (u, (f, (g, (t, ua))))))));

val reflexive_proof : Proofterm.proof = equality_axm "reflexive" % NONE;

fun is_reflexive_proof (Proofterm.PAxm (a, uu, uv) % uw) =
  ((a : string) = "Pure.reflexive")
  | is_reflexive_proof Proofterm.MinProof = false
  | is_reflexive_proof (Proofterm.PBound v) = false
  | is_reflexive_proof (Proofterm.Abst (v, va, vb)) = false
  | is_reflexive_proof (Proofterm.AbsP (v, va, vb)) = false
  | is_reflexive_proof (Proofterm.MinProof % va) = false
  | is_reflexive_proof (Proofterm.PBound vb % va) = false
  | is_reflexive_proof (Proofterm.Abst (vb, vc, vd) % va) = false
  | is_reflexive_proof (Proofterm.AbsP (vb, vc, vd) % va) = false
  | is_reflexive_proof (vb % vc % va) = false
  | is_reflexive_proof (vb %% vc % va) = false
  | is_reflexive_proof (Proofterm.Hyp vb % va) = false
  | is_reflexive_proof (Proofterm.PClass (vb, vc) % va) = false
  | is_reflexive_proof (Proofterm.Oracle (vb, vc, vd) % va) = false
  | is_reflexive_proof (Proofterm.PThm vb % va) = false
  | is_reflexive_proof (v %% va) = false
  | is_reflexive_proof (Proofterm.Hyp v) = false
  | is_reflexive_proof (Proofterm.PAxm (v, va, vb)) = false
  | is_reflexive_proof (Proofterm.PClass (v, va)) = false
  | is_reflexive_proof (Proofterm.Oracle (v, va, vb)) = false
  | is_reflexive_proof (Proofterm.PThm v) = false;

fun symmetric_proof prf =
  (if is_reflexive_proof prf then prf
    else equality_axm "symmetric" % NONE % NONE %% prf);

fun zabstract_proof z i (ZAbst (x, t, p)) =
  ZAbst (x, t, zabstract_proof z (IntInf.+ (i, (1 : IntInf.int))) p)
  | zabstract_proof z i (ZAbsp (x, t, p)) =
    ZAbsp (x, zabstract_term z i t, zabstract_proof z i p)
  | zabstract_proof z i (ZAppt (p, t)) =
    ZAppt (zabstract_proof z i p, zabstract_term z i t)
  | zabstract_proof z i (ZAppp (p, q)) =
    ZAppp (zabstract_proof z i p, zabstract_proof z i q)
  | zabstract_proof z i ZNop = ZNop
  | zabstract_proof z i (ZConstp v) = ZConstp v
  | zabstract_proof z i (ZBoundp v) = ZBoundp v
  | zabstract_proof z i (ZHyp v) = ZHyp v
  | zabstract_proof z i (OFCLASSp (v, va)) = OFCLASSp (v, va);

fun term_typs (Const (uu, t)) = [t]
  | term_typs (Free (uv, t)) = [t]
  | term_typs (Var (uw, t)) = [t]
  | term_typs (Bound ux) = []
  | term_typs (Abs (uy, t, b)) = t :: term_typs b
  | term_typs (t $ u) = term_typs t @ term_typs u;

fun add_tvars t xs =
  fold (fn ta => fn acc =>
         (case ta of Type (_, _) => acc | TFree (_, _) => acc
           | TVar (v, s) =>
             insert
               (equal_prod (equal_prod equal_literal equal_integer)
                 (equal_list equal_literal))
               (v, s) acc))
    (maps atyps (term_typs t)) xs;

fun betapplys t [] = t
  | betapplys t (u :: us) = betapplys (betapply t u) us;

fun map_atyps f (Type (a, ts)) = Type (a, map (map_atyps f) ts)
  | map_atyps f (TFree (v, va)) = f (TFree (v, va))
  | map_atyps f (TVar (v, va)) = f (TVar (v, va));

fun map_types f (Const (c, t)) = Const (c, f t)
  | map_types f (Free (x, t)) = Free (x, f t)
  | map_types f (Var (xi, t)) = Var (xi, f t)
  | map_types f (Bound i) = Bound i
  | map_types f (Abs (x, t, b)) = Abs (x, f t, map_types f b)
  | map_types f (t $ u) = map_types f t $ map_types f u;

fun lift_rule_prems gprop gmax orule =
  map (lift_all (IntInf.+ (gmax, (1 : IntInf.int))) gprop)
    (strip_imp_prems (th_prop orule));

fun lift_rule_proof gprop gmax orule p =
  lift_proof gprop (IntInf.+ (gmax, (1 : IntInf.int)))
    (lift_rule_prems gprop gmax orule) p;

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun nat_of_integer k =
  (if IntInf.<= (k, (0 : IntInf.int)) then Zero_nat
    else let
           val (l, j) = divmod_integer k (2 : IntInf.int);
           val la = nat_of_integer l;
           val lb = plus_nata la la;
         in
           (if ((j : IntInf.int) = (0 : IntInf.int)) then lb
             else plus_nata lb one_nata)
         end);

fun zassumption_proof ta env bs bi n visible prf =
  let
    val normt = (fn t => bindM (zterm_of ta t) (znorm_term ta env));
  in
    bindM (mapM normt bs)
      (fn ns =>
        bindM (normt bi)
          (fn na =>
            znorm_proof ta env visible
              (zAbsps ns
                (zAppps prf
                  (map ZBoundp
                     (downto
                       (IntInf.- (integer_of_nat
                                    (size_list bs), (1 : IntInf.int)))
                       (0 : IntInf.int)) @
                    [zmk_asm_prf na n (~1 : IntInf.int)])))))
  end;

fun ares_zproof ta state ctx x prf =
  let
    val ARes (env, n, _) = x;
  in
    bindM (liftMZ (full_prop_of (th_tpairs state) (th_prop state)))
      (fn p => zassumption_proof ta env (ac_Bs ctx) (ac_Bi ctx) n [p] prf)
  end;

fun test_hyps bi = is_none (dest_all (strip_imp_concl (strip_all_body bi)));

fun equal_elim_proof a b prf1 prf2 =
  equality_axm "equal_elim" % SOME (remove_types a) % SOME (remove_types b) %%
    prf1 %%
    prf2;

fun equal_intr_proof a b prf1 prf2 =
  equality_axm "equal_intr" % SOME (remove_types a) % SOME (remove_types b) %%
    prf1 %%
    prf2;

fun transitive_proof ua u prf1 prf2 =
  (if is_reflexive_proof prf1 then prf2
    else (if is_reflexive_proof prf2 then prf1
           else (if ((ua : typ) = propT)
                  then equality_axm "transitive" % NONE %
                         SOME (remove_types u) %
                         NONE %%
                         prf1 %%
                         prf2
                  else equality_axm "transitive" % NONE % NONE % NONE %% prf1 %%
                         prf2)));

fun zreflexive_proof taa ta t =
  bindM (zterm_of taa t)
    (fn x => zaxiom_proof "reflexive" [(tvar_a, ztyp_of ta)] [("x", x)]);

fun zis_reflexive_proof (ZConstp ((ZAxiom a, uu), uv)) =
  ((a : string) = "Pure.reflexive")
  | zis_reflexive_proof ZNop = false
  | zis_reflexive_proof (ZConstp ((ZOracle ve, vd), vb)) = false
  | zis_reflexive_proof (ZConstp ((ZThm ve, vd), vb)) = false
  | zis_reflexive_proof (ZBoundp v) = false
  | zis_reflexive_proof (ZAbst (v, va, vb)) = false
  | zis_reflexive_proof (ZAbsp (v, va, vb)) = false
  | zis_reflexive_proof (ZAppt (v, va)) = false
  | zis_reflexive_proof (ZAppp (v, va)) = false
  | zis_reflexive_proof (ZHyp v) = false
  | zis_reflexive_proof (OFCLASSp (v, va)) = false;

fun zsymmetric_proof taa ta t u prf =
  (if zis_reflexive_proof prf then return prf
    else bindM (zterm_of taa t)
           (fn x =>
             bindM (zterm_of taa u)
               (fn y =>
                 bindM (zaxiom_proof "symmetric" [(tvar_a, ztyp_of ta)]
                         [("x", x), ("y", y)])
                   (fn ax => return (ZAppp (ax, prf))))));

fun add_tfrees t xs =
  fold (fn ta => fn acc =>
         (case ta of Type (_, _) => acc
           | TFree (a, s) =>
             insert (equal_prod equal_literal (equal_list equal_literal)) (a, s)
               acc
           | TVar (_, _) => acc))
    (maps atyps (term_typs t)) xs;

fun check_inst [] = returnW ()
  | check_inst (((v, t), (ua, (u, uu))) :: xs) =
    (if ((t : typ) = u) then check_inst xs
      else raiseW (INST_CONFLICT ((v, t), ua, u)));

fun generalizeT tfrees gi (Type (a, ts)) =
  Type (a, map (generalizeT tfrees gi) ts)
  | generalizeT tfrees gi (TFree (a, s)) =
    (if member equal_literal tfrees a then TVar ((a, gi), s) else TFree (a, s))
  | generalizeT tfrees gi (TVar (v, va)) = TVar (v, va);

fun clean_index_aux xs i =
  (if not (null xs) andalso
        equal_chara (last xs)
          (Chara (true, true, true, true, true, false, true, false))
    then clean_index_aux (butlast xs) (IntInf.+ (i, (1 : IntInf.int)))
    else (xs, i));

fun clean_index xi =
  let
    val (ys, a) = clean_index_aux (explode (fst xi)) (snd xi);
  in
    (implode ys, a)
  end;

fun generalize_term tfrees frees gi (Free (x, t)) =
  (if member equal_literal frees x
    then Var (clean_index (x, gi), generalizeT tfrees gi t)
    else Free (x, generalizeT tfrees gi t))
  | generalize_term tfrees frees gi (Var (xi, t)) =
    Var (xi, generalizeT tfrees gi t)
  | generalize_term tfrees frees gi (Const (c, t)) =
    Const (c, generalizeT tfrees gi t)
  | generalize_term tfrees frees gi (Bound i) = Bound i
  | generalize_term tfrees frees gi (Abs (x, ta, t)) =
    Abs (x, generalizeT tfrees gi ta, generalize_term tfrees frees gi t)
  | generalize_term tfrees frees gi (t $ u) =
    generalize_term tfrees frees gi t $ generalize_term tfrees frees gi u;

fun generalize tfrees frees gi hyps th =
  (if null tfrees andalso null frees then returnW th
    else (if IntInf.<= (gi, th_maxidx th)
           then raiseW (THM ("generalize: bad index", gi, State))
           else (if list_ex (bad_term tfrees frees) hyps
                  then raiseW
                         (THM ("generalize: variable free in assumptions",
                                (0 : IntInf.int), State))
                  else let
                         val gen = generalize_term tfrees frees gi;
                         val p = gen (th_prop th);
                         val tps =
                           map (fn (t, u) => (gen t, gen u)) (th_tpairs th);
                       in
                         returnW
                           (mk_rep (maxidx_tpairs tps (maxidx_of_term p)) tps p)
                       end)));

fun tvar_names t =
  maps (fn a =>
         (case a of Type (_, _) => [] | TFree (_, _) => []
           | TVar ((aa, _), _) => [aa]))
    (maps atyps (term_typs t));

fun lift_rule_zproof ta gprop gmax orule p =
  zlift_proof ta gprop (IntInf.+ (gmax, (1 : IntInf.int)))
    (lift_rule_prems gprop gmax orule) p;

fun abstract_rule_res b hyps ct th =
  bindW (abstract_rule_data b hyps ct th)
    (fn (u, (f, g)) =>
      bindW (liftMT (mk_equals (f, g)))
        (fn p =>
          returnW
            (mk_rep (maxidx_typ (ct_T ct) (th_maxidx th)) (th_tpairs th) p,
              (u, (f, g)))));

fun adjust_maxidx_thm i th =
  (if (((th_maxidx th) : IntInf.int) = i) then th
    else (if IntInf.< (th_maxidx th, i)
           then mk_rep i (th_tpairs th) (th_prop th)
           else mk_rep
                  (max ord_integer
                    (maxidx_tpairs (th_tpairs th) (maxidx_of_term (th_prop th)))
                    i)
                  (th_tpairs th) (th_prop th)));

fun combination_proof f g t u prf1 prf2 =
  liftMP
    (bindM (beta_norm f)
      (fn fa =>
        bindM (beta_norm g)
          (fn ga =>
            let
              val ax0 = equality_axm "combination";
              val ax =
                (if check_comb prf1 then ax0 % NONE % NONE
                  else (if is_reflexive_proof prf1
                         then ax0 % SOME (remove_types fa) % NONE
                         else ax0 % SOME (remove_types fa) %
                                SOME (remove_types ga)));
            in
              return (ax % comb_arg fa t % comb_arg ga u %% prf1 %% prf2)
            end)));

fun prf_abstract_term v lev (Abs (a, ta, t)) =
  (if aconv_term v (Abs (a, ta, t)) then Bound lev
    else Abs (a, ta, prf_abstract_term v (IntInf.+ (lev, (1 : IntInf.int))) t))
  | prf_abstract_term v lev (t $ u) =
    (if aconv_term v (t $ u) then Bound lev
      else prf_abstract_term v lev t $ prf_abstract_term v lev u)
  | prf_abstract_term v lev (Const (va, vb)) =
    (if aconv_term v (Const (va, vb)) then Bound lev else Const (va, vb))
  | prf_abstract_term v lev (Free (va, vb)) =
    (if aconv_term v (Free (va, vb)) then Bound lev else Free (va, vb))
  | prf_abstract_term v lev (Var (va, vb)) =
    (if aconv_term v (Var (va, vb)) then Bound lev else Var (va, vb))
  | prf_abstract_term v lev (Bound va) =
    (if aconv_term v (Bound va) then Bound lev else Bound va);

fun prf_abstract_over_aux v lev (Proofterm.AbsP (a, t, p)) =
  Proofterm.AbsP (a, map_option (prf_abstract_term v lev) t,
    prf_abstract_over_aux v lev p)
  | prf_abstract_over_aux v lev (Proofterm.Abst (a, t, p)) =
    Proofterm.Abst (a, t,
      prf_abstract_over_aux v (IntInf.+ (lev, (1 : IntInf.int))) p)
  | prf_abstract_over_aux v lev (p %% q) =
    prf_abstract_over_aux v lev p %% prf_abstract_over_aux v lev q
  | prf_abstract_over_aux v lev (p % t) =
    prf_abstract_over_aux v lev p % map_option (prf_abstract_term v lev) t
  | prf_abstract_over_aux v lev Proofterm.MinProof = Proofterm.MinProof
  | prf_abstract_over_aux v lev (Proofterm.PBound va) = Proofterm.PBound va
  | prf_abstract_over_aux v lev (Proofterm.Hyp va) = Proofterm.Hyp va
  | prf_abstract_over_aux v lev (Proofterm.PAxm (va, vb, vc)) =
    Proofterm.PAxm (va, vb, vc)
  | prf_abstract_over_aux v lev (Proofterm.PClass (va, vb)) =
    Proofterm.PClass (va, vb)
  | prf_abstract_over_aux v lev (Proofterm.Oracle (va, vb, vc)) =
    Proofterm.Oracle (va, vb, vc)
  | prf_abstract_over_aux v lev (Proofterm.PThm va) = Proofterm.PThm va;

fun prf_abstract_over v p = prf_abstract_over_aux v (0 : IntInf.int) p;

fun forall_intr_proof a v prf =
  Proofterm.Abst (a, NONE, prf_abstract_over v prf);

fun zequal_elim_proof ta t u prf1 prf2 =
  bindM (zterm_of ta t)
    (fn a =>
      bindM (zterm_of ta u)
        (fn b =>
          bindM (zaxiom_proof "equal_elim" [] [("A", a), ("B", b)])
            (fn ax => return (ZAppp (ZAppp (ax, prf1), prf2)))));

fun zequal_intr_proof ta t u prf1 prf2 =
  bindM (zterm_of ta t)
    (fn a =>
      bindM (zterm_of ta u)
        (fn b =>
          bindM (zaxiom_proof "equal_intr" [] [("A", a), ("B", b)])
            (fn ax => return (ZAppp (ZAppp (ax, prf1), prf2)))));

fun ztransitive_proof taa ta t u v prf1 prf2 =
  (if zis_reflexive_proof prf1 then return prf2
    else (if zis_reflexive_proof prf2 then return prf1
           else bindM (zterm_of taa t)
                  (fn x =>
                    bindM (zterm_of taa u)
                      (fn y =>
                        bindM (zterm_of taa v)
                          (fn z =>
                            bindM (zaxiom_proof "transitive"
                                    [(tvar_a, ztyp_of ta)]
                                    [("x", x), ("y", y), ("z", z)])
                              (fn ax =>
                                return (ZAppp (ZAppp (ax, prf1), prf2))))))));

fun check_instT alg [] = returnW ()
  | check_instT alg ((((a, i), s), (u, uu)) :: xs) =
    bindW (liftMT (of_sort alg u s))
      (fn ok =>
        (if ok then check_instT alg xs else raiseW (NOT_OF_SORT (u, s))));

fun dest_equals t =
  (case dest_eq_any t of NONE => raisea (Term_Error ("dest_equals", [t]))
    | SOME a => return a);

fun freeze_tvar alist t =
  (case t of Type (_, _) => t | TFree (_, _) => t
    | TVar (ix, s) =>
      (case map_of (equal_prod equal_literal equal_integer) alist ix
        of NONE => t | SOME a => TFree (a, s)));

fun insert_free v xs =
  (if list_ex
        (fn (y, u) => ((y : string) = (fst v)) andalso ((u : typ) = (snd v))) xs
    then xs else v :: xs);

fun inst_beta_m tT tt (Const (c, t)) m = let
   val (ta, a) = instT_m tT t m;
 in
   (Const (c, ta), a)
 end
  | inst_beta_m tT tt (Free (x, t)) m = let
  val (ta, a) = instT_m tT t m;
in
  (Free (x, ta), a)
end
  | inst_beta_m tT tt (Var (xi, t)) m = inst_beta_spine tT tt (Var (xi, t)) [] m
  | inst_beta_m tT tt (Bound i) m = (Bound i, m)
  | inst_beta_m tT tt (Abs (x, t, b)) m =
    let
      val (ta, m1) = instT_m tT t m;
      val (ba, a) = inst_beta_m tT tt b m1;
    in
      (Abs (x, ta, ba), a)
    end
  | inst_beta_m tT tt (t $ u) m = let
                                    val (ua, a) = inst_beta_m tT tt u m;
                                  in
                                    inst_beta_spine tT tt t [ua] a
                                  end
and inst_beta_spine tT tt (t $ u) args m =
  let
    val (ua, a) = inst_beta_m tT tt u m;
  in
    inst_beta_spine tT tt t (ua :: args) a
  end
  | inst_beta_spine tT tt (Var ((x, i), t)) args m =
    let
      val (ta, m1) = instT_m tT t m;
    in
      (case lookup_vara tt ((x, i), ta)
        of NONE => (list_comb (Var ((x, i), ta)) args, max ord_integer m1 i)
        | SOME (tb, j) =>
          ((if is_Abs tb then betapplys tb args else list_comb tb args),
            max ord_integer m1 j))
    end
  | inst_beta_spine tT tt (Const (c, t)) args m =
    let
      val (ta, a) = instT_m tT t m;
    in
      (list_comb (Const (c, ta)) args, a)
    end
  | inst_beta_spine tT tt (Free (x, t)) args m =
    let
      val (ta, a) = instT_m tT t m;
    in
      (list_comb (Free (x, ta)) args, a)
    end
  | inst_beta_spine tT tt (Bound i) args m = (list_comb (Bound i) args, m)
  | inst_beta_spine tT tt (Abs (x, t, b)) args m =
    let
      val (ta, m1) = instT_m tT t m;
      val (ba, a) = inst_beta_m tT tt b m1;
    in
      (list_comb (Abs (x, ta, ba)) args, a)
    end;

fun instantiate alg beta instT insts th =
  (if null instT andalso null insts then returnW th
    else bindW (check_instT alg instT)
           (fn _ =>
             bindW (check_inst insts)
               (fn _ =>
                 let
                   val inst = map (fn (v, (u, (_, j))) => (v, (u, j))) insts;
                   val subst =
                     (if beta then inst_beta_m instT inst
                       else inst_m instT inst);
                   val (p, m1) = subst (th_prop th) (~1 : IntInf.int);
                   val (tps, m) =
                     fold (fn (t, u) => fn (acc, i) =>
                            let
                              val (ta, i1) = subst t i;
                              val (ua, a) = subst u i1;
                            in
                              (acc @ [(ta, ua)], a)
                            end)
                       (th_tpairs th) ([], m1);
                 in
                   returnW (mk_rep m tps p)
                 end)));

fun lookup_zvar [] v = NONE
  | lookup_zvar (((xi, t), x) :: xs) v =
    (if equal_proda equal_literal equal_integer xi (fst v) andalso
          ((t : ztyp) = (snd v))
      then SOME x else lookup_zvar xs v);

fun strip_all_vars t =
  (case dest_all t of NONE => []
    | SOME (a, (ta, b)) => (a, ta) :: strip_all_vars b);

fun rotate_data k i state =
  bindW (dest_state state i)
    (fn (tpairs, (bs, (bi, c))) =>
      let
        val params = strip_all_vars bi;
        val rest = strip_all_body bi;
        val asms = strip_imp_prems rest;
        val concl = strip_imp_concl rest;
        val n = integer_of_nat (size_list asms);
        val m = (if IntInf.< (k, (0 : IntInf.int)) then IntInf.+ (n, k) else k);
      in
        bindW (if (((0 : IntInf.int) : IntInf.int) = m) orelse
                    ((m : IntInf.int) = n)
                then returnW bi
                else (if IntInf.< ((0 : IntInf.int), m) andalso IntInf.< (m, n)
                       then returnW
                              (list_forall params
                                (list_implies
                                  (drop (nat_of_integer m) asms @
                                    take (nat_of_integer m) asms)
                                  concl))
                       else raiseW (THM ("rotate_rule", k, State))))
          (fn bia =>
            returnW
              (mk_rep (th_maxidx state) tpairs (list_implies (bs @ [bia]) c),
                (bs, (bia, (params, (asms, m))))))
      end);

fun rotate_rule k i state =
  bindW (rotate_data k i state) (fn (th, _) => returnW th);

fun find_index_from p [] k = NONE
  | find_index_from p (x :: xs) k =
    (if p x then SOME k
      else find_index_from p xs (IntInf.+ (k, (1 : IntInf.int))));

fun eq_assumption i state =
  bindW (dest_state state i)
    (fn (tpairs, (bs, (bi, c))) =>
      let
        val (_, (asms, concl)) = assum_problems (~1 : IntInf.int) bi;
      in
        (case find_index_from (fn asm => aeconv asm concl) asms (0 : IntInf.int)
          of NONE => raiseW (THM ("eq_assumption", (0 : IntInf.int), State))
          | SOME n =>
            returnW
              (IntInf.+ (n, (1 : IntInf.int)),
                Thm_rep_ext (th_maxidx state, tpairs, list_implies bs c, ())))
      end);

fun flexflex_rule ops th =
  bindW (bo_unifiers ops (empty_env (th_maxidx th)) (th_tpairs th))
    (fn us => returnW (FQ us));

fun implies_intr_proof h prf =
  Proofterm.AbsP ("H", NONE, abshyp h (0 : IntInf.int) prf);

fun zcombination_proof taa ta ua f g t u prf1 prf2 =
  bindM (zterm_of taa f)
    (fn fa =>
      bindM (zterm_of taa g)
        (fn ga =>
          bindM (zterm_of taa t)
            (fn x =>
              bindM (zterm_of taa u)
                (fn y =>
                  bindM (zaxiom_proof "combination"
                          [(tvar_a, ztyp_of ta), (tvar_b, ztyp_of ua)]
                          [("f", fa), ("g", ga), ("x", x), ("y", y)])
                    (fn ax => return (ZAppp (ZAppp (ax, prf1), prf2)))))));

fun zforall_elim_proof ta t p =
  bindM (zterm_of ta t) (fn tb => return (ZAppt (p, tb)));

fun zforall_intr_proof ta t a x prf =
  bindM (zterm_of ta x)
    (fn z =>
      return (ZAbst (a, ztyp_of t, zabstract_proof z (0 : IntInf.int) prf)));

fun permute_data j k rl =
  let
    val prems = strip_imp_prems (th_prop rl);
    val concl = strip_imp_concl (th_prop rl);
  in
    (if IntInf.< (j, (0 : IntInf.int)) orelse
          IntInf.< (integer_of_nat (size_list prems), j)
      then raiseW (UExn (PExn Subscript))
      else let
             val moved = drop (nat_of_integer j) prems;
             val fixed = take (nat_of_integer j) prems;
             val n_j = integer_of_nat (size_list moved);
             val m =
               (if IntInf.< (k, (0 : IntInf.int)) then IntInf.+ (n_j, k)
                 else k);
           in
             bindW (if (((0 : IntInf.int) : IntInf.int) = m) orelse
                         ((m : IntInf.int) = n_j)
                     then returnW (prems, th_prop rl)
                     else (if IntInf.< ((0 : IntInf.int), m) andalso
                                IntInf.< (m, n_j)
                            then let
                                   val premsa =
                                     fixed @
                                       drop (nat_of_integer m) moved @
 take (nat_of_integer m) moved;
                                 in
                                   returnW (premsa, list_implies premsa concl)
                                 end
                            else raiseW (THM ("permute_prems: k", k, State))))
               (fn (premsa, p) =>
                 returnW (mk_rep (th_maxidx rl) (th_tpairs rl) p, (premsa, m)))
           end)
  end;

fun rotate_proof bs bi params asms m prf =
  let
    val i = integer_of_nat (size_list asms);
    val j = integer_of_nat (size_list bs);
  in
    mk_AbsP (bs @ [bi])
      (proof_combP prf
        (map Proofterm.PBound (downto j (1 : IntInf.int)) @
          [mk_Abst params
             (mk_AbsP asms
               (proof_combP
                 (proof_combt (Proofterm.PBound i)
                   (map Bound
                     (downto
                       (IntInf.- (integer_of_nat
                                    (size_list params), (1 : IntInf.int)))
                       (0 : IntInf.int))))
                 (map Proofterm.PBound
                   (downto (IntInf.- (IntInf.- (i, m), (1 : IntInf.int)))
                      (0 : IntInf.int) @
                     downto (IntInf.- (i, (1 : IntInf.int)))
                       (IntInf.- (i, m))))))]))
  end;

fun varify_tfree names t =
  (case t of Type (_, _) => t
    | TFree (a, s) =>
      (case map_of (equal_prod equal_literal (equal_list equal_literal)) names
              (a, s)
        of NONE => t | SOME (aa, b) => TVar (aa, b))
    | TVar (_, _) => t);

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
  bindW (dest_state state i)
    (fn dst =>
      bindW (cprem_of state i)
        (fn goal =>
          let
            val (_, (_, (bi, _))) = dst;
          in
            returnW
              (res rep
                (BRCtx
                  (trace, match_flg, state, dst, goal, strip_assums_concl bi,
                    strip_assums_hyp bi, test_hyps bi))
                brules)
          end));

fun make th_maxidx th_tpairs th_prop =
  Thm_rep_ext (th_maxidx, th_tpairs, th_prop, ());

fun abstract_rule_proof a x prf =
  equality_axm "abstract_rule" % NONE % NONE %% forall_intr_proof a x prf;

fun eta_long_conversion ct =
  liftMT
    (bindM (eta_long [] (ct_t ct))
      (fn t =>
        bindM (mk_equals (ct_t ct, t))
          (fn p => return (mk_rep (ct_maxidx ct) [] p))));

fun zimplies_intr_proof ta a prf =
  bindM (zterm_of ta a)
    (fn h => return (ZAbsp ("H", h, zabshyp h (0 : IntInf.int) prf)));

fun permute_prems j k rl =
  bindW (permute_data j k rl) (fn (th, _) => returnW th);

fun string_of_int i =
  implode
    (if IntInf.< (i, (0 : IntInf.int))
      then Chara (false, true, true, true, true, true, true, false) ::
             digits (nat_of_integer (IntInf.~ i))
      else digits (nat_of_integer i));

fun varifyT_proof names prf =
  (if null names then prf
    else map_proof_terms (map_types (map_atyps (varify_tfree names)))
           (map_atyps (varify_tfree names)) prf);

fun zrotate_proof ta bs bi params asms m prf =
  let
    val i = integer_of_nat (size_list asms);
    val j = integer_of_nat (size_list bs);
  in
    bindM (mapM (zterm_of ta) (bs @ [bi]))
      (fn bsa =>
        bindM (mapM (zterm_of ta) asms)
          (fn asmsa =>
            return
              (zAbsps bsa
                (zAppps prf
                  (map ZBoundp (downto j (1 : IntInf.int)) @
                    [zAbsts (map (fn (a, t) => (a, ztyp_of t)) params)
                       (zAbsps asmsa
                         (zAppps
                           (zAppts (ZBoundp i)
                             (map ZBound
                               (downto
                                 (IntInf.- (integer_of_nat
      (size_list params), (1 : IntInf.int)))
                                 (0 : IntInf.int))))
                           (map ZBoundp
                             (downto
                                (IntInf.- (IntInf.- (i, m), (1 : IntInf.int)))
                                (0 : IntInf.int) @
                               downto (IntInf.- (i, (1 : IntInf.int)))
                                 (IntInf.- (i, m))))))])))))
  end;

fun flexflex_zproof ta th env prf =
  bindM (liftMZ (full_prop_of (th_tpairs th) (th_prop th)))
    (fn p => znorm_proof ta env [p] prf);

fun zabstract_rule_proof taa ta ua a x t u prf =
  bindM (zterm_of taa t)
    (fn f =>
      bindM (zterm_of taa u)
        (fn g =>
          bindM (zaxiom_proof "abstract_rule"
                  [(tvar_a, ztyp_of ta), (tvar_b, ztyp_of ua)]
                  [("f", f), ("g", g)])
            (fn ax =>
              bindM (zforall_intr_proof taa ta a x prf)
                (fn p => return (ZAppp (ax, p))))));

fun string_of_indexname xi =
  (if (((snd xi) : IntInf.int) = (0 : IntInf.int)) then fst xi
    else fst xi ^ "_" ^ string_of_int (snd xi));

fun add_tfree_names t xs =
  fold (fn ta => fn acc =>
         (case ta of Type (_, _) => acc
           | TFree (a, _) => insert equal_literal a acc | TVar (_, _) => acc))
    (maps atyps (term_typs t)) xs;

fun legacy_freeze_names vl t =
  fst (foldr
        ((fn ix => fn (pairs, used) =>
           let
             val v = hd (vl used [string_of_indexname ix]);
           in
             ((ix, v) :: pairs, v :: used)
           end) o
          fst)
        (add_tvars t []) ([], add_tfree_names t []));

fun legacy_freezeT vl th =
  liftMT
    (bindM (full_prop_of (th_tpairs th) (th_prop th))
      (fn p1 =>
        let
          val alist = legacy_freeze_names vl p1;
          val p2 =
            (if null alist then p1
              else map_types (map_atyps (freeze_tvar alist)) p1);
        in
          bindM (strip_prems (integer_of_nat (size_list (th_tpairs th))) [] p2)
            (fn (ts, p3) =>
              bindM (mapM dest_equals ts)
                (fn tps => return (mk_rep (maxidx_of_term p2) (rev tps) p3)))
        end));

fun varify_global_names vl fixed t =
  let
    val xs =
      fold (fn ta => fn acc =>
             (case ta of Type (_, _) => acc
               | TFree (a, s) =>
                 (if member
                       (equal_prod equal_literal (equal_list equal_literal))
                       fixed (a, s)
                   then acc
                   else insert
                          (equal_prod equal_literal (equal_list equal_literal))
                          (a, s) acc)
               | TVar (_, _) => acc))
        (maps atyps (term_typs t)) [];
    val ys = vl (tvar_names t) (map fst xs);
  in
    map (fn (a, b) => let
                        val (aa, s) = a;
                      in
                        (fn ba => ((aa, s), ((ba, (0 : IntInf.int)), s)))
                      end
                        b)
      (zip xs ys)
  end;

fun varifyT_global vl fixed hyps th =
  liftMT
    let
      val tfrees = fold add_tfrees hyps fixed;
    in
      bindM (full_prop_of (th_tpairs th) (th_prop th))
        (fn p1 =>
          let
            val names = varify_global_names vl tfrees p1;
            val p2 = map_types (map_atyps (varify_tfree names)) p1;
          in
            bindM (strip_prems (integer_of_nat (size_list (th_tpairs th))) []
                    p2)
              (fn (ts, p3) =>
                bindM (mapM dest_equals ts)
                  (fn tps =>
                    return
                      (names,
                        mk_rep (max ord_integer (0 : IntInf.int) (th_maxidx th))
                          (rev tps) p3)))
          end)
    end;

fun zvarifyT_proof names prf =
  (if null names then return prf
    else let
           val typ =
             zsubst_type
               (fn (a, b) =>
                 let
                   val (aa, i) = a;
                 in
                   (fn s =>
                     (if ((i : IntInf.int) = (~1 : IntInf.int))
                       then map_option (fn (ab, ba) => ZTVar (ab, ba))
                              (map_of
                                (equal_prod equal_literal
                                  (equal_list equal_literal))
                                names (aa, s))
                       else NONE))
                 end
                   b);
         in
           map_zproof typ (fn t => return (zsubst_term typ (fn _ => NONE) t))
             prf
         end);

fun generalize_proof tfrees frees gi prop prf =
  let
    val gen =
      (if null frees then []
        else fold (fn a => fn acc =>
                    (case a of Const (_, _) => acc
                      | Free (x, t) =>
                        (if member equal_literal frees x
                          then insert_free (x, t) acc else acc)
                      | Var (_, _) => acc | Bound _ => acc
                      | Abs (_, _, _) => acc | _ $ _ => acc))
               (aterms (generalize_term tfrees [] gi prop)) []);
    val p1 =
      map_proof_terms (generalize_term tfrees [] gi) (generalizeT tfrees gi)
        prf;
    val a = fold (fn (x, t) => forall_intr_proof x (Free (x, t))) gen p1;
  in
    foldr (fn (x, t) => fn p => p % SOME (Var (clean_index (x, gi), t))) gen a
  end;

fun incr_indexes_thm i th =
  (if IntInf.< (i, (0 : IntInf.int))
    then raiseW (THM ("negative increment", (0 : IntInf.int), State))
    else (if ((i : IntInf.int) = (0 : IntInf.int)) then returnW th
           else returnW
                  (mk_rep (IntInf.+ (th_maxidx th, i))
                    (map (fn (t, u) =>
                           (incr_indexes [] i t, incr_indexes [] i u))
                      (th_tpairs th))
                    (incr_indexes [] i (th_prop th)))));

fun instantiate_proof instT inst prf =
  let
    val tT = map (fn (v, t) => (v, (t, (~1 : IntInf.int)))) instT;
    val tt = map (fn (v, t) => (v, (remove_types t, (~1 : IntInf.int)))) inst;
  in
    map_proof_terms (fn t => fst (inst_m tT tt t (~1 : IntInf.int)))
      (fn t => fst (instT_m tT t (~1 : IntInf.int))) prf
  end;

fun zgeneralize_proof tfrees frees gi prf =
  let
    val typ =
      zsubst_type
        (fn (a, b) =>
          let
            val (aa, i) = a;
          in
            (fn s =>
              (if ((i : IntInf.int) = (~1 : IntInf.int)) andalso
                    member equal_literal tfrees aa
                then SOME (ZTVar ((aa, gi), s)) else NONE))
          end
            b);
    val var =
      (fn (a, b) =>
        let
          val (x, i) = a;
        in
          (fn t =>
            (if ((i : IntInf.int) = (~1 : IntInf.int)) andalso
                  member equal_literal frees x
              then SOME (ZVar ((x, gi), t)) else NONE))
        end
          b);
  in
    map_zproof typ (fn t => return (zsubst_term typ var t)) prf
  end;

fun incr_indexes_proof i prf =
  map_proof_terms (incr_indexes [] i) (incr_tvar i) prf;

fun zinstantiate_proof ta instT inst prf =
  bindM (mapM (fn (a, b) =>
                let
                  val (v, t) = a;
                in
                  (fn tb =>
                    bindM (zterm_of ta tb)
                      (fn taa => return ((v, ztyp_of t), taa)))
                end
                  b)
          inst)
    (fn zinst =>
      let
        val typ =
          zsubst_type
            (map_of
              (equal_prod (equal_prod equal_literal equal_integer)
                (equal_list equal_literal))
              (map (fn (v, t) => (v, ztyp_of t)) instT));
      in
        map_zproof typ (fn t => return (zsubst_term typ (lookup_zvar zinst) t))
          prf
      end);

fun eq_assumption_zproof ta bs bi n prf =
  zassumption_proof ta (empty_env (~1 : IntInf.int)) bs bi n [] prf;

fun permute_prems_proof prems j k prf =
  let
    val n = integer_of_nat (size_list prems);
  in
    mk_AbsP prems
      (proof_combP prf
        (map Proofterm.PBound
          (downto (IntInf.- (n, (1 : IntInf.int))) (IntInf.- (n, j)) @
            downto (IntInf.- (k, (1 : IntInf.int))) (0 : IntInf.int) @
              downto (IntInf.- (IntInf.- (n, j), (1 : IntInf.int))) k)))
  end;

fun zincr_indexes_proof inc prf =
  let
    val typ = zincr_tvar inc;
    val var =
      (fn (a, b) =>
        let
          val (x, i) = a;
        in
          (fn t =>
            (if IntInf.<= ((0 : IntInf.int), i)
              then SOME (ZVar ((x, IntInf.+ (i, inc)), t)) else NONE))
        end
          b);
  in
    map_zproof typ (fn t => return (zsubst_term typ var t)) prf
  end;

fun legacy_freezeT_proof vl t prf =
  let
    val alist = legacy_freeze_names vl t;
  in
    (if null alist then prf
      else map_proof_terms (map_types (map_atyps (freeze_tvar alist)))
             (map_atyps (freeze_tvar alist)) prf)
  end;

fun zpermute_prems_proof ta prems j k prf =
  let
    val n = integer_of_nat (size_list prems);
  in
    bindM (mapM (zterm_of ta) prems)
      (fn ps =>
        return
          (zAbsps ps
            (zAppps prf
              (map ZBoundp
                (downto (IntInf.- (n, (1 : IntInf.int))) (IntInf.- (n, j)) @
                  downto (IntInf.- (k, (1 : IntInf.int))) (0 : IntInf.int) @
                    downto (IntInf.- (IntInf.- (n, j), (1 : IntInf.int))) k)))))
  end;

fun zlegacy_freezeT_proof vl t prf =
  let
    val alist = legacy_freeze_names vl t;
  in
    (if null alist then return prf
      else let
             val typ =
               zsubst_type
                 (fn (ix, s) =>
                   map_option (fn a => ZTVar ((a, (~1 : IntInf.int)), s))
                     (map_of (equal_prod equal_literal equal_integer) alist
                       ix));
           in
             map_zproof typ
               (fn ta => return (zsubst_term typ (fn _ => NONE) ta)) prf
           end)
  end;

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



(** generated code: type arguments of constants, exceptions, evaluation **)

structure G = Bicompose_Generated;


fun ztypargs thy =
  let val consts = Sign.consts_of thy in
    fn c => fn T =>
      (SOME (G.Ok (Consts.typargs consts (c, T)))
        handle TYPE (msg, Ts, ts) => SOME (G.Err (G.Type_Error (msg, Ts, ts)))
          | Subscript => SOME (G.Err G.Subscript))
  end;

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
    SOME (G.Ok p) => p
  | SOME (G.Err (G.ZExn exn)) => raise_pexn exn
  | SOME (G.Err (G.BAD_INST inst)) => raise ZTerm.BAD_INST inst
  | SOME (G.Err G.ZOption) => raise Option.Option
  | NONE => raise Fail "zproof: undefined result");


(* evaluation of the generated code: events, exceptions, unifiers *)

fun typ_clash context (tye, T, U) =
  if Config.get_generic context Pattern.unify_trace_failure then
    let
      val ctxt = Context.proof_of context;
      val t = Syntax.string_of_typ ctxt (Envir.norm_type tye T);
      val u = Syntax.string_of_typ ctxt (Envir.norm_type tye U);
    in tracing ("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ();

fun event context ev =
  (case ev of
    G.Ev_Unif (G.Typ_Clash (tye, T, U)) => typ_clash context (tye, T, U)
  | _ => ());

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
  | G.THM (msg, i, G.No_Thm) => raise THM (msg, i, [])
  | G.ERROR msg => error msg
  | G.COMPOSE => raise Fail "bicompose: COMPOSE"
  | G.NOT_OF_SORT _ => raise Fail "unexpected NOT_OF_SORT"
  | G.INST_CONFLICT _ => raise Fail "unexpected INST_CONFLICT");

fun run_with evf thms r =
  (case r of
    SOME (evs, res) =>
      (List.app evf evs;
        (case res of
          G.Ok x => x
        | G.Err exn => raise_exn thms exn))
  | NONE => raise Fail "bicompose: undefined result");

fun run context = run_with (event context);

fun run_proof thms r =
  (case r of
    SOME (ws, res) =>
      (List.app (fn s => warning ("type conflict in norm_proof:\n" ^ s)) ws;
        (case res of
          G.Ok p => p
        | G.Err exn => raise_exn thms (G.UExn (G.PExn exn))))
  | NONE => raise Fail "bicompose_proof: undefined result");

fun ops context =
  G.BOps
    (fn env => fn tus => SOME ([], G.Ok (Unify.unifiers (context, env, tus))),
     fn xq => SOME ([], G.Ok (Seq.pull xq)),
     Name.variant_list []);

fun rep_of (Thm (_, {maxidx, tpairs, prop, ...})) = G.make maxidx tpairs prop;

fun no_thms () = raise Fail "no theorems";
fun run1 th r = run_with (K ()) (fn () => (th, th)) r;
fun run2 th1 th2 r = run_with (K ()) (fn () => (th2, th1)) r;
fun run0 r = run_with (K ()) no_thms r;
fun ct_rep (Cterm {t, T, maxidx, ...}) = G.CTerm (t, T, maxidx);


(*implicit alpha-conversion*)
fun renamed_prop prop' (th as Thm (der, {cert, tags, constraints, shyps, hyps, ...})) =
  let val rep = run1 th (G.renamed_prop prop' (rep_of th)) in
    Thm (der, {cert = cert, tags = tags, maxidx = G.th_maxidx rep, constraints = constraints,
      shyps = shyps, hyps = hyps, tpairs = G.th_tpairs rep, prop = G.th_prop rep})
  end;

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
    val ct as Cterm {t = A, sorts, ...} = adjust_maxidx_cterm ~1 raw_ct;
    val Thm (der, {tags, constraints, shyps, hyps, ...}) = th;
    val rep = run1 th (G.weaken (ct_rep raw_ct) (rep_of th));
  in
    Thm (der,
     {cert = join_certificate1 (ct, th),
      tags = tags,
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = Sorts.union sorts shyps,
      hyps = insert_hyps A hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
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
    (th as Thm (der, {cert, tags, maxidx, constraints, shyps, hyps, ...})) =
  if maxidx = i then th
  else
    let val rep = G.adjust_maxidx_thm i (rep_of th) in
      Thm (der, {maxidx = G.th_maxidx rep, cert = cert, tags = tags, constraints = constraints,
        shyps = shyps, hyps = hyps, tpairs = G.th_tpairs rep, prop = G.th_prop rep})
    end;

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


fun thy_of cert cts ths = Context.certificate_theory cert handle ERROR msg =>
  raise CONTEXT (msg, [], cts, ths, NONE);

(*the theorem of a certified term without hypotheses*)
fun conversion_thm (ct as Cterm {cert, t, T, sorts, ...}) rep =
  let
    fun zproof () = run_zproof (G.zreflexive_proof (ztypargs (thy_of cert [ct] [])) T t);
    fun proof () = G.reflexive_proof;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

(*The assumption rule A |- A*)
fun assume raw_ct =
  let
    val rep = run0 (G.assume_rule (ct_rep raw_ct));
    val ct as Cterm {cert, t = prop, sorts, ...} = adjust_maxidx_cterm ~1 raw_ct;
    fun zproof () = run_zproof (G.zassume_proof (ztypargs (thy_of cert [ct] [])) prop);
    fun proof () = Proofterm.Hyp prop;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = [],
      shyps = sorts,
      hyps = [prop],
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

fun assume_cterm A = assume A
  handle THM (msg, _, _) => raise CTERM (msg, [A]);



(*Implication introduction*)
fun implies_intr
    (ct as Cterm {t = A, sorts, ...})
    (th as Thm (der, {hyps, constraints, shyps, ...})) =
  let
    val rep = run1 th (G.implies_intr (ct_rep ct) (rep_of th));
    val cert = join_certificate1 (ct, th);
    fun zproof p = run_zproof (G.zimplies_intr_proof (ztypargs (thy_of cert [ct] [th])) A p);
    fun proof p = G.implies_intr_proof A p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = Sorts.union sorts shyps,
      hyps = remove_hyps A hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



(*Implication elimination*)
fun implies_elim thAB thA =
  let
    val Thm (derA, {hyps = hypsA, constraints = constraintsA, shyps = shypsA, ...}) = thA
    and Thm (der, {hyps, constraints, shyps, ...}) = thAB;
    val rep = run2 thAB thA (G.implies_elim (rep_of thAB) (rep_of thA));
  in
    Thm (deriv_rule2 (curry ZAppp) (curry Proofterm.%%) der derA,
     {cert = join_certificate2 (thAB, thA),
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = union_constraints constraintsA constraints,
      shyps = Sorts.union shypsA shyps,
      hyps = union_hyps hypsA hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



(*Forall introduction.  The Free or Var x must not be free in the hypotheses.*)
fun occs x ts tpairs =
  let fun occs t = Logic.occs (x, t)
  in exists occs ts orelse exists (occs o fst) tpairs orelse exists (occs o snd) tpairs end;

fun forall_intr
    (ct as Cterm {t = x, T, sorts, ...})
    (th as Thm (der, {constraints, shyps, hyps, ...})) =
  let
    val rep = run1 th (G.forall_intr hyps (ct_rep ct) (rep_of th));
    val a = (case x of Free (a, _) => a | Var ((a, _), _) => a | _ => raise Match);
    val cert = join_certificate1 (ct, th);
    fun zproof p = run_zproof (G.zforall_intr_proof (ztypargs (thy_of cert [ct] [th])) T a x p);
    fun proof p = G.forall_intr_proof a x p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = Sorts.union sorts shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



(*Forall elimination*)
fun forall_elim
    (ct as Cterm {t, sorts, ...})
    (th as Thm (der, {constraints, shyps, hyps, ...})) =
  let
    val rep = run1 th (G.forall_elim (ct_rep ct) (rep_of th));
    val cert = join_certificate1 (ct, th);
    fun zproof p = run_zproof (G.zforall_elim_proof (ztypargs (thy_of cert [ct] [th])) t p);
    fun proof p = p % SOME t;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = Sorts.union sorts shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



(*Reflexivity*)
fun reflexive ct = conversion_thm ct (run0 (G.reflexive (ct_rep ct)));



(*Symmetry*)
fun symmetric (th as Thm (der, {cert, constraints, shyps, hyps, prop, ...})) =
  let
    val rep = run1 th (G.symmetric (rep_of th));
    val (T, t, u) = (case prop of Const (_, Type (_, [T, _])) $ t $ u => (T, t, u) | _ => raise Match);
    fun zproof p = run_zproof (G.zsymmetric_proof (ztypargs (thy_of cert [] [th])) T t u p);
  in
    Thm (deriv_rule1 zproof G.symmetric_proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



(*Transitivity*)
fun transitive th1 th2 =
  let
    val Thm (der1, {hyps = hyps1, constraints = constraints1, shyps = shyps1, prop = prop1, ...}) = th1
    and Thm (der2, {hyps = hyps2, constraints = constraints2, shyps = shyps2, prop = prop2, ...}) = th2;
    val rep = run2 th1 th2 (G.transitive (rep_of th1) (rep_of th2));
    val (T, t1, u, t2) =
      (case (prop1, prop2) of
        (Const (_, Type (_, [T, _])) $ t1 $ u, _ $ _ $ t2) => (T, t1, u, t2)
      | _ => raise Match);
    val cert = join_certificate2 (th1, th2);
    fun zproof p q = run_zproof (G.ztransitive_proof (ztypargs (thy_of cert [] [th1, th2])) T t1 u t2 p q);
    fun proof p = G.transitive_proof T u p;
  in
    Thm (deriv_rule2 zproof proof der1 der2,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = union_constraints constraints1 constraints2,
      shyps = Sorts.union shyps1 shyps2,
      hyps = union_hyps hyps1 hyps2,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



(*Beta-conversion: fully beta-reduces the term if full = true*)
fun beta_conversion full ct = conversion_thm ct (run0 (G.beta_conversion full (ct_rep ct)));

fun eta_conversion ct = conversion_thm ct (run0 (G.eta_conversion (ct_rep ct)));

fun eta_long_conversion ct = conversion_thm ct (run0 (G.eta_long_conversion (ct_rep ct)));



(*The abstraction rule.  The Free or Var x must not be free in the hypotheses.*)
fun abstract_rule b
    (ct as Cterm {t = x, T, sorts, ...})
    (th as Thm (der, {hyps, constraints, shyps, ...})) =
  let
    val (rep, (U, (f, g))) = run1 th (G.abstract_rule_res b hyps (ct_rep ct) (rep_of th));
    val cert = join_certificate1 (ct, th);
    fun zproof p =
      run_zproof (G.zabstract_rule_proof (ztypargs (thy_of cert [ct] [th])) T U b x f g p);
    fun proof p = G.abstract_rule_proof b x p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = Sorts.union sorts shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



(*The combination rule*)
fun combination th1 th2 =
  let
    val Thm (der1, {constraints = constraints1, shyps = shyps1, hyps = hyps1, ...}) = th1
    and Thm (der2, {constraints = constraints2, shyps = shyps2, hyps = hyps2, ...}) = th2;
    val (rep, (fT, (U, (f, (g, (t, u)))))) = run2 th1 th2 (G.combination_res (rep_of th1) (rep_of th2));
    val cert = join_certificate2 (th1, th2);
    fun zproof p q =
      run_zproof (G.zcombination_proof (ztypargs (thy_of cert [] [th1, th2])) fT U f g t u p q);
    fun proof p q = run_proof (fn () => (th2, th1)) (G.combination_proof f g t u p q);
  in
    Thm (deriv_rule2 zproof proof der1 der2,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = union_constraints constraints1 constraints2,
      shyps = Sorts.union shyps1 shyps2,
      hyps = union_hyps hyps1 hyps2,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



(*Equality introduction and the equal propositions rule*)
fun gen_equal model zproof_of proof_of (A, B) th1 th2 =
  let
    val Thm (der1, {constraints = constraints1, shyps = shyps1, hyps = hyps1, ...}) = th1
    and Thm (der2, {constraints = constraints2, shyps = shyps2, hyps = hyps2, ...}) = th2;
    val rep = run2 th1 th2 (model (rep_of th1) (rep_of th2));
    val cert = join_certificate2 (th1, th2);
    fun proof p q = proof_of (A ()) (B ()) p q;
    fun zproof p q =
      run_zproof (zproof_of (ztypargs (thy_of cert [] [th1, th2])) (A ()) (B ()) p q);
  in
    Thm (deriv_rule2 zproof proof der1 der2,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = union_constraints constraints1 constraints2,
      shyps = Sorts.union shyps1 shyps2,
      hyps = union_hyps hyps1 hyps2,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;

fun equal_intr th1 th2 =
  let val (A, B) = (case prop_of th1 of _ $ A $ B => (A, B) | _ => (Term.dummy, Term.dummy)) in
    gen_equal G.equal_intr G.zequal_intr_proof G.equal_intr_proof (K A, K B) th1 th2
  end;



fun equal_elim th1 th2 =
  let val (A, B) = (case prop_of th1 of _ $ A $ B => (A, B) | _ => (Term.dummy, Term.dummy)) in
    gen_equal G.equal_elim G.zequal_elim_proof G.equal_elim_proof (K A, K B) th1 th2
  end;

(**** Derived rules ****)


(*Smash unifies the list of term pairs leaving no flex-flex pairs.
  Instantiates the theorem and deletes trivial tpairs.  Resulting
  sequence may contain multiple elements if the tpairs are not all
  flex-flex.  The new theorems are computed by the generated code.*)
fun flexflex_rule opt_ctxt =
  solve_constraints #> (fn th =>
    let
      val Thm (der, {cert, constraints, shyps, hyps, ...}) = th;
      val (context, cert') = make_context_certificate [th] opt_ctxt cert;
      val ops =
        Bicompose_Generated.BOps
          (fn env => fn tus =>
            SOME ([], Bicompose_Generated.Ok (Seq.map (rpair []) (Unify.smash_unifiers context tus env))),
           fn xq => SOME ([], Bicompose_Generated.Ok (Seq.pull xq)),
           Name.variant_list []);
      fun smash (env, _) = SOME ([], Bicompose_Generated.Ok env);
      fun eval r = run context (fn () => (th, th)) r;
      val rep = rep_of th;
      fun mk (env, th') =
        if Envir.is_empty env then th
        else
          let
            val thy' = Context.certificate_theory cert' handle ERROR msg =>
              raise CONTEXT (msg, [], [], [th], Option.map Context.Proof opt_ctxt);
            fun zproof p = run_zproof (Bicompose_Generated.flexflex_zproof (ztypargs thy') rep env p);
            fun proof p =
              run_proof (fn () => (th, th)) (Bicompose_Generated.norm_proof_remove_types env p);
          in
            Thm (deriv_rule1 zproof proof der,
             {cert = cert',
              tags = [],
              maxidx = Bicompose_Generated.th_maxidx th',
              constraints = insert_constraints_env thy' env constraints,
              shyps = Envir.insert_sorts env shyps,
              hyps = hyps,
              tpairs = Bicompose_Generated.th_tpairs th',
              prop = Bicompose_Generated.th_prop th'})
          end;
      fun to_seq s =
        Seq.make (fn () =>
          (case eval (Bicompose_Generated.fpull ops smash rep s) of
            NONE => NONE
          | SOME (x, s') => SOME (mk x, to_seq s')));
    in to_seq (eval (Bicompose_Generated.flexflex_rule ops rep)) end);


(*Generalization of fixed variables
           A
  --------------------
  A[?'a/'a, ?x/x, ...]
*)

fun generalize (tfrees, frees) idx th =
  if Names.is_empty tfrees andalso Names.is_empty frees then th
  else
    let
      val Thm (der, {cert, constraints, shyps, hyps, prop, ...}) = th;
      val tfrees' = Names.list_set tfrees and frees' = Names.list_set frees;
      val rep = run1 th (G.generalize tfrees' frees' idx hyps (rep_of th));
      val zproof = run_zproof o G.zgeneralize_proof tfrees' frees' idx;
      val proof = G.generalize_proof tfrees' frees' idx prop;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert,
        tags = [],
        maxidx = G.th_maxidx rep,
        constraints = constraints,
        shyps = shyps,
        hyps = hyps,
        tpairs = G.th_tpairs rep,
        prop = G.th_prop rep})
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

(*Left-to-right replacements: ctpairs = [..., (vi, ti), ...].
  Instantiates distinct Vars by terms of same type.
  Does NOT normalize the resulting theorem!*)
fun gen_instantiate beta (instT, inst) th =
  if TVars.is_empty instT andalso Vars.is_empty inst then th
  else
    let
      val Thm (der, {cert, hyps, constraints, shyps, ...}) = th;
      val cert' = cert
        |> TVars.fold add_instT_cert instT
        |> Vars.fold add_inst_cert inst;
      val thy' =
        Context.certificate_theory cert' handle ERROR msg =>
          raise CONTEXT (msg, TVars.dest instT |> map #2, Vars.dest inst |> map #2, [th], NONE);
      val shyps' = shyps
        |> TVars.fold add_instT_sorts instT
        |> Vars.fold add_inst_sorts inst;
      val instT' = TVars.dest instT |> map (fn (v, Ctyp {T, maxidx, ...}) => (v, (T, maxidx)));
      val inst' = Vars.dest inst |> map (fn (v, Cterm {t, T, maxidx, ...}) => (v, (t, (T, maxidx))));
      val rep =
        (case G.instantiate (Sign.classes_of thy') beta instT' inst' (rep_of th) of
          SOME (_, G.Err (G.NOT_OF_SORT (_, S))) =>
            raise THM ("Type not of sort " ^ Syntax.string_of_sort_global thy' S, 0, [th])
        | SOME (_, G.Err (G.INST_CONFLICT (v as (_, T), u, U))) =>
            let
              fun pretty_typing t ty =
                Pretty.block [Syntax.pretty_term_global thy' t, Pretty.str " ::",
                  Pretty.brk 1, Syntax.pretty_typ_global thy' ty];
              val msg =
                Pretty.string_of (Pretty.big_list "instantiate: type conflict"
                 [Pretty.item [pretty_typing (Var v) T],
                  Pretty.item [pretty_typing u U]]);
            in raise THM (msg, 0, [th]) end
        | r => run1 th r);
      val constraints' =
        fold (fn ((_, S), (T, _)) => insert_constraints thy' (T, S)) instT' constraints;
      val Ts = map (fn (v, (T, _)) => (v, T)) instT';
      val ts = map (fn (v, (t, _)) => (v, t)) inst';
      fun zproof p = run_zproof (G.zinstantiate_proof (ztypargs thy') Ts ts p);
      fun proof p = G.instantiate_proof Ts ts p;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert',
        tags = [],
        maxidx = G.th_maxidx rep,
        constraints = constraints',
        shyps = shyps',
        hyps = hyps,
        tpairs = G.th_tpairs rep,
        prop = G.th_prop rep})
      |> solve_constraints
    end
    handle TYPE (msg, _, _) => raise THM (msg, 0, [th]);

val instantiate = gen_instantiate false;
val instantiate_beta = gen_instantiate true;

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
fun trivial (ct as Cterm {cert, t = A, sorts, ...}) =
  let
    val rep = run0 (G.trivial (ct_rep ct));
    fun zproof () = run_zproof (G.ztrivial_proof (ztypargs (thy_of cert [ct] [])) A);
    fun proof () = G.trivial_proof;
  in
    Thm (deriv_rule0 zproof proof,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = [],
      shyps = sorts,
      hyps = [],
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
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
    val Cterm {t = prop', sorts, ...} = global_cterm_of thy prop;

    fun zproof () = ZTerm.of_class_proof (T, c);
    fun proof () = Proofterm.PClass (T, c);
  in
    if prop <> prop' then raise THM ("of_class: bad proposition via cterm_of", 0, [])
    else
      (case G.of_class (Sign.classes_of thy) T c of
        SOME (_, G.Err (G.NOT_OF_SORT _)) =>
          raise THM ("of_class: type not of class " ^ Syntax.string_of_sort_global thy [c], 0, [])
      | r =>
          let val rep = run0 r in
            Thm (deriv_rule0 zproof proof,
             {cert = cert,
              tags = [],
              maxidx = G.th_maxidx rep,
              constraints = insert_constraints thy (T, [c]) [],
              shyps = sorts,
              hyps = [],
              tpairs = G.th_tpairs rep,
              prop = G.th_prop rep})
          end)
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
fun varifyT_global' fixed (th as Thm (der, {cert, constraints, shyps, hyps, ...})) =
  let
    val (al, rep) =
      run1 th (G.varifyT_global Name.variant_list (TFrees.list_set fixed) hyps (rep_of th));
    fun zproof p = run_zproof (G.zvarifyT_proof al p);
    fun proof p = G.varifyT_proof al p;
  in
    (al, Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep}))
  end;

val varifyT_global = #2 o varifyT_global' TFrees.empty;

(*Replace all TVars by TFrees that are often new*)
fun legacy_freezeT (th as Thm (der, {cert, constraints, shyps, hyps, tpairs, prop, ...})) =
  let
    val rep = run1 th (G.legacy_freezeT Name.variant_list (rep_of th));
    val prop1 = attach_tpairs tpairs prop;
    fun zproof p = run_zproof (G.zlegacy_freezeT_proof Name.variant_list prop1 p);
    fun proof p = G.legacy_freezeT_proof Name.variant_list prop1 p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
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


(*Prepare orule for resolution by lifting it over the parameters and
assumptions of goal.  The logical part of the lifted rule is computed by the generated code.*)
fun lift_rule goal orule =
  let
    val Cterm {t = gprop, T, maxidx = gmax, sorts, ...} = goal;
    val Thm (der, {maxidx, constraints, shyps, hyps, tpairs, prop, ...}) = orule;
  in
    if T <> propT then raise THM ("lift_rule: the term must have type prop", 0, [])
    else
      let
        val cert = join_certificate1 (goal, orule);
        val rep = Bicompose_Generated.make maxidx tpairs prop;
        fun zproof p =
          let
            val thy = Context.certificate_theory cert
              handle ERROR msg => raise CONTEXT (msg, [], [goal], [orule], NONE);
          in
            run_zproof (Bicompose_Generated.lift_rule_zproof (ztypargs thy) gprop gmax rep p)
          end;
        fun proof p = Bicompose_Generated.lift_rule_proof gprop gmax rep p;
        val lifted = Bicompose_Generated.lift_rule gprop gmax rep;
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

fun incr_indexes i (thm as Thm (der, {cert, constraints, shyps, hyps, ...})) =
  if i < 0 then raise THM ("negative increment", 0, [thm])
  else if i = 0 then thm
  else
    let
      val rep = run1 thm (G.incr_indexes_thm i (rep_of thm));
      fun zproof p = run_zproof (G.zincr_indexes_proof i p);
      fun proof p = G.incr_indexes_proof i p;
    in
      Thm (deriv_rule1 zproof proof der,
       {cert = cert,
        tags = [],
        maxidx = G.th_maxidx rep,
        constraints = constraints,
        shyps = shyps,
        hyps = hyps,
        tpairs = G.th_tpairs rep,
        prop = G.th_prop rep})
    end;



(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  The new theorems are computed by the generated code. *)
fun assumption opt_ctxt i state =
  let
    val Thm (der, {cert, constraints, shyps, hyps, ...}) = state;
    val (context, cert') = make_context_certificate [state] opt_ctxt cert;
    fun eval r = run context (fn () => (state, state)) r;
    val rep = rep_of state;
    val s0 = eval (Bicompose_Generated.assumption i rep);
    val ctx = Bicompose_Generated.aseq_ctx s0;
    fun mk (res as Bicompose_Generated.ARes (env, _, th')) =
      let
        val thy' = Context.certificate_theory cert' handle ERROR msg =>
          raise CONTEXT (msg, [], [], [state], Option.map Context.Proof opt_ctxt);
        fun zproof p = run_zproof (Bicompose_Generated.ares_zproof (ztypargs thy') rep ctx res p);
        fun proof p = run_proof (fn () => (state, state)) (Bicompose_Generated.ares_proof ctx res p);
      in
        Thm (deriv_rule1 zproof proof der,
         {tags = [],
          maxidx = Bicompose_Generated.th_maxidx th',
          constraints = insert_constraints_env thy' env constraints,
          shyps = Envir.insert_sorts env shyps,
          hyps = hyps,
          tpairs = Bicompose_Generated.th_tpairs th',
          prop = Bicompose_Generated.th_prop th',
          cert = cert'})
      end;
    fun to_seq s =
      Seq.make (fn () =>
        (case eval (Bicompose_Generated.apull (ops context) s) of
          NONE => NONE
        | SOME (res, s') => SOME (mk res, to_seq s')));
  in to_seq s0 end;

(*Solve subgoal Bi of proof state B1...Bn/C by assumption.
  Checks if Bi's conclusion is alpha/eta-convertible to one of its assumptions.
  The new theorem is computed by the generated code.*)
fun eq_assumption i state =
  let
    val Thm (der, {cert, constraints, shyps, hyps, ...}) = state;
    val (n, th') =
      run_with (K ()) (fn () => (state, state)) (Bicompose_Generated.eq_assumption i (rep_of state));
    val (_, Bs, Bi, _) = dest_state (state, i);
    fun zproof p =
      let
        val thy = Context.certificate_theory cert
          handle ERROR msg => raise CONTEXT (msg, [], [], [state], NONE);
      in run_zproof (Bicompose_Generated.eq_assumption_zproof (ztypargs thy) Bs Bi n p) end;
    fun proof p = Bicompose_Generated.assumption_proof Bs Bi n p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = Bicompose_Generated.th_maxidx th',
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = Bicompose_Generated.th_tpairs th',
      prop = Bicompose_Generated.th_prop th'})
  end;



(*For rotate_tac: fast rotation of assumptions of subgoal i*)
fun rotate_rule k i state =
  let
    val Thm (der, {cert, constraints, shyps, hyps, ...}) = state;
    val (rep, (Bs, (Bi', (params, (asms, m))))) = run1 state (G.rotate_data k i (rep_of state));
    fun zproof p =
      run_zproof (G.zrotate_proof (ztypargs (thy_of cert [] [state])) Bs Bi' params asms m p);
    fun proof p = G.rotate_proof Bs Bi' params asms m p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;


(*Rotates a rule's premises to the left by k, leaving the first j premises
  unchanged.  Does nothing if k=0 or if k equals n-j, where n is the
  number of premises.  Useful with eresolve_tac and underlies defer_tac*)
fun permute_prems j k rl =
  let
    val Thm (der, {cert, constraints, shyps, hyps, ...}) = rl;
    val (rep, (prems', m)) = run1 rl (G.permute_data j k (rep_of rl));
    fun zproof p =
      run_zproof (G.zpermute_prems_proof (ztypargs (thy_of cert [] [rl])) prems' j m p);
    fun proof p = G.permute_prems_proof prems' j m p;
  in
    Thm (deriv_rule1 zproof proof der,
     {cert = cert,
      tags = [],
      maxidx = G.th_maxidx rep,
      constraints = constraints,
      shyps = shyps,
      hyps = hyps,
      tpairs = G.th_tpairs rep,
      prop = G.th_prop rep})
  end;



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

fun mk_thm opt_ctxt cert flatten (state, Bs, nlift) orule
    (res as G.BRes (env, ntpairs, prop, _, _)) =
  let
    val Thm (sder, {constraints = constraints2, shyps = shyps2, hyps = hyps2, ...}) = state
    and Thm (rder, {constraints = constraints1, shyps = shyps1, hyps = hyps1, ...}) = orule;
    val thy' = Context.certificate_theory cert handle ERROR msg =>
      raise CONTEXT (msg, [], [], [state, orule], Option.map Context.Proof opt_ctxt);
    val constraints' =
      union_constraints constraints1 constraints2
      |> insert_constraints_env thy' env;
    fun zproof p q =
      run_zproof
        (G.bres_zproof (ztypargs thy') (rep_of state) Bs nlift flatten (rep_of orule) res p q);
    fun proof p q =
      run_proof (fn () => (state, orule)) (G.bres_proof (rep_of state) Bs nlift flatten res p q);
  in
    Thm (deriv_rule2 zproof proof rder sder,
     {tags = [],
      maxidx = Envir.maxidx_of env,
      constraints = constraints',
      shyps = Envir.insert_sorts env (Sorts.union shyps1 shyps2),
      hyps = union_hyps hyps1 hyps2,
      tpairs = ntpairs,
      prop = prop,
      cert = cert})
  end;

in

fun bicompose_aux opt_ctxt {flatten, match, incremented} (state, (stpairs, Bs, Bi, C), lifted)
    (eres_flg, orule, nsubgoal) =
  let
    val Thm (_, {maxidx=smax, tpairs = stpairs0, prop = sprop, ...}) = state
    and Thm (_, {maxidx=rmax, tpairs = rtpairs, prop = rprop, ...}) = orule
    (*How many hyps to skip over during normalization*)
    and nlift = G.bres_nlift Bi eres_flg;
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
  Puts the rule above:  rule/state.  Renames vars in the rules. *)
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
            SOME (mk_thm opt_ctxt cert true (state, Bs, G.bres_nlift Bi eres_flg) (Lazy.force orule) res,
              to_seq s'))
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
