(*  Title:      Pure/theory.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel
    Copyright   1996  University of Cambridge

Theories
*)

signature THEORY =
  sig
  type theory
  exception THEORY of string * theory list
  val rep_theory        : theory ->
    {sign: Sign.sg, oraopt: (Sign.sg * exn -> term) option,
     new_axioms: term Symtab.table, parents: theory list}
  val sign_of           : theory -> Sign.sg
  val syn_of            : theory -> Syntax.syntax
  val stamps_of_thy     : theory -> string ref list
  val parents_of        : theory -> theory list
  val subthy            : theory * theory -> bool
  val eq_thy            : theory * theory -> bool
  val proto_pure_thy    : theory
  val pure_thy          : theory
  val cpure_thy         : theory
  (*theory primitives*)
  val add_classes	: (class * class list) list -> theory -> theory
  val add_classrel	: (class * class) list -> theory -> theory
  val add_defsort	: sort -> theory -> theory
  val add_types		: (string * int * mixfix) list -> theory -> theory
  val add_tyabbrs	: (string * string list * string * mixfix) list
    -> theory -> theory
  val add_tyabbrs_i	: (string * string list * typ * mixfix) list
    -> theory -> theory
  val add_arities	: (string * sort list * sort) list -> theory -> theory
  val add_consts	: (string * string * mixfix) list -> theory -> theory
  val add_consts_i	: (string * typ * mixfix) list -> theory -> theory
  val add_syntax	: (string * string * mixfix) list -> theory -> theory
  val add_syntax_i	: (string * typ * mixfix) list -> theory -> theory
  val add_trfuns	:
    (string * (Syntax.ast list -> Syntax.ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (Syntax.ast list -> Syntax.ast)) list -> theory -> theory
  val add_trrules     : (string * string)Syntax.trrule list -> theory -> theory
  val add_trrules_i	: Syntax.ast Syntax.trrule list -> theory -> theory
  val cert_axm          : Sign.sg -> string * term -> string * term
  val read_axm          : Sign.sg -> string * string -> string * term
  val inferT_axm        : Sign.sg -> string * term -> string * term
  val add_axioms	: (string * string) list -> theory -> theory
  val add_axioms_i	: (string * term) list -> theory -> theory
  val add_thyname	: string -> theory -> theory

  val set_oracle	: (Sign.sg * exn -> term) -> theory -> theory

  val merge_theories    : theory * theory -> theory
  val merge_thy_list    : bool -> theory list -> theory
end;


structure Theory : THEORY =
struct
(*** Theories ***)

datatype theory =
  Theory of {
    sign: Sign.sg,
    oraopt: (Sign.sg * exn -> term) option,
    new_axioms: term Symtab.table,
    parents: theory list};

fun rep_theory (Theory args) = args;

(*errors involving theories*)
exception THEORY of string * theory list;


val sign_of = #sign o rep_theory;
val syn_of = #syn o Sign.rep_sg o sign_of;

(*stamps associated with a theory*)
val stamps_of_thy = #stamps o Sign.rep_sg o sign_of;

(*return the immediate ancestors*)
val parents_of = #parents o rep_theory;


(*compare theories*)
val subthy = Sign.subsig o pairself sign_of;
val eq_thy = Sign.eq_sg o pairself sign_of;


(* the Pure theories *)

val proto_pure_thy =
  Theory {sign = Sign.proto_pure, oraopt = None, 
	  new_axioms = Symtab.null, parents = []};

val pure_thy =
  Theory {sign = Sign.pure, oraopt = None, 
	  new_axioms = Symtab.null, parents = []};

val cpure_thy =
  Theory {sign = Sign.cpure, oraopt = None, 
	  new_axioms = Symtab.null, parents = []};



(** extend theory **)

fun err_dup_axms names =
  error ("Duplicate axiom name(s) " ^ commas_quote names);

fun ext_thy (thy as Theory {sign, oraopt, new_axioms, parents}) 
            sign1 new_axms =
  let
    val draft = Sign.is_draft sign;
    val new_axioms1 =
      Symtab.extend_new (if draft then new_axioms else Symtab.null, new_axms)
        handle Symtab.DUPS names => err_dup_axms names;
    val parents1 = if draft then parents else [thy];
  in
    Theory {sign = sign1, oraopt = oraopt, 
	    new_axioms = new_axioms1, parents = parents1}
  end;


(* extend signature of a theory *)

fun ext_sg extfun decls (thy as Theory {sign, ...}) =
  ext_thy thy (extfun decls sign) [];

val add_classes   = ext_sg Sign.add_classes;
val add_classrel  = ext_sg Sign.add_classrel;
val add_defsort   = ext_sg Sign.add_defsort;
val add_types     = ext_sg Sign.add_types;
val add_tyabbrs   = ext_sg Sign.add_tyabbrs;
val add_tyabbrs_i = ext_sg Sign.add_tyabbrs_i;
val add_arities   = ext_sg Sign.add_arities;
val add_consts    = ext_sg Sign.add_consts;
val add_consts_i  = ext_sg Sign.add_consts_i;
val add_syntax    = ext_sg Sign.add_syntax;
val add_syntax_i  = ext_sg Sign.add_syntax_i;
val add_trfuns    = ext_sg Sign.add_trfuns;
val add_trrules   = ext_sg Sign.add_trrules;
val add_trrules_i = ext_sg Sign.add_trrules_i;
val add_thyname   = ext_sg Sign.add_name;


(* prepare axioms *)

fun err_in_axm name =
  error ("The error(s) above occurred in axiom " ^ quote name);

fun no_vars tm =
  if null (term_vars tm) andalso null (term_tvars tm) then tm
  else error "Illegal schematic variable(s) in term";

fun cert_axm sg (name, raw_tm) =
  let
    val (t, T, _) = Sign.certify_term sg raw_tm
      handle TYPE arg => error (Sign.exn_type_msg sg arg)
	   | TERM (msg, _) => error msg;
  in
    assert (T = propT) "Term not of type prop";
    (name, no_vars t)
  end
  handle ERROR => err_in_axm name;

(*Some duplication of code with read_def_cterm*)
fun read_axm sg (name, str) = 
  let val ts = Syntax.read (#syn (Sign.rep_sg sg)) propT str;
      val (_, t, _) =
          Sign.infer_types sg (K None) (K None) [] true (ts,propT);
  in cert_axm sg (name,t) end;

fun inferT_axm sg (name, pre_tm) =
  let val t = #2(Sign.infer_types sg (K None) (K None) [] true
                                     ([pre_tm], propT))
  in  (name, no_vars t) end
  handle ERROR => err_in_axm name;


(* extend axioms of a theory *)

fun ext_axms prep_axm axms (thy as Theory {sign, ...}) =
  let
    val sign1 = Sign.make_draft sign;
    val axioms = map (apsnd (Term.compress_term o Logic.varify) o 
		      prep_axm sign) 
	         axms;
  in
    ext_thy thy sign1 axioms
  end;

val add_axioms = ext_axms read_axm;
val add_axioms_i = ext_axms cert_axm;


(** Set oracle of theory **)

fun set_oracle oracle 
               (thy as Theory {sign, oraopt = None, new_axioms, parents}) =
      if Sign.is_draft sign then
	Theory {sign = sign, 
		oraopt = Some oracle, 
		new_axioms = new_axioms, 
		parents = parents}
      else raise THEORY ("Can only set oracle of a draft", [thy])
  | set_oracle _ thy = raise THEORY ("Oracle already set", [thy]);


(** merge theories **)

fun merge_thy_list mk_draft thys =
  let
    fun is_union thy = forall (fn t => subthy (t, thy)) thys;
    val is_draft = Sign.is_draft o sign_of;

    fun add_sign (sg, Theory {sign, ...}) =
      Sign.merge (sg, sign) handle TERM (msg, _) => error msg;
  in
    case (find_first is_union thys, exists is_draft thys) of
      (Some thy, _) => thy
    | (None, true) => raise THEORY ("Illegal merge of draft theories", thys)
    | (None, false) => Theory {
        sign =
          (if mk_draft then Sign.make_draft else I)
          (foldl add_sign (Sign.proto_pure, thys)),
	oraopt = None,
        new_axioms = Symtab.null,
        parents = thys}
  end;

fun merge_theories (thy1, thy2) = merge_thy_list false [thy1, thy2];


end;

open Theory;
