(*  Title:      Pure/theory.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel
    Copyright   1996  University of Cambridge

Theories.
*)

(*this part made pervasive*)
signature BASIC_THEORY =
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
  val cert_axm          : Sign.sg -> string * term -> string * term
  val read_axm          : Sign.sg -> string * string -> string * term
  val inferT_axm        : Sign.sg -> string * term -> string * term
  val merge_theories    : theory * theory -> theory
end

signature THEORY =
sig
  include BASIC_THEORY
  (*theory extendsion primitives*)
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
  val add_modesyntax	: string * bool -> (string * string * mixfix) list -> theory -> theory
  val add_modesyntax_i	: string * bool -> (string * typ * mixfix) list -> theory -> theory
  val add_trfuns	:
    (string * (Syntax.ast list -> Syntax.ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (Syntax.ast list -> Syntax.ast)) list -> theory -> theory
  val add_trfunsT	:
    (string * (typ -> term list -> term)) list -> theory -> theory
  val add_tokentrfuns:
    (string * string * (string -> string * int)) list -> theory -> theory
  val add_trrules     : (string * string)Syntax.trrule list -> theory -> theory
  val add_trrules_i	: Syntax.ast Syntax.trrule list -> theory -> theory
  val add_axioms	: (string * string) list -> theory -> theory
  val add_axioms_i	: (string * term) list -> theory -> theory
  val add_defs		: (string * string) list -> theory -> theory
  val add_defs_i	: (string * term) list -> theory -> theory
  val add_name		: string -> theory -> theory

  val set_oracle	: (Sign.sg * exn -> term) -> theory -> theory

  val merge_thy_list    : bool -> theory list -> theory
end;


structure Theory: THEORY =
struct

(** datatype theory **)

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

val add_classes      = ext_sg Sign.add_classes;
val add_classrel     = ext_sg Sign.add_classrel;
val add_defsort      = ext_sg Sign.add_defsort;
val add_types        = ext_sg Sign.add_types;
val add_tyabbrs      = ext_sg Sign.add_tyabbrs;
val add_tyabbrs_i    = ext_sg Sign.add_tyabbrs_i;
val add_arities      = ext_sg Sign.add_arities;
val add_consts       = ext_sg Sign.add_consts;
val add_consts_i     = ext_sg Sign.add_consts_i;
val add_syntax       = ext_sg Sign.add_syntax;
val add_syntax_i     = ext_sg Sign.add_syntax_i;
val add_modesyntax   = curry (ext_sg Sign.add_modesyntax);
val add_modesyntax_i = curry (ext_sg Sign.add_modesyntax_i);
val add_trfuns       = ext_sg Sign.add_trfuns;
val add_trfunsT      = ext_sg Sign.add_trfunsT;
val add_tokentrfuns  = ext_sg Sign.add_tokentrfuns;
val add_trrules      = ext_sg Sign.add_trrules;
val add_trrules_i    = ext_sg Sign.add_trrules_i;
val add_name         = ext_sg Sign.add_name;


(* prepare axioms *)

fun err_in_axm name =
  error ("The error(s) above occurred in axiom " ^ quote name);

fun no_vars tm =
  if null (term_vars tm) andalso null (term_tvars tm) then tm
  else error "Illegal schematic variable(s) in term";

fun cert_axm sg (name, raw_tm) =
  let
    val (t, T, _) = Sign.certify_term sg raw_tm
      handle TYPE (msg, _, _) => error msg
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
  in cert_axm sg (name,t) end
  handle ERROR => err_in_axm name;

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



(** add constant definitions **)

(* all_axioms_of *)

(*results may contain duplicates!*)

fun ancestry_of thy =
  thy :: List.concat (map ancestry_of (parents_of thy));

val all_axioms_of =
  List.concat o map (Symtab.dest o #new_axioms o rep_theory) o ancestry_of;


(* clash_types, clash_consts *)

(*check if types have common instance (ignoring sorts)*)

fun clash_types ty1 ty2 =
  let
    val ty1' = Type.varifyT ty1;
    val ty2' = incr_tvar (maxidx_of_typ ty1' + 1) (Type.varifyT ty2);
  in
    Type.raw_unify (ty1', ty2')
  end;

fun clash_consts (c1, ty1) (c2, ty2) =
  c1 = c2 andalso clash_types ty1 ty2;


(* clash_defns *)

fun clash_defn c_ty (name, tm) =
  let val (c, ty') = dest_Const (head_of (fst (Logic.dest_equals tm))) in
    if clash_consts c_ty (c, ty') then Some (name, ty') else None
  end handle TERM _ => None;

fun clash_defns c_ty axms =
  distinct (mapfilter (clash_defn c_ty) axms);


(* dest_defn *)

fun dest_defn tm =
  let
    fun err msg = raise_term msg [tm];

    val (lhs, rhs) = Logic.dest_equals (Logic.strip_imp_concl tm)
      handle TERM _ => err "Not a meta-equality (==)";
    val (head, args) = strip_comb lhs;
    val (c, ty) = dest_Const head
      handle TERM _ => err "Head of lhs not a constant";

    fun occs_const (Const c_ty') = (c_ty' = (c, ty))
      | occs_const (Abs (_, _, t)) = occs_const t
      | occs_const (t $ u) = occs_const t orelse occs_const u
      | occs_const _ = false;

    val show_frees = commas_quote o map (fst o dest_Free);
    val show_tfrees = commas_quote o map fst;

    val lhs_dups = duplicates args;
    val rhs_extras = gen_rems (op =) (term_frees rhs, args);
    val rhs_extrasT = gen_rems (op =) (term_tfrees rhs, typ_tfrees ty);
  in
    if not (forall is_Free args) then
      err "Arguments (on lhs) must be variables"
    else if not (null lhs_dups) then
      err ("Duplicate variables on lhs: " ^ show_frees lhs_dups)
    else if not (null rhs_extras) then
      err ("Extra variables on rhs: " ^ show_frees rhs_extras)
    else if not (null rhs_extrasT) then
      err ("Extra type variables on rhs: " ^ show_tfrees rhs_extrasT)
    else if occs_const rhs then
      err ("Constant to be defined occurs on rhs")
    else (c, ty)
  end;


(* check_defn *)

fun err_in_defn name msg =
  (writeln msg; error ("The error(s) above occurred in definition " ^ quote name));

fun check_defn sign (axms, (name, tm)) =
  let
    fun show_const (c, ty) = quote (Pretty.string_of (Pretty.block
      [Pretty.str (c ^ " ::"), Pretty.brk 1, Sign.pretty_typ sign ty]));

    fun show_defn c (dfn, ty') = show_const (c, ty') ^ " in " ^ dfn;
    fun show_defns c = cat_lines o map (show_defn c);

    val (c, ty) = dest_defn tm
      handle TERM (msg, _) => err_in_defn name msg;
    val defns = clash_defns (c, ty) axms;
  in
    if not (null defns) then
      err_in_defn name ("Definition of " ^ show_const (c, ty) ^
        "\nclashes with " ^ show_defns c defns)
    else (name, tm) :: axms
  end;


(* add_defs *)

fun ext_defns prep_axm raw_axms thy =
  let
    val axms = map (prep_axm (sign_of thy)) raw_axms;
    val all_axms = all_axioms_of thy;
  in
    foldl (check_defn (sign_of thy)) (all_axms, axms);
    add_axioms_i axms thy
  end;

val add_defs_i = ext_defns cert_axm;
val add_defs = ext_defns read_axm;



(** Set oracle of theory **)

(* FIXME support more than one oracle (!?) *)

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

structure BasicTheory: BASIC_THEORY = Theory;
open BasicTheory;
