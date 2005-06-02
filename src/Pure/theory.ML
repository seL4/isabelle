(*  Title:      Pure/theory.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

The abstract type "theory" of theories.
*)
signature BASIC_THEORY =
sig
  type theory
  exception THEORY of string * theory list
  val rep_theory: theory ->
    {sign: Sign.sg,
      const_deps: Defs.graph,
      axioms: term Symtab.table,
      oracles: ((Sign.sg * Object.T -> term) * stamp) Symtab.table,
      parents: theory list,
      ancestors: theory list}
  val sign_of: theory -> Sign.sg
  val is_draft: theory -> bool
  val syn_of: theory -> Syntax.syntax
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val subthy: theory * theory -> bool
  val eq_thy: theory * theory -> bool
  val cert_axm: Sign.sg -> string * term -> string * term
  val read_def_axm: Sign.sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> string * string -> string * term
  val read_axm: Sign.sg -> string * string -> string * term
  val inferT_axm: Sign.sg -> string * term -> string * term
end

signature THEORY =
sig
  include BASIC_THEORY
  val axiomK: string
  val oracleK: string
  (*theory extension primitives*)
  val add_classes: (bclass * xclass list) list -> theory -> theory
  val add_classes_i: (bclass * class list) list -> theory -> theory
  val add_classrel: (xclass * xclass) list -> theory -> theory
  val add_classrel_i: (class * class) list -> theory -> theory
  val add_defsort: string -> theory -> theory
  val add_defsort_i: sort -> theory -> theory
  val add_types: (bstring * int * mixfix) list -> theory -> theory
  val add_nonterminals: bstring list -> theory -> theory
  val add_tyabbrs: (bstring * string list * string * mixfix) list
    -> theory -> theory
  val add_tyabbrs_i: (bstring * string list * typ * mixfix) list
    -> theory -> theory
  val add_arities: (xstring * string list * string) list -> theory -> theory
  val add_arities_i: (string * sort list * sort) list -> theory -> theory
  val add_consts: (bstring * string * mixfix) list -> theory -> theory
  val add_consts_i: (bstring * typ * mixfix) list -> theory -> theory
  val add_syntax: (bstring * string * mixfix) list -> theory -> theory
  val add_syntax_i: (bstring * typ * mixfix) list -> theory -> theory
  val add_modesyntax: string * bool -> (bstring * string * mixfix) list -> theory -> theory
  val add_modesyntax_i: string * bool -> (bstring * typ * mixfix) list -> theory -> theory
  val del_modesyntax: string * bool -> (bstring * string * mixfix) list -> theory -> theory
  val del_modesyntax_i: string * bool -> (bstring * typ * mixfix) list -> theory -> theory
  val add_trfuns:
    (string * (Syntax.ast list -> Syntax.ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (Syntax.ast list -> Syntax.ast)) list -> theory -> theory
  val add_trfunsT:
    (string * (bool -> typ -> term list -> term)) list -> theory -> theory
  val add_advanced_trfuns:
    (string * (Sign.sg -> Syntax.ast list -> Syntax.ast)) list *
    (string * (Sign.sg -> term list -> term)) list *
    (string * (Sign.sg -> term list -> term)) list *
    (string * (Sign.sg -> Syntax.ast list -> Syntax.ast)) list -> theory -> theory
  val add_advanced_trfunsT:
    (string * (Sign.sg -> bool -> typ -> term list -> term)) list -> theory -> theory
  val add_tokentrfuns:
    (string * string * (string -> string * real)) list -> theory -> theory
  val add_mode_tokentrfuns: string -> (string * (string -> string * real)) list
    -> theory -> theory
  val add_trrules: (xstring * string) Syntax.trrule list -> theory -> theory
  val add_trrules_i: Syntax.ast Syntax.trrule list -> theory -> theory
  val add_axioms: (bstring * string) list -> theory -> theory
  val add_axioms_i: (bstring * term) list -> theory -> theory
  val add_oracle: bstring * (Sign.sg * Object.T -> term) -> theory -> theory
  val add_finals: bool -> string list -> theory -> theory
  val add_finals_i: bool -> term list -> theory -> theory
  val add_defs: bool -> (bstring * string) list -> theory -> theory
  val add_defs_i: bool -> (bstring * term) list -> theory -> theory
  val add_path: string -> theory -> theory
  val parent_path: theory -> theory
  val root_path: theory -> theory
  val absolute_path: theory -> theory
  val qualified_names: theory -> theory
  val no_base_names: theory -> theory
  val custom_accesses: (string list -> string list list) -> theory -> theory
  val set_policy: (string -> bstring -> string) * (string list -> string list list) ->
    theory -> theory
  val restore_naming: theory -> theory -> theory
  val hide_space: bool -> string * xstring list -> theory -> theory
  val hide_space_i: bool -> string * string list -> theory -> theory
  val hide_classes: bool -> string list -> theory -> theory
  val hide_types: bool -> string list -> theory -> theory
  val hide_consts: bool -> string list -> theory -> theory
  val add_name: string -> theory -> theory
  val copy: theory -> theory
  val prep_ext: theory -> theory
  val prep_ext_merge: theory list -> theory
  val requires: theory -> string -> string -> unit
  val assert_super: theory -> theory -> theory
  val pre_pure: theory
end;

signature PRIVATE_THEORY =
sig
  include THEORY
  val init_data: Object.kind -> (Object.T * (Object.T -> Object.T) * (Object.T -> Object.T) *
    (Object.T * Object.T -> Object.T) * (Sign.sg -> Object.T -> unit)) -> theory -> theory
  val print_data: Object.kind -> theory -> unit
  val get_data: Object.kind -> (Object.T -> 'a) -> theory -> 'a
  val put_data: Object.kind -> ('a -> Object.T) -> 'a -> theory -> theory
end;


structure Theory: PRIVATE_THEORY =
struct


(** datatype theory **)

datatype theory =
  Theory of {
    sign: Sign.sg,
    const_deps: Defs.graph,
    axioms: term Symtab.table,
    oracles: ((Sign.sg * Object.T -> term) * stamp) Symtab.table,
    parents: theory list,
    ancestors: theory list};

fun make_theory sign const_deps axioms oracles parents ancestors =
  Theory {sign = sign, const_deps = const_deps, axioms = axioms,
    oracles = oracles, parents = parents, ancestors = ancestors};

fun rep_theory (Theory args) = args;

val sign_of = #sign o rep_theory;
val is_draft = Sign.is_draft o sign_of;
val syn_of = Sign.syn_of o sign_of;
val parents_of = #parents o rep_theory;
val ancestors_of = #ancestors o rep_theory;

(*errors involving theories*)
exception THEORY of string * theory list;

(*compare theories*)
val subthy = Sign.subsig o pairself sign_of;
val eq_thy = Sign.eq_sg o pairself sign_of;

(*check for some theory*)
fun requires thy name what =
  if Sign.exists_stamp name (sign_of thy) then ()
  else error ("Require theory " ^ quote name ^ " as an ancestor for " ^ what);

fun assert_super thy1 thy2 =
  if subthy (thy1, thy2) then thy2
  else raise THEORY ("Not a super theory", [thy1, thy2]);

(*partial Pure theory*)
val pre_pure =
  make_theory Sign.pre_pure Defs.empty Symtab.empty Symtab.empty [] [];



(** extend theory **)

(*name spaces*)
val axiomK = "axiom";
val oracleK = "oracle";


(* extend logical part of a theory *)

fun err_dup_axms names =
  error ("Duplicate axiom name(s): " ^ commas_quote names);

fun err_dup_oras names =
  error ("Duplicate oracles: " ^ commas_quote names);

fun ext_theory thy ext_sg new_axms new_oras =
  let
    val Theory {sign, const_deps, axioms, oracles, parents, ancestors} = thy;
    val draft = Sign.is_draft sign;
    val axioms' =
      Symtab.extend (if draft then axioms else Symtab.empty, new_axms)
        handle Symtab.DUPS names => err_dup_axms names;
    val oracles' =
      Symtab.extend (oracles, new_oras)
        handle Symtab.DUPS names => err_dup_oras names;
    val (parents', ancestors') =
      if draft then (parents, ancestors) else ([thy], thy :: ancestors);
  in
    make_theory (ext_sg sign) const_deps axioms' oracles' parents' ancestors'
  end;


(* extend signature of a theory *)

fun ext_sign ext_sg args thy = ext_theory thy (ext_sg args) [] [];

val add_classes            = ext_sign Sign.add_classes;
val add_classes_i          = ext_sign Sign.add_classes_i;
val add_classrel           = ext_sign Sign.add_classrel;
val add_classrel_i         = ext_sign Sign.add_classrel_i;
val add_defsort            = ext_sign Sign.add_defsort;
val add_defsort_i          = ext_sign Sign.add_defsort_i;
val add_types              = ext_sign Sign.add_types;
val add_nonterminals       = ext_sign Sign.add_nonterminals;
val add_tyabbrs            = ext_sign Sign.add_tyabbrs;
val add_tyabbrs_i          = ext_sign Sign.add_tyabbrs_i;
val add_arities            = ext_sign Sign.add_arities;
val add_arities_i          = ext_sign Sign.add_arities_i;
val add_consts             = ext_sign Sign.add_consts;
val add_consts_i           = ext_sign Sign.add_consts_i;
val add_syntax             = ext_sign Sign.add_syntax;
val add_syntax_i           = ext_sign Sign.add_syntax_i;
val add_modesyntax         = curry (ext_sign Sign.add_modesyntax);
val add_modesyntax_i       = curry (ext_sign Sign.add_modesyntax_i);
val del_modesyntax         = curry (ext_sign Sign.del_modesyntax);
val del_modesyntax_i       = curry (ext_sign Sign.del_modesyntax_i);
val add_trfuns             = ext_sign Sign.add_trfuns;
val add_trfunsT            = ext_sign Sign.add_trfunsT;
val add_advanced_trfuns    = ext_sign Sign.add_advanced_trfuns;
val add_advanced_trfunsT   = ext_sign Sign.add_advanced_trfunsT;
val add_tokentrfuns        = ext_sign Sign.add_tokentrfuns;
fun add_mode_tokentrfuns m = add_tokentrfuns o map (fn (s, f) => (m, s, f));
val add_trrules            = ext_sign Sign.add_trrules;
val add_trrules_i          = ext_sign Sign.add_trrules_i;
val add_path               = ext_sign Sign.add_path;
val parent_path            = add_path "..";
val root_path              = add_path "/";
val absolute_path          = add_path "//";
val qualified_names        = ext_sign (K Sign.qualified_names) ();
val no_base_names          = ext_sign (K Sign.no_base_names) ();
val custom_accesses        = ext_sign Sign.custom_accesses;
val set_policy             = ext_sign Sign.set_policy;
val restore_naming         = ext_sign Sign.restore_naming o sign_of;
val add_space              = ext_sign Sign.add_space;
val hide_space             = ext_sign o Sign.hide_space;
val hide_space_i           = ext_sign o Sign.hide_space_i;
fun hide_classes b         = curry (hide_space_i b) Sign.classK;
fun hide_types b           = curry (hide_space_i b) Sign.typeK;
fun hide_consts b          = curry (hide_space_i b) Sign.constK;
val add_name               = ext_sign Sign.add_name;
val copy                   = ext_sign (K Sign.copy) ();
val prep_ext               = ext_sign (K Sign.prep_ext) ();



(** add axioms **)

(* prepare axioms *)

fun err_in_axm name =
  error ("The error(s) above occurred in axiom " ^ quote name);

fun no_vars sg tm = (case (term_vars tm, term_tvars tm) of
    ([], []) => tm
  | (ts, ixns) => error (Pretty.string_of (Pretty.block (Pretty.breaks
      (Pretty.str "Illegal schematic variable(s) in term:" ::
       map (Sign.pretty_term sg) ts @
       map (Sign.pretty_typ sg o TVar) ixns)))));

fun cert_axm sg (name, raw_tm) =
  let
    val (t, T, _) = Sign.certify_term (Sign.pp sg) sg raw_tm
      handle TYPE (msg, _, _) => error msg
           | TERM (msg, _) => error msg;
  in
    Term.no_dummy_patterns t handle TERM (msg, _) => error msg;
    assert (T = propT) "Term not of type prop";
    (name, no_vars sg t)
  end;

(*some duplication of code with read_def_cterm*)
fun read_def_axm (sg, types, sorts) used (name, str) =
  let
    val ts = Syntax.read (Sign.is_logtype sg) (Sign.syn_of sg) propT str;
    val (t, _) = Sign.infer_types (Sign.pp sg) sg types sorts used true (ts, propT);
  in cert_axm sg (name, t) end
  handle ERROR => err_in_axm name;

fun read_axm sg name_str = read_def_axm (sg, K NONE, K NONE) [] name_str;

fun inferT_axm sg (name, pre_tm) =
  let val (t, _) = Sign.infer_types (Sign.pp sg) sg
    (K NONE) (K NONE) [] true ([pre_tm], propT);
  in (name, no_vars sg t) end
  handle ERROR => err_in_axm name;


(* extend axioms of a theory *)

fun ext_axms prep_axm raw_axms (thy as Theory {sign, ...}) =
  let
    val raw_axms' = map (apfst (Sign.full_name sign)) raw_axms;
    val axioms =
      map (apsnd (Term.compress_term o Logic.varify) o prep_axm sign) raw_axms';
    val ext_sg = Sign.add_space (axiomK, map fst axioms);
  in ext_theory thy ext_sg axioms [] end;

val add_axioms = ext_axms read_axm;
val add_axioms_i = ext_axms cert_axm;


(* add oracle **)

fun add_oracle (raw_name, oracle) (thy as Theory {sign, ...}) =
  let
    val name = Sign.full_name sign raw_name;
    val ext_sg = Sign.add_space (oracleK, [name]);
  in ext_theory thy ext_sg [] [(name, (oracle, stamp ()))] end;



(** add constant definitions **)

(* clash_types, clash_consts *)

(*check if types have common instance (ignoring sorts)

fun clash_types ty1 ty2 =
  let
    val ty1' = Type.varifyT ty1;
    val ty2' = incr_tvar (maxidx_of_typ ty1' + 1) (Type.varifyT ty2);
  in Type.raw_unify (ty1', ty2') end;

fun clash_consts (c1, ty1) (c2, ty2) =
  c1 = c2 andalso clash_types ty1 ty2;
*)


(* clash_defns 

fun clash_defn c_ty (name, tm) =
  let val (c, ty') = dest_Const (head_of (fst (Logic.dest_equals (Logic.strip_imp_concl tm)))) in
    if clash_consts c_ty (c, ty') then SOME (name, ty') else NONE
  end handle TERM _ => NONE;

fun clash_defns c_ty axms =
  distinct (List.mapPartial (clash_defn c_ty) axms);
*)


(* overloading *)

datatype overloading = NoOverloading | Useless | Plain;

fun overloading sg declT defT =
  let val T = Term.incr_tvar (maxidx_of_typ declT + 1) (Type.varifyT defT) in
    if Sign.typ_instance sg (declT, T) then NoOverloading
    else if Sign.typ_instance sg (Type.strip_sorts declT, Type.strip_sorts T) then Useless
    else Plain
  end;


(* dest_defn *)

fun dest_defn tm =
  let
    fun err msg = raise TERM (msg, [tm]);

    val (lhs, rhs) = Logic.dest_equals (Logic.strip_imp_concl tm)
      handle TERM _ => err "Not a meta-equality (==)";
    val (head, args) = strip_comb lhs;
    val c_ty as (c, ty) = dest_Const head
      handle TERM _ => err "Head of lhs not a constant";

    fun dest_free (Free (x, _)) = x
      | dest_free (Const ("TYPE", Type ("itself", [TFree (x, _)]))) = x
      | dest_free _ = raise Match;

    val show_frees = commas_quote o map dest_free;
    val show_tfrees = commas_quote o map fst;

    val lhs_dups = duplicates args;
    val rhs_extras = gen_rems (op =) (term_frees rhs, args);
    val rhs_extrasT = gen_rems (op =) (term_tfrees rhs, typ_tfrees ty);
  in
    if not (forall (can dest_free) args) then
      err "Arguments (on lhs) must be variables"
    else if not (null lhs_dups) then
      err ("Duplicate variables on lhs: " ^ show_frees lhs_dups)
    else if not (null rhs_extras) then
      err ("Extra variables on rhs: " ^ show_frees rhs_extras)
    else if not (null rhs_extrasT) then
      err ("Extra type variables on rhs: " ^ show_tfrees rhs_extrasT)
    else if exists_Const (fn c_ty' => c_ty' = c_ty) rhs then
      err ("Constant to be defined occurs on rhs")
    else (c_ty, rhs)
  end;


(* check_defn *)

fun err_in_defn sg name msg =
  error (cat_lines [msg, "The error(s) above occurred in definition " ^ quote name]);

fun pretty_const sg (c, ty) = [Pretty.str c, Pretty.str " ::", Pretty.quote (Sign.pretty_typ sg (#1 (Type.freeze_thaw_type ty)))];

fun cycle_msg sg (infinite, namess) = 
  let val header = if not (infinite) then "cyclic dependency found: " else "infinite chain found: "
  in
      Pretty.string_of (Pretty.block (((Pretty.str header) :: Pretty.fbrk :: (
        let      
	    fun f last (ty, constname, defname) =  
		(pretty_const sg (constname, ty)) @ (if last then [] else [Pretty.str (" depends via "^ quote defname^ " on ")])
          	
	in
	    foldr (fn (x,r) => (f (r=[]) x)@[Pretty.fbrk]@r) [] namess
	end))))
  end

fun check_defn sg overloaded ((deps, axms), def as (bname, tm)) =
  let
    val name = Sign.full_name sg bname;
      
    fun pretty_const (c, ty) = [Pretty.str c, Pretty.str " ::", Pretty.brk 1,
      Pretty.quote (Sign.pretty_typ sg (#1 (Type.freeze_thaw_type ty)))];

    fun def_txt (c_ty, txt) = Pretty.block
      (Pretty.str "Definition of " :: pretty_const c_ty @
        (if txt = "" then [] else [Pretty.str txt]));

    fun show_defn c (dfn, ty') = Pretty.block
      (Pretty.str "  " :: pretty_const (c, ty') @ [Pretty.str " in ", Pretty.str dfn]);

    val (c_ty as (c, ty), rhs) = dest_defn tm
      handle TERM (msg, _) => err_in_defn sg name msg;

    fun decl deps c = 
	(case Sign.const_type sg c of 
	     SOME T => (Defs.declare deps (c, T) handle _ => deps, T)
	   | NONE => err_in_defn sg name ("Undeclared constant " ^ quote c));

    val (deps, c_decl) = decl deps c

    val body = Term.term_constsT rhs
    val deps = foldl (fn ((c, _), deps) => fst (decl deps c)) deps body

  in
      (case overloading sg c_decl ty of
         Useless =>
           err_in_defn sg name (Pretty.string_of (Pretty.chunks
           [Library.setmp show_sorts true def_txt (c_ty, ""), Pretty.str
              "imposes additional sort constraints on the declared type of the constant"]))   
       | ov =>
	 let 
	     val deps' = Defs.define deps c_ty name body
		 handle Defs.DEFS s => err_in_defn sg name ("DEFS: "^s) 
		      | Defs.CIRCULAR s => err_in_defn sg name (cycle_msg sg (false, s))
                      | Defs.INFINITE_CHAIN s => err_in_defn sg name (cycle_msg sg (true, s)) 
                      | Defs.CLASH (_, def1, def2) => err_in_defn sg name (
			  "clashing definitions "^ quote def1 ^" and "^ quote def2)
		      | Defs.FINAL cfinal =>
			err_in_defn sg name (Pretty.string_of (Pretty.block
			  ([Pretty.str "The constant",Pretty.brk 1] @
			   pretty_const cfinal @
			   [Pretty.brk 1,Pretty.str "has been declared final"]))) 
	 in
	     ((if ov = Plain andalso not overloaded then
		   warning (Pretty.string_of (Pretty.chunks
		     [def_txt (c_ty, ""), Pretty.str ("is strictly less general than the declared type (see " ^ quote name ^ ")")]))
	       else
		   ()); (deps', def::axms))
	 end)
  end;


(* add_defs *)

fun ext_defns prep_axm overloaded raw_axms thy =
  let
    val Theory {sign, const_deps, axioms, oracles, parents, ancestors} = thy;
    val all_axioms = List.concat (map (Symtab.dest o #axioms o rep_theory) (thy :: ancestors));

    val axms = map (prep_axm sign) raw_axms;
    val (const_deps', _) = Library.foldl (check_defn sign overloaded) ((const_deps, all_axioms), axms);
  in
    make_theory sign const_deps' axioms oracles parents ancestors
    |> add_axioms_i axms
  end;

val add_defs_i = ext_defns cert_axm;
val add_defs = ext_defns read_axm;


(* add_finals *)

fun ext_finals prep_term overloaded raw_terms thy =
  let
    val Theory {sign, const_deps, axioms, oracles, parents, ancestors} = thy;
    fun mk_final (tm, finals) =
	let
            fun err msg = raise TERM(msg,[tm])
            val (c,ty) = dest_Const tm
		handle TERM _ => err "Can only make constants final"
            val c_decl =
		(case Sign.const_type sign c of 
		     SOME T => T
		   | NONE => err ("Undeclared constant " ^ quote c))
	    val _ =
		case overloading sign c_decl ty of
		    NoOverloading => ()
		  | Useless => err "Sort constraints too strong"
		  | Plain => (if overloaded then () else warning "Type is more general than declared")
	    val finals = Defs.declare finals (c, c_decl) handle _ => finals
	in
	    Defs.finalize finals (c,ty)
	end
    val consts = map (prep_term sign) raw_terms;
    val const_deps' = foldl mk_final const_deps consts;
  in
    make_theory sign const_deps' axioms oracles parents ancestors
  end;

local
  fun read_term sg = Sign.simple_read_term sg TypeInfer.logicT;
  fun cert_term sg = #1 o Sign.certify_term (Sign.pp sg) sg;
in
val add_finals = ext_finals read_term;
val add_finals_i = ext_finals cert_term;
end;

fun merge_final sg =
  let
    fun merge_single (tys,ty) =
      if exists (curry (Sign.typ_instance sg) ty) tys
      then tys
      else (ty::gen_rem (Sign.typ_instance sg) (tys,ty));
    fun merge ([],_) = []
      | merge (_,[]) = []
      | merge input = Library.foldl merge_single input;
  in
    SOME o merge
  end;


(** additional theory data **)

val init_data = curry (ext_sign Sign.init_data);
fun print_data kind = Sign.print_data kind o sign_of;
fun get_data kind f = Sign.get_data kind f o sign_of;
fun put_data kind f = ext_sign (Sign.put_data kind f);



(** merge theories **)          (*exception ERROR*)

(*merge list of theories from left to right, preparing extend*)
fun prep_ext_merge thys =
  let
    val sign' = Sign.prep_ext_merge (map sign_of thys)

    val depss = map (#const_deps o rep_theory) thys;
    val deps' = foldl (uncurry Defs.merge) (hd depss) (tl depss)
      handle Defs.CIRCULAR namess => error (cycle_msg sign' (false, namess))
	   | Defs.INFINITE_CHAIN namess => error (cycle_msg sign' (true, namess))

    val axioms' = Symtab.empty;

    fun eq_ora ((_, (_, s1: stamp)), (_, (_, s2))) = s1 = s2;
    val oracles' =
      Symtab.make (gen_distinct eq_ora
        (List.concat (map (Symtab.dest o #oracles o rep_theory) thys)))
      handle Symtab.DUPS names => err_dup_oras names;

    val parents' = gen_distinct eq_thy thys;
    val ancestors' =
      gen_distinct eq_thy (parents' @ List.concat (map ancestors_of thys));
  in
    make_theory sign' deps' axioms' oracles' parents' ancestors'
  end;


end;

structure BasicTheory: BASIC_THEORY = Theory;
open BasicTheory;
