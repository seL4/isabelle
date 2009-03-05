(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Storing/printing FOL clauses and arity clauses.
Typed equality is treated differently.
*)

(*FIXME: combine with res_hol_clause!*)
signature RES_CLAUSE =
sig
  val schematic_var_prefix: string
  val fixed_var_prefix: string
  val tvar_prefix: string
  val tfree_prefix: string
  val clause_prefix: string
  val const_prefix: string
  val tconst_prefix: string
  val class_prefix: string
  val union_all: ''a list list -> ''a list
  val const_trans_table: string Symtab.table
  val type_const_trans_table: string Symtab.table
  val ascii_of: string -> string
  val undo_ascii_of: string -> string
  val paren_pack : string list -> string
  val make_schematic_var : string * int -> string
  val make_fixed_var : string -> string
  val make_schematic_type_var : string * int -> string
  val make_fixed_type_var : string -> string
  val dfg_format: bool ref
  val make_fixed_const : string -> string
  val make_fixed_type_const : string -> string
  val make_type_class : string -> string
  datatype kind = Axiom | Conjecture
  type axiom_name = string
  datatype fol_type =
      AtomV of string
    | AtomF of string
    | Comp of string * fol_type list
  val string_of_fol_type : fol_type -> string
  datatype type_literal = LTVar of string * string | LTFree of string * string
  exception CLAUSE of string * term
  val add_typs : typ list -> type_literal list
  val get_tvar_strs: typ list -> string list
  datatype arLit =
      TConsLit of class * string * string list
    | TVarLit of class * string
  datatype arityClause = ArityClause of
   {axiom_name: axiom_name, conclLit: arLit, premLits: arLit list}
  datatype classrelClause = ClassrelClause of
   {axiom_name: axiom_name, subclass: class, superclass: class}
  val make_classrel_clauses: theory -> class list -> class list -> classrelClause list
  val make_arity_clauses: theory -> string list -> class list -> class list * arityClause list
  val add_type_sort_preds: typ * int Symtab.table -> int Symtab.table
  val add_classrelClause_preds : classrelClause * int Symtab.table -> int Symtab.table
  val class_of_arityLit: arLit -> class
  val add_arityClause_preds: arityClause * int Symtab.table -> int Symtab.table
  val add_foltype_funcs: fol_type * int Symtab.table -> int Symtab.table
  val add_arityClause_funcs: arityClause * int Symtab.table -> int Symtab.table
  val init_functab: int Symtab.table
  val writeln_strs: TextIO.outstream -> string list -> unit
  val dfg_sign: bool -> string -> string
  val dfg_of_typeLit: bool -> type_literal -> string
  val gen_dfg_cls: int * string * kind * string list * string list * string list -> string
  val string_of_preds: (string * Int.int) list -> string
  val string_of_funcs: (string * int) list -> string
  val string_of_symbols: string -> string -> string
  val string_of_start: string -> string
  val string_of_descrip : string -> string
  val dfg_tfree_clause : string -> string
  val dfg_classrelClause: classrelClause -> string
  val dfg_arity_clause: arityClause -> string
  val tptp_sign: bool -> string -> string
  val tptp_of_typeLit : bool -> type_literal -> string
  val gen_tptp_cls : int * string * kind * string list * string list -> string
  val tptp_tfree_clause : string -> string
  val tptp_arity_clause : arityClause -> string
  val tptp_classrelClause : classrelClause -> string
end

structure ResClause: RES_CLAUSE =
struct

val schematic_var_prefix = "V_";
val fixed_var_prefix = "v_";

val tvar_prefix = "T_";
val tfree_prefix = "t_";

val clause_prefix = "cls_";
val arclause_prefix = "clsarity_"
val clrelclause_prefix = "clsrel_";

val const_prefix = "c_";
val tconst_prefix = "tc_";
val class_prefix = "class_";

fun union_all xss = foldl (op union) [] xss;

(*Provide readable names for the more common symbolic functions*)
val const_trans_table =
      Symtab.make [(@{const_name "op ="}, "equal"),
                   (@{const_name HOL.less_eq}, "lessequals"),
                   (@{const_name HOL.less}, "less"),
                   (@{const_name "op &"}, "and"),
                   (@{const_name "op |"}, "or"),
                   (@{const_name HOL.plus}, "plus"),
                   (@{const_name HOL.minus}, "minus"),
                   (@{const_name HOL.times}, "times"),
                   (@{const_name Divides.div}, "div"),
                   (@{const_name HOL.divide}, "divide"),
                   (@{const_name "op -->"}, "implies"),
                   (@{const_name Set.empty}, "emptyset"),
                   (@{const_name "op :"}, "in"),
                   (@{const_name Un}, "union"),
                   (@{const_name Int}, "inter"),
                   ("List.append", "append"),
                   ("ATP_Linkup.fequal", "fequal"),
                   ("ATP_Linkup.COMBI", "COMBI"),
                   ("ATP_Linkup.COMBK", "COMBK"),
                   ("ATP_Linkup.COMBB", "COMBB"),
                   ("ATP_Linkup.COMBC", "COMBC"),
                   ("ATP_Linkup.COMBS", "COMBS"),
                   ("ATP_Linkup.COMBB'", "COMBB_e"),
                   ("ATP_Linkup.COMBC'", "COMBC_e"),
                   ("ATP_Linkup.COMBS'", "COMBS_e")];

val type_const_trans_table =
      Symtab.make [("*", "prod"),
                   ("+", "sum"),
                   ("~=>", "map")];

(*Escaping of special characters.
  Alphanumeric characters are left unchanged.
  The character _ goes to __
  Characters in the range ASCII space to / go to _A to _P, respectively.
  Other printing characters go to _nnn where nnn is the decimal ASCII code.*)
val A_minus_space = Char.ord #"A" - Char.ord #" ";

fun stringN_of_int 0 _ = ""
  | stringN_of_int k n = stringN_of_int (k-1) (n div 10) ^ Int.toString (n mod 10);

fun ascii_of_c c =
  if Char.isAlphaNum c then String.str c
  else if c = #"_" then "__"
  else if #" " <= c andalso c <= #"/"
       then "_" ^ String.str (Char.chr (Char.ord c + A_minus_space))
  else if Char.isPrint c
       then ("_" ^ stringN_of_int 3 (Char.ord c))  (*fixed width, in case more digits follow*)
  else ""

val ascii_of = String.translate ascii_of_c;

(** Remove ASCII armouring from names in proof files **)

(*We don't raise error exceptions because this code can run inside the watcher.
  Also, the errors are "impossible" (hah!)*)
fun undo_ascii_aux rcs [] = String.implode(rev rcs)
  | undo_ascii_aux rcs [#"_"] = undo_ascii_aux (#"_"::rcs) []  (*ERROR*)
      (*Three types of _ escapes: __, _A to _P, _nnn*)
  | undo_ascii_aux rcs (#"_" :: #"_" :: cs) = undo_ascii_aux (#"_"::rcs) cs
  | undo_ascii_aux rcs (#"_" :: c :: cs) =
      if #"A" <= c andalso c<= #"P"  (*translation of #" " to #"/"*)
      then undo_ascii_aux (Char.chr(Char.ord c - A_minus_space) :: rcs) cs
      else
        let val digits = List.take (c::cs, 3) handle Subscript => []
        in
            case Int.fromString (String.implode digits) of
                NONE => undo_ascii_aux (c:: #"_"::rcs) cs  (*ERROR*)
              | SOME n => undo_ascii_aux (Char.chr n :: rcs) (List.drop (cs, 2))
        end
  | undo_ascii_aux rcs (c::cs) = undo_ascii_aux (c::rcs) cs;

val undo_ascii_of = undo_ascii_aux [] o String.explode;

(* convert a list of strings into one single string; surrounded by brackets *)
fun paren_pack [] = ""   (*empty argument list*)
  | paren_pack strings = "(" ^ commas strings ^ ")";

(*TSTP format uses (...) rather than the old [...]*)
fun tptp_pack strings = "(" ^ space_implode " | " strings ^ ")";


(*Remove the initial ' character from a type variable, if it is present*)
fun trim_type_var s =
  if s <> "" andalso String.sub(s,0) = #"'" then String.extract(s,1,NONE)
  else error ("trim_type: Malformed type variable encountered: " ^ s);

fun ascii_of_indexname (v,0) = ascii_of v
  | ascii_of_indexname (v,i) = ascii_of v ^ "_" ^ Int.toString i;

fun make_schematic_var v = schematic_var_prefix ^ (ascii_of_indexname v);
fun make_fixed_var x = fixed_var_prefix ^ (ascii_of x);

fun make_schematic_type_var (x,i) =
      tvar_prefix ^ (ascii_of_indexname (trim_type_var x,i));
fun make_fixed_type_var x = tfree_prefix ^ (ascii_of (trim_type_var x));

(*HACK because SPASS truncates identifiers to 63 characters :-(( *)
val dfg_format = ref false;

(*32-bit hash,so we expect no collisions unless there are around 65536 long identifiers...*)
fun controlled_length s =
  if size s > 60 andalso !dfg_format
  then Word.toString (Polyhash.hashw_string(s,0w0))
  else s;

fun lookup_const c =
    case Symtab.lookup const_trans_table c of
        SOME c' => c'
      | NONE => controlled_length (ascii_of c);

fun lookup_type_const c =
    case Symtab.lookup type_const_trans_table c of
        SOME c' => c'
      | NONE => controlled_length (ascii_of c);

fun make_fixed_const "op =" = "equal"   (*MUST BE "equal" because it's built-in to ATPs*)
  | make_fixed_const c      = const_prefix ^ lookup_const c;

fun make_fixed_type_const c = tconst_prefix ^ lookup_type_const c;

fun make_type_class clas = class_prefix ^ ascii_of clas;


(***** definitions and functions for FOL clauses, for conversion to TPTP or DFG format. *****)

datatype kind = Axiom | Conjecture;

type axiom_name = string;

(**** Isabelle FOL clauses ****)

(*FIXME: give the constructors more sensible names*)
datatype fol_type = AtomV of string
                  | AtomF of string
                  | Comp of string * fol_type list;

fun string_of_fol_type (AtomV x) = x
  | string_of_fol_type (AtomF x) = x
  | string_of_fol_type (Comp(tcon,tps)) =
      tcon ^ (paren_pack (map string_of_fol_type tps));

(*First string is the type class; the second is a TVar or TFfree*)
datatype type_literal = LTVar of string * string | LTFree of string * string;

exception CLAUSE of string * term;

fun atomic_type (TFree (a,_)) = AtomF(make_fixed_type_var a)
  | atomic_type (TVar (v,_))  = AtomV(make_schematic_type_var v);

(*Flatten a type to a fol_type while accumulating sort constraints on the TFrees and
  TVars it contains.*)
fun type_of (Type (a, Ts)) =
      let val (folTyps, ts) = types_of Ts
          val t = make_fixed_type_const a
      in (Comp(t,folTyps), ts) end
  | type_of T = (atomic_type T, [T])
and types_of Ts =
      let val (folTyps,ts) = ListPair.unzip (map type_of Ts)
      in (folTyps, union_all ts) end;

(*Make literals for sorted type variables*)
fun sorts_on_typs_aux (_, [])   = []
  | sorts_on_typs_aux ((x,i),  s::ss) =
      let val sorts = sorts_on_typs_aux ((x,i), ss)
      in
          if s = "HOL.type" then sorts
          else if i = ~1 then LTFree(make_type_class s, make_fixed_type_var x) :: sorts
          else LTVar(make_type_class s, make_schematic_type_var (x,i)) :: sorts
      end;

fun sorts_on_typs (TFree (a,s)) = sorts_on_typs_aux ((a,~1),s)
  | sorts_on_typs (TVar (v,s))  = sorts_on_typs_aux (v,s);

fun pred_of_sort (LTVar (s,ty)) = (s,1)
  | pred_of_sort (LTFree (s,ty)) = (s,1)

(*Given a list of sorted type variables, return a list of type literals.*)
fun add_typs Ts = foldl (op union) [] (map sorts_on_typs Ts);

(*The correct treatment of TFrees like 'a in lemmas (axiom clauses) is not clear.
  * Ignoring them leads to unsound proofs, since we do nothing to ensure that 'a
    in a lemma has the same sort as 'a in the conjecture.
  * Deleting such clauses will lead to problems with locales in other use of local results
    where 'a is fixed. Probably we should delete clauses unless the sorts agree.
  * Currently we include a class constraint in the clause, exactly as with TVars.
*)

(** make axiom and conjecture clauses. **)

fun get_tvar_strs [] = []
  | get_tvar_strs ((TVar (indx,s))::Ts) =
      insert (op =) (make_schematic_type_var indx) (get_tvar_strs Ts)
  | get_tvar_strs((TFree _)::Ts) = get_tvar_strs Ts



(**** Isabelle arities ****)

exception ARCLAUSE of string;

datatype arLit = TConsLit of class * string * string list
               | TVarLit of class * string;

datatype arityClause =
         ArityClause of {axiom_name: axiom_name,
                         conclLit: arLit,
                         premLits: arLit list};


fun gen_TVars 0 = []
  | gen_TVars n = ("T_" ^ Int.toString n) :: gen_TVars (n-1);

fun pack_sort(_,[])  = []
  | pack_sort(tvar, "HOL.type"::srt) = pack_sort(tvar, srt)   (*IGNORE sort "type"*)
  | pack_sort(tvar, cls::srt) =  (cls, tvar) :: pack_sort(tvar, srt);

(*Arity of type constructor tcon :: (arg1,...,argN)res*)
fun make_axiom_arity_clause (tcons, axiom_name, (cls,args)) =
   let val tvars = gen_TVars (length args)
       val tvars_srts = ListPair.zip (tvars,args)
   in
      ArityClause {axiom_name = axiom_name, 
                   conclLit = TConsLit (cls, make_fixed_type_const tcons, tvars),
                   premLits = map TVarLit (union_all(map pack_sort tvars_srts))}
   end;


(**** Isabelle class relations ****)

datatype classrelClause =
         ClassrelClause of {axiom_name: axiom_name,
                            subclass: class,
                            superclass: class};

(*Generate all pairs (sub,super) such that sub is a proper subclass of super in theory thy.*)
fun class_pairs thy [] supers = []
  | class_pairs thy subs supers =
      let val class_less = Sorts.class_less(Sign.classes_of thy)
          fun add_super sub (super,pairs) =
                if class_less (sub,super) then (sub,super)::pairs else pairs
          fun add_supers (sub,pairs) = foldl (add_super sub) pairs supers
      in  foldl add_supers [] subs  end;

fun make_classrelClause (sub,super) =
  ClassrelClause {axiom_name = clrelclause_prefix ^ ascii_of sub ^ "_" ^ ascii_of super,
                  subclass = make_type_class sub,
                  superclass = make_type_class super};

fun make_classrel_clauses thy subs supers =
  map make_classrelClause (class_pairs thy subs supers);


(** Isabelle arities **)

fun arity_clause _ _ (tcons, []) = []
  | arity_clause seen n (tcons, ("HOL.type",_)::ars) =  (*ignore*)
      arity_clause seen n (tcons,ars)
  | arity_clause seen n (tcons, (ar as (class,_)) :: ars) =
      if class mem_string seen then (*multiple arities for the same tycon, class pair*)
          make_axiom_arity_clause (tcons, lookup_type_const tcons ^ "_" ^ class ^ "_" ^ Int.toString n, ar) ::
          arity_clause seen (n+1) (tcons,ars)
      else
          make_axiom_arity_clause (tcons, lookup_type_const tcons ^ "_" ^ class, ar) ::
          arity_clause (class::seen) n (tcons,ars)

fun multi_arity_clause [] = []
  | multi_arity_clause ((tcons,ars) :: tc_arlists) =
      arity_clause [] 1 (tcons, ars)  @  multi_arity_clause tc_arlists

(*Generate all pairs (tycon,class,sorts) such that tycon belongs to class in theory thy
  provided its arguments have the corresponding sorts.*)
fun type_class_pairs thy tycons classes =
  let val alg = Sign.classes_of thy
      fun domain_sorts (tycon,class) = Sorts.mg_domain alg tycon [class]
      fun add_class tycon (class,pairs) =
            (class, domain_sorts(tycon,class))::pairs
            handle Sorts.CLASS_ERROR _ => pairs
      fun try_classes tycon = (tycon, foldl (add_class tycon) [] classes)
  in  map try_classes tycons  end;

(*Proving one (tycon, class) membership may require proving others, so iterate.*)
fun iter_type_class_pairs thy tycons [] = ([], [])
  | iter_type_class_pairs thy tycons classes =
      let val cpairs = type_class_pairs thy tycons classes
          val newclasses = union_all (union_all (union_all (map (map #2 o #2) cpairs))) \\ classes \\ HOLogic.typeS
          val _ = if null newclasses then ()
                  else Output.debug (fn _ => "New classes: " ^ space_implode ", " newclasses)
          val (classes', cpairs') = iter_type_class_pairs thy tycons newclasses
      in  (classes' union classes, cpairs' union cpairs)  end;

fun make_arity_clauses thy tycons classes =
  let val (classes', cpairs) = iter_type_class_pairs thy tycons classes
  in  (classes', multi_arity_clause cpairs)  end;


(**** Find occurrences of predicates in clauses ****)

(*FIXME: multiple-arity checking doesn't work, as update_new is the wrong
  function (it flags repeated declarations of a function, even with the same arity)*)

fun update_many (tab, keypairs) = foldl (uncurry Symtab.update) tab keypairs;

fun add_type_sort_preds (T, preds) =
      update_many (preds, map pred_of_sort (sorts_on_typs T));

fun add_classrelClause_preds (ClassrelClause {subclass,superclass,...}, preds) =
  Symtab.update (subclass,1) (Symtab.update (superclass,1) preds);

fun class_of_arityLit (TConsLit (tclass, _, _)) = tclass
  | class_of_arityLit (TVarLit (tclass, _)) = tclass;

fun add_arityClause_preds (ArityClause {conclLit,premLits,...}, preds) =
  let val classes = map (make_type_class o class_of_arityLit) (conclLit::premLits)
      fun upd (class,preds) = Symtab.update (class,1) preds
  in  foldl upd preds classes  end;

(*** Find occurrences of functions in clauses ***)

fun add_foltype_funcs (AtomV _, funcs) = funcs
  | add_foltype_funcs (AtomF a, funcs) = Symtab.update (a,0) funcs
  | add_foltype_funcs (Comp(a,tys), funcs) =
      foldl add_foltype_funcs (Symtab.update (a, length tys) funcs) tys;

(*TFrees are recorded as constants*)
fun add_type_sort_funcs (TVar _, funcs) = funcs
  | add_type_sort_funcs (TFree (a, _), funcs) =
      Symtab.update (make_fixed_type_var a, 0) funcs

fun add_arityClause_funcs (ArityClause {conclLit,...}, funcs) =
  let val TConsLit (_, tcons, tvars) = conclLit
  in  Symtab.update (tcons, length tvars) funcs  end;

(*This type can be overlooked because it is built-in...*)
val init_functab = Symtab.update ("tc_itself", 1) Symtab.empty;


(**** String-oriented operations ****)

fun string_of_clausename (cls_id,ax_name) =
    clause_prefix ^ ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) =
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);

fun writeln_strs os = List.app (fn s => TextIO.output (os, s));


(**** Producing DFG files ****)

(*Attach sign in DFG syntax: false means negate.*)
fun dfg_sign true s = s
  | dfg_sign false s = "not(" ^ s ^ ")"

fun dfg_of_typeLit pos (LTVar (s,ty))  = dfg_sign pos (s ^ "(" ^ ty ^ ")")
  | dfg_of_typeLit pos (LTFree (s,ty)) = dfg_sign pos (s ^ "(" ^ ty ^ ")");

(*Enclose the clause body by quantifiers, if necessary*)
fun dfg_forall [] body = body
  | dfg_forall vars body = "forall([" ^ commas vars ^ "],\n" ^ body ^ ")"

fun gen_dfg_cls (cls_id, ax_name, Axiom, lits, tylits, vars) =
      "clause( %(axiom)\n" ^
      dfg_forall vars ("or(" ^ commas (tylits@lits) ^ ")") ^ ",\n" ^
      string_of_clausename (cls_id,ax_name) ^  ").\n\n"
  | gen_dfg_cls (cls_id, ax_name, Conjecture, lits, _, vars) =
      "clause( %(negated_conjecture)\n" ^
      dfg_forall vars ("or(" ^ commas lits ^ ")") ^ ",\n" ^
      string_of_clausename (cls_id,ax_name) ^  ").\n\n";

fun string_of_arity (name, num) =  "(" ^ name ^ "," ^ Int.toString num ^ ")"

fun string_of_preds [] = ""
  | string_of_preds preds = "predicates[" ^ commas(map string_of_arity preds) ^ "].\n";

fun string_of_funcs [] = ""
  | string_of_funcs funcs = "functions[" ^ commas(map string_of_arity funcs) ^ "].\n" ;

fun string_of_symbols predstr funcstr =
  "list_of_symbols.\n" ^ predstr  ^ funcstr  ^ "end_of_list.\n\n";

fun string_of_start name = "begin_problem(" ^ name ^ ").\n\n";

fun string_of_descrip name =
  "list_of_descriptions.\nname({*" ^ name ^
  "*}).\nauthor({*Isabelle*}).\nstatus(unknown).\ndescription({*auto-generated*}).\nend_of_list.\n\n"

fun dfg_tfree_clause tfree_lit =
  "clause( %(negated_conjecture)\n" ^ "or( " ^ tfree_lit ^ "),\n" ^ "tfree_tcs" ^ ").\n\n"

fun dfg_of_arLit (TConsLit (c,t,args)) =
      dfg_sign true (make_type_class c ^ "(" ^ t ^ paren_pack args ^ ")")
  | dfg_of_arLit (TVarLit (c,str)) =
      dfg_sign false (make_type_class c ^ "(" ^ str ^ ")")

fun dfg_classrelLits sub sup =  "not(" ^ sub ^ "(T)), " ^ sup ^ "(T)";

fun dfg_classrelClause (ClassrelClause {axiom_name,subclass,superclass,...}) =
  "clause(forall([T],\nor( " ^ dfg_classrelLits subclass superclass ^ ")),\n" ^
  axiom_name ^ ").\n\n";

fun string_of_ar axiom_name = arclause_prefix ^ ascii_of axiom_name;

fun dfg_arity_clause (ArityClause{axiom_name,conclLit,premLits,...}) =
  let val TConsLit (_,_,tvars) = conclLit
      val lits = map dfg_of_arLit (conclLit :: premLits)
  in
      "clause( %(axiom)\n" ^
      dfg_forall tvars ("or( " ^ commas lits ^ ")") ^ ",\n" ^
      string_of_ar axiom_name ^ ").\n\n"
  end;


(**** Produce TPTP files ****)

(*Attach sign in TPTP syntax: false means negate.*)
fun tptp_sign true s = s
  | tptp_sign false s = "~ " ^ s

fun tptp_of_typeLit pos (LTVar (s,ty))  = tptp_sign pos (s ^ "(" ^ ty ^ ")")
  | tptp_of_typeLit pos (LTFree (s,ty)) = tptp_sign pos  (s ^ "(" ^ ty ^ ")");

fun gen_tptp_cls (cls_id,ax_name,Axiom,lits,tylits) =
      "cnf(" ^ string_of_clausename (cls_id,ax_name) ^ ",axiom," ^ 
               tptp_pack (tylits@lits) ^ ").\n"
  | gen_tptp_cls (cls_id,ax_name,Conjecture,lits,_) =
      "cnf(" ^ string_of_clausename (cls_id,ax_name) ^ ",negated_conjecture," ^ 
               tptp_pack lits ^ ").\n";

fun tptp_tfree_clause tfree_lit =
    "cnf(" ^ "tfree_tcs," ^ "negated_conjecture" ^ "," ^ tptp_pack[tfree_lit] ^ ").\n";

fun tptp_of_arLit (TConsLit (c,t,args)) =
      tptp_sign true (make_type_class c ^ "(" ^ t ^ paren_pack args ^ ")")
  | tptp_of_arLit (TVarLit (c,str)) =
      tptp_sign false (make_type_class c ^ "(" ^ str ^ ")")

fun tptp_arity_clause (ArityClause{axiom_name,conclLit,premLits,...}) =
  "cnf(" ^ string_of_ar axiom_name ^ ",axiom," ^
  tptp_pack (map tptp_of_arLit (conclLit :: premLits)) ^ ").\n";

fun tptp_classrelLits sub sup =
  let val tvar = "(T)"
  in  tptp_pack [tptp_sign false (sub^tvar), tptp_sign true (sup^tvar)]  end;

fun tptp_classrelClause (ClassrelClause {axiom_name,subclass,superclass,...}) =
  "cnf(" ^ axiom_name ^ ",axiom," ^ tptp_classrelLits subclass superclass ^ ").\n"

end;
