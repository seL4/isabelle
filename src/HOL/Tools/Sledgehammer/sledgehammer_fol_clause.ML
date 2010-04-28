(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fol_clause.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Storing/printing FOL clauses and arity clauses.  Typed equality is
treated differently.

FIXME: combine with sledgehammer_hol_clause!
*)

signature SLEDGEHAMMER_FOL_CLAUSE =
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
  val make_fixed_const : bool -> string -> string
  val make_fixed_type_const : bool -> string -> string
  val make_type_class : string -> string
  type name = string * string
  type name_pool = string Symtab.table * string Symtab.table
  val empty_name_pool : bool -> name_pool option
  val pool_map : ('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b
  val nice_name : name -> name_pool option -> string * name_pool option
  datatype kind = Axiom | Conjecture
  type axiom_name = string
  datatype fol_type =
    TyVar of name |
    TyFree of name |
    TyConstr of name * fol_type list
  val string_of_fol_type :
    fol_type -> name_pool option -> string * name_pool option
  datatype type_literal = LTVar of string * string | LTFree of string * string
  exception CLAUSE of string * term
  val add_typs : typ list -> type_literal list
  val get_tvar_strs: typ list -> string list
  datatype arLit =
      TConsLit of class * string * string list
    | TVarLit of class * string
  datatype arity_clause = ArityClause of
   {axiom_name: axiom_name, conclLit: arLit, premLits: arLit list}
  datatype classrel_clause = ClassrelClause of
   {axiom_name: axiom_name, subclass: class, superclass: class}
  val make_classrel_clauses: theory -> class list -> class list -> classrel_clause list
  val make_arity_clauses_dfg: bool -> theory -> string list -> class list -> class list * arity_clause list
  val make_arity_clauses: theory -> string list -> class list -> class list * arity_clause list
  val add_type_sort_preds: typ -> int Symtab.table -> int Symtab.table
  val add_classrel_clause_preds :
    classrel_clause -> int Symtab.table -> int Symtab.table
  val class_of_arityLit: arLit -> class
  val add_arity_clause_preds: arity_clause -> int Symtab.table -> int Symtab.table
  val add_fol_type_funcs: fol_type -> int Symtab.table -> int Symtab.table
  val add_arity_clause_funcs:
    arity_clause -> int Symtab.table -> int Symtab.table
  val init_functab: int Symtab.table
  val dfg_sign: bool -> string -> string
  val dfg_of_typeLit: bool -> type_literal -> string
  val gen_dfg_cls: int * string * kind * string list * string list * string list -> string
  val string_of_preds: (string * Int.int) list -> string
  val string_of_funcs: (string * int) list -> string
  val string_of_symbols: string -> string -> string
  val string_of_start: string -> string
  val string_of_descrip : string -> string
  val dfg_tfree_clause : string -> string
  val dfg_classrel_clause: classrel_clause -> string
  val dfg_arity_clause: arity_clause -> string
  val tptp_sign: bool -> string -> string
  val tptp_of_typeLit : bool -> type_literal -> string
  val gen_tptp_cls : int * string * kind * string list * string list -> string
  val tptp_tfree_clause : string -> string
  val tptp_arity_clause : arity_clause -> string
  val tptp_classrel_clause : classrel_clause -> string
end

structure Sledgehammer_FOL_Clause : SLEDGEHAMMER_FOL_CLAUSE =
struct

open Sledgehammer_Util

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

fun union_all xss = fold (union (op =)) xss []

(* Provide readable names for the more common symbolic functions *)
val const_trans_table =
  Symtab.make [(@{const_name "op ="}, "equal"),
               (@{const_name "op &"}, "and"),
               (@{const_name "op |"}, "or"),
               (@{const_name "op -->"}, "implies"),
               (@{const_name "op :"}, "in")]

val type_const_trans_table =
  Symtab.make [(@{type_name "*"}, "prod"),
               (@{type_name "+"}, "sum")]

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

val max_dfg_symbol_length =
  if is_new_spass_version then 1000000 (* arbitrary large number *) else 63

(* HACK because SPASS 3.0 truncates identifiers to 63 characters. *)
fun controlled_length dfg s =
  if dfg andalso size s > max_dfg_symbol_length then
    String.extract (s, 0, SOME (max_dfg_symbol_length div 2 - 1)) ^ "__" ^
    String.extract (s, size s - max_dfg_symbol_length div 2 + 1, NONE)
  else
    s

fun lookup_const dfg c =
    case Symtab.lookup const_trans_table c of
        SOME c' => c'
      | NONE => controlled_length dfg (ascii_of c);

fun lookup_type_const dfg c =
    case Symtab.lookup type_const_trans_table c of
        SOME c' => c'
      | NONE => controlled_length dfg (ascii_of c);

(* "op =" MUST BE "equal" because it's built into ATPs. *)
fun make_fixed_const _ (@{const_name "op ="}) = "equal"
  | make_fixed_const dfg c = const_prefix ^ lookup_const dfg c;

fun make_fixed_type_const dfg c = tconst_prefix ^ lookup_type_const dfg c;

fun make_type_class clas = class_prefix ^ ascii_of clas;


(**** name pool ****)
 
type name = string * string
type name_pool = string Symtab.table * string Symtab.table

fun empty_name_pool readable_names =
  if readable_names then SOME (`I Symtab.empty) else NONE

fun pool_map f xs =
  fold_rev (fn x => fn (ys, pool) => f x pool |>> (fn y => y :: ys)) xs
  o pair []

fun add_nice_name full_name nice_prefix j the_pool =
  let
    val nice_name = nice_prefix ^ (if j = 0 then "" else "_" ^ Int.toString j)
  in
    case Symtab.lookup (snd the_pool) nice_name of
      SOME full_name' =>
      if full_name = full_name' then (nice_name, the_pool)
      else add_nice_name full_name nice_prefix (j + 1) the_pool
    | NONE =>
      (nice_name, (Symtab.update_new (full_name, nice_name) (fst the_pool),
                   Symtab.update_new (nice_name, full_name) (snd the_pool)))
  end

fun translate_first_char f s =
  String.str (f (String.sub (s, 0))) ^ String.extract (s, 1, NONE)

fun readable_name full_name s =
  let
    val s = s |> Long_Name.base_name
              |> fold remove_all ["\<^sub>", "\<^bsub>", "\<^esub>", "\<^isub>"]
    val s' = s |> explode |> rev |> dropwhile (curry (op =) "'")
    val s' =
      (s' |> rev
          |> implode
          |> String.translate
                 (fn c => if Char.isAlphaNum c orelse c = #"_" then String.str c
                          else ""))
      ^ replicate_string (String.size s - length s') "_"
    val s' =
      if s' = "" orelse not (Char.isAlpha (String.sub (s', 0))) then "X" ^ s'
      else s'
    (* Avoid "equal", since it's built into ATPs; and "op" is very ambiguous
       ("op &", "op |", etc.). *)
    val s' = if s' = "equal" orelse s' = "op" then full_name else s'
  in
    case (Char.isLower (String.sub (full_name, 0)),
          Char.isLower (String.sub (s', 0))) of
      (true, false) => translate_first_char Char.toLower s'
    | (false, true) => translate_first_char Char.toUpper s'
    | _ => s'
  end

fun nice_name (full_name, _) NONE = (full_name, NONE)
  | nice_name (full_name, desired_name) (SOME the_pool) =
    case Symtab.lookup (fst the_pool) full_name of
      SOME nice_name => (nice_name, SOME the_pool)
    | NONE => add_nice_name full_name (readable_name full_name desired_name) 0
                            the_pool
              |> apsnd SOME

(**** Definitions and functions for FOL clauses, for conversion to TPTP or DFG
      format ****)

datatype kind = Axiom | Conjecture;

type axiom_name = string;

(**** Isabelle FOL clauses ****)

datatype fol_type =
  TyVar of name |
  TyFree of name |
  TyConstr of name * fol_type list

fun string_of_fol_type (TyVar sp) pool = nice_name sp pool
  | string_of_fol_type (TyFree sp) pool = nice_name sp pool
  | string_of_fol_type (TyConstr (sp, tys)) pool =
    let
      val (s, pool) = nice_name sp pool
      val (ss, pool) = pool_map string_of_fol_type tys pool
    in (s ^ paren_pack ss, pool) end

(*First string is the type class; the second is a TVar or TFfree*)
datatype type_literal = LTVar of string * string | LTFree of string * string;

exception CLAUSE of string * term;

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
fun add_typs Ts = fold (union (op =)) (map sorts_on_typs Ts) []

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

datatype arLit = TConsLit of class * string * string list
               | TVarLit of class * string;

datatype arity_clause =
         ArityClause of {axiom_name: axiom_name,
                         conclLit: arLit,
                         premLits: arLit list};


fun gen_TVars 0 = []
  | gen_TVars n = ("T_" ^ Int.toString n) :: gen_TVars (n-1);

fun pack_sort(_,[])  = []
  | pack_sort(tvar, "HOL.type"::srt) = pack_sort(tvar, srt)   (*IGNORE sort "type"*)
  | pack_sort(tvar, cls::srt) =  (cls, tvar) :: pack_sort(tvar, srt);

(*Arity of type constructor tcon :: (arg1,...,argN)res*)
fun make_axiom_arity_clause dfg (tcons, axiom_name, (cls,args)) =
   let val tvars = gen_TVars (length args)
       val tvars_srts = ListPair.zip (tvars,args)
   in
      ArityClause {axiom_name = axiom_name, 
                   conclLit = TConsLit (cls, make_fixed_type_const dfg tcons, tvars),
                   premLits = map TVarLit (union_all(map pack_sort tvars_srts))}
   end;


(**** Isabelle class relations ****)

datatype classrel_clause =
         ClassrelClause of {axiom_name: axiom_name,
                            subclass: class,
                            superclass: class};

(*Generate all pairs (sub,super) such that sub is a proper subclass of super in theory thy.*)
fun class_pairs thy [] supers = []
  | class_pairs thy subs supers =
      let
        val class_less = Sorts.class_less (Sign.classes_of thy)
        fun add_super sub super = class_less (sub, super) ? cons (sub, super)
        fun add_supers sub = fold (add_super sub) supers
      in fold add_supers subs [] end

fun make_classrel_clause (sub,super) =
  ClassrelClause {axiom_name = clrelclause_prefix ^ ascii_of sub ^ "_" ^ ascii_of super,
                  subclass = make_type_class sub,
                  superclass = make_type_class super};

fun make_classrel_clauses thy subs supers =
  map make_classrel_clause (class_pairs thy subs supers);


(** Isabelle arities **)

fun arity_clause dfg _ _ (tcons, []) = []
  | arity_clause dfg seen n (tcons, ("HOL.type",_)::ars) =  (*ignore*)
      arity_clause dfg seen n (tcons,ars)
  | arity_clause dfg seen n (tcons, (ar as (class,_)) :: ars) =
      if class mem_string seen then (*multiple arities for the same tycon, class pair*)
          make_axiom_arity_clause dfg (tcons, lookup_type_const dfg tcons ^ "_" ^ class ^ "_" ^ Int.toString n, ar) ::
          arity_clause dfg seen (n+1) (tcons,ars)
      else
          make_axiom_arity_clause dfg (tcons, lookup_type_const dfg tcons ^ "_" ^ class, ar) ::
          arity_clause dfg (class::seen) n (tcons,ars)

fun multi_arity_clause dfg [] = []
  | multi_arity_clause dfg ((tcons, ars) :: tc_arlists) =
      arity_clause dfg [] 1 (tcons, ars) @ multi_arity_clause dfg tc_arlists

(*Generate all pairs (tycon,class,sorts) such that tycon belongs to class in theory thy
  provided its arguments have the corresponding sorts.*)
fun type_class_pairs thy tycons classes =
  let val alg = Sign.classes_of thy
      fun domain_sorts tycon = Sorts.mg_domain alg tycon o single
      fun add_class tycon class =
        cons (class, domain_sorts tycon class)
        handle Sorts.CLASS_ERROR _ => I
      fun try_classes tycon = (tycon, fold (add_class tycon) classes [])
  in  map try_classes tycons  end;

(*Proving one (tycon, class) membership may require proving others, so iterate.*)
fun iter_type_class_pairs thy tycons [] = ([], [])
  | iter_type_class_pairs thy tycons classes =
      let val cpairs = type_class_pairs thy tycons classes
          val newclasses = union_all (union_all (union_all (map (map #2 o #2) cpairs)))
            |> subtract (op =) classes |> subtract (op =) HOLogic.typeS
          val (classes', cpairs') = iter_type_class_pairs thy tycons newclasses
      in (union (op =) classes' classes, union (op =) cpairs' cpairs) end;

fun make_arity_clauses_dfg dfg thy tycons classes =
  let val (classes', cpairs) = iter_type_class_pairs thy tycons classes
  in  (classes', multi_arity_clause dfg cpairs)  end;
val make_arity_clauses = make_arity_clauses_dfg false;

(**** Find occurrences of predicates in clauses ****)

(*FIXME: multiple-arity checking doesn't work, as update_new is the wrong
  function (it flags repeated declarations of a function, even with the same arity)*)

fun update_many keypairs = fold Symtab.update keypairs

val add_type_sort_preds = update_many o map pred_of_sort o sorts_on_typs

fun add_classrel_clause_preds (ClassrelClause {subclass, superclass, ...}) =
  Symtab.update (subclass, 1) #> Symtab.update (superclass, 1)

fun class_of_arityLit (TConsLit (tclass, _, _)) = tclass
  | class_of_arityLit (TVarLit (tclass, _)) = tclass;

fun add_arity_clause_preds (ArityClause {conclLit, premLits, ...}) =
  let
    val classes = map (make_type_class o class_of_arityLit)
                      (conclLit :: premLits)
  in fold (Symtab.update o rpair 1) classes end;

(*** Find occurrences of functions in clauses ***)

fun add_fol_type_funcs (TyVar _) = I
  | add_fol_type_funcs (TyFree (s, _)) = Symtab.update (s, 0)
  | add_fol_type_funcs (TyConstr ((s, _), tys)) =
    Symtab.update (s, length tys) #> fold add_fol_type_funcs tys

(*TFrees are recorded as constants*)
fun add_type_sort_funcs (TVar _, funcs) = funcs
  | add_type_sort_funcs (TFree (a, _), funcs) =
      Symtab.update (make_fixed_type_var a, 0) funcs

fun add_arity_clause_funcs (ArityClause {conclLit,...}) funcs =
  let val TConsLit (_, tcons, tvars) = conclLit
  in  Symtab.update (tcons, length tvars) funcs  end;

(*This type can be overlooked because it is built-in...*)
val init_functab = Symtab.update ("tc_itself", 1) Symtab.empty;


(**** String-oriented operations ****)

fun string_of_clausename (cls_id,ax_name) =
    clause_prefix ^ ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) =
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);


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

fun dfg_classrel_clause (ClassrelClause {axiom_name,subclass,superclass,...}) =
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

fun tptp_sign true s = s
  | tptp_sign false s = "~ " ^ s

fun tptp_of_typeLit pos (LTVar (s, ty))  = tptp_sign pos (s ^ "(" ^ ty ^ ")")
  | tptp_of_typeLit pos (LTFree (s, ty)) = tptp_sign pos (s ^ "(" ^ ty ^ ")")

fun tptp_cnf name kind formula =
  "cnf(" ^ name ^ ", " ^ kind ^ ",\n    " ^ formula ^ ").\n"

fun gen_tptp_cls (cls_id, ax_name, Axiom, lits, tylits) =
      tptp_cnf (string_of_clausename (cls_id, ax_name)) "axiom"
               (tptp_pack (tylits @ lits))
  | gen_tptp_cls (cls_id, ax_name, Conjecture, lits, _) =
      tptp_cnf (string_of_clausename (cls_id, ax_name)) "negated_conjecture"
               (tptp_pack lits)

fun tptp_tfree_clause tfree_lit =
    tptp_cnf "tfree_tcs" "negated_conjecture" (tptp_pack [tfree_lit])

fun tptp_of_arLit (TConsLit (c,t,args)) =
      tptp_sign true (make_type_class c ^ "(" ^ t ^ paren_pack args ^ ")")
  | tptp_of_arLit (TVarLit (c,str)) =
      tptp_sign false (make_type_class c ^ "(" ^ str ^ ")")

fun tptp_arity_clause (ArityClause{axiom_name,conclLit,premLits,...}) =
  tptp_cnf (string_of_ar axiom_name) "axiom"
           (tptp_pack (map tptp_of_arLit (conclLit :: premLits)))

fun tptp_classrelLits sub sup =
  let val tvar = "(T)"
  in  tptp_pack [tptp_sign false (sub^tvar), tptp_sign true (sup^tvar)]  end;

fun tptp_classrel_clause (ClassrelClause {axiom_name,subclass,superclass,...}) =
  tptp_cnf axiom_name "axiom" (tptp_classrelLits subclass superclass)

end;
