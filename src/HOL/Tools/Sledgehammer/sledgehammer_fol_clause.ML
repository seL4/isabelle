(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fol_clause.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Storing/printing FOL clauses and arity clauses.  Typed equality is
treated differently.

FIXME: combine with sledgehammer_hol_clause!
*)

signature SLEDGEHAMMER_FOL_CLAUSE =
sig
  val type_wrapper_name : string
  val schematic_var_prefix: string
  val fixed_var_prefix: string
  val tvar_prefix: string
  val tfree_prefix: string
  val const_prefix: string
  val tconst_prefix: string
  val class_prefix: string
  val union_all: ''a list list -> ''a list
  val invert_const: string -> string
  val ascii_of: string -> string
  val undo_ascii_of: string -> string
  val strip_prefix: string -> string -> string option
  val make_schematic_var : string * int -> string
  val make_fixed_var : string -> string
  val make_schematic_type_var : string * int -> string
  val make_fixed_type_var : string -> string
  val make_fixed_const : string -> string
  val make_fixed_type_const : string -> string
  val make_type_class : string -> string
  type name = string * string
  type name_pool = string Symtab.table * string Symtab.table
  val empty_name_pool : bool -> name_pool option
  val pool_map : ('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b
  val nice_name : name -> name_pool option -> string * name_pool option
  datatype kind = Axiom | Conjecture
  datatype type_literal =
    TyLitVar of string * name |
    TyLitFree of string * name
  val type_literals_for_types : typ list -> type_literal list
  datatype arLit =
      TConsLit of class * string * string list
    | TVarLit of class * string
  datatype arity_clause = ArityClause of
   {axiom_name: string, conclLit: arLit, premLits: arLit list}
  datatype classrel_clause = ClassrelClause of
   {axiom_name: string, subclass: class, superclass: class}
  val make_classrel_clauses: theory -> class list -> class list -> classrel_clause list
  val make_arity_clauses: theory -> string list -> class list -> class list * arity_clause list
end

structure Sledgehammer_FOL_Clause : SLEDGEHAMMER_FOL_CLAUSE =
struct

val type_wrapper_name = "ti"

val schematic_var_prefix = "V_";
val fixed_var_prefix = "v_";

val tvar_prefix = "T_";
val tfree_prefix = "t_";

val classrel_clause_prefix = "clsrel_";

val const_prefix = "c_";
val tconst_prefix = "tc_";
val class_prefix = "class_";

fun union_all xss = fold (union (op =)) xss []

(* Readable names for the more common symbolic functions. Do not mess with the
   last nine entries of the table unless you know what you are doing. *)
val const_trans_table =
  Symtab.make [(@{const_name "op ="}, "equal"),
               (@{const_name "op &"}, "and"),
               (@{const_name "op |"}, "or"),
               (@{const_name "op -->"}, "implies"),
               (@{const_name "op :"}, "in"),
               (@{const_name fequal}, "fequal"),
               (@{const_name COMBI}, "COMBI"),
               (@{const_name COMBK}, "COMBK"),
               (@{const_name COMBB}, "COMBB"),
               (@{const_name COMBC}, "COMBC"),
               (@{const_name COMBS}, "COMBS"),
               (@{const_name True}, "True"),
               (@{const_name False}, "False"),
               (@{const_name If}, "If"),
               (@{type_name "*"}, "prod"),
               (@{type_name "+"}, "sum")]

(* Invert the table of translations between Isabelle and ATPs. *)
val const_trans_table_inv =
  Symtab.update ("fequal", @{const_name "op ="})
                (Symtab.make (map swap (Symtab.dest const_trans_table)))

val invert_const = perhaps (Symtab.lookup const_trans_table_inv)

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

(* If string s has the prefix s1, return the result of deleting it,
   un-ASCII'd. *)
fun strip_prefix s1 s =
  if String.isPrefix s1 s then
    SOME (undo_ascii_of (String.extract (s, size s1, NONE)))
  else
    NONE

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

fun lookup_const c =
  case Symtab.lookup const_trans_table c of
    SOME c' => c'
  | NONE => ascii_of c

(* "op =" MUST BE "equal" because it's built into ATPs. *)
fun make_fixed_const @{const_name "op ="} = "equal"
  | make_fixed_const c = const_prefix ^ lookup_const c

fun make_fixed_type_const c = tconst_prefix ^ lookup_const c

fun make_type_class clas = class_prefix ^ ascii_of clas;


(**** name pool ****)
 
type name = string * string
type name_pool = string Symtab.table * string Symtab.table

fun empty_name_pool readable_names =
  if readable_names then SOME (`I Symtab.empty) else NONE

fun pool_fold f xs z = pair z #> fold_rev (fn x => uncurry (f x)) xs
fun pool_map f xs =
  pool_fold (fn x => fn ys => fn pool => f x pool |>> (fn y => y :: ys)) xs []

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
    val s = s |> Long_Name.base_name |> Name.desymbolize false
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

(**** Definitions and functions for FOL clauses for TPTP format output ****)

datatype kind = Axiom | Conjecture;

(**** Isabelle FOL clauses ****)

(* The first component is the type class; the second is a TVar or TFree. *)
datatype type_literal =
  TyLitVar of string * name |
  TyLitFree of string * name

exception CLAUSE of string * term;

(*Make literals for sorted type variables*)
fun sorts_on_typs_aux (_, [])   = []
  | sorts_on_typs_aux ((x,i),  s::ss) =
      let val sorts = sorts_on_typs_aux ((x,i), ss)
      in
          if s = "HOL.type" then sorts
          else if i = ~1 then TyLitFree (make_type_class s, `make_fixed_type_var x) :: sorts
          else TyLitVar (make_type_class s, (make_schematic_type_var (x,i), x)) :: sorts
      end;

fun sorts_on_typs (TFree (a,s)) = sorts_on_typs_aux ((a,~1),s)
  | sorts_on_typs (TVar (v,s))  = sorts_on_typs_aux (v,s);

(*Given a list of sorted type variables, return a list of type literals.*)
fun type_literals_for_types Ts =
  fold (union (op =)) (map sorts_on_typs Ts) []

(** make axiom and conjecture clauses. **)

(**** Isabelle arities ****)

datatype arLit = TConsLit of class * string * string list
               | TVarLit of class * string;

datatype arity_clause =
  ArityClause of {axiom_name: string, conclLit: arLit, premLits: arLit list}


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

datatype classrel_clause =
  ClassrelClause of {axiom_name: string, subclass: class, superclass: class}

(*Generate all pairs (sub,super) such that sub is a proper subclass of super in theory thy.*)
fun class_pairs _ [] _ = []
  | class_pairs thy subs supers =
      let
        val class_less = Sorts.class_less (Sign.classes_of thy)
        fun add_super sub super = class_less (sub, super) ? cons (sub, super)
        fun add_supers sub = fold (add_super sub) supers
      in fold add_supers subs [] end

fun make_classrel_clause (sub,super) =
  ClassrelClause {axiom_name = classrel_clause_prefix ^ ascii_of sub ^ "_" ^
                               ascii_of super,
                  subclass = make_type_class sub,
                  superclass = make_type_class super};

fun make_classrel_clauses thy subs supers =
  map make_classrel_clause (class_pairs thy subs supers);


(** Isabelle arities **)

fun arity_clause _ _ (_, []) = []
  | arity_clause seen n (tcons, ("HOL.type",_)::ars) =  (*ignore*)
      arity_clause seen n (tcons,ars)
  | arity_clause seen n (tcons, (ar as (class,_)) :: ars) =
      if member (op =) seen class then (*multiple arities for the same tycon, class pair*)
          make_axiom_arity_clause (tcons, lookup_const tcons ^ "_" ^ class ^ "_" ^ Int.toString n, ar) ::
          arity_clause seen (n+1) (tcons,ars)
      else
          make_axiom_arity_clause (tcons, lookup_const tcons ^ "_" ^ class, ar) ::
          arity_clause (class::seen) n (tcons,ars)

fun multi_arity_clause [] = []
  | multi_arity_clause ((tcons, ars) :: tc_arlists) =
      arity_clause [] 1 (tcons, ars) @ multi_arity_clause tc_arlists

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
fun iter_type_class_pairs _ _ [] = ([], [])
  | iter_type_class_pairs thy tycons classes =
      let val cpairs = type_class_pairs thy tycons classes
          val newclasses = union_all (union_all (union_all (map (map #2 o #2) cpairs)))
            |> subtract (op =) classes |> subtract (op =) HOLogic.typeS
          val (classes', cpairs') = iter_type_class_pairs thy tycons newclasses
      in (union (op =) classes' classes, union (op =) cpairs' cpairs) end;

fun make_arity_clauses thy tycons classes =
  let val (classes', cpairs) = iter_type_class_pairs thy tycons classes
  in  (classes', multi_arity_clause cpairs)  end;

end;
