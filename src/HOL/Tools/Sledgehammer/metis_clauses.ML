(*  Title:      HOL/Tools/Sledgehammer/metis_clauses.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Storing/printing FOL clauses and arity clauses.  Typed equality is
treated differently.
*)

signature METIS_CLAUSES =
sig
  type name = string * string
  datatype type_literal =
    TyLitVar of name * name |
    TyLitFree of name * name
  datatype arLit =
    TConsLit of name * name * name list |
    TVarLit of name * name
  datatype arity_clause =
    ArityClause of {axiom_name: string, conclLit: arLit, premLits: arLit list}
  datatype class_rel_clause =
    ClassRelClause of {axiom_name: string, subclass: name, superclass: name}
  datatype combtyp =
    CombTVar of name |
    CombTFree of name |
    CombType of name * combtyp list
  datatype combterm =
    CombConst of name * combtyp * combtyp list (* Const and Free *) |
    CombVar of name * combtyp |
    CombApp of combterm * combterm
  datatype fol_literal = FOLLiteral of bool * combterm

  val type_wrapper_name : string
  val bound_var_prefix : string
  val schematic_var_prefix: string
  val fixed_var_prefix: string
  val tvar_prefix: string
  val tfree_prefix: string
  val const_prefix: string
  val type_const_prefix: string
  val class_prefix: string
  val union_all: ''a list list -> ''a list
  val invert_const: string -> string
  val ascii_of: string -> string
  val undo_ascii_of: string -> string
  val strip_prefix_and_undo_ascii: string -> string -> string option
  val make_bound_var : string -> string
  val make_schematic_var : string * int -> string
  val make_fixed_var : string -> string
  val make_schematic_type_var : string * int -> string
  val make_fixed_type_var : string -> string
  val make_fixed_const : string -> string
  val make_fixed_type_const : string -> string
  val make_type_class : string -> string
  val skolem_theory_name: string
  val skolem_prefix: string
  val skolem_infix: string
  val is_skolem_const_name: string -> bool
  val num_type_args: theory -> string -> int
  val type_literals_for_types : typ list -> type_literal list
  val make_class_rel_clauses: theory -> class list -> class list -> class_rel_clause list
  val make_arity_clauses: theory -> string list -> class list -> class list * arity_clause list
  val combtyp_of : combterm -> combtyp
  val strip_combterm_comb : combterm -> combterm * combterm list
  val combterm_from_term :
    theory -> (string * typ) list -> term -> combterm * typ list
  val literals_of_term : theory -> term -> fol_literal list * typ list
  val conceal_skolem_terms :
    int -> (string * term) list -> term -> (string * term) list * term
  val reveal_skolem_terms : (string * term) list -> term -> term
  val tfree_classes_of_terms : term list -> string list
  val tvar_classes_of_terms : term list -> string list
  val type_consts_of_terms : theory -> term list -> string list
end

structure Metis_Clauses : METIS_CLAUSES =
struct

val type_wrapper_name = "ti"

val bound_var_prefix = "B_"
val schematic_var_prefix = "V_"
val fixed_var_prefix = "v_"

val tvar_prefix = "T_";
val tfree_prefix = "t_";

val class_rel_clause_prefix = "clsrel_";

val const_prefix = "c_";
val type_const_prefix = "tc_";
val class_prefix = "class_";

fun union_all xss = fold (union (op =)) xss []

(* Readable names for the more common symbolic functions. Do not mess with the
   last nine entries of the table unless you know what you are doing. *)
val const_trans_table =
  Symtab.make [(@{type_name Product_Type.prod}, "prod"),
               (@{type_name Sum_Type.sum}, "sum"),
               (@{const_name "op ="}, "equal"),
               (@{const_name "op &"}, "and"),
               (@{const_name "op |"}, "or"),
               (@{const_name "op -->"}, "implies"),
               (@{const_name Set.member}, "in"),
               (@{const_name fequal}, "fequal"),
               (@{const_name COMBI}, "COMBI"),
               (@{const_name COMBK}, "COMBK"),
               (@{const_name COMBB}, "COMBB"),
               (@{const_name COMBC}, "COMBC"),
               (@{const_name COMBS}, "COMBS"),
               (@{const_name True}, "True"),
               (@{const_name False}, "False"),
               (@{const_name If}, "If")]

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
fun strip_prefix_and_undo_ascii s1 s =
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

fun make_bound_var x = bound_var_prefix ^ ascii_of x
fun make_schematic_var v = schematic_var_prefix ^ ascii_of_indexname v
fun make_fixed_var x = fixed_var_prefix ^ ascii_of x

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

fun make_fixed_type_const c = type_const_prefix ^ lookup_const c

fun make_type_class clas = class_prefix ^ ascii_of clas;

val skolem_theory_name = "Sledgehammer" ^ Long_Name.separator ^ "Sko"
val skolem_prefix = "sko_"
val skolem_infix = "$"

(* Hack: Could return false positives (e.g., a user happens to declare a
   constant called "SomeTheory.sko_means_shoe_in_$wedish". *)
val is_skolem_const_name =
  Long_Name.base_name
  #> String.isPrefix skolem_prefix andf String.isSubstring skolem_infix

(* The number of type arguments of a constant, zero if it's monomorphic. For
   (instances of) Skolem pseudoconstants, this information is encoded in the
   constant name. *)
fun num_type_args thy s =
  if String.isPrefix skolem_theory_name s then
    s |> unprefix skolem_theory_name
      |> space_explode skolem_infix |> hd
      |> space_explode "_" |> List.last |> Int.fromString |> the
  else
    (s, Sign.the_const_type thy s) |> Sign.const_typargs thy |> length

(**** Definitions and functions for FOL clauses for TPTP format output ****)

type name = string * string

(**** Isabelle FOL clauses ****)

(* The first component is the type class; the second is a TVar or TFree. *)
datatype type_literal =
  TyLitVar of name * name |
  TyLitFree of name * name

exception CLAUSE of string * term;

(*Make literals for sorted type variables*)
fun sorts_on_typs_aux (_, [])   = []
  | sorts_on_typs_aux ((x,i),  s::ss) =
      let val sorts = sorts_on_typs_aux ((x,i), ss)
      in
          if s = "HOL.type" then sorts
          else if i = ~1 then TyLitFree (`make_type_class s, `make_fixed_type_var x) :: sorts
          else TyLitVar (`make_type_class s, (make_schematic_type_var (x,i), x)) :: sorts
      end;

fun sorts_on_typs (TFree (a,s)) = sorts_on_typs_aux ((a,~1),s)
  | sorts_on_typs (TVar (v,s))  = sorts_on_typs_aux (v,s);

(*Given a list of sorted type variables, return a list of type literals.*)
fun type_literals_for_types Ts =
  fold (union (op =)) (map sorts_on_typs Ts) []

(** make axiom and conjecture clauses. **)

(**** Isabelle arities ****)

datatype arLit =
  TConsLit of name * name * name list |
  TVarLit of name * name

datatype arity_clause =
  ArityClause of {axiom_name: string, conclLit: arLit, premLits: arLit list}


fun gen_TVars 0 = []
  | gen_TVars n = ("T_" ^ Int.toString n) :: gen_TVars (n-1);

fun pack_sort(_,[])  = []
  | pack_sort(tvar, "HOL.type"::srt) = pack_sort (tvar, srt)   (*IGNORE sort "type"*)
  | pack_sort(tvar, cls::srt) =
    (`make_type_class cls, (tvar, tvar)) :: pack_sort (tvar, srt)

(*Arity of type constructor tcon :: (arg1,...,argN)res*)
fun make_axiom_arity_clause (tcons, axiom_name, (cls,args)) =
  let
    val tvars = gen_TVars (length args)
    val tvars_srts = ListPair.zip (tvars, args)
  in
    ArityClause {axiom_name = axiom_name, 
                 conclLit = TConsLit (`make_type_class cls,
                                      `make_fixed_type_const tcons,
                                      tvars ~~ tvars),
                 premLits = map TVarLit (union_all (map pack_sort tvars_srts))}
  end


(**** Isabelle class relations ****)

datatype class_rel_clause =
  ClassRelClause of {axiom_name: string, subclass: name, superclass: name}

(*Generate all pairs (sub,super) such that sub is a proper subclass of super in theory thy.*)
fun class_pairs _ [] _ = []
  | class_pairs thy subs supers =
      let
        val class_less = Sorts.class_less (Sign.classes_of thy)
        fun add_super sub super = class_less (sub, super) ? cons (sub, super)
        fun add_supers sub = fold (add_super sub) supers
      in fold add_supers subs [] end

fun make_class_rel_clause (sub,super) =
  ClassRelClause {axiom_name = class_rel_clause_prefix ^ ascii_of sub ^ "_" ^
                               ascii_of super,
                  subclass = `make_type_class sub,
                  superclass = `make_type_class super};

fun make_class_rel_clauses thy subs supers =
  map make_class_rel_clause (class_pairs thy subs supers);


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

datatype combtyp =
  CombTVar of name |
  CombTFree of name |
  CombType of name * combtyp list

datatype combterm =
  CombConst of name * combtyp * combtyp list (* Const and Free *) |
  CombVar of name * combtyp |
  CombApp of combterm * combterm

datatype fol_literal = FOLLiteral of bool * combterm

(*********************************************************************)
(* convert a clause with type Term.term to a clause with type clause *)
(*********************************************************************)

(*Result of a function type; no need to check that the argument type matches.*)
fun result_type (CombType (_, [_, tp2])) = tp2
  | result_type _ = raise Fail "non-function type"

fun combtyp_of (CombConst (_, tp, _)) = tp
  | combtyp_of (CombVar (_, tp)) = tp
  | combtyp_of (CombApp (t1, _)) = result_type (combtyp_of t1)

(*gets the head of a combinator application, along with the list of arguments*)
fun strip_combterm_comb u =
    let fun stripc (CombApp(t,u), ts) = stripc (t, u::ts)
        |   stripc  x =  x
    in stripc(u,[]) end

fun type_of (Type (a, Ts)) =
    let val (folTypes,ts) = types_of Ts in
      (CombType (`make_fixed_type_const a, folTypes), ts)
    end
  | type_of (tp as TFree (a, _)) = (CombTFree (`make_fixed_type_var a), [tp])
  | type_of (tp as TVar (x, _)) =
    (CombTVar (make_schematic_type_var x, string_of_indexname x), [tp])
and types_of Ts =
    let val (folTyps, ts) = ListPair.unzip (map type_of Ts) in
      (folTyps, union_all ts)
    end

(* same as above, but no gathering of sort information *)
fun simp_type_of (Type (a, Ts)) =
      CombType (`make_fixed_type_const a, map simp_type_of Ts)
  | simp_type_of (TFree (a, _)) = CombTFree (`make_fixed_type_var a)
  | simp_type_of (TVar (x, _)) =
    CombTVar (make_schematic_type_var x, string_of_indexname x)

(* Converts a term (with combinators) into a combterm. Also accummulates sort
   infomation. *)
fun combterm_from_term thy bs (P $ Q) =
      let val (P', tsP) = combterm_from_term thy bs P
          val (Q', tsQ) = combterm_from_term thy bs Q
      in  (CombApp (P', Q'), union (op =) tsP tsQ)  end
  | combterm_from_term thy _ (Const (c, T)) =
      let
        val (tp, ts) = type_of T
        val tvar_list =
          (if String.isPrefix skolem_theory_name c then
             [] |> Term.add_tvarsT T |> map TVar
           else
             (c, T) |> Sign.const_typargs thy)
          |> map simp_type_of
        val c' = CombConst (`make_fixed_const c, tp, tvar_list)
      in  (c',ts)  end
  | combterm_from_term _ _ (Free (v, T)) =
      let val (tp,ts) = type_of T
          val v' = CombConst (`make_fixed_var v, tp, [])
      in  (v',ts)  end
  | combterm_from_term _ _ (Var (v, T)) =
      let val (tp,ts) = type_of T
          val v' = CombVar ((make_schematic_var v, string_of_indexname v), tp)
      in  (v',ts)  end
  | combterm_from_term _ bs (Bound j) =
      let
        val (s, T) = nth bs j
        val (tp, ts) = type_of T
        val v' = CombConst (`make_bound_var s, tp, [])
      in (v', ts) end
  | combterm_from_term _ _ (Abs _) = raise Fail "HOL clause: Abs"

fun predicate_of thy ((@{const Not} $ P), pos) = predicate_of thy (P, not pos)
  | predicate_of thy (t, pos) =
    (combterm_from_term thy [] (Envir.eta_contract t), pos)

fun literals_of_term1 args thy (@{const Trueprop} $ P) =
    literals_of_term1 args thy P
  | literals_of_term1 args thy (@{const "op |"} $ P $ Q) =
    literals_of_term1 (literals_of_term1 args thy P) thy Q
  | literals_of_term1 (lits, ts) thy P =
    let val ((pred, ts'), pol) = predicate_of thy (P, true) in
      (FOLLiteral (pol, pred) :: lits, union (op =) ts ts')
    end
val literals_of_term = literals_of_term1 ([], [])

fun skolem_name i j num_T_args =
  skolem_prefix ^ (space_implode "_" (map Int.toString [i, j, num_T_args])) ^
  skolem_infix ^ "g"

fun conceal_skolem_terms i skolems t =
  if exists_Const (curry (op =) @{const_name skolem_id} o fst) t then
    let
      fun aux skolems
              (t as (Const (@{const_name skolem_id}, Type (_, [_, T])) $ _)) =
          let
            val (skolems, s) =
              if i = ~1 then
                (skolems, @{const_name undefined})
              else case AList.find (op aconv) skolems t of
                s :: _ => (skolems, s)
              | [] =>
                let
                  val s = skolem_theory_name ^ "." ^
                          skolem_name i (length skolems)
                                        (length (Term.add_tvarsT T []))
                in ((s, t) :: skolems, s) end
          in (skolems, Const (s, T)) end
        | aux skolems (t1 $ t2) =
          let
            val (skolems, t1) = aux skolems t1
            val (skolems, t2) = aux skolems t2
          in (skolems, t1 $ t2) end
        | aux skolems (Abs (s, T, t')) =
          let val (skolems, t') = aux skolems t' in
            (skolems, Abs (s, T, t'))
          end
        | aux skolems t = (skolems, t)
    in aux skolems t end
  else
    (skolems, t)

fun reveal_skolem_terms skolems =
  map_aterms (fn t as Const (s, _) =>
                 if String.isPrefix skolem_theory_name s then
                   AList.lookup (op =) skolems s |> the
                   |> map_types Type_Infer.paramify_vars
                 else
                   t
               | t => t)


(***************************************************************)
(* Type Classes Present in the Axiom or Conjecture Clauses     *)
(***************************************************************)

fun set_insert (x, s) = Symtab.update (x, ()) s

fun add_classes (sorts, cset) = List.foldl set_insert cset (flat sorts)

(*Remove this trivial type class*)
fun delete_type cset = Symtab.delete_safe (the_single @{sort HOL.type}) cset;

fun tfree_classes_of_terms ts =
  let val sorts_list = map (map #2 o OldTerm.term_tfrees) ts
  in  Symtab.keys (delete_type (List.foldl add_classes Symtab.empty sorts_list))  end;

fun tvar_classes_of_terms ts =
  let val sorts_list = map (map #2 o OldTerm.term_tvars) ts
  in  Symtab.keys (delete_type (List.foldl add_classes Symtab.empty sorts_list))  end;

(*fold type constructors*)
fun fold_type_consts f (Type (a, Ts)) x = fold (fold_type_consts f) Ts (f (a,x))
  | fold_type_consts _ _ x = x;

(*Type constructors used to instantiate overloaded constants are the only ones needed.*)
fun add_type_consts_in_term thy =
  let
    val const_typargs = Sign.const_typargs thy
    fun aux (Const x) = fold (fold_type_consts set_insert) (const_typargs x)
      | aux (Abs (_, _, u)) = aux u
      | aux (Const (@{const_name skolem_id}, _) $ _) = I
      | aux (t $ u) = aux t #> aux u
      | aux _ = I
  in aux end

fun type_consts_of_terms thy ts =
  Symtab.keys (fold (add_type_consts_in_term thy) ts Symtab.empty);

end;
