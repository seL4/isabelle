(*  Title:      HOL/Tools/Sledgehammer/metis_translate.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Kong W. Susanto, Cambridge University Computer Laboratory
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Metis.
*)

signature METIS_TRANSLATE =
sig
  type name = string * string
  datatype type_literal =
    TyLitVar of name * name |
    TyLitFree of name * name
  datatype arLit =
    TConsLit of name * name * name list |
    TVarLit of name * name
  datatype arity_clause =
    ArityClause of {name: string, conclLit: arLit, premLits: arLit list}
  datatype class_rel_clause =
    ClassRelClause of {name: string, subclass: name, superclass: name}
  datatype combtyp =
    CombTVar of name |
    CombTFree of name |
    CombType of name * combtyp list
  datatype combterm =
    CombConst of name * combtyp * combtyp list (* Const and Free *) |
    CombVar of name * combtyp |
    CombApp of combterm * combterm
  datatype fol_literal = FOLLiteral of bool * combterm

  datatype mode = FO | HO | FT
  type logic_map =
    {axioms: (Metis_Thm.thm * thm) list,
     tfrees: type_literal list,
     old_skolems: (string * term) list}

  val type_wrapper_name : string
  val bound_var_prefix : string
  val schematic_var_prefix: string
  val fixed_var_prefix: string
  val tvar_prefix: string
  val tfree_prefix: string
  val const_prefix: string
  val type_const_prefix: string
  val class_prefix: string
  val new_skolem_const_prefix : string
  val invert_const: string -> string
  val ascii_of: string -> string
  val unascii_of: string -> string
  val strip_prefix_and_unascii: string -> string -> string option
  val make_bound_var : string -> string
  val make_schematic_var : string * int -> string
  val make_fixed_var : string -> string
  val make_schematic_type_var : string * int -> string
  val make_fixed_type_var : string -> string
  val make_fixed_const : string -> string
  val make_fixed_type_const : string -> string
  val make_type_class : string -> string
  val num_type_args: theory -> string -> int
  val new_skolem_var_from_const: string -> indexname
  val type_literals_for_types : typ list -> type_literal list
  val make_class_rel_clauses :
    theory -> class list -> class list -> class_rel_clause list
  val make_arity_clauses :
    theory -> string list -> class list -> class list * arity_clause list
  val combtyp_of : combterm -> combtyp
  val strip_combterm_comb : combterm -> combterm * combterm list
  val combterm_from_term :
    theory -> int -> (string * typ) list -> term -> combterm * typ list
  val reveal_old_skolem_terms : (string * term) list -> term -> term
  val tfree_classes_of_terms : term list -> string list
  val tvar_classes_of_terms : term list -> string list
  val type_consts_of_terms : theory -> term list -> string list
  val string_of_mode : mode -> string
  val build_logic_map :
    mode -> Proof.context -> bool -> thm list -> thm list list
    -> mode * logic_map
end

structure Metis_Translate : METIS_TRANSLATE =
struct

val type_wrapper_name = "ti"

val bound_var_prefix = "B_"
val schematic_var_prefix = "V_"
val fixed_var_prefix = "v_"

val tvar_prefix = "T_";
val tfree_prefix = "t_";

val const_prefix = "c_";
val type_const_prefix = "tc_";
val class_prefix = "class_";

val skolem_const_prefix = "Sledgehammer" ^ Long_Name.separator ^ "Sko"
val old_skolem_const_prefix = skolem_const_prefix ^ "o"
val new_skolem_const_prefix = skolem_const_prefix ^ "n"

fun union_all xss = fold (union (op =)) xss []

(* Readable names for the more common symbolic functions. Do not mess with the
   last nine entries of the table unless you know what you are doing. *)
val const_trans_table =
  Symtab.make [(@{type_name Product_Type.prod}, "prod"),
               (@{type_name Sum_Type.sum}, "sum"),
               (@{const_name HOL.eq}, "equal"),
               (@{const_name HOL.conj}, "and"),
               (@{const_name HOL.disj}, "or"),
               (@{const_name HOL.implies}, "implies"),
               (@{const_name Set.member}, "member"),
               (@{const_name fequal}, "fequal"),
               (@{const_name Meson.COMBI}, "COMBI"),
               (@{const_name Meson.COMBK}, "COMBK"),
               (@{const_name Meson.COMBB}, "COMBB"),
               (@{const_name Meson.COMBC}, "COMBC"),
               (@{const_name Meson.COMBS}, "COMBS"),
               (@{const_name True}, "True"),
               (@{const_name False}, "False"),
               (@{const_name If}, "If")]

(* Invert the table of translations between Isabelle and ATPs. *)
val const_trans_table_inv =
  Symtab.update ("fequal", @{const_name HOL.eq})
                (Symtab.make (map swap (Symtab.dest const_trans_table)))

val invert_const = perhaps (Symtab.lookup const_trans_table_inv)

(*Escaping of special characters.
  Alphanumeric characters are left unchanged.
  The character _ goes to __
  Characters in the range ASCII space to / go to _A to _P, respectively.
  Other characters go to _nnn where nnn is the decimal ASCII code.*)
val A_minus_space = Char.ord #"A" - Char.ord #" ";

fun stringN_of_int 0 _ = ""
  | stringN_of_int k n = stringN_of_int (k-1) (n div 10) ^ Int.toString (n mod 10);

fun ascii_of_c c =
  if Char.isAlphaNum c then String.str c
  else if c = #"_" then "__"
  else if #" " <= c andalso c <= #"/"
       then "_" ^ String.str (Char.chr (Char.ord c + A_minus_space))
  else ("_" ^ stringN_of_int 3 (Char.ord c))  (*fixed width, in case more digits follow*)

val ascii_of = String.translate ascii_of_c;

(** Remove ASCII armouring from names in proof files **)

(*We don't raise error exceptions because this code can run inside the watcher.
  Also, the errors are "impossible" (hah!)*)
fun unascii_aux rcs [] = String.implode(rev rcs)
  | unascii_aux rcs [#"_"] = unascii_aux (#"_"::rcs) []  (*ERROR*)
      (*Three types of _ escapes: __, _A to _P, _nnn*)
  | unascii_aux rcs (#"_" :: #"_" :: cs) = unascii_aux (#"_"::rcs) cs
  | unascii_aux rcs (#"_" :: c :: cs) =
      if #"A" <= c andalso c<= #"P"  (*translation of #" " to #"/"*)
      then unascii_aux (Char.chr(Char.ord c - A_minus_space) :: rcs) cs
      else
        let val digits = List.take (c::cs, 3) handle Subscript => []
        in
            case Int.fromString (String.implode digits) of
                NONE => unascii_aux (c:: #"_"::rcs) cs  (*ERROR*)
              | SOME n => unascii_aux (Char.chr n :: rcs) (List.drop (cs, 2))
        end
  | unascii_aux rcs (c::cs) = unascii_aux (c::rcs) cs
val unascii_of = unascii_aux [] o String.explode

(* If string s has the prefix s1, return the result of deleting it,
   un-ASCII'd. *)
fun strip_prefix_and_unascii s1 s =
  if String.isPrefix s1 s then
    SOME (unascii_of (String.extract (s, size s1, NONE)))
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

(* HOL.eq MUST BE "equal" because it's built into ATPs. *)
fun make_fixed_const @{const_name HOL.eq} = "equal"
  | make_fixed_const c = const_prefix ^ lookup_const c

fun make_fixed_type_const c = type_const_prefix ^ lookup_const c

fun make_type_class clas = class_prefix ^ ascii_of clas;

(* The number of type arguments of a constant, zero if it's monomorphic. For
   (instances of) Skolem pseudoconstants, this information is encoded in the
   constant name. *)
fun num_type_args thy s =
  if String.isPrefix skolem_const_prefix s then
    s |> space_explode Long_Name.separator |> List.last |> Int.fromString |> the
  else
    (s, Sign.the_const_type thy s) |> Sign.const_typargs thy |> length

fun new_skolem_var_from_const s =
  let
    val ss = s |> space_explode Long_Name.separator
    val n = length ss
  in (nth ss (n - 2), nth ss (n - 3) |> Int.fromString |> the) end


(**** Definitions and functions for FOL clauses for TPTP format output ****)

type name = string * string

(**** Isabelle FOL clauses ****)

(* The first component is the type class; the second is a TVar or TFree. *)
datatype type_literal =
  TyLitVar of name * name |
  TyLitFree of name * name

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
  ArityClause of {name: string, conclLit: arLit, premLits: arLit list}


fun gen_TVars 0 = []
  | gen_TVars n = ("T_" ^ Int.toString n) :: gen_TVars (n-1);

fun pack_sort(_,[])  = []
  | pack_sort(tvar, "HOL.type"::srt) = pack_sort (tvar, srt)   (*IGNORE sort "type"*)
  | pack_sort(tvar, cls::srt) =
    (`make_type_class cls, (tvar, tvar)) :: pack_sort (tvar, srt)

(*Arity of type constructor tcon :: (arg1,...,argN)res*)
fun make_axiom_arity_clause (tcons, name, (cls,args)) =
  let
    val tvars = gen_TVars (length args)
    val tvars_srts = ListPair.zip (tvars, args)
  in
    ArityClause {name = name,
                 conclLit = TConsLit (`make_type_class cls,
                                      `make_fixed_type_const tcons,
                                      tvars ~~ tvars),
                 premLits = map TVarLit (union_all (map pack_sort tvars_srts))}
  end


(**** Isabelle class relations ****)

datatype class_rel_clause =
  ClassRelClause of {name: string, subclass: name, superclass: name}

(*Generate all pairs (sub,super) such that sub is a proper subclass of super in theory thy.*)
fun class_pairs _ [] _ = []
  | class_pairs thy subs supers =
      let
        val class_less = Sorts.class_less (Sign.classes_of thy)
        fun add_super sub super = class_less (sub, super) ? cons (sub, super)
        fun add_supers sub = fold (add_super sub) supers
      in fold add_supers subs [] end

fun make_class_rel_clause (sub,super) =
  ClassRelClause {name = sub ^ "_" ^ super,
                  subclass = `make_type_class sub,
                  superclass = `make_type_class super}

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

fun combtype_of (Type (a, Ts)) =
    let val (folTypes, ts) = combtypes_of Ts in
      (CombType (`make_fixed_type_const a, folTypes), ts)
    end
  | combtype_of (tp as TFree (a, _)) = (CombTFree (`make_fixed_type_var a), [tp])
  | combtype_of (tp as TVar (x, _)) =
    (CombTVar (make_schematic_type_var x, string_of_indexname x), [tp])
and combtypes_of Ts =
  let val (folTyps, ts) = ListPair.unzip (map combtype_of Ts) in
    (folTyps, union_all ts)
  end

(* same as above, but no gathering of sort information *)
fun simple_combtype_of (Type (a, Ts)) =
    CombType (`make_fixed_type_const a, map simple_combtype_of Ts)
  | simple_combtype_of (TFree (a, _)) = CombTFree (`make_fixed_type_var a)
  | simple_combtype_of (TVar (x, _)) =
    CombTVar (make_schematic_type_var x, string_of_indexname x)

fun new_skolem_const_name th_no s num_T_args =
  [new_skolem_const_prefix, string_of_int th_no, s, string_of_int num_T_args]
  |> space_implode Long_Name.separator

(* Converts a term (with combinators) into a combterm. Also accummulates sort
   infomation. *)
fun combterm_from_term thy th_no bs (P $ Q) =
      let val (P', tsP) = combterm_from_term thy th_no bs P
          val (Q', tsQ) = combterm_from_term thy th_no bs Q
      in  (CombApp (P', Q'), union (op =) tsP tsQ)  end
  | combterm_from_term thy _ _ (Const (c, T)) =
      let
        val (tp, ts) = combtype_of T
        val tvar_list =
          (if String.isPrefix old_skolem_const_prefix c then
             [] |> Term.add_tvarsT T |> map TVar
           else
             (c, T) |> Sign.const_typargs thy)
          |> map simple_combtype_of
        val c' = CombConst (`make_fixed_const c, tp, tvar_list)
      in  (c',ts)  end
  | combterm_from_term _ _ _ (Free (v, T)) =
      let val (tp, ts) = combtype_of T
          val v' = CombConst (`make_fixed_var v, tp, [])
      in  (v',ts)  end
  | combterm_from_term _ th_no _ (Var (v as (s, _), T)) =
    let
      val (tp, ts) = combtype_of T
      val v' =
        if String.isPrefix Meson_Clausify.new_skolem_var_prefix s then
          let
            val tys = T |> strip_type |> swap |> op ::
            val s' = new_skolem_const_name th_no s (length tys)
          in
            CombConst (`make_fixed_const s', tp, map simple_combtype_of tys)
          end
        else
          CombVar ((make_schematic_var v, string_of_indexname v), tp)
    in (v', ts) end
  | combterm_from_term _ _ bs (Bound j) =
      let
        val (s, T) = nth bs j
        val (tp, ts) = combtype_of T
        val v' = CombConst (`make_bound_var s, tp, [])
      in (v', ts) end
  | combterm_from_term _ _ _ (Abs _) = raise Fail "HOL clause: Abs"

fun predicate_of thy th_no ((@{const Not} $ P), pos) =
    predicate_of thy th_no (P, not pos)
  | predicate_of thy th_no (t, pos) =
    (combterm_from_term thy th_no [] (Envir.eta_contract t), pos)

fun literals_of_term1 args thy th_no (@{const Trueprop} $ P) =
    literals_of_term1 args thy th_no P
  | literals_of_term1 args thy th_no (@{const HOL.disj} $ P $ Q) =
    literals_of_term1 (literals_of_term1 args thy th_no P) thy th_no Q
  | literals_of_term1 (lits, ts) thy th_no P =
    let val ((pred, ts'), pol) = predicate_of thy th_no (P, true) in
      (FOLLiteral (pol, pred) :: lits, union (op =) ts ts')
    end
val literals_of_term = literals_of_term1 ([], [])

fun old_skolem_const_name i j num_T_args =
  old_skolem_const_prefix ^ Long_Name.separator ^
  (space_implode Long_Name.separator (map Int.toString [i, j, num_T_args]))

fun conceal_old_skolem_terms i old_skolems t =
  if exists_Const (curry (op =) @{const_name Meson.skolem} o fst) t then
    let
      fun aux old_skolems
             (t as (Const (@{const_name Meson.skolem}, Type (_, [_, T])) $ _)) =
          let
            val (old_skolems, s) =
              if i = ~1 then
                (old_skolems, @{const_name undefined})
              else case AList.find (op aconv) old_skolems t of
                s :: _ => (old_skolems, s)
              | [] =>
                let
                  val s = old_skolem_const_name i (length old_skolems)
                                                (length (Term.add_tvarsT T []))
                in ((s, t) :: old_skolems, s) end
          in (old_skolems, Const (s, T)) end
        | aux old_skolems (t1 $ t2) =
          let
            val (old_skolems, t1) = aux old_skolems t1
            val (old_skolems, t2) = aux old_skolems t2
          in (old_skolems, t1 $ t2) end
        | aux old_skolems (Abs (s, T, t')) =
          let val (old_skolems, t') = aux old_skolems t' in
            (old_skolems, Abs (s, T, t'))
          end
        | aux old_skolems t = (old_skolems, t)
    in aux old_skolems t end
  else
    (old_skolems, t)

fun reveal_old_skolem_terms old_skolems =
  map_aterms (fn t as Const (s, _) =>
                 if String.isPrefix old_skolem_const_prefix s then
                   AList.lookup (op =) old_skolems s |> the
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
    fun aux (Const x) =
        fold (fold_type_consts set_insert) (Sign.const_typargs thy x)
      | aux (Abs (_, _, u)) = aux u
      | aux (Const (@{const_name Meson.skolem}, _) $ _) = I
      | aux (t $ u) = aux t #> aux u
      | aux _ = I
  in aux end

fun type_consts_of_terms thy ts =
  Symtab.keys (fold (add_type_consts_in_term thy) ts Symtab.empty);

(* ------------------------------------------------------------------------- *)
(* HOL to FOL  (Isabelle to Metis)                                           *)
(* ------------------------------------------------------------------------- *)

datatype mode = FO | HO | FT  (* first-order, higher-order, fully-typed *)

fun string_of_mode FO = "FO"
  | string_of_mode HO = "HO"
  | string_of_mode FT = "FT"

fun fn_isa_to_met_sublevel "equal" = "=" (* FIXME: "c_fequal" *)
  | fn_isa_to_met_sublevel x = x
fun fn_isa_to_met_toplevel "equal" = "="
  | fn_isa_to_met_toplevel x = x

fun metis_lit b c args = (b, (c, args));

fun metis_term_from_combtyp (CombTVar (s, _)) = Metis_Term.Var s
  | metis_term_from_combtyp (CombTFree (s, _)) = Metis_Term.Fn (s, [])
  | metis_term_from_combtyp (CombType ((s, _), tps)) =
    Metis_Term.Fn (s, map metis_term_from_combtyp tps);

(*These two functions insert type literals before the real literals. That is the
  opposite order from TPTP linkup, but maybe OK.*)

fun hol_term_to_fol_FO tm =
  case strip_combterm_comb tm of
      (CombConst ((c, _), _, tys), tms) =>
        let val tyargs = map metis_term_from_combtyp tys
            val args   = map hol_term_to_fol_FO tms
        in Metis_Term.Fn (c, tyargs @ args) end
    | (CombVar ((v, _), _), []) => Metis_Term.Var v
    | _ => raise Fail "non-first-order combterm"

fun hol_term_to_fol_HO (CombConst ((a, _), _, tylist)) =
      Metis_Term.Fn (fn_isa_to_met_sublevel a, map metis_term_from_combtyp tylist)
  | hol_term_to_fol_HO (CombVar ((s, _), _)) = Metis_Term.Var s
  | hol_term_to_fol_HO (CombApp (tm1, tm2)) =
       Metis_Term.Fn (".", map hol_term_to_fol_HO [tm1, tm2]);

(*The fully-typed translation, to avoid type errors*)
fun wrap_type (tm, ty) =
  Metis_Term.Fn (type_wrapper_name, [tm, metis_term_from_combtyp ty])

fun hol_term_to_fol_FT (CombVar ((s, _), ty)) = wrap_type (Metis_Term.Var s, ty)
  | hol_term_to_fol_FT (CombConst((a, _), ty, _)) =
      wrap_type (Metis_Term.Fn(fn_isa_to_met_sublevel a, []), ty)
  | hol_term_to_fol_FT (tm as CombApp(tm1,tm2)) =
       wrap_type (Metis_Term.Fn(".", map hol_term_to_fol_FT [tm1,tm2]),
                  combtyp_of tm)

fun hol_literal_to_fol FO (FOLLiteral (pos, tm)) =
      let val (CombConst((p, _), _, tys), tms) = strip_combterm_comb tm
          val tylits = if p = "equal" then [] else map metis_term_from_combtyp tys
          val lits = map hol_term_to_fol_FO tms
      in metis_lit pos (fn_isa_to_met_toplevel p) (tylits @ lits) end
  | hol_literal_to_fol HO (FOLLiteral (pos, tm)) =
     (case strip_combterm_comb tm of
          (CombConst(("equal", _), _, _), tms) =>
            metis_lit pos "=" (map hol_term_to_fol_HO tms)
        | _ => metis_lit pos "{}" [hol_term_to_fol_HO tm])   (*hBOOL*)
  | hol_literal_to_fol FT (FOLLiteral (pos, tm)) =
     (case strip_combterm_comb tm of
          (CombConst(("equal", _), _, _), tms) =>
            metis_lit pos "=" (map hol_term_to_fol_FT tms)
        | _ => metis_lit pos "{}" [hol_term_to_fol_FT tm])   (*hBOOL*);

fun literals_of_hol_term thy th_no mode t =
      let val (lits, types_sorts) = literals_of_term thy th_no t
      in  (map (hol_literal_to_fol mode) lits, types_sorts) end;

(*Sign should be "true" for conjecture type constraints, "false" for type lits in clauses.*)
fun metis_of_type_literals pos (TyLitVar ((s, _), (s', _))) =
    metis_lit pos s [Metis_Term.Var s']
  | metis_of_type_literals pos (TyLitFree ((s, _), (s', _))) =
    metis_lit pos s [Metis_Term.Fn (s',[])]

fun default_sort _ (TVar _) = false
  | default_sort ctxt (TFree (x, s)) = (s = the_default [] (Variable.def_sort ctxt (x, ~1)));

fun metis_of_tfree tf =
  Metis_Thm.axiom (Metis_LiteralSet.singleton (metis_of_type_literals true tf));

fun hol_thm_to_fol is_conjecture th_no ctxt type_lits mode j old_skolems th =
  let
    val thy = ProofContext.theory_of ctxt
    val (old_skolems, (mlits, types_sorts)) =
     th |> prop_of |> Logic.strip_imp_concl
        |> conceal_old_skolem_terms j old_skolems
        ||> (HOLogic.dest_Trueprop #> literals_of_hol_term thy th_no mode)
  in
    if is_conjecture then
      (Metis_Thm.axiom (Metis_LiteralSet.fromList mlits),
       type_literals_for_types types_sorts, old_skolems)
    else
      let
        val tylits = filter_out (default_sort ctxt) types_sorts
                     |> type_literals_for_types
        val mtylits =
          if type_lits then map (metis_of_type_literals false) tylits else []
      in
        (Metis_Thm.axiom (Metis_LiteralSet.fromList(mtylits @ mlits)), [],
         old_skolems)
      end
  end;

val helpers =
  [("c_COMBI", (false, map (`I) @{thms Meson.COMBI_def})),
   ("c_COMBK", (false, map (`I) @{thms Meson.COMBK_def})),
   ("c_COMBB", (false, map (`I) @{thms Meson.COMBB_def})),
   ("c_COMBC", (false, map (`I) @{thms Meson.COMBC_def})),
   ("c_COMBS", (false, map (`I) @{thms Meson.COMBS_def})),
   ("c_fequal", (false, map (rpair @{thm equal_imp_equal})
                            @{thms fequal_imp_equal equal_imp_fequal})),
   ("c_True", (true, map (`I) @{thms True_or_False})),
   ("c_False", (true, map (`I) @{thms True_or_False})),
   ("c_If", (true, map (`I) @{thms if_True if_False True_or_False}))]

(* ------------------------------------------------------------------------- *)
(* Logic maps manage the interface between HOL and first-order logic.        *)
(* ------------------------------------------------------------------------- *)

type logic_map =
  {axioms: (Metis_Thm.thm * thm) list,
   tfrees: type_literal list,
   old_skolems: (string * term) list}

fun is_quasi_fol_clause thy =
  Meson.is_fol_term thy o snd o conceal_old_skolem_terms ~1 [] o prop_of

(*Extract TFree constraints from context to include as conjecture clauses*)
fun init_tfrees ctxt =
  let fun add ((a,i),s) Ts = if i = ~1 then TFree(a,s) :: Ts else Ts in
    Vartab.fold add (#2 (Variable.constraints_of ctxt)) []
    |> type_literals_for_types
  end;

(*Insert non-logical axioms corresponding to all accumulated TFrees*)
fun add_tfrees {axioms, tfrees, old_skolems} : logic_map =
     {axioms = map (rpair TrueI o metis_of_tfree) (distinct (op =) tfrees) @
               axioms,
      tfrees = tfrees, old_skolems = old_skolems}

(*transform isabelle type / arity clause to metis clause *)
fun add_type_thm [] lmap = lmap
  | add_type_thm ((ith, mth) :: cls) {axioms, tfrees, old_skolems} =
      add_type_thm cls {axioms = (mth, ith) :: axioms, tfrees = tfrees,
                        old_skolems = old_skolems}

fun const_in_metis c (pred, tm_list) =
  let
    fun in_mterm (Metis_Term.Var _) = false
      | in_mterm (Metis_Term.Fn (".", tm_list)) = exists in_mterm tm_list
      | in_mterm (Metis_Term.Fn (nm, tm_list)) = c=nm orelse exists in_mterm tm_list
  in  c = pred orelse exists in_mterm tm_list  end;

(* ARITY CLAUSE *)
fun m_arity_cls (TConsLit ((c, _), (t, _), args)) =
    metis_lit true c [Metis_Term.Fn(t, map (Metis_Term.Var o fst) args)]
  | m_arity_cls (TVarLit ((c, _), (s, _))) =
    metis_lit false c [Metis_Term.Var s]
(*TrueI is returned as the Isabelle counterpart because there isn't any.*)
fun arity_cls (ArityClause {conclLit, premLits, ...}) =
  (TrueI,
   Metis_Thm.axiom (Metis_LiteralSet.fromList (map m_arity_cls (conclLit :: premLits))));

(* CLASSREL CLAUSE *)
fun m_class_rel_cls (subclass, _) (superclass, _) =
  [metis_lit false subclass [Metis_Term.Var "T"], metis_lit true superclass [Metis_Term.Var "T"]];
fun class_rel_cls (ClassRelClause {subclass, superclass, ...}) =
  (TrueI, Metis_Thm.axiom (Metis_LiteralSet.fromList (m_class_rel_cls subclass superclass)));

fun type_ext thy tms =
  let val subs = tfree_classes_of_terms tms
      val supers = tvar_classes_of_terms tms
      and tycons = type_consts_of_terms thy tms
      val (supers', arity_clauses) = make_arity_clauses thy tycons supers
      val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in  map class_rel_cls class_rel_clauses @ map arity_cls arity_clauses
  end;

(* Function to generate metis clauses, including comb and type clauses *)
fun build_logic_map mode0 ctxt type_lits cls thss =
  let val thy = ProofContext.theory_of ctxt
      (*The modes FO and FT are sticky. HO can be downgraded to FO.*)
      fun set_mode FO = FO
        | set_mode HO =
          if forall (forall (is_quasi_fol_clause thy)) (cls :: thss) then FO
          else HO
        | set_mode FT = FT
      val mode = set_mode mode0
      (*transform isabelle clause to metis clause *)
      fun add_thm th_no is_conjecture (metis_ith, isa_ith)
                  {axioms, tfrees, old_skolems} : logic_map =
        let
          val (mth, tfree_lits, old_skolems) =
            hol_thm_to_fol is_conjecture th_no ctxt type_lits mode (length axioms)
                           old_skolems metis_ith
        in
           {axioms = (mth, Meson.make_meta_clause isa_ith) :: axioms,
            tfrees = union (op =) tfree_lits tfrees, old_skolems = old_skolems}
        end;
      val lmap = {axioms = [], tfrees = init_tfrees ctxt, old_skolems = []}
                 |> fold (add_thm 0 true o `I) cls
                 |> add_tfrees
                 |> fold (fn (th_no, ths) => fold (add_thm th_no false o `I) ths)
                         (1 upto length thss ~~ thss)
      val clause_lists = map (Metis_Thm.clause o #1) (#axioms lmap)
      fun is_used c =
        exists (Metis_LiteralSet.exists (const_in_metis c o #2)) clause_lists
      val lmap =
        if mode = FO then
          lmap
        else
          let
            val helper_ths =
              helpers |> filter (is_used o fst)
                      |> maps (fn (c, (needs_full_types, thms)) =>
                                  if not (is_used c) orelse
                                     needs_full_types andalso mode <> FT then
                                    []
                                  else
                                    thms)
          in lmap |> fold (add_thm ~1 false) helper_ths end
  in
    (mode, add_type_thm (type_ext thy (maps (map prop_of) (cls :: thss))) lmap)
  end

end;
