(*  Title:      Pure/type_infer.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Type inference.
*)

signature TYPE_INFER =
sig
  val anyT: sort -> typ
  val logicT: typ
  val polymorphicT: typ -> typ
  val appl_error: Pretty.pp -> string -> term -> typ -> term -> typ -> string list
  val constrain: term -> typ -> term
  val param: int -> string * sort -> typ
  val paramify_dummies: int * typ -> int * typ
  val get_sort: Type.tsig -> (indexname -> sort option) -> (sort -> sort)
    -> (indexname * sort) list -> indexname -> sort
  val infer_types: Pretty.pp
    -> Type.tsig -> (string -> typ option) -> (indexname -> typ option)
    -> (indexname -> sort option) -> (string -> string) -> (typ -> typ)
    -> (sort -> sort) -> string list -> bool -> typ list -> term list
    -> term list * (indexname * typ) list
end;

structure TypeInfer: TYPE_INFER =
struct


(** term encodings **)

(*
  Flavours of term encodings:

    parse trees (type term):
      A very complicated structure produced by the syntax module's
      read functions.  Encodes types and sorts as terms; may contain
      explicit constraints and partial typing information (where
      dummies serve as wildcards).

      Parse trees are INTERNAL! Users should never encounter them,
      except in parse / print translation functions.

    raw terms (type term):
      Provide the user interface to type inferences.  They may contain
      partial type information (dummies are wildcards) or explicit
      type constraints (introduced via constrain: term -> typ ->
      term).

      The type inference function also lets users specify a certain
      subset of TVars to be treated as non-rigid inference parameters.

    preterms (type preterm):
      The internal representation for type inference.

    well-typed term (type term):
      Fully typed lambda terms to be accepted by appropriate
      certification functions.
*)



(** pretyps and preterms **)

(*links to parameters may get instantiated, anything else is rigid*)
datatype pretyp =
  PType of string * pretyp list |
  PTFree of string * sort |
  PTVar of indexname * sort |
  Param of sort |
  Link of pretyp ref;

datatype preterm =
  PConst of string * pretyp |
  PFree of string * pretyp |
  PVar of indexname * pretyp |
  PBound of int |
  PAbs of string * pretyp * preterm |
  PAppl of preterm * preterm |
  Constraint of preterm * pretyp;


(* utils *)

val mk_param = Link o ref o Param;

fun deref (T as Link (ref (Param _))) = T
  | deref (Link (ref T)) = deref T
  | deref T = T;

fun foldl_pretyps f (x, PConst (_, T)) = f (x, T)
  | foldl_pretyps f (x, PFree (_, T)) = f (x, T)
  | foldl_pretyps f (x, PVar (_, T)) = f (x, T)
  | foldl_pretyps _ (x, PBound _) = x
  | foldl_pretyps f (x, PAbs (_, T, t)) = foldl_pretyps f (f (x, T), t)
  | foldl_pretyps f (x, PAppl (t, u)) = foldl_pretyps f (foldl_pretyps f (x, t), u)
  | foldl_pretyps f (x, Constraint (t, T)) = f (foldl_pretyps f (x, t), T);



(** raw typs/terms to pretyps/preterms **)

(* pretyp(s)_of *)

fun anyT S = TFree ("'_dummy_", S);
val logicT = anyT [];

(*indicate polymorphic Vars*)
fun polymorphicT T = Type ("_polymorphic_", [T]);

fun pretyp_of is_param (params, typ) =
  let
    fun add_parms (ps, TVar (xi as (x, _), S)) =
          if is_param xi andalso is_none (assoc (ps, xi))
          then (xi, mk_param S) :: ps else ps
      | add_parms (ps, TFree _) = ps
      | add_parms (ps, Type (_, Ts)) = foldl add_parms (ps, Ts);

    val params' = add_parms (params, typ);

    fun pre_of (TVar (v as (xi, _))) =
          (case assoc (params', xi) of
            None => PTVar v
          | Some p => p)
      | pre_of (TFree ("'_dummy_", S)) = mk_param S
      | pre_of (TFree v) = PTFree v
      | pre_of (T as Type (a, Ts)) =
          if T = dummyT then mk_param []
          else PType (a, map pre_of Ts);
  in (params', pre_of typ) end;

fun pretyps_of is_param = foldl_map (pretyp_of is_param);


(* preterm(s)_of *)

fun preterm_of const_type is_param ((vparams, params), tm) =
  let
    fun add_vparm (ps, xi) =
      if is_none (assoc (ps, xi)) then
        (xi, mk_param []) :: ps
      else ps;

    fun add_vparms (ps, Var (xi, Type ("_polymorphic_", _))) = ps
      | add_vparms (ps, Var (xi, _)) = add_vparm (ps, xi)
      | add_vparms (ps, Free (x, _)) = add_vparm (ps, (x, ~1))
      | add_vparms (ps, Abs (_, _, t)) = add_vparms (ps, t)
      | add_vparms (ps, t $ u) = add_vparms (add_vparms (ps, t), u)
      | add_vparms (ps, _) = ps;

    val vparams' = add_vparms (vparams, tm);
    fun var_param xi = the (assoc (vparams', xi));


    val preT_of = pretyp_of is_param;

    fun constrain (ps, t) T =
      if T = dummyT then (ps, t)
      else
        let val (ps', T') = preT_of (ps, T)
        in (ps', Constraint (t, T')) end;

    fun pre_of (ps, Const (c, T)) =
          (case const_type c of
            Some U => constrain (ps, PConst (c, snd (pretyp_of (K true) ([], U)))) T
          | None => raise TYPE ("No such constant: " ^ quote c, [], []))
      | pre_of (ps, Var (xi, Type ("_polymorphic_", [T]))) =
          (ps, PVar (xi, snd (pretyp_of (K true) ([], T))))
      | pre_of (ps, Var (xi, T)) = constrain (ps, PVar (xi, var_param xi)) T
      | pre_of (ps, Free (x, T)) = constrain (ps, PFree (x, var_param (x, ~1))) T
      | pre_of (ps, Const ("_type_constraint_", T) $ t) = constrain (pre_of (ps, t)) T
      | pre_of (ps, Bound i) = (ps, PBound i)
      | pre_of (ps, Abs (x, T, t)) =
          let
            val (ps', T') = preT_of (ps, T);
            val (ps'', t') = pre_of (ps', t);
          in (ps'', PAbs (x, T', t')) end
      | pre_of (ps, t $ u) =
          let
            val (ps', t') = pre_of (ps, t);
            val (ps'', u') = pre_of (ps', u);
          in (ps'', PAppl (t', u')) end;

    val (params', tm') = pre_of (params, tm);
  in ((vparams', params'), tm') end;

fun preterms_of const_type is_param = foldl_map (preterm_of const_type is_param);



(** pretyps/terms to typs/terms **)

(* add_parms *)

fun add_parmsT (rs, PType (_, Ts)) = foldl add_parmsT (rs, Ts)
  | add_parmsT (rs, Link (r as ref (Param _))) = r ins rs
  | add_parmsT (rs, Link (ref T)) = add_parmsT (rs, T)
  | add_parmsT (rs, _) = rs;

val add_parms = foldl_pretyps add_parmsT;


(* add_names *)

fun add_namesT (xs, PType (_, Ts)) = foldl add_namesT (xs, Ts)
  | add_namesT (xs, PTFree (x, _)) = x ins xs
  | add_namesT (xs, PTVar ((x, _), _)) = x ins xs
  | add_namesT (xs, Link (ref T)) = add_namesT (xs, T)
  | add_namesT (xs, Param _) = xs;

val add_names = foldl_pretyps add_namesT;


(* simple_typ/term_of *)

(*deref links, fail on params*)
fun simple_typ_of (PType (a, Ts)) = Type (a, map simple_typ_of Ts)
  | simple_typ_of (PTFree v) = TFree v
  | simple_typ_of (PTVar v) = TVar v
  | simple_typ_of (Link (ref T)) = simple_typ_of T
  | simple_typ_of (Param _) = sys_error "simple_typ_of: illegal Param";

(*convert types, drop constraints*)
fun simple_term_of (PConst (c, T)) = Const (c, simple_typ_of T)
  | simple_term_of (PFree (x, T)) = Free (x, simple_typ_of T)
  | simple_term_of (PVar (xi, T)) = Var (xi, simple_typ_of T)
  | simple_term_of (PBound i) = Bound i
  | simple_term_of (PAbs (x, T, t)) = Abs (x, simple_typ_of T, simple_term_of t)
  | simple_term_of (PAppl (t, u)) = simple_term_of t $ simple_term_of u
  | simple_term_of (Constraint (t, _)) = simple_term_of t;


(* typs_terms_of *)                             (*DESTRUCTIVE*)

fun typs_terms_of used mk_var prfx (Ts, ts) =
  let
    fun elim (r as ref (Param S), x) = r := mk_var (x, S)
      | elim _ = ();

    val used' = foldl add_names (foldl add_namesT (used, Ts), ts);
    val parms = rev (foldl add_parms (foldl add_parmsT ([], Ts), ts));
    val names = Term.invent_names used' (prfx ^ "'a") (length parms);
  in
    seq2 elim (parms, names);
    (map simple_typ_of Ts, map simple_term_of ts)
  end;



(** order-sorted unification of types **)       (*DESTRUCTIVE*)

exception NO_UNIFIER of string;


fun unify pp classes arities =
  let

    (* adjust sorts of parameters *)

    fun not_in_sort x S' S =
      "Variable " ^ x ^ "::" ^ Pretty.string_of_sort pp S' ^ " not of sort " ^
        Pretty.string_of_sort pp S;

    fun no_domain (a, c) = "No way to get " ^ Pretty.string_of_arity pp (a, [], [c]);

    fun meet (_, []) = ()
      | meet (Link (r as (ref (Param S'))), S) =
          if Sorts.sort_le classes (S', S) then ()
          else r := mk_param (Sorts.inter_sort classes (S', S))
      | meet (Link (ref T), S) = meet (T, S)
      | meet (PType (a, Ts), S) =
          seq2 meet (Ts, Sorts.mg_domain (classes, arities) a S
            handle Sorts.DOMAIN ac => raise NO_UNIFIER (no_domain ac))
      | meet (PTFree (x, S'), S) =
          if Sorts.sort_le classes (S', S) then ()
          else raise NO_UNIFIER (not_in_sort x S' S)
      | meet (PTVar (xi, S'), S) =
          if Sorts.sort_le classes (S', S) then ()
          else raise NO_UNIFIER (not_in_sort (Syntax.string_of_vname xi) S' S)
      | meet (Param _, _) = sys_error "meet";


    (* occurs check and assigment *)

    fun occurs_check r (Link (r' as ref T)) =
          if r = r' then raise NO_UNIFIER "Occurs check!"
          else occurs_check r T
      | occurs_check r (PType (_, Ts)) = seq (occurs_check r) Ts
      | occurs_check _ _ = ();

    fun assign r T S =
      (case deref T of
        T' as Link (r' as ref (Param _)) =>
          if r = r' then () else (meet (T', S); r := T')
      | T' => (occurs_check r T'; meet (T', S); r := T'));


    (* unification *)

    fun unif (Link (r as ref (Param S)), T) = assign r T S
      | unif (T, Link (r as ref (Param S))) = assign r T S
      | unif (Link (ref T), U) = unif (T, U)
      | unif (T, Link (ref U)) = unif (T, U)
      | unif (PType (a, Ts), PType (b, Us)) =
          if a <> b then
            raise NO_UNIFIER ("Clash of types " ^ quote a ^ " and " ^ quote b)
          else seq2 unif (Ts, Us)
      | unif (T, U) = if T = U then () else raise NO_UNIFIER "";

  in unif end;



(** type inference **)

fun appl_error pp why t T u U =
 ["Type error in application: " ^ why,
  "",
  Pretty.string_of (Pretty.block
    [Pretty.str "Operator:", Pretty.brk 2, Pretty.term pp t,
      Pretty.str " ::", Pretty.brk 1, Pretty.typ pp T]),
  Pretty.string_of (Pretty.block
    [Pretty.str "Operand:", Pretty.brk 3, Pretty.term pp u,
      Pretty.str " ::", Pretty.brk 1, Pretty.typ pp U]),
  ""];


(* infer *)                                     (*DESTRUCTIVE*)

fun infer pp classes arities =
  let
    (* errors *)

    fun unif_failed msg =
      "Type unification failed" ^ (if msg = "" then "" else ": " ^ msg) ^ "\n";

    fun prep_output bs ts Ts =
      let
        val (Ts_bTs', ts') = typs_terms_of [] PTFree "??" (Ts @ map snd bs, ts);
        val (Ts',Ts'') = Library.splitAt(length Ts, Ts_bTs');
        val xs = map Free (map fst bs ~~ Ts'');
        val ts'' = map (fn t => subst_bounds (xs, t)) ts';
      in (ts'', Ts') end;

    fun err_loose i =
      raise TYPE ("Loose bound variable: B." ^ string_of_int i, [], []);

    fun err_appl msg bs t T u U =
      let
        val ([t', u'], [T', U']) = prep_output bs [t, u] [T, U];
        val why =
          (case T' of
            Type ("fun", _) => "Incompatible operand type"
          | _ => "Operator not of function type");
        val text = unif_failed msg ^ cat_lines (appl_error pp why t' T' u' U');
      in raise TYPE (text, [T', U'], [t', u']) end;

    fun err_constraint msg bs t T U =
      let
        val ([t'], [T', U']) = prep_output bs [t] [T, U];
        val text = cat_lines
         [unif_failed msg,
          "Cannot meet type constraint:", "",
          Pretty.string_of (Pretty.block
           [Pretty.str "Term:", Pretty.brk 2, Pretty.term pp t',
            Pretty.str " ::", Pretty.brk 1, Pretty.typ pp T']),
          Pretty.string_of (Pretty.block
           [Pretty.str "Type:", Pretty.brk 2, Pretty.typ pp U']), ""];
      in raise TYPE (text, [T', U'], [t']) end;


    (* main *)

    val unif = unify pp classes arities;

    fun inf _ (PConst (_, T)) = T
      | inf _ (PFree (_, T)) = T
      | inf _ (PVar (_, T)) = T
      | inf bs (PBound i) = snd (nth_elem (i, bs) handle LIST _ => err_loose i)
      | inf bs (PAbs (x, T, t)) = PType ("fun", [T, inf ((x, T) :: bs) t])
      | inf bs (PAppl (t, u)) =
          let
            val T = inf bs t;
            val U = inf bs u;
            val V = mk_param [];
            val U_to_V = PType ("fun", [U, V]);
            val _ = unif (U_to_V, T) handle NO_UNIFIER msg => err_appl msg bs t T u U;
          in V end
      | inf bs (Constraint (t, U)) =
          let val T = inf bs t in
            unif (T, U) handle NO_UNIFIER msg => err_constraint msg bs t T U;
            T
          end;

  in inf [] end;


(* basic_infer_types *)

fun basic_infer_types pp const_type classes arities used freeze is_param ts Ts =
  let
    (*convert to preterms/typs*)
    val (Tps, Ts') = pretyps_of (K true) ([], Ts);
    val ((vps, ps), ts') = preterms_of const_type is_param (([], Tps), ts);

    (*run type inference*)
    val tTs' = ListPair.map Constraint (ts', Ts');
    val _ = seq (fn t => (infer pp classes arities t; ())) tTs';

    (*collect result unifier*)
    fun ch_var (xi, Link (r as ref (Param S))) = (r := PTVar (xi, S); None)
      | ch_var xi_T = Some xi_T;
    val env = mapfilter ch_var Tps;

    (*convert back to terms/typs*)
    val mk_var =
      if freeze then PTFree
      else (fn (x, S) => PTVar ((x, 0), S));
    val (final_Ts, final_ts) = typs_terms_of used mk_var "" (Ts', ts');
    val final_env = map (apsnd simple_typ_of) env;
  in (final_ts, final_Ts, final_env) end;



(** type inference **)

(* user constraints *)

fun constrain t T =
  if T = dummyT then t
  else Const ("_type_constraint_", T) $ t;


(* user parameters *)

fun is_param (x, _) = size x > 0 andalso ord x = ord "?";
fun param i (x, S) = TVar (("?" ^ x, i), S);

fun paramify_dummies (maxidx, TFree ("'_dummy_", S)) =
      (maxidx + 1, param (maxidx + 1) ("'dummy", S))
  | paramify_dummies (maxidx, Type (a, Ts)) =
      let val (maxidx', Ts') = foldl_map paramify_dummies (maxidx, Ts)
      in (maxidx', Type (a, Ts')) end
  | paramify_dummies arg = arg;


(* decode sort constraints *)

fun get_sort tsig def_sort map_sort raw_env =
  let
    fun eq ((xi, S), (xi', S')) =
      xi = xi' andalso Type.eq_sort tsig (S, S');

    val env = gen_distinct eq (map (apsnd map_sort) raw_env);
    val _ = (case gen_duplicates eq_fst env of [] => ()
      | dups => error ("Inconsistent sort constraints for type variable(s) "
          ^ commas_quote (map (Syntax.string_of_vname' o fst) dups)));

    fun get xi =
      (case (assoc (env, xi), def_sort xi) of
        (None, None) => Type.defaultS tsig
      | (None, Some S) => S
      | (Some S, None) => S
      | (Some S, Some S') =>
          if Type.eq_sort tsig (S, S') then S'
          else error ("Sort constraint inconsistent with default for type variable " ^
            quote (Syntax.string_of_vname' xi)));
  in get end;


(* decode_types -- transform parse tree into raw term *)

fun decode_types tsig is_const def_type def_sort map_const map_type map_sort tm =
  let
    fun get_type xi = if_none (def_type xi) dummyT;
    fun is_free x = is_some (def_type (x, ~1));
    val raw_env = Syntax.raw_term_sorts tm;
    val sort_of = get_sort tsig def_sort map_sort raw_env;

    val certT = Type.cert_typ tsig o map_type;
    fun decodeT t = certT (Syntax.typ_of_term sort_of map_sort t);

    fun decode (Const ("_constrain", _) $ t $ typ) =
          constrain (decode t) (decodeT typ)
      | decode (Const ("_constrainAbs", _) $ (Abs (x, T, t)) $ typ) =
          if T = dummyT then Abs (x, decodeT typ, decode t)
          else constrain (Abs (x, certT T, decode t)) (decodeT typ --> dummyT)
      | decode (Abs (x, T, t)) = Abs (x, certT T, decode t)
      | decode (t $ u) = decode t $ decode u
      | decode (Free (x, T)) =
          let val c = map_const x in
            if not (is_free x) andalso (is_const c orelse NameSpace.is_qualified c) then
              Const (c, certT T)
            else if T = dummyT then Free (x, get_type (x, ~1))
            else constrain (Free (x, certT T)) (get_type (x, ~1))
          end
      | decode (Var (xi, T)) =
          if T = dummyT then Var (xi, get_type xi)
          else constrain (Var (xi, certT T)) (get_type xi)
      | decode (t as Bound _) = t
      | decode (Const (c, T)) = Const (map_const c, certT T);
  in decode tm end;


(* infer_types *)

(*Given [T1,...,Tn] and [t1,...,tn], ensure that the type of ti
  unifies with Ti (for i=1,...,n).

  tsig: type signature
  const_type: name mapping and signature lookup
  def_type: partial map from indexnames to types (constrains Frees, Vars)
  def_sort: partial map from indexnames to sorts (constrains TFrees, TVars)
  used: list of already used type variables
  freeze: if true then generated parameters are turned into TFrees, else TVars*)

fun infer_types pp tsig const_type def_type def_sort
    map_const map_type map_sort used freeze pat_Ts raw_ts =
  let
    val {classes, arities, ...} = Type.rep_tsig tsig;
    val pat_Ts' = map (Type.cert_typ tsig) pat_Ts;
    val is_const = is_some o const_type;
    val raw_ts' =
      map (decode_types tsig is_const def_type def_sort map_const map_type map_sort) raw_ts;
    val (ts, Ts, unifier) = basic_infer_types pp const_type
      classes arities used freeze is_param raw_ts' pat_Ts';
  in (ts, unifier) end;

end;
