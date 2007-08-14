(*  Title:      Pure/type_infer.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Simple type inference.
*)

signature TYPE_INFER =
sig
  val anyT: sort -> typ
  val logicT: typ
  val polymorphicT: typ -> typ
  val constrain: term -> typ -> term
  val param: int -> string * sort -> typ
  val paramify_vars: typ -> typ
  val paramify_dummies: typ -> int -> typ * int
  val appl_error: Pretty.pp -> string -> term -> typ -> term -> typ -> string list
  val infer_types: Pretty.pp -> Type.tsig -> Type.mode ->
    (string -> typ option) -> (indexname -> typ option) ->
    Name.context -> bool -> (term * typ) list -> (term * typ) list * (indexname * typ) list
end;

structure TypeInfer: TYPE_INFER =
struct


(** type parameters and constraints **)

fun anyT S = TFree ("'_dummy_", S);
val logicT = anyT [];

(*indicate polymorphic Vars*)
fun polymorphicT T = Type ("_polymorphic_", [T]);

fun constrain t T =
  if T = dummyT then t
  else Const ("_type_constraint_", T --> T) $ t;


(* user parameters *)

fun is_param_default (x, _) = size x > 0 andalso ord x = ord "?";
fun param i (x, S) = TVar (("?" ^ x, i), S);

val paramify_vars = Term.map_atyps (fn TVar ((x, i), S) => param i (x, S) | T => T);

val paramify_dummies =
  let
    fun dummy S maxidx = (param (maxidx + 1) ("'dummy", S), maxidx + 1);

    fun paramify (TFree ("'_dummy_", S)) maxidx = dummy S maxidx
      | paramify (Type ("dummy", _)) maxidx = dummy [] maxidx
      | paramify (Type (a, Ts)) maxidx =
          let val (Ts', maxidx') = fold_map paramify Ts maxidx
          in (Type (a, Ts'), maxidx') end
      | paramify T maxidx = (T, maxidx);
  in paramify end;



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

fun fold_pretyps f (PConst (_, T)) x = f T x
  | fold_pretyps f (PFree (_, T)) x = f T x
  | fold_pretyps f (PVar (_, T)) x = f T x
  | fold_pretyps _ (PBound _) x = x
  | fold_pretyps f (PAbs (_, T, t)) x = fold_pretyps f t (f T x)
  | fold_pretyps f (PAppl (t, u)) x = fold_pretyps f u (fold_pretyps f t x)
  | fold_pretyps f (Constraint (t, T)) x = f T (fold_pretyps f t x);



(** raw typs/terms to pretyps/preterms **)

(* pretyp_of *)

fun pretyp_of is_param typ params =
  let
    val params' = fold_atyps
      (fn TVar (xi as (x, _), S) =>
          (fn ps =>
            if is_param xi andalso not (Vartab.defined ps xi)
            then Vartab.update (xi, mk_param S) ps else ps)
        | _ => I) typ params;

    fun pre_of (TVar (v as (xi, _))) =
          (case Vartab.lookup params' xi of
            NONE => PTVar v
          | SOME p => p)
      | pre_of (TFree ("'_dummy_", S)) = mk_param S
      | pre_of (TFree v) = PTFree v
      | pre_of (T as Type (a, Ts)) =
          if T = dummyT then mk_param []
          else PType (a, map pre_of Ts);
  in (pre_of typ, params') end;


(* preterm_of *)

fun preterm_of const_type is_param tm (vparams, params) =
  let
    fun add_vparm xi ps =
      if not (Vartab.defined ps xi) then
        Vartab.update (xi, mk_param []) ps
      else ps;

    val vparams' = fold_aterms
      (fn Var (_, Type ("_polymorphic_", _)) => I
        | Var (xi, _) => add_vparm xi
        | Free (x, _) => add_vparm (x, ~1)
        | _ => I)
      tm vparams;
    fun var_param xi = the (Vartab.lookup vparams' xi);

    val preT_of = pretyp_of is_param;
    fun polyT_of T = fst (pretyp_of (K true) T Vartab.empty);

    fun constraint T t ps =
      if T = dummyT then (t, ps)
      else
        let val (T', ps') = preT_of T ps
        in (Constraint (t, T'), ps') end;

    fun pre_of (Const (c, T)) ps =
          (case const_type c of
            SOME U => constraint T (PConst (c, polyT_of U)) ps
          | NONE => raise TYPE ("No such constant: " ^ quote c, [], []))
      | pre_of (Var (xi, Type ("_polymorphic_", [T]))) ps = (PVar (xi, polyT_of T), ps)
      | pre_of (Var (xi, T)) ps = constraint T (PVar (xi, var_param xi)) ps
      | pre_of (Free (x, T)) ps = constraint T (PFree (x, var_param (x, ~1))) ps
      | pre_of (Const ("_type_constraint_", Type ("fun", [T, _])) $ t) ps =
          pre_of t ps |-> constraint T
      | pre_of (Bound i) ps = (PBound i, ps)
      | pre_of (Abs (x, T, t)) ps =
          let
            val (T', ps') = preT_of T ps;
            val (t', ps'') = pre_of t ps';
          in (PAbs (x, T', t'), ps'') end
      | pre_of (t $ u) ps =
          let
            val (t', ps') = pre_of t ps;
            val (u', ps'') = pre_of u ps';
          in (PAppl (t', u'), ps'') end;

    val (tm', params') = pre_of tm params;
  in (tm', (vparams', params')) end;



(** pretyps/terms to typs/terms **)

(* add_parms *)

fun add_parmsT (PType (_, Ts)) rs = fold add_parmsT Ts rs
  | add_parmsT (Link (r as ref (Param _))) rs = insert (op =) r rs
  | add_parmsT (Link (ref T)) rs = add_parmsT T rs
  | add_parmsT _ rs = rs;

val add_parms = fold_pretyps add_parmsT;


(* add_names *)

fun add_namesT (PType (_, Ts)) = fold add_namesT Ts
  | add_namesT (PTFree (x, _)) = Name.declare x
  | add_namesT (PTVar ((x, _), _)) = Name.declare x
  | add_namesT (Link (ref T)) = add_namesT T
  | add_namesT (Param _) = I;

val add_names = fold_pretyps add_namesT;


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

    val used' = fold add_names ts (fold add_namesT Ts used);
    val parms = rev (fold add_parms ts (fold add_parmsT Ts []));
    val names = Name.invents used' (prfx ^ "'a") (length parms);
  in
    ListPair.app elim (parms, names);
    (map simple_typ_of Ts, map simple_term_of ts)
  end;



(** order-sorted unification of types **)       (*DESTRUCTIVE*)

exception NO_UNIFIER of string;

fun unify pp tsig =
  let

    (* adjust sorts of parameters *)

    fun not_of_sort x S' S =
      "Variable " ^ x ^ "::" ^ Pretty.string_of_sort pp S' ^ " not of sort " ^
        Pretty.string_of_sort pp S;

    fun meet (_, []) = ()
      | meet (Link (r as (ref (Param S'))), S) =
          if Type.subsort tsig (S', S) then ()
          else r := mk_param (Type.inter_sort tsig (S', S))
      | meet (Link (ref T), S) = meet (T, S)
      | meet (PType (a, Ts), S) =
          ListPair.app meet (Ts, Type.arity_sorts pp tsig a S
            handle ERROR msg => raise NO_UNIFIER msg)
      | meet (PTFree (x, S'), S) =
          if Type.subsort tsig (S', S) then ()
          else raise NO_UNIFIER (not_of_sort x S' S)
      | meet (PTVar (xi, S'), S) =
          if Type.subsort tsig (S', S) then ()
          else raise NO_UNIFIER (not_of_sort (Term.string_of_vname xi) S' S)
      | meet (Param _, _) = sys_error "meet";


    (* occurs check and assigment *)

    fun occurs_check r (Link (r' as ref T)) =
          if r = r' then raise NO_UNIFIER "Occurs check!"
          else occurs_check r T
      | occurs_check r (PType (_, Ts)) = List.app (occurs_check r) Ts
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
          else ListPair.app unif (Ts, Us)
      | unif (T, U) = if T = U then () else raise NO_UNIFIER "";

  in unif end;



(** type inference **)

(* appl_error *)

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

fun infer pp tsig =
  let
    (* errors *)

    fun unif_failed msg =
      "Type unification failed" ^ (if msg = "" then "" else ": " ^ msg) ^ "\n";

    fun prep_output bs ts Ts =
      let
        val (Ts_bTs', ts') = typs_terms_of Name.context PTFree "??" (Ts @ map snd bs, ts);
        val (Ts', Ts'') = chop (length Ts) Ts_bTs';
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

    val unif = unify pp tsig;

    fun inf _ (PConst (_, T)) = T
      | inf _ (PFree (_, T)) = T
      | inf _ (PVar (_, T)) = T
      | inf bs (PBound i) = snd (List.nth (bs, i) handle Subscript => err_loose i)
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


(* infer_types *)

fun infer_types pp tsig mode const_type var_type used freeze args =
  let
    (*certify types*)
    fun certT T = Type.cert_typ_mode mode tsig T;
    val (raw_ts, raw_Ts) = split_list args;
    val ts = map (Term.map_types certT) raw_ts;
    val Ts = map certT raw_Ts;

    (*constrain vars*)
    val get_type = the_default dummyT o var_type;
    val constrain_vars = Term.map_aterms
      (fn Free (x, T) => constrain (Free (x, get_type (x, ~1))) T
        | Var (xi, T) => constrain (Var (xi, get_type xi)) T
        | t => t);

    (*convert to preterms/typs*)
    val (Ts', Tps) = fold_map (pretyp_of (K true)) Ts Vartab.empty;
    val (ts', (vps, ps)) =
      fold_map (preterm_of const_type is_param_default o constrain_vars) ts (Vartab.empty, Tps);

    (*run type inference*)
    val tTs' = ListPair.map Constraint (ts', Ts');
    val _ = List.app (fn t => (infer pp tsig t; ())) tTs';

    (*convert back to terms/typs*)
    val mk_var =
      if freeze then PTFree
      else (fn (x, S) => PTVar ((x, 0), S));
    val (final_Ts, final_ts) = typs_terms_of used mk_var "" (Ts', ts');

    (*collect result unifier*)
    val redundant = fn (xi, TVar (yi, _)) => xi = yi | _ => false;
    val env = filter_out redundant (map (apsnd simple_typ_of) (Vartab.dest Tps));

  in (final_ts ~~ final_Ts, env) end;

end;
