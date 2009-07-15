(*  Title:      Pure/type_infer.ML
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Simple type inference.
*)

signature TYPE_INFER =
sig
  val anyT: sort -> typ
  val polymorphicT: typ -> typ
  val constrain: typ -> term -> term
  val is_param: indexname -> bool
  val param: int -> string * sort -> typ
  val paramify_vars: typ -> typ
  val paramify_dummies: typ -> int -> typ * int
  val fixate_params: Name.context -> term list -> term list
  val appl_error: Pretty.pp -> string -> term -> typ -> term -> typ -> string list
  val infer_types: Pretty.pp -> Type.tsig -> (typ list -> typ list) ->
    (string -> typ option) -> (indexname -> typ option) -> Name.context -> int ->
    term list -> term list
end;

structure TypeInfer: TYPE_INFER =
struct


(** type parameters and constraints **)

fun anyT S = TFree ("'_dummy_", S);

(*indicate polymorphic Vars*)
fun polymorphicT T = Type ("_polymorphic_", [T]);

val constrain = Syntax.type_constraint;


(* user parameters *)

fun is_param (x, _: int) = String.isPrefix "?" x;
fun param i (x, S) = TVar (("?" ^ x, i), S);

val paramify_vars =
  perhaps (Term_Subst.map_atypsT_option (fn TVar ((x, i), S) => SOME (param i (x, S)) | _ => NONE));

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

fun fixate_params name_context ts =
  let
    fun subst_param (xi, S) (inst, used) =
      if is_param xi then
        let
          val [a] = Name.invents used Name.aT 1;
          val used' = Name.declare a used;
        in (((xi, S), TFree (a, S)) :: inst, used') end
      else (inst, used);
    val name_context' = (fold o fold_types) Term.declare_typ_names ts name_context;
    val (inst, _) = fold_rev subst_param (fold Term.add_tvars ts []) ([], name_context');
  in (map o map_types) (Term_Subst.instantiateT inst) ts end;



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

fun pretyp_of is_para typ params =
  let
    val params' = fold_atyps
      (fn TVar (xi as (x, _), S) =>
          (fn ps =>
            if is_para xi andalso not (Vartab.defined ps xi)
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

fun preterm_of const_type is_para tm (vparams, params) =
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

    val preT_of = pretyp_of is_para;
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

fun typs_terms_of used maxidx (Ts, ts) =
  let
    fun elim (r as ref (Param S), x) = r := PTVar ((x, maxidx + 1), S)
      | elim _ = ();

    val used' = fold add_names ts (fold add_namesT Ts used);
    val parms = rev (fold add_parms ts (fold add_parmsT Ts []));
    val names = Name.invents used' ("?" ^ Name.aT) (length parms);
    val _ = ListPair.app elim (parms, names);
  in (map simple_typ_of Ts, map simple_term_of ts) end;



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
        val (Ts_bTs', ts') = typs_terms_of Name.context ~1 (Ts @ map snd bs, ts);
        val (Ts', Ts'') = chop (length Ts) Ts_bTs';
        fun prep t =
          let val xs = rev (Term.variant_frees t (rev (map fst bs ~~ Ts'')))
          in Term.subst_bounds (map Syntax.mark_boundT xs, t) end;
      in (map prep ts', Ts') end;

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
      | inf bs (PBound i) = snd (nth bs i handle Subscript => err_loose i)
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

fun infer_types pp tsig check_typs const_type var_type used maxidx raw_ts =
  let
    (*constrain vars*)
    val get_type = the_default dummyT o var_type;
    val constrain_vars = Term.map_aterms
      (fn Free (x, T) => constrain T (Free (x, get_type (x, ~1)))
        | Var (xi, T) => constrain T (Var (xi, get_type xi))
        | t => t);

    (*convert to preterms*)
    val ts = burrow_types check_typs raw_ts;
    val (ts', (vps, ps)) =
      fold_map (preterm_of const_type is_param o constrain_vars) ts (Vartab.empty, Vartab.empty);

    (*do type inference*)
    val _ = List.app (ignore o infer pp tsig) ts';
  in #2 (typs_terms_of used maxidx ([], ts')) end;

end;
