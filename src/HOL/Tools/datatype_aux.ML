(*  Title:      HOL/Tools/datatype_aux.ML
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   1998  TU Muenchen

Auxiliary functions for defining datatypes
*)

signature DATATYPE_AUX =
sig
  val quiet_mode : bool ref
  val message : string -> unit
  
  val foldl1 : ('a * 'a -> 'a) -> 'a list -> 'a

  val get_thy : string -> theory -> theory option

  val add_path : bool -> string -> theory -> theory
  val parent_path : bool -> theory -> theory

  val store_thmss : string -> string list -> thm list list -> theory -> theory
  val store_thms : string -> string list -> thm list -> theory -> theory

  val split_conj_thm : thm -> thm list
  val mk_conj : term list -> term
  val mk_disj : term list -> term

  val indtac : thm -> int -> tactic
  val exh_tac : (string -> thm) -> int -> tactic

  datatype dtyp =
      DtTFree of string
    | DtType of string * (dtyp list)
    | DtRec of int;

  type datatype_info

  val dtyp_of_typ : (string * string list) list -> typ -> dtyp
  val mk_Free : string -> typ -> int -> term
  val is_rec_type : dtyp -> bool
  val typ_of_dtyp : (int * (string * dtyp list *
    (string * dtyp list) list)) list -> (string * sort) list -> dtyp -> typ
  val dest_DtTFree : dtyp -> string
  val dest_DtRec : dtyp -> int
  val dest_TFree : typ -> string
  val dest_conj : term -> term list
  val get_nonrec_types : (int * (string * dtyp list *
    (string * dtyp list) list)) list -> (string * sort) list -> typ list
  val get_rec_types : (int * (string * dtyp list *
    (string * dtyp list) list)) list -> (string * sort) list -> typ list
  val check_nonempty : (int * (string * dtyp list *
    (string * dtyp list) list)) list list -> unit
  val unfold_datatypes : 
    datatype_info Symtab.table ->
      (int * (string * dtyp list *
        (string * dtyp list) list)) list -> int ->
          (int * (string * dtyp list *
            (string * dtyp list) list)) list list * int
end;

structure DatatypeAux : DATATYPE_AUX =
struct

val quiet_mode = ref false;
fun message s = if !quiet_mode then () else writeln s;

(* FIXME: move to library ? *)
fun foldl1 f (x::xs) = foldl f (x, xs);

fun get_thy name thy = find_first
  (equal name o Sign.name_of o Theory.sign_of) (Theory.ancestors_of thy);

fun add_path flat_names s = if flat_names then I else Theory.add_path s;
fun parent_path flat_names = if flat_names then I else Theory.parent_path;

(* store theorems in theory *)

fun store_thmss label tnames thmss thy =
  foldr (fn ((tname, thms), thy') => thy' |>
    Theory.add_path tname |>
    PureThy.add_thmss [((label, thms), [])] |>
    Theory.parent_path)
      (tnames ~~ thmss, thy);

fun store_thms label tnames thms thy =
  foldr (fn ((tname, thm), thy') => thy' |>
    Theory.add_path tname |>
    PureThy.add_thms [((label, thm), [])] |>
    Theory.parent_path)
      (tnames ~~ thms, thy);

(* split theorem thm_1 & ... & thm_n into n theorems *)

fun split_conj_thm th =
  ((th RS conjunct1)::(split_conj_thm (th RS conjunct2))) handle _ => [th];

val mk_conj = foldr1 (HOLogic.mk_binop "op &");
val mk_disj = foldr1 (HOLogic.mk_binop "op |");

fun dest_conj (Const ("op &", _) $ t $ t') = t::(dest_conj t')
  | dest_conj t = [t];

(* instantiate induction rule *)

fun indtac indrule i st =
  let
    val ts = dest_conj (HOLogic.dest_Trueprop (concl_of indrule));
    val ts' = dest_conj (HOLogic.dest_Trueprop
      (Logic.strip_imp_concl (nth_elem (i - 1, prems_of st))));
    val getP = if can HOLogic.dest_imp (hd ts) then
      (apfst Some) o HOLogic.dest_imp else pair None;
    fun abstr (t1, t2) = (case t1 of
        None => let val [Free (s, T)] = add_term_frees (t2, [])
          in absfree (s, T, t2) end
      | Some (_ $ t' $ _) => Abs ("x", fastype_of t', abstract_over (t', t2)))
    val cert = cterm_of (Thm.sign_of_thm st);
    val Ps = map (cert o head_of o snd o getP) ts;
    val indrule' = cterm_instantiate (Ps ~~
      (map (cert o abstr o getP) ts')) indrule
  in
    rtac indrule' i st
  end;

(* perform exhaustive case analysis on last parameter of subgoal i *)

fun exh_tac exh_thm_of i state =
  let
    val sg = Thm.sign_of_thm state;
    val prem = nth_elem (i - 1, prems_of state);
    val params = Logic.strip_params prem;
    val (_, Type (tname, _)) = hd (rev params);
    val exhaustion = lift_rule (state, i) (exh_thm_of tname);
    val prem' = hd (prems_of exhaustion);
    val _ $ (_ $ lhs $ _) = hd (rev (Logic.strip_assums_hyp prem'));
    val exhaustion' = cterm_instantiate [(cterm_of sg (head_of lhs),
      cterm_of sg (foldr (fn ((_, T), t) => Abs ("z", T, t))
        (params, Bound 0)))] exhaustion
  in compose_tac (false, exhaustion', nprems_of exhaustion) i state
  end;

(********************** Internal description of datatypes *********************)

datatype dtyp =
    DtTFree of string
  | DtType of string * (dtyp list)
  | DtRec of int;

(* information about datatypes *)

type datatype_info =
  {index : int,
   descr : (int * (string * dtyp list *
     (string * dtyp list) list)) list,
   rec_names : string list,
   rec_rewrites : thm list,
   case_name : string,
   case_rewrites : thm list,
   induction : thm,
   exhaustion : thm,
   distinct : thm list,
   inject : thm list,
   nchotomy : thm,
   case_cong : thm};

fun mk_Free s T i = Free (s ^ (string_of_int i), T);

fun subst_DtTFree _ substs (T as (DtTFree name)) =
      (case assoc (substs, name) of
         None => T
       | Some U => U)
  | subst_DtTFree i substs (DtType (name, ts)) =
      DtType (name, map (subst_DtTFree i substs) ts)
  | subst_DtTFree i _ (DtRec j) = DtRec (i + j);

fun dest_DtTFree (DtTFree a) = a;
fun dest_DtRec (DtRec i) = i;

fun is_rec_type (DtType (_, dts)) = exists is_rec_type dts
  | is_rec_type (DtRec _) = true
  | is_rec_type _ = false;

fun dest_TFree (TFree (n, _)) = n;

fun dtyp_of_typ _ (TFree (n, _)) = DtTFree n
  | dtyp_of_typ _ (TVar _) = error "Illegal schematic type variable(s)"
  | dtyp_of_typ new_dts (Type (tname, Ts)) =
      (case assoc (new_dts, tname) of
         None => DtType (tname, map (dtyp_of_typ new_dts) Ts)
       | Some vs => if map (try dest_TFree) Ts = map Some vs then
             DtRec (find_index (curry op = tname o fst) new_dts)
           else error ("Illegal occurence of recursive type " ^ tname));

fun typ_of_dtyp descr sorts (DtTFree a) = TFree (a, the (assoc (sorts, a)))
  | typ_of_dtyp descr sorts (DtRec i) =
      let val (s, ds, _) = the (assoc (descr, i))
      in Type (s, map (typ_of_dtyp descr sorts) ds) end
  | typ_of_dtyp descr sorts (DtType (s, ds)) =
      Type (s, map (typ_of_dtyp descr sorts) ds);

(* find all non-recursive types in datatype description *)

fun get_nonrec_types descr sorts =
  let fun add (Ts, T as DtTFree _) = T ins Ts
        | add (Ts, T as DtType _) = T ins Ts
        | add (Ts, _) = Ts
  in map (typ_of_dtyp descr sorts) (foldl (fn (Ts, (_, (_, _, constrs))) =>
    foldl (fn (Ts', (_, cargs)) =>
      foldl add (Ts', cargs)) (Ts, constrs)) ([], descr))
  end;

(* get all recursive types in datatype description *)

fun get_rec_types descr sorts = map (fn (_ , (s, ds, _)) =>
  Type (s, map (typ_of_dtyp descr sorts) ds)) descr;

(* nonemptiness check for datatypes *)

fun check_nonempty descr =
  let
    val descr' = flat descr;
    fun is_nonempty_dt is i =
      let
        val (_, _, constrs) = the (assoc (descr', i));
        fun arg_nonempty (DtRec i) = if i mem is then false
              else is_nonempty_dt (i::is) i
          | arg_nonempty _ = true;
      in exists ((forall arg_nonempty) o snd) constrs
      end
  in assert_all (fn (i, _) => is_nonempty_dt [i] i) (hd descr)
    (fn (_, (s, _, _)) => "Nonemptiness check failed for datatype " ^ s)
  end;

(* unfold a list of mutually recursive datatype specifications *)
(* all types of the form DtType (dt_name, [..., DtRec _, ...]) *)
(* need to be unfolded                                         *)

fun unfold_datatypes (dt_info : datatype_info Symtab.table) descr i =
  let
    fun get_dt_descr i tname dts =
      (case Symtab.lookup (dt_info, tname) of
         None => error (tname ^ " is not a datatype - can't use it in\
           \ indirect recursion")
       | (Some {index, descr, ...}) =>
           let val (_, vars, _) = the (assoc (descr, index));
               val subst = ((map dest_DtTFree vars) ~~ dts) handle _ =>
                 error ("Type constructor " ^ tname ^ " used with wrong\
                  \ number of arguments")
           in (i + index, map (fn (j, (tn, args, cs)) => (i + j,
             (tn, map (subst_DtTFree i subst) args,
              map (apsnd (map (subst_DtTFree i subst))) cs))) descr)
           end);

    (* unfold a single constructor argument *)

    fun unfold_arg ((i, Ts, descrs), T as (DtType (tname, dts))) =
          if is_rec_type T then
            let val (index, descr) = get_dt_descr i tname dts;
                val (descr', i') = unfold_datatypes dt_info descr (i + length descr)
            in (i', Ts @ [DtRec index], descrs @ descr') end
          else (i, Ts @ [T], descrs)
      | unfold_arg ((i, Ts, descrs), T) = (i, Ts @ [T], descrs);

    (* unfold a constructor *)

    fun unfold_constr ((i, constrs, descrs), (cname, cargs)) =
      let val (i', cargs', descrs') = foldl unfold_arg ((i, [], descrs), cargs)
      in (i', constrs @ [(cname, cargs')], descrs') end;

    (* unfold a single datatype *)

    fun unfold_datatype ((i, dtypes, descrs), (j, (tname, tvars, constrs))) =
      let val (i', constrs', descrs') =
        foldl unfold_constr ((i, [], descrs), constrs)
      in (i', dtypes @ [(j, (tname, tvars, constrs'))], descrs')
      end;

    val (i', descr', descrs) = foldl unfold_datatype ((i, [],[]), descr);

  in (descr' :: descrs, i') end;

end;
