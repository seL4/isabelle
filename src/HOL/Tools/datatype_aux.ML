(*  Title:      HOL/Tools/datatype_aux.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Auxiliary functions for defining datatypes.
*)

signature DATATYPE_AUX =
sig
  val quiet_mode : bool ref
  val message : string -> unit
  
  val foldl1 : ('a * 'a -> 'a) -> 'a list -> 'a

  val add_path : bool -> string -> theory -> theory
  val parent_path : bool -> theory -> theory

  val store_thmss : string -> string list -> thm list list -> theory -> theory * thm list list
  val store_thms_atts : string -> string list -> theory attribute list list -> thm list
    -> theory -> theory * thm list
  val store_thms : string -> string list -> thm list -> theory -> theory * thm list

  val split_conj_thm : thm -> thm list
  val mk_conj : term list -> term
  val mk_disj : term list -> term

  val app_bnds : term -> int -> term

  val cong_tac : int -> tactic
  val indtac : thm -> int -> tactic
  val exh_tac : (string -> thm) -> int -> tactic

  datatype simproc_dist = QuickAndDirty
                        | FewConstrs of thm list
                        | ManyConstrs of thm * simpset;

  datatype dtyp =
      DtTFree of string
    | DtType of string * (dtyp list)
    | DtRec of int;
  type descr
  type datatype_info

  exception Datatype
  val name_of_typ : typ -> string
  val dtyp_of_typ : (string * string list) list -> typ -> dtyp
  val mk_Free : string -> typ -> int -> term
  val is_rec_type : dtyp -> bool
  val typ_of_dtyp : descr -> (string * sort) list -> dtyp -> typ
  val dest_DtTFree : dtyp -> string
  val dest_DtRec : dtyp -> int
  val strip_dtyp : dtyp -> dtyp list * dtyp
  val body_index : dtyp -> int
  val mk_fun_dtyp : dtyp list -> dtyp -> dtyp
  val dest_TFree : typ -> string
  val get_nonrec_types : descr -> (string * sort) list -> typ list
  val get_branching_types : descr -> (string * sort) list -> typ list
  val get_arities : descr -> int list
  val get_rec_types : descr -> (string * sort) list -> typ list
  val check_nonempty : descr list -> unit
  val unfold_datatypes : 
    Sign.sg -> descr -> (string * sort) list -> datatype_info Symtab.table ->
      descr -> int -> descr list * int
end;

structure DatatypeAux : DATATYPE_AUX =
struct

val quiet_mode = ref false;
fun message s = if !quiet_mode then () else writeln s;

(* FIXME: move to library ? *)
fun foldl1 f (x::xs) = foldl f (x, xs);

fun add_path flat_names s = if flat_names then I else Theory.add_path s;
fun parent_path flat_names = if flat_names then I else Theory.parent_path;


(* store theorems in theory *)

fun store_thmss label tnames thmss thy =
  (thy, tnames ~~ thmss) |>
  foldl_map (fn (thy', (tname, thms)) => thy' |>
    Theory.add_path tname |>
    (apsnd hd o PureThy.add_thmss [((label, thms), [])]) |>>
    Theory.parent_path);

fun store_thms_atts label tnames attss thms thy =
  (thy, tnames ~~ attss ~~ thms) |>
  foldl_map (fn (thy', ((tname, atts), thm)) => thy' |>
    Theory.add_path tname |>
    (apsnd hd o PureThy.add_thms [((label, thm), atts)]) |>>
    Theory.parent_path);

fun store_thms label tnames = store_thms_atts label tnames (replicate (length tnames) []);


(* split theorem thm_1 & ... & thm_n into n theorems *)

fun split_conj_thm th =
  ((th RS conjunct1)::(split_conj_thm (th RS conjunct2))) handle THM _ => [th];

val mk_conj = foldr1 (HOLogic.mk_binop "op &");
val mk_disj = foldr1 (HOLogic.mk_binop "op |");

fun app_bnds t i = list_comb (t, map Bound (i - 1 downto 0));


fun cong_tac i st = (case Logic.strip_assums_concl
  (nth_elem (i - 1, prems_of st)) of
    _ $ (_ $ (f $ x) $ (g $ y)) =>
      let
        val cong' = lift_rule (st, i) cong;
        val _ $ (_ $ (f' $ x') $ (g' $ y')) =
          Logic.strip_assums_concl (prop_of cong');
        val insts = map (pairself (cterm_of (#sign (rep_thm st))) o
          apsnd (curry list_abs (Logic.strip_params (concl_of cong'))) o
            apfst head_of) [(f', f), (g', g), (x', x), (y', y)]
      in compose_tac (false, cterm_instantiate insts cong', 2) i st
        handle THM _ => no_tac st
      end
  | _ => no_tac st);

(* instantiate induction rule *)

fun indtac indrule i st =
  let
    val ts = HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of indrule));
    val ts' = HOLogic.dest_conj (HOLogic.dest_Trueprop
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

(* handling of distinctness theorems *)

datatype simproc_dist = QuickAndDirty
                      | FewConstrs of thm list
                      | ManyConstrs of thm * simpset;

(********************** Internal description of datatypes *********************)

datatype dtyp =
    DtTFree of string
  | DtType of string * (dtyp list)
  | DtRec of int;

(* information about datatypes *)

type descr = (int * (string * dtyp list * (string * dtyp list) list)) list;

type datatype_info =
  {index : int,
   descr : descr,
   rec_names : string list,
   rec_rewrites : thm list,
   case_name : string,
   case_rewrites : thm list,
   induction : thm,
   exhaustion : thm,
   distinct : simproc_dist,
   inject : thm list,
   nchotomy : thm,
   case_cong : thm,
   weak_case_cong : thm};

fun mk_Free s T i = Free (s ^ (string_of_int i), T);

fun subst_DtTFree _ substs (T as (DtTFree name)) =
      (case assoc (substs, name) of
         None => T
       | Some U => U)
  | subst_DtTFree i substs (DtType (name, ts)) =
      DtType (name, map (subst_DtTFree i substs) ts)
  | subst_DtTFree i _ (DtRec j) = DtRec (i + j);

exception Datatype;

fun dest_DtTFree (DtTFree a) = a
  | dest_DtTFree _ = raise Datatype;

fun dest_DtRec (DtRec i) = i
  | dest_DtRec _ = raise Datatype;

fun is_rec_type (DtType (_, dts)) = exists is_rec_type dts
  | is_rec_type (DtRec _) = true
  | is_rec_type _ = false;

fun strip_dtyp (DtType ("fun", [T, U])) = apfst (cons T) (strip_dtyp U)
  | strip_dtyp T = ([], T);

val body_index = dest_DtRec o snd o strip_dtyp;

fun mk_fun_dtyp [] U = U
  | mk_fun_dtyp (T :: Ts) U = DtType ("fun", [T, mk_fun_dtyp Ts U]);

fun dest_TFree (TFree (n, _)) = n;

fun name_of_typ (Type (s, Ts)) =
      let val s' = Sign.base_name s
      in space_implode "_" (filter (not o equal "") (map name_of_typ Ts) @
        [if Syntax.is_identifier s' then s' else "x"])
      end
  | name_of_typ _ = "";

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
  map (typ_of_dtyp descr sorts) (foldl (fn (Ts, (_, (_, _, constrs))) =>
    foldl (fn (Ts', (_, cargs)) =>
      filter_out is_rec_type cargs union Ts') (Ts, constrs)) ([], descr));

(* get all recursive types in datatype description *)

fun get_rec_types descr sorts = map (fn (_ , (s, ds, _)) =>
  Type (s, map (typ_of_dtyp descr sorts) ds)) descr;

(* get all branching types *)

fun get_branching_types descr sorts =
  map (typ_of_dtyp descr sorts) (foldl (fn (Ts, (_, (_, _, constrs))) =>
    foldl (fn (Ts', (_, cargs)) => foldr op union (map (fst o strip_dtyp)
      cargs, Ts')) (Ts, constrs)) ([], descr));

fun get_arities descr = foldl (fn (is, (_, (_, _, constrs))) =>
  foldl (fn (is', (_, cargs)) => map (length o fst o strip_dtyp)
    (filter is_rec_type cargs) union is') (is, constrs)) ([], descr);

(* nonemptiness check for datatypes *)

fun check_nonempty descr =
  let
    val descr' = flat descr;
    fun is_nonempty_dt is i =
      let
        val (_, _, constrs) = the (assoc (descr', i));
        fun arg_nonempty (_, DtRec i) = if i mem is then false
              else is_nonempty_dt (i::is) i
          | arg_nonempty _ = true;
      in exists ((forall (arg_nonempty o strip_dtyp)) o snd) constrs
      end
  in assert_all (fn (i, _) => is_nonempty_dt [i] i) (hd descr)
    (fn (_, (s, _, _)) => "Nonemptiness check failed for datatype " ^ s)
  end;

(* unfold a list of mutually recursive datatype specifications *)
(* all types of the form DtType (dt_name, [..., DtRec _, ...]) *)
(* need to be unfolded                                         *)

fun unfold_datatypes sign orig_descr sorts (dt_info : datatype_info Symtab.table) descr i =
  let
    fun typ_error T msg = error ("Non-admissible type expression\n" ^
      Sign.string_of_typ sign (typ_of_dtyp (orig_descr @ descr) sorts T) ^ "\n" ^ msg);

    fun get_dt_descr T i tname dts =
      (case Symtab.lookup (dt_info, tname) of
         None => typ_error T (tname ^ " is not a datatype - can't use it in\
           \ nested recursion")
       | (Some {index, descr, ...}) =>
           let val (_, vars, _) = the (assoc (descr, index));
               val subst = ((map dest_DtTFree vars) ~~ dts) handle LIST _ =>
                 typ_error T ("Type constructor " ^ tname ^ " used with wrong\
                  \ number of arguments")
           in (i + index, map (fn (j, (tn, args, cs)) => (i + j,
             (tn, map (subst_DtTFree i subst) args,
              map (apsnd (map (subst_DtTFree i subst))) cs))) descr)
           end);

    (* unfold a single constructor argument *)

    fun unfold_arg ((i, Ts, descrs), T) =
      if is_rec_type T then
        let val (Us, U) = strip_dtyp T
        in if exists is_rec_type Us then
            typ_error T "Non-strictly positive recursive occurrence of type"
          else (case U of
              DtType (tname, dts) =>  
                let
                  val (index, descr) = get_dt_descr T i tname dts;
                  val (descr', i') = unfold_datatypes sign orig_descr sorts
                    dt_info descr (i + length descr)
                in (i', Ts @ [mk_fun_dtyp Us (DtRec index)], descrs @ descr') end
            | _ => (i, Ts @ [T], descrs))
        end
      else (i, Ts @ [T], descrs);

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
