(*  Title:      HOL/Tools/Datatype/datatype_aux.ML
    Author:     Stefan Berghofer, TU Muenchen

Datatype package: auxiliary data structures and functions.
*)

signature DATATYPE_COMMON =
sig
  type config = {strict : bool, quiet : bool}
  val default_config : config
  datatype dtyp =
      DtTFree of string * sort
    | DtType of string * dtyp list
    | DtRec of int
  type descr = (int * (string * dtyp list * (string * dtyp list) list)) list
  type info =
   {index : int,
    descr : descr,
    inject : thm list,
    distinct : thm list,
    induct : thm,
    inducts : thm list,
    exhaust : thm,
    nchotomy : thm,
    rec_names : string list,
    rec_rewrites : thm list,
    case_name : string,
    case_rewrites : thm list,
    case_cong : thm,
    weak_case_cong : thm,
    split : thm,
    split_asm: thm}
end

signature DATATYPE_AUX =
sig
  include DATATYPE_COMMON

  val message : config -> string -> unit

  val store_thmss_atts : string -> string list -> attribute list list -> thm list list
    -> theory -> thm list list * theory
  val store_thmss : string -> string list -> thm list list -> theory -> thm list list * theory
  val store_thms_atts : string -> string list -> attribute list list -> thm list
    -> theory -> thm list * theory
  val store_thms : string -> string list -> thm list -> theory -> thm list * theory

  val split_conj_thm : thm -> thm list
  val mk_conj : term list -> term
  val mk_disj : term list -> term

  val app_bnds : term -> int -> term

  val ind_tac : thm -> string list -> int -> tactic
  val exh_tac : (string -> thm) -> int -> tactic

  exception Datatype
  exception Datatype_Empty of string
  val name_of_typ : typ -> string
  val dtyp_of_typ : (string * (string * sort) list) list -> typ -> dtyp
  val mk_Free : string -> typ -> int -> term
  val is_rec_type : dtyp -> bool
  val typ_of_dtyp : descr -> dtyp -> typ
  val dest_DtTFree : dtyp -> string * sort
  val dest_DtRec : dtyp -> int
  val strip_dtyp : dtyp -> dtyp list * dtyp
  val body_index : dtyp -> int
  val mk_fun_dtyp : dtyp list -> dtyp -> dtyp
  val get_nonrec_types : descr -> typ list
  val get_branching_types : descr -> typ list
  val get_arities : descr -> int list
  val get_rec_types : descr -> typ list
  val interpret_construction : descr -> (string * sort) list ->
    {atyp: typ -> 'a, dtyp: typ list -> int * bool -> string * typ list -> 'a} ->
    ((string * typ list) * (string * 'a list) list) list
  val check_nonempty : descr list -> unit
  val unfold_datatypes : Proof.context -> descr -> info Symtab.table ->
    descr -> int -> descr list * int
  val find_shortest_path : descr -> int -> (string * int) option
end;

structure Datatype_Aux : DATATYPE_AUX =
struct

(* datatype option flags *)

type config = {strict : bool, quiet : bool};
val default_config : config = {strict = true, quiet = false};

fun message ({quiet = true, ...} : config) s = writeln s
  | message _ _ = ();


(* store theorems in theory *)

fun store_thmss_atts label tnames attss thmss =
  fold_map (fn ((tname, atts), thms) =>
    Global_Theory.add_thmss
      [((Binding.qualify true tname (Binding.name label), thms), atts)]
    #-> (fn thm::_ => pair thm)) (tnames ~~ attss ~~ thmss)
  ##> Theory.checkpoint;

fun store_thmss label tnames = store_thmss_atts label tnames (replicate (length tnames) []);

fun store_thms_atts label tnames attss thmss =
  fold_map (fn ((tname, atts), thms) =>
    Global_Theory.add_thms
      [((Binding.qualify true tname (Binding.name label), thms), atts)]
    #-> (fn thm::_ => pair thm)) (tnames ~~ attss ~~ thmss)
  ##> Theory.checkpoint;

fun store_thms label tnames = store_thms_atts label tnames (replicate (length tnames) []);


(* split theorem thm_1 & ... & thm_n into n theorems *)

fun split_conj_thm th =
  ((th RS conjunct1)::(split_conj_thm (th RS conjunct2))) handle THM _ => [th];

val mk_conj = foldr1 (HOLogic.mk_binop @{const_name HOL.conj});
val mk_disj = foldr1 (HOLogic.mk_binop @{const_name HOL.disj});

fun app_bnds t i = list_comb (t, map Bound (i - 1 downto 0));


(* instantiate induction rule *)

fun ind_tac indrule indnames = CSUBGOAL (fn (cgoal, i) =>
  let
    val cert = cterm_of (Thm.theory_of_cterm cgoal);
    val goal = term_of cgoal;
    val ts = HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of indrule));
    val ts' = HOLogic.dest_conj (HOLogic.dest_Trueprop (Logic.strip_imp_concl goal));
    val getP =
      if can HOLogic.dest_imp (hd ts)
      then apfst SOME o HOLogic.dest_imp
      else pair NONE;
    val flt =
      if null indnames then I
      else filter (member (op =) indnames o fst);
    fun abstr (t1, t2) =
      (case t1 of
        NONE =>
          (case flt (Term.add_frees t2 []) of
            [(s, T)] => SOME (absfree (s, T) t2)
          | _ => NONE)
      | SOME (_ $ t') => SOME (Abs ("x", fastype_of t', abstract_over (t', t2))));
    val insts =
      map_filter (fn (t, u) =>
        (case abstr (getP u) of
          NONE => NONE
        | SOME u' => SOME (t |> getP |> snd |> head_of |> cert, cert u'))) (ts ~~ ts');
    val indrule' = cterm_instantiate insts indrule;
  in rtac indrule' i end);


(* perform exhaustive case analysis on last parameter of subgoal i *)

fun exh_tac exh_thm_of = CSUBGOAL (fn (cgoal, i) =>
  let
    val thy = Thm.theory_of_cterm cgoal;
    val goal = term_of cgoal;
    val params = Logic.strip_params goal;
    val (_, Type (tname, _)) = hd (rev params);
    val exhaustion = Thm.lift_rule cgoal (exh_thm_of tname);
    val prem' = hd (prems_of exhaustion);
    val _ $ (_ $ lhs $ _) = hd (rev (Logic.strip_assums_hyp prem'));
    val exhaustion' =
      cterm_instantiate [(cterm_of thy (head_of lhs),
        cterm_of thy (fold_rev (fn (_, T) => fn t => Abs ("z", T, t)) params (Bound 0)))] exhaustion;
  in compose_tac (false, exhaustion', nprems_of exhaustion) i end);


(********************** Internal description of datatypes *********************)

datatype dtyp =
    DtTFree of string * sort
  | DtType of string * dtyp list
  | DtRec of int;

(* information about datatypes *)

(* index, datatype name, type arguments, constructor name, types of constructor's arguments *)
type descr = (int * (string * dtyp list * (string * dtyp list) list)) list;

type info =
  {index : int,
   descr : descr,
   inject : thm list,
   distinct : thm list,
   induct : thm,
   inducts : thm list,
   exhaust : thm,
   nchotomy : thm,
   rec_names : string list,
   rec_rewrites : thm list,
   case_name : string,
   case_rewrites : thm list,
   case_cong : thm,
   weak_case_cong : thm,
   split : thm,
   split_asm: thm};

fun mk_Free s T i = Free (s ^ string_of_int i, T);

fun subst_DtTFree _ substs (T as DtTFree a) = the_default T (AList.lookup (op =) substs a)
  | subst_DtTFree i substs (DtType (name, ts)) = DtType (name, map (subst_DtTFree i substs) ts)
  | subst_DtTFree i _ (DtRec j) = DtRec (i + j);

exception Datatype;
exception Datatype_Empty of string;

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

fun name_of_typ (Type (s, Ts)) =
      let val s' = Long_Name.base_name s in
        space_implode "_"
          (filter_out (equal "") (map name_of_typ Ts) @
            [if Lexicon.is_identifier s' then s' else "x"])
      end
  | name_of_typ _ = "";

fun dtyp_of_typ _ (TFree a) = DtTFree a
  | dtyp_of_typ _ (TVar _) = error "Illegal schematic type variable(s)"
  | dtyp_of_typ new_dts (Type (tname, Ts)) =
      (case AList.lookup (op =) new_dts tname of
        NONE => DtType (tname, map (dtyp_of_typ new_dts) Ts)
      | SOME vs =>
          if map (try dest_TFree) Ts = map SOME vs then
            DtRec (find_index (curry op = tname o fst) new_dts)
          else error ("Illegal occurrence of recursive type " ^ quote tname));

fun typ_of_dtyp descr (DtTFree a) = TFree a
  | typ_of_dtyp descr (DtRec i) =
      let val (s, ds, _) = the (AList.lookup (op =) descr i)
      in Type (s, map (typ_of_dtyp descr) ds) end
  | typ_of_dtyp descr (DtType (s, ds)) = Type (s, map (typ_of_dtyp descr) ds);

(* find all non-recursive types in datatype description *)

fun get_nonrec_types descr =
  map (typ_of_dtyp descr) (fold (fn (_, (_, _, constrs)) =>
    fold (fn (_, cargs) => union (op =) (filter_out is_rec_type cargs)) constrs) descr []);

(* get all recursive types in datatype description *)

fun get_rec_types descr = map (fn (_ , (s, ds, _)) =>
  Type (s, map (typ_of_dtyp descr) ds)) descr;

(* get all branching types *)

fun get_branching_types descr =
  map (typ_of_dtyp descr)
    (fold
      (fn (_, (_, _, constrs)) =>
        fold (fn (_, cargs) => fold (strip_dtyp #> fst #> fold (insert op =)) cargs) constrs)
      descr []);

fun get_arities descr =
  fold
    (fn (_, (_, _, constrs)) =>
      fold (fn (_, cargs) =>
        fold (insert op =) (map (length o fst o strip_dtyp) (filter is_rec_type cargs))) constrs)
    descr [];

(* interpret construction of datatype *)

fun interpret_construction descr vs {atyp, dtyp} =
  let
    val typ_of =
      typ_of_dtyp descr #>
      map_atyps (fn TFree (a, _) => TFree (a, the (AList.lookup (op =) vs a)) | T => T);
    fun interpT dT =
      (case strip_dtyp dT of
        (dTs, DtRec l) =>
          let
            val (tyco, dTs', _) = the (AList.lookup (op =) descr l);
            val Ts = map typ_of dTs;
            val Ts' = map typ_of dTs';
            val is_proper = forall (can dest_TFree) Ts';
          in dtyp Ts (l, is_proper) (tyco, Ts') end
      | _ => atyp (typ_of dT));
    fun interpC (c, dTs) = (c, map interpT dTs);
    fun interpD (_, (tyco, dTs, cs)) = ((tyco, map typ_of dTs), map interpC cs);
  in map interpD descr end;

(* nonemptiness check for datatypes *)

fun check_nonempty descr =
  let
    val descr' = flat descr;
    fun is_nonempty_dt is i =
      let
        val (_, _, constrs) = the (AList.lookup (op =) descr' i);
        fun arg_nonempty (_, DtRec i) =
              if member (op =) is i then false
              else is_nonempty_dt (i :: is) i
          | arg_nonempty _ = true;
      in exists (forall (arg_nonempty o strip_dtyp) o snd) constrs end
  in
    assert_all (fn (i, _) => is_nonempty_dt [i] i) (hd descr)
      (fn (_, (s, _, _)) => raise Datatype_Empty s)
  end;

(* unfold a list of mutually recursive datatype specifications *)
(* all types of the form DtType (dt_name, [..., DtRec _, ...]) *)
(* need to be unfolded                                         *)

fun unfold_datatypes ctxt orig_descr (dt_info : info Symtab.table) descr i =
  let
    fun typ_error T msg =
      error ("Non-admissible type expression\n" ^
        Syntax.string_of_typ ctxt (typ_of_dtyp (orig_descr @ descr) T) ^ "\n" ^ msg);

    fun get_dt_descr T i tname dts =
      (case Symtab.lookup dt_info tname of
        NONE =>
          typ_error T (quote tname ^ " is not a datatype - can't use it in nested recursion")
      | SOME {index, descr, ...} =>
          let
            val (_, vars, _) = the (AList.lookup (op =) descr index);
            val subst = map dest_DtTFree vars ~~ dts
              handle ListPair.UnequalLengths =>
                typ_error T ("Type constructor " ^ quote tname ^
                  " used with wrong number of arguments");
          in
            (i + index,
              map (fn (j, (tn, args, cs)) =>
                (i + j, (tn, map (subst_DtTFree i subst) args,
                  map (apsnd (map (subst_DtTFree i subst))) cs))) descr)
          end);

    (* unfold a single constructor argument *)

    fun unfold_arg T (i, Ts, descrs) =
      if is_rec_type T then
        let val (Us, U) = strip_dtyp T in
          if exists is_rec_type Us then
            typ_error T "Non-strictly positive recursive occurrence of type"
          else
            (case U of
              DtType (tname, dts) =>
                let
                  val (index, descr) = get_dt_descr T i tname dts;
                  val (descr', i') =
                    unfold_datatypes ctxt orig_descr dt_info descr (i + length descr);
                in (i', Ts @ [mk_fun_dtyp Us (DtRec index)], descrs @ descr') end
            | _ => (i, Ts @ [T], descrs))
        end
      else (i, Ts @ [T], descrs);

    (* unfold a constructor *)

    fun unfold_constr (cname, cargs) (i, constrs, descrs) =
      let val (i', cargs', descrs') = fold unfold_arg cargs (i, [], descrs)
      in (i', constrs @ [(cname, cargs')], descrs') end;

    (* unfold a single datatype *)

    fun unfold_datatype (j, (tname, tvars, constrs)) (i, dtypes, descrs) =
      let val (i', constrs', descrs') = fold unfold_constr constrs (i, [], descrs)
      in (i', dtypes @ [(j, (tname, tvars, constrs'))], descrs') end;

    val (i', descr', descrs) = fold unfold_datatype descr (i, [], []);

  in (descr' :: descrs, i') end;

(* find shortest path to constructor with no recursive arguments *)

fun find_nonempty descr is i =
  let
    fun arg_nonempty (_, DtRec i) =
          if member (op =) is i
          then NONE
          else Option.map (Integer.add 1 o snd) (find_nonempty descr (i :: is) i)
      | arg_nonempty _ = SOME 0;
    fun max_inf (SOME i) (SOME j) = SOME (Integer.max i j)
      | max_inf _ _ = NONE;
    fun max xs = fold max_inf xs (SOME 0);
    val (_, _, constrs) = the (AList.lookup (op =) descr i);
    val xs =
      sort (int_ord o pairself snd)
        (map_filter (fn (s, dts) => Option.map (pair s)
          (max (map (arg_nonempty o strip_dtyp) dts))) constrs)
  in if null xs then NONE else SOME (hd xs) end;

fun find_shortest_path descr i = find_nonempty descr [i] i;

end;
