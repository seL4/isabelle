(*  Title:      Pure/proofterm.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

LF style proof terms.
*)

infix 8 % %% %>;

signature BASIC_PROOFTERM =
sig
  val proofs: int ref

  datatype proof =
     PBound of int
   | Abst of string * typ option * proof
   | AbsP of string * term option * proof
   | % of proof * term option
   | %% of proof * proof
   | Hyp of term
   | PThm of (string * (string * string list) list) * proof * term * typ list option
   | PAxm of string * term * typ list option
   | Oracle of string * term * typ list option
   | MinProof of proof list;

  val %> : proof * term -> proof
end;

signature PROOFTERM =
sig
  include BASIC_PROOFTERM

  val infer_derivs : (proof -> proof -> proof) -> bool * proof -> bool * proof -> bool * proof
  val infer_derivs' : (proof -> proof) -> (bool * proof -> bool * proof)

  (** primitive operations **)
  val proof_combt : proof * term list -> proof
  val proof_combt' : proof * term option list -> proof
  val proof_combP : proof * proof list -> proof
  val strip_combt : proof -> proof * term option list
  val strip_combP : proof -> proof * proof list
  val strip_thm : proof -> proof
  val map_proof_terms : (term -> term) -> (typ -> typ) -> proof -> proof
  val fold_proof_terms : (term * 'a -> 'a) -> (typ * 'a -> 'a) -> 'a * proof -> 'a
  val add_prf_names : string list * proof -> string list
  val add_prf_tfree_names : string list * proof -> string list
  val add_prf_tvar_ixns : indexname list * proof -> indexname list
  val maxidx_of_proof : proof -> int
  val size_of_proof : proof -> int
  val change_type : typ list option -> proof -> proof
  val prf_abstract_over : term -> proof -> proof
  val prf_incr_bv : int -> int -> int -> int -> proof -> proof
  val incr_pboundvars : int -> int -> proof -> proof
  val prf_loose_bvar1 : proof -> int -> bool
  val prf_loose_Pbvar1 : proof -> int -> bool
  val prf_add_loose_bnos : int -> int -> proof ->
    int list * int list -> int list * int list
  val norm_proof : Envir.env -> proof -> proof
  val norm_proof' : Envir.env -> proof -> proof
  val prf_subst_bounds : term list -> proof -> proof
  val prf_subst_pbounds : proof list -> proof -> proof
  val freeze_thaw_prf : proof -> proof * (proof -> proof)

  val thms_of_proof : (term * proof) list Symtab.table -> proof ->
    (term * proof) list Symtab.table
  val axms_of_proof : proof Symtab.table -> proof -> proof Symtab.table
  val oracles_of_proof : proof list -> proof -> proof list

  (** proof terms for specific inference rules **)
  val implies_intr_proof : term -> proof -> proof
  val forall_intr_proof : term -> string -> proof -> proof
  val varify_proof : term -> string list -> proof -> proof
  val freezeT : term -> proof -> proof
  val rotate_proof : term list -> term -> int -> proof -> proof
  val permute_prems_prf : term list -> int -> int -> proof -> proof
  val instantiate : (indexname * typ) list -> (term * term) list -> proof -> proof
  val lift_proof : term -> int -> term -> proof -> proof
  val assumption_proof : term list -> term -> int -> proof -> proof
  val bicompose_proof : term list -> term list -> term list -> term option ->
    int -> proof -> proof -> proof
  val equality_axms : (string * term) list
  val reflexive_axm : proof
  val symmetric_axm : proof
  val transitive_axm : proof
  val equal_intr_axm : proof
  val equal_elim_axm : proof
  val abstract_rule_axm : proof
  val combination_axm : proof
  val reflexive : proof
  val symmetric : proof -> proof
  val transitive : term -> typ -> proof -> proof -> proof
  val abstract_rule : term -> string -> proof -> proof
  val combination : term -> term -> term -> term -> typ -> proof -> proof -> proof
  val equal_intr : term -> term -> proof -> proof -> proof
  val equal_elim : term -> term -> proof -> proof -> proof
  val axm_proof : string -> term -> proof
  val oracle_proof : string -> term -> proof
  val thm_proof : Sign.sg -> string * (string * string list) list ->
    term list -> term -> proof -> proof
  val get_name_tags : term list -> term -> proof -> string * (string * string list) list

  (** rewriting on proof terms **)
  val add_prf_rrules : (proof * proof) list -> theory -> theory
  val add_prf_rprocs : (string * (Term.typ list -> proof -> proof option)) list ->
    theory -> theory
  val rewrite_proof : Type.type_sig -> (proof * proof) list *
    (string * (typ list -> proof -> proof option)) list -> proof -> proof
  val rewrite_proof_notypes : (proof * proof) list *
    (string * (typ list -> proof -> proof option)) list -> proof -> proof
  val init : theory -> theory
  
end

structure Proofterm : PROOFTERM =
struct

open Envir;

datatype proof =
   PBound of int
 | Abst of string * typ option * proof
 | AbsP of string * term option * proof
 | op % of proof * term option
 | op %% of proof * proof
 | Hyp of term
 | PThm of (string * (string * string list) list) * proof * term * typ list option
 | PAxm of string * term * typ list option
 | Oracle of string * term * typ list option
 | MinProof of proof list;

fun oracles_of_proof prfs prf =
  let
    fun oras_of (tabs, Abst (_, _, prf)) = oras_of (tabs, prf)
      | oras_of (tabs, AbsP (_, _, prf)) = oras_of (tabs, prf)
      | oras_of (tabs, prf % _) = oras_of (tabs, prf)
      | oras_of (tabs, prf1 %% prf2) = oras_of (oras_of (tabs, prf1), prf2)
      | oras_of (tabs as (thms, oras), PThm ((name, _), prf, prop, _)) =
          (case Symtab.lookup (thms, name) of
             None => oras_of ((Symtab.update ((name, [prop]), thms), oras), prf)
           | Some ps => if prop mem ps then tabs else
               oras_of ((Symtab.update ((name, prop::ps), thms), oras), prf))
      | oras_of ((thms, oras), prf as Oracle _) = (thms, prf ins oras)
      | oras_of (tabs, MinProof prfs) = foldl oras_of (tabs, prfs)
      | oras_of (tabs, _) = tabs
  in
    snd (oras_of ((Symtab.empty, prfs), prf))
  end;

fun thms_of_proof tab (Abst (_, _, prf)) = thms_of_proof tab prf
  | thms_of_proof tab (AbsP (_, _, prf)) = thms_of_proof tab prf
  | thms_of_proof tab (prf1 %% prf2) = thms_of_proof (thms_of_proof tab prf1) prf2
  | thms_of_proof tab (prf % _) = thms_of_proof tab prf
  | thms_of_proof tab (prf' as PThm ((s, _), prf, prop, _)) =
      (case Symtab.lookup (tab, s) of
         None => thms_of_proof (Symtab.update ((s, [(prop, prf')]), tab)) prf
       | Some ps => if exists (equal prop o fst) ps then tab else
           thms_of_proof (Symtab.update ((s, (prop, prf')::ps), tab)) prf)
  | thms_of_proof tab (MinProof prfs) = foldl (uncurry thms_of_proof) (tab, prfs)
  | thms_of_proof tab _ = tab;

fun axms_of_proof tab (Abst (_, _, prf)) = axms_of_proof tab prf
  | axms_of_proof tab (AbsP (_, _, prf)) = axms_of_proof tab prf
  | axms_of_proof tab (prf1 %% prf2) = axms_of_proof (axms_of_proof tab prf1) prf2
  | axms_of_proof tab (prf % _) = axms_of_proof tab prf
  | axms_of_proof tab (prf as PAxm (s, _, _)) = Symtab.update ((s, prf), tab)
  | axms_of_proof tab (MinProof prfs) = foldl (uncurry axms_of_proof) (tab, prfs)
  | axms_of_proof tab _ = tab;

(** collect all theorems, axioms and oracles **)

fun mk_min_proof (prfs, Abst (_, _, prf)) = mk_min_proof (prfs, prf)
  | mk_min_proof (prfs, AbsP (_, _, prf)) = mk_min_proof (prfs, prf)
  | mk_min_proof (prfs, prf % _) = mk_min_proof (prfs, prf)
  | mk_min_proof (prfs, prf1 %% prf2) = mk_min_proof (mk_min_proof (prfs, prf1), prf2)
  | mk_min_proof (prfs, prf as PThm _) = prf ins prfs
  | mk_min_proof (prfs, prf as PAxm _) = prf ins prfs
  | mk_min_proof (prfs, prf as Oracle _) = prf ins prfs
  | mk_min_proof (prfs, MinProof prfs') = prfs union prfs'
  | mk_min_proof (prfs, _) = prfs;

(** proof objects with different levels of detail **)

val proofs = ref 2;

fun err_illegal_level i =
  error ("Illegal level of detail for proof objects: " ^ string_of_int i);

fun if_ora b = if b then oracles_of_proof else K;

fun infer_derivs f (ora1, prf1) (ora2, prf2) =
  (ora1 orelse ora2, 
   case !proofs of
     2 => f prf1 prf2
   | 1 => MinProof (mk_min_proof (mk_min_proof ([], prf1), prf2))
   | 0 => MinProof (if_ora ora2 (if_ora ora1 [] prf1) prf2)
   | i => err_illegal_level i);

fun infer_derivs' f (ora, prf) =
  (ora,
   case !proofs of
     2 => f prf
   | 1 => MinProof (mk_min_proof ([], prf))
   | 0 => MinProof (if_ora ora [] prf)
   | i => err_illegal_level i);

fun (prf %> t) = prf % Some t;

val proof_combt = foldl (op %>);
val proof_combt' = foldl (op %);
val proof_combP = foldl (op %%);

fun strip_combt prf = 
    let fun stripc (prf % t, ts) = stripc (prf, t::ts)
          | stripc  x =  x 
    in  stripc (prf, [])  end;

fun strip_combP prf = 
    let fun stripc (prf %% prf', prfs) = stripc (prf, prf'::prfs)
          | stripc  x =  x
    in  stripc (prf, [])  end;

fun strip_thm prf = (case strip_combt (fst (strip_combP prf)) of
      (PThm (_, prf', _, _), _) => prf'
    | _ => prf);

val mk_Abst = foldr (fn ((s, T:typ), prf) => Abst (s, None, prf));
fun mk_AbsP (i, prf) = funpow i (fn prf => AbsP ("H", None, prf)) prf;

fun apsome' f None = raise SAME
  | apsome' f (Some x) = Some (f x);

fun same f x =
  let val x' = f x
  in if x = x' then raise SAME else x' end;

fun map_proof_terms f g =
  let
    fun mapp (Abst (s, T, prf)) = (Abst (s, apsome' (same g) T, mapph prf)
          handle SAME => Abst (s, T, mapp prf))
      | mapp (AbsP (s, t, prf)) = (AbsP (s, apsome' (same f) t, mapph prf)
          handle SAME => AbsP (s, t, mapp prf))
      | mapp (prf % t) = (mapp prf % apsome f t
          handle SAME => prf % apsome' (same f) t)
      | mapp (prf1 %% prf2) = (mapp prf1 %% mapph prf2
          handle SAME => prf1 %% mapp prf2)
      | mapp (PThm (a, prf, prop, Some Ts)) =
          PThm (a, prf, prop, Some (same (map g) Ts))
      | mapp (PAxm (a, prop, Some Ts)) =
          PAxm (a, prop, Some (same (map g) Ts))
      | mapp _ = raise SAME
    and mapph prf = (mapp prf handle SAME => prf)

  in mapph end;

fun fold_proof_terms f g (a, Abst (_, Some T, prf)) = fold_proof_terms f g (g (T, a), prf)
  | fold_proof_terms f g (a, Abst (_, None, prf)) = fold_proof_terms f g (a, prf)
  | fold_proof_terms f g (a, AbsP (_, Some t, prf)) = fold_proof_terms f g (f (t, a), prf)
  | fold_proof_terms f g (a, AbsP (_, None, prf)) = fold_proof_terms f g (a, prf)
  | fold_proof_terms f g (a, prf % Some t) = f (t, fold_proof_terms f g (a, prf))
  | fold_proof_terms f g (a, prf % None) = fold_proof_terms f g (a, prf)
  | fold_proof_terms f g (a, prf1 %% prf2) = fold_proof_terms f g
      (fold_proof_terms f g (a, prf1), prf2)
  | fold_proof_terms _ g (a, PThm (_, _, _, Some Ts)) = foldr g (Ts, a)
  | fold_proof_terms _ g (a, PAxm (_, prop, Some Ts)) = foldr g (Ts, a)
  | fold_proof_terms _ _ (a, _) = a;

val add_prf_names = fold_proof_terms add_term_names ((uncurry K) o swap);
val add_prf_tfree_names = fold_proof_terms add_term_tfree_names add_typ_tfree_names;
val add_prf_tvar_ixns = fold_proof_terms add_term_tvar_ixns (add_typ_ixns o swap);

fun maxidx_of_proof prf = fold_proof_terms
  (Int.max o apfst maxidx_of_term) (Int.max o apfst maxidx_of_typ) (~1, prf); 

fun size_of_proof (Abst (_, _, prf)) = 1 + size_of_proof prf
  | size_of_proof (AbsP (_, t, prf)) =
      if_none (apsome size_of_term t) 1 + size_of_proof prf
  | size_of_proof (prf1 %% prf2) = size_of_proof prf1 + size_of_proof prf2
  | size_of_proof (prf % t) =
      if_none (apsome size_of_term t) 1 + size_of_proof prf
  | size_of_proof _ = 1;

fun change_type opTs (PThm (name, prf, prop, _)) = PThm (name, prf, prop, opTs)
  | change_type opTs (PAxm (name, prop, _)) = PAxm (name, prop, opTs)
  | change_type opTs (Oracle (name, prop, _)) = Oracle (name, prop, opTs)
  | change_type _ prf = prf;


(***** utilities *****)

fun strip_abs (_::Ts) (Abs (_, _, t)) = strip_abs Ts t
  | strip_abs _ t = t;

fun mk_abs Ts t = foldl (fn (t', T) => Abs ("", T, t')) (t, Ts);


(*Abstraction of a proof term over its occurrences of v, 
    which must contain no loose bound variables.
  The resulting proof term is ready to become the body of an Abst.*)

fun prf_abstract_over v =
  let
    fun abst' lev u = if v aconv u then Bound lev else
      (case u of
         Abs (a, T, t) => Abs (a, T, abst' (lev + 1) t)
       | f $ t => (abst' lev f $ absth' lev t handle SAME => f $ abst' lev t)
       | _ => raise SAME)
    and absth' lev t = (abst' lev t handle SAME => t);

    fun abst lev (AbsP (a, t, prf)) =
          (AbsP (a, apsome' (abst' lev) t, absth lev prf)
           handle SAME => AbsP (a, t, abst lev prf))
      | abst lev (Abst (a, T, prf)) = Abst (a, T, abst (lev + 1) prf)
      | abst lev (prf1 %% prf2) = (abst lev prf1 %% absth lev prf2
          handle SAME => prf1 %% abst lev prf2)
      | abst lev (prf % t) = (abst lev prf % apsome (absth' lev) t
          handle SAME => prf % apsome' (abst' lev) t)
      | abst _ _ = raise SAME
    and absth lev prf = (abst lev prf handle SAME => prf)

  in absth 0 end;


(*increments a proof term's non-local bound variables
  required when moving a proof term within abstractions
     inc is  increment for bound variables
     lev is  level at which a bound variable is considered 'loose'*)

fun incr_bv' inct tlev t = incr_bv (inct, tlev, t);

fun prf_incr_bv' incP inct Plev tlev (PBound i) =
      if i >= Plev then PBound (i+incP) else raise SAME 
  | prf_incr_bv' incP inct Plev tlev (AbsP (a, t, body)) =
      (AbsP (a, apsome' (same (incr_bv' inct tlev)) t,
         prf_incr_bv incP inct (Plev+1) tlev body) handle SAME =>
           AbsP (a, t, prf_incr_bv' incP inct (Plev+1) tlev body))
  | prf_incr_bv' incP inct Plev tlev (Abst (a, T, body)) =
      Abst (a, T, prf_incr_bv' incP inct Plev (tlev+1) body)
  | prf_incr_bv' incP inct Plev tlev (prf %% prf') = 
      (prf_incr_bv' incP inct Plev tlev prf %% prf_incr_bv incP inct Plev tlev prf'
       handle SAME => prf %% prf_incr_bv' incP inct Plev tlev prf')
  | prf_incr_bv' incP inct Plev tlev (prf % t) = 
      (prf_incr_bv' incP inct Plev tlev prf % apsome (incr_bv' inct tlev) t
       handle SAME => prf % apsome' (same (incr_bv' inct tlev)) t)
  | prf_incr_bv' _ _ _ _ _ = raise SAME
and prf_incr_bv incP inct Plev tlev prf =
      (prf_incr_bv' incP inct Plev tlev prf handle SAME => prf);

fun incr_pboundvars  0 0 prf = prf
  | incr_pboundvars incP inct prf = prf_incr_bv incP inct 0 0 prf;


fun prf_loose_bvar1 (prf1 %% prf2) k = prf_loose_bvar1 prf1 k orelse prf_loose_bvar1 prf2 k
  | prf_loose_bvar1 (prf % Some t) k = prf_loose_bvar1 prf k orelse loose_bvar1 (t, k)
  | prf_loose_bvar1 (_ % None) _ = true
  | prf_loose_bvar1 (AbsP (_, Some t, prf)) k = loose_bvar1 (t, k) orelse prf_loose_bvar1 prf k
  | prf_loose_bvar1 (AbsP (_, None, _)) k = true
  | prf_loose_bvar1 (Abst (_, _, prf)) k = prf_loose_bvar1 prf (k+1)
  | prf_loose_bvar1 _ _ = false;

fun prf_loose_Pbvar1 (PBound i) k = i = k
  | prf_loose_Pbvar1 (prf1 %% prf2) k = prf_loose_Pbvar1 prf1 k orelse prf_loose_Pbvar1 prf2 k
  | prf_loose_Pbvar1 (prf % _) k = prf_loose_Pbvar1 prf k
  | prf_loose_Pbvar1 (AbsP (_, _, prf)) k = prf_loose_Pbvar1 prf (k+1)
  | prf_loose_Pbvar1 (Abst (_, _, prf)) k = prf_loose_Pbvar1 prf k
  | prf_loose_Pbvar1 _ _ = false;

fun prf_add_loose_bnos plev tlev (PBound i) (is, js) =
      if i < plev then (is, js) else ((i-plev) ins is, js)
  | prf_add_loose_bnos plev tlev (prf1 %% prf2) p =
      prf_add_loose_bnos plev tlev prf2
        (prf_add_loose_bnos plev tlev prf1 p)
  | prf_add_loose_bnos plev tlev (prf % opt) (is, js) =
      prf_add_loose_bnos plev tlev prf (case opt of
          None => (is, ~1 ins js)
        | Some t => (is, add_loose_bnos (t, tlev, js)))
  | prf_add_loose_bnos plev tlev (AbsP (_, opt, prf)) (is, js) =
      prf_add_loose_bnos (plev+1) tlev prf (case opt of
          None => (is, ~1 ins js)
        | Some t => (is, add_loose_bnos (t, tlev, js)))
  | prf_add_loose_bnos plev tlev (Abst (_, _, prf)) p =
      prf_add_loose_bnos plev (tlev+1) prf p
  | prf_add_loose_bnos _ _ _ _ = ([], []);


(**** substitutions ****)

fun norm_proof env =
  let
    val envT = type_env env;
    fun norm (Abst (s, T, prf)) = (Abst (s, apsome' (norm_type_same envT) T, normh prf)
          handle SAME => Abst (s, T, norm prf))
      | norm (AbsP (s, t, prf)) = (AbsP (s, apsome' (norm_term_same env) t, normh prf)
          handle SAME => AbsP (s, t, norm prf))
      | norm (prf % t) = (norm prf % apsome (norm_term env) t
          handle SAME => prf % apsome' (norm_term_same env) t)
      | norm (prf1 %% prf2) = (norm prf1 %% normh prf2
          handle SAME => prf1 %% norm prf2)
      | norm (PThm (s, prf, t, Ts)) = PThm (s, prf, t, apsome' (norm_types_same envT) Ts)
      | norm (PAxm (s, prop, Ts)) = PAxm (s, prop, apsome' (norm_types_same envT) Ts)
      | norm _ = raise SAME
    and normh prf = (norm prf handle SAME => prf);
  in normh end;

(***** Remove some types in proof term (to save space) *****)

fun remove_types (Abs (s, _, t)) = Abs (s, dummyT, remove_types t)
  | remove_types (t $ u) = remove_types t $ remove_types u
  | remove_types (Const (s, _)) = Const (s, dummyT)
  | remove_types t = t;

fun remove_types_env (Envir.Envir {iTs, asol, maxidx}) =
  Envir.Envir {iTs = iTs, asol = Vartab.map remove_types asol, maxidx = maxidx};

fun norm_proof' env prf = norm_proof (remove_types_env env) prf;

(**** substitution of bound variables ****)

fun prf_subst_bounds args prf =
  let
    val n = length args;
    fun subst' lev (Bound i) =
         (if i<lev then raise SAME    (*var is locally bound*)
          else  incr_boundvars lev (List.nth (args, i-lev))
                  handle Subscript => Bound (i-n)  (*loose: change it*))
      | subst' lev (Abs (a, T, body)) = Abs (a, T,  subst' (lev+1) body)
      | subst' lev (f $ t) = (subst' lev f $ substh' lev t
          handle SAME => f $ subst' lev t)
      | subst' _ _ = raise SAME
    and substh' lev t = (subst' lev t handle SAME => t);

    fun subst lev (AbsP (a, t, body)) = (AbsP (a, apsome' (subst' lev) t, substh lev body)
          handle SAME => AbsP (a, t, subst lev body))
      | subst lev (Abst (a, T, body)) = Abst (a, T, subst (lev+1) body)
      | subst lev (prf %% prf') = (subst lev prf %% substh lev prf'
          handle SAME => prf %% subst lev prf')
      | subst lev (prf % t) = (subst lev prf % apsome (substh' lev) t
          handle SAME => prf % apsome' (subst' lev) t)
      | subst _ _ = raise SAME
    and substh lev prf = (subst lev prf handle SAME => prf)
  in case args of [] => prf | _ => substh 0 prf end;

fun prf_subst_pbounds args prf =
  let
    val n = length args;
    fun subst (PBound i) Plev tlev =
 	 (if i < Plev then raise SAME    (*var is locally bound*)
          else incr_pboundvars Plev tlev (List.nth (args, i-Plev))
                 handle Subscript => PBound (i-n)  (*loose: change it*))
      | subst (AbsP (a, t, body)) Plev tlev = AbsP (a, t, subst body (Plev+1) tlev)
      | subst (Abst (a, T, body)) Plev tlev = Abst (a, T, subst body Plev (tlev+1))
      | subst (prf %% prf') Plev tlev = (subst prf Plev tlev %% substh prf' Plev tlev
          handle SAME => prf %% subst prf' Plev tlev)
      | subst (prf % t) Plev tlev = subst prf Plev tlev % t
      | subst  prf _ _ = raise SAME
    and substh prf Plev tlev = (subst prf Plev tlev handle SAME => prf)
  in case args of [] => prf | _ => substh prf 0 0 end;


(**** Freezing and thawing of variables in proof terms ****)

fun frzT names =
  map_type_tvar (fn (ixn, xs) => TFree (the (assoc (names, ixn)), xs));

fun thawT names =
  map_type_tfree (fn (s, xs) => case assoc (names, s) of
      None => TFree (s, xs)
    | Some ixn => TVar (ixn, xs));

fun freeze names names' (t $ u) =
      freeze names names' t $ freeze names names' u
  | freeze names names' (Abs (s, T, t)) =
      Abs (s, frzT names' T, freeze names names' t)
  | freeze names names' (Const (s, T)) = Const (s, frzT names' T)
  | freeze names names' (Free (s, T)) = Free (s, frzT names' T)
  | freeze names names' (Var (ixn, T)) =
      Free (the (assoc (names, ixn)), frzT names' T)
  | freeze names names' t = t;

fun thaw names names' (t $ u) =
      thaw names names' t $ thaw names names' u
  | thaw names names' (Abs (s, T, t)) =
      Abs (s, thawT names' T, thaw names names' t)
  | thaw names names' (Const (s, T)) = Const (s, thawT names' T)
  | thaw names names' (Free (s, T)) = 
      let val T' = thawT names' T
      in case assoc (names, s) of
          None => Free (s, T')
        | Some ixn => Var (ixn, T')
      end
  | thaw names names' (Var (ixn, T)) = Var (ixn, thawT names' T)
  | thaw names names' t = t;

fun freeze_thaw_prf prf =
  let
    val (fs, Tfs, vs, Tvs) = fold_proof_terms
      (fn (t, (fs, Tfs, vs, Tvs)) =>
         (add_term_frees (t, fs), add_term_tfree_names (t, Tfs),
          add_term_vars (t, vs), add_term_tvar_ixns (t, Tvs)))
      (fn (T, (fs, Tfs, vs, Tvs)) =>
         (fs, add_typ_tfree_names (T, Tfs),
          vs, add_typ_ixns (Tvs, T)))
            (([], [], [], []), prf);
    val fs' = map (fst o dest_Free) fs;
    val vs' = map (fst o dest_Var) vs;
    val names = vs' ~~ variantlist (map fst vs', fs');
    val names' = Tvs ~~ variantlist (map fst Tvs, Tfs);
    val rnames = map swap names;
    val rnames' = map swap names';
  in
    (map_proof_terms (freeze names names') (frzT names') prf,
     map_proof_terms (thaw rnames rnames') (thawT rnames'))
  end;


(***** implication introduction *****)

fun implies_intr_proof h prf =
  let
    fun abshyp i (Hyp t) = if h aconv t then PBound i else raise SAME
      | abshyp i (Abst (s, T, prf)) = Abst (s, T, abshyp i prf)
      | abshyp i (AbsP (s, t, prf)) = AbsP (s, t, abshyp (i+1) prf)
      | abshyp i (prf % t) = abshyp i prf % t
      | abshyp i (prf1 %% prf2) = (abshyp i prf1 %% abshyph i prf2
          handle SAME => prf1 %% abshyp i prf2)
      | abshyp _ _ = raise SAME
    and abshyph i prf = (abshyp i prf handle SAME => prf)
  in
    AbsP ("H", None (*h*), abshyph 0 prf)
  end;


(***** forall introduction *****)

fun forall_intr_proof x a prf = Abst (a, None, prf_abstract_over x prf);


(***** varify *****)

fun varify_proof t fixed prf =
  let
    val fs = add_term_tfree_names (t, []) \\ fixed;
    val ixns = add_term_tvar_ixns (t, []);
    val fmap = fs ~~ variantlist (fs, map #1 ixns)
    fun thaw (f as (a, S)) =
      (case assoc (fmap, a) of
        None => TFree f
      | Some b => TVar ((b, 0), S));
  in map_proof_terms (map_term_types (map_type_tfree thaw)) (map_type_tfree thaw) prf
  end;


local

fun new_name (ix, (pairs,used)) =
  let val v = variant used (string_of_indexname ix)
  in  ((ix, v) :: pairs, v :: used)  end;

fun freeze_one alist (ix, sort) = (case assoc (alist, ix) of
    None => TVar (ix, sort)
  | Some name => TFree (name, sort));

in

fun freezeT t prf =
  let
    val used = it_term_types add_typ_tfree_names (t, [])
    and tvars = map #1 (it_term_types add_typ_tvars (t, []));
    val (alist, _) = foldr new_name (tvars, ([], used));
  in
    (case alist of
      [] => prf (*nothing to do!*)
    | _ =>
      let val frzT = map_type_tvar (freeze_one alist)
      in map_proof_terms (map_term_types frzT) frzT prf end)
  end;

end;


(***** rotate assumptions *****)

fun rotate_proof Bs Bi m prf =
  let
    val params = Term.strip_all_vars Bi;
    val asms = Logic.strip_imp_prems (Term.strip_all_body Bi);
    val i = length asms;
    val j = length Bs;
  in
    mk_AbsP (j+1, proof_combP (prf, map PBound
      (j downto 1) @ [mk_Abst (params, mk_AbsP (i,
        proof_combP (proof_combt (PBound i, map Bound ((length params - 1) downto 0)),
          map PBound (((i-m-1) downto 0) @ ((i-1) downto (i-m))))))]))
  end;


(***** permute premises *****)

fun permute_prems_prf prems j k prf =
  let val n = length prems
  in mk_AbsP (n, proof_combP (prf,
    map PBound ((n-1 downto n-j) @ (k-1 downto 0) @ (n-j-1 downto k))))
  end;


(***** instantiation *****)

fun instantiate vTs tpairs =
  map_proof_terms (subst_atomic (map (apsnd remove_types) tpairs) o
    subst_TVars vTs) (typ_subst_TVars vTs);


(***** lifting *****)

fun lift_proof Bi inc prop prf =
  let
    val (_, lift_all) = Logic.lift_fns (Bi, inc);

    fun lift'' Us Ts t = strip_abs Ts (Logic.incr_indexes (Us, inc) (mk_abs Ts t));

    fun lift' Us Ts (Abst (s, T, prf)) =
          (Abst (s, apsome' (same (incr_tvar inc)) T, lifth' Us (dummyT::Ts) prf)
           handle SAME => Abst (s, T, lift' Us (dummyT::Ts) prf))
      | lift' Us Ts (AbsP (s, t, prf)) =
          (AbsP (s, apsome' (same (lift'' Us Ts)) t, lifth' Us Ts prf)
           handle SAME => AbsP (s, t, lift' Us Ts prf))
      | lift' Us Ts (prf % t) = (lift' Us Ts prf % apsome (lift'' Us Ts) t
          handle SAME => prf % apsome' (same (lift'' Us Ts)) t)
      | lift' Us Ts (prf1 %% prf2) = (lift' Us Ts prf1 %% lifth' Us Ts prf2
          handle SAME => prf1 %% lift' Us Ts prf2)
      | lift' _ _ (PThm (s, prf, prop, Ts)) =
          PThm (s, prf, prop, apsome' (same (map (incr_tvar inc))) Ts)
      | lift' _ _ (PAxm (s, prop, Ts)) =
          PAxm (s, prop, apsome' (same (map (incr_tvar inc))) Ts)
      | lift' _ _ _ = raise SAME
    and lifth' Us Ts prf = (lift' Us Ts prf handle SAME => prf);

    val ps = map lift_all (Logic.strip_imp_prems prop);
    val k = length ps;

    fun mk_app (b, (i, j, prf)) = 
          if b then (i-1, j, prf %% PBound i) else (i, j-1, prf %> Bound j);

    fun lift Us bs i j (Const ("==>", _) $ A $ B) =
	    AbsP ("H", None (*A*), lift Us (true::bs) (i+1) j B)
      | lift Us bs i j (Const ("all", _) $ Abs (a, T, t)) = 
	    Abst (a, None (*T*), lift (T::Us) (false::bs) i (j+1) t)
      | lift Us bs i j _ = proof_combP (lifth' (rev Us) [] prf,
            map (fn k => (#3 (foldr mk_app (bs, (i-1, j-1, PBound k)))))
              (i + k - 1 downto i));
  in
    mk_AbsP (k, lift [] [] 0 0 Bi)
  end;


(***** proof by assumption *****)

fun mk_asm_prf (Const ("==>", _) $ A $ B) i = AbsP ("H", None (*A*), mk_asm_prf B (i+1))
  | mk_asm_prf (Const ("all", _) $ Abs (a, T, t)) i = Abst (a, None (*T*), mk_asm_prf t i)
  | mk_asm_prf _ i = PBound i;

fun assumption_proof Bs Bi n prf =
  mk_AbsP (length Bs, proof_combP (prf,
    map PBound (length Bs - 1 downto 0) @ [mk_asm_prf Bi (~n)]));


(***** Composition of object rule with proof state *****)

fun flatten_params_proof i j n (Const ("==>", _) $ A $ B, k) =
      AbsP ("H", None (*A*), flatten_params_proof (i+1) j n (B, k))
  | flatten_params_proof i j n (Const ("all", _) $ Abs (a, T, t), k) =
      Abst (a, None (*T*), flatten_params_proof i (j+1) n (t, k))
  | flatten_params_proof i j n (_, k) = proof_combP (proof_combt (PBound (k+i),
      map Bound (j-1 downto 0)), map PBound (i-1 downto 0 \ i-n));

fun bicompose_proof Bs oldAs newAs A n rprf sprf =
  let
    val la = length newAs;
    val lb = length Bs;
  in
    mk_AbsP (lb+la, proof_combP (sprf,
      map PBound (lb + la - 1 downto la)) %%
        proof_combP (rprf, (if n>0 then [mk_asm_prf (the A) (~n)] else []) @
          map (flatten_params_proof 0 0 n) (oldAs ~~ (la - 1 downto 0))))
  end;


(***** axioms for equality *****)

val aT = TFree ("'a", ["logic"]);
val bT = TFree ("'b", ["logic"]);
val x = Free ("x", aT);
val y = Free ("y", aT);
val z = Free ("z", aT);
val A = Free ("A", propT);
val B = Free ("B", propT);
val f = Free ("f", aT --> bT);
val g = Free ("g", aT --> bT);

local open Logic in

val equality_axms =
  [("reflexive", mk_equals (x, x)),
   ("symmetric", mk_implies (mk_equals (x, y), mk_equals (y, x))),
   ("transitive", list_implies ([mk_equals (x, y), mk_equals (y, z)], mk_equals (x, z))),
   ("equal_intr", list_implies ([mk_implies (A, B), mk_implies (B, A)], mk_equals (A, B))),
   ("equal_elim", list_implies ([mk_equals (A, B), A], B)),
   ("abstract_rule", Logic.mk_implies
      (all aT $ Abs ("x", aT, equals bT $ (f $ Bound 0) $ (g $ Bound 0)),
       equals (aT --> bT) $
         Abs ("x", aT, f $ Bound 0) $ Abs ("x", aT, g $ Bound 0))),
   ("combination", Logic.list_implies
      ([Logic.mk_equals (f, g), Logic.mk_equals (x, y)],
       Logic.mk_equals (f $ x, g $ y)))];

val [reflexive_axm, symmetric_axm, transitive_axm, equal_intr_axm,
  equal_elim_axm, abstract_rule_axm, combination_axm] =
    map (fn (s, t) => PAxm ("ProtoPure." ^ s, varify t, None)) equality_axms;

end;

val reflexive = reflexive_axm % None;

fun symmetric (prf as PAxm ("ProtoPure.reflexive", _, _) % _) = prf
  | symmetric prf = symmetric_axm % None % None %% prf;

fun transitive _ _ (PAxm ("ProtoPure.reflexive", _, _) % _) prf2 = prf2
  | transitive _ _ prf1 (PAxm ("ProtoPure.reflexive", _, _) % _) = prf1
  | transitive u (Type ("prop", [])) prf1 prf2 =
      transitive_axm % None % Some (remove_types u) % None %% prf1 %% prf2
  | transitive u T prf1 prf2 =
      transitive_axm % None % None % None %% prf1 %% prf2;

fun abstract_rule x a prf =
  abstract_rule_axm % None % None %% forall_intr_proof x a prf;

fun check_comb (PAxm ("ProtoPure.combination", _, _) % f % g % _ % _ %% prf %% _) =
      is_some f orelse check_comb prf
  | check_comb (PAxm ("ProtoPure.transitive", _, _) % _ % _ % _ %% prf1 %% prf2) =
      check_comb prf1 andalso check_comb prf2
  | check_comb (PAxm ("ProtoPure.symmetric", _, _) % _ % _ %% prf) = check_comb prf
  | check_comb _ = false;

fun combination f g t u (Type (_, [T, U])) prf1 prf2 =
  let
    val f = Envir.beta_norm f;
    val g = Envir.beta_norm g;
    val prf =  if check_comb prf1 then
        combination_axm % None % None
      else (case prf1 of
          PAxm ("ProtoPure.reflexive", _, _) % _ =>
            combination_axm %> remove_types f % None
        | _ => combination_axm %> remove_types f %> remove_types g)
  in
    (case T of
       Type ("fun", _) => prf %
         (case head_of f of
            Abs _ => Some (remove_types t)
          | Var _ => Some (remove_types t)
          | _ => None) %
         (case head_of g of
            Abs _ => Some (remove_types u)
          | Var _ => Some (remove_types u)
          | _ => None) %% prf1 %% prf2
     | _ => prf % None % None %% prf1 %% prf2)
  end;

fun equal_intr A B prf1 prf2 =
  equal_intr_axm %> remove_types A %> remove_types B %% prf1 %% prf2;

fun equal_elim A B prf1 prf2 =
  equal_elim_axm %> remove_types A %> remove_types B %% prf1 %% prf2;


(***** axioms and theorems *****)

fun vars_of t = rev (foldl_aterms
  (fn (vs, v as Var _) => v ins vs | (vs, _) => vs) ([], t));

fun test_args _ [] = true
  | test_args is (Bound i :: ts) =
      not (i mem is) andalso test_args (i :: is) ts
  | test_args _ _ = false;

fun is_fun (Type ("fun", _)) = true
  | is_fun (TVar _) = true
  | is_fun _ = false;

fun add_funvars Ts (vs, t) =
  if is_fun (fastype_of1 (Ts, t)) then
    vs union mapfilter (fn Var (ixn, T) =>
      if is_fun T then Some ixn else None | _ => None) (vars_of t)
  else vs;

fun add_npvars q p Ts (vs, Const ("==>", _) $ t $ u) =
      add_npvars q p Ts (add_npvars q (not p) Ts (vs, t), u)
  | add_npvars q p Ts (vs, Const ("all", Type (_, [Type (_, [T, _]), _])) $ t) =
      add_npvars q p Ts (vs, if p andalso q then betapply (t, Var (("",0), T)) else t)
  | add_npvars q p Ts (vs, Abs (_, T, t)) = add_npvars q p (T::Ts) (vs, t)
  | add_npvars _ _ Ts (vs, t) = add_npvars' Ts (vs, t)
and add_npvars' Ts (vs, t) = (case strip_comb t of
    (Var (ixn, _), ts) => if test_args [] ts then vs
      else foldl (add_npvars' Ts) (overwrite (vs,
        (ixn, foldl (add_funvars Ts) (if_none (assoc (vs, ixn)) [], ts))), ts)
  | (Abs (_, T, u), ts) => foldl (add_npvars' (T::Ts)) (vs, u :: ts)
  | (_, ts) => foldl (add_npvars' Ts) (vs, ts));

fun prop_vars (Const ("==>", _) $ P $ Q) = prop_vars P union prop_vars Q
  | prop_vars (Const ("all", _) $ Abs (_, _, t)) = prop_vars t
  | prop_vars t = (case strip_comb t of
      (Var (ixn, _), _) => [ixn] | _ => []);

fun is_proj t =
  let
    fun is_p i t = (case strip_comb t of
        (Bound j, []) => false
      | (Bound j, ts) => j >= i orelse exists (is_p i) ts
      | (Abs (_, _, u), _) => is_p (i+1) u
      | (_, ts) => exists (is_p i) ts)
  in (case strip_abs_body t of
        Bound _ => true
      | t' => is_p 0 t')
  end;

fun needed_vars prop = 
  foldl op union ([], map op ins (add_npvars true true [] ([], prop))) union
  prop_vars prop;

fun gen_axm_proof c name prop =
  let
    val nvs = needed_vars prop;
    val args = map (fn (v as Var (ixn, _)) =>
        if ixn mem nvs then Some v else None) (vars_of prop) @
      map Some (sort (make_ord atless) (term_frees prop));
  in
    proof_combt' (c (name, prop, None), args)
  end;

val axm_proof = gen_axm_proof PAxm;
val oracle_proof = gen_axm_proof Oracle;

fun shrink ls lev (prf as Abst (a, T, body)) =
      let val (b, is, ch, body') = shrink ls (lev+1) body
      in (b, is, ch, if ch then Abst (a, T, body') else prf) end
  | shrink ls lev (prf as AbsP (a, t, body)) =
      let val (b, is, ch, body') = shrink (lev::ls) lev body
      in (b orelse 0 mem is, mapfilter (fn 0 => None | i => Some (i-1)) is,
        ch, if ch then AbsP (a, t, body') else prf)
      end
  | shrink ls lev prf =
      let val (is, ch, _, prf') = shrink' ls lev [] [] prf
      in (false, is, ch, prf') end
and shrink' ls lev ts prfs (prf as prf1 %% prf2) =
      let
        val p as (_, is', ch', prf') = shrink ls lev prf2;
        val (is, ch, ts', prf'') = shrink' ls lev ts (p::prfs) prf1
      in (is union is', ch orelse ch', ts',
          if ch orelse ch' then prf'' %% prf' else prf)
      end
  | shrink' ls lev ts prfs (prf as prf1 % t) =
      let val (is, ch, (ch', t')::ts', prf') = shrink' ls lev (t::ts) prfs prf1
      in (is, ch orelse ch', ts', if ch orelse ch' then prf' % t' else prf) end
  | shrink' ls lev ts prfs (prf as PBound i) =
      (if exists (fn Some (Bound j) => lev-j <= nth_elem (i, ls) | _ => true) ts
         orelse not (null (duplicates
           (foldl (fn (js, Some (Bound j)) => j :: js | (js, _) => js) ([], ts))))
         orelse exists #1 prfs then [i] else [], false, map (pair false) ts, prf)
  | shrink' ls lev ts prfs (prf as Hyp _) = ([], false, map (pair false) ts, prf)
  | shrink' ls lev ts prfs (prf as MinProof _) =
      ([], false, map (pair false) ts, prf)
  | shrink' ls lev ts prfs prf =
      let
        val prop = (case prf of PThm (_, _, prop, _) => prop | PAxm (_, prop, _) => prop
          | Oracle (_, prop, _) => prop | _ => error "shrink: proof not in normal form");
        val vs = vars_of prop;
        val (ts', ts'') = splitAt (length vs, ts)
        val insts = take (length ts', map (fst o dest_Var) vs) ~~ ts';
        val nvs = foldl (fn (ixns', (ixn, ixns)) =>
          ixn ins (case assoc (insts, ixn) of
              Some (Some t) => if is_proj t then ixns union ixns' else ixns'
            | _ => ixns union ixns'))
              (needed prop ts'' prfs, add_npvars false true [] ([], prop));
        val insts' = map
          (fn (ixn, x as Some _) => if ixn mem nvs then (false, x) else (true, None)
            | (_, x) => (false, x)) insts
      in ([], false, insts' @ map (pair false) ts'', prf) end
and needed (Const ("==>", _) $ t $ u) ts ((b, _, _, _)::prfs) =
      (if b then map (fst o dest_Var) (vars_of t) else []) union needed u ts prfs
  | needed (Var (ixn, _)) (_::_) _ = [ixn]
  | needed _ _ _ = [];


(**** Simple first order matching functions for terms and proofs ****)

exception PMatch;

(** see pattern.ML **)

fun flt (i: int) = filter (fn n => n < i);

fun fomatch Ts tymatch j =
  let
    fun mtch (instsp as (tyinsts, insts)) = fn
        (Var (ixn, T), t)  =>
          if j>0 andalso not (null (flt j (loose_bnos t)))
          then raise PMatch
          else (tymatch (tyinsts, fn () => (T, fastype_of1 (Ts, t))),
            (ixn, t) :: insts)
      | (Free (a, T), Free (b, U)) =>
	  if a=b then (tymatch (tyinsts, K (T, U)), insts) else raise PMatch
      | (Const (a, T), Const (b, U))  =>
	  if a=b then (tymatch (tyinsts, K (T, U)), insts) else raise PMatch
      | (f $ t, g $ u) => mtch (mtch instsp (f, g)) (t, u)
      | (Bound i, Bound j) => if i=j then instsp else raise PMatch
      | _ => raise PMatch
  in mtch end;

fun match_proof Ts tymatch =
  let
    fun optmatch _ inst (None, _) = inst
      | optmatch _ _ (Some _, None) = raise PMatch
      | optmatch mtch inst (Some x, Some y) = mtch inst (x, y)

    fun matcht Ts j (pinst, tinst) (t, u) =
      (pinst, fomatch Ts tymatch j tinst (t, Envir.beta_norm u));
    fun matchT (pinst, (tyinsts, insts)) p =
      (pinst, (tymatch (tyinsts, K p), insts));
    fun matchTs inst (Ts, Us) = foldl (uncurry matchT) (inst, Ts ~~ Us);

    fun mtch Ts i j (pinst, tinst) (Hyp (Var (ixn, _)), prf) =
          if i = 0 andalso j = 0 then ((ixn, prf) :: pinst, tinst)
          else (case apfst (flt i) (apsnd (flt j)
                  (prf_add_loose_bnos 0 0 prf ([], []))) of
              ([], []) => ((ixn, incr_pboundvars (~i) (~j) prf) :: pinst, tinst)
            | ([], _) => if j = 0 then
                   ((ixn, incr_pboundvars (~i) (~j) prf) :: pinst, tinst)
                 else raise PMatch
            | _ => raise PMatch)
      | mtch Ts i j inst (prf1 % opt1, prf2 % opt2) =
          optmatch (matcht Ts j) (mtch Ts i j inst (prf1, prf2)) (opt1, opt2)
      | mtch Ts i j inst (prf1 %% prf2, prf1' %% prf2') =
          mtch Ts i j (mtch Ts i j inst (prf1, prf1')) (prf2, prf2')
      | mtch Ts i j inst (Abst (_, opT, prf1), Abst (_, opU, prf2)) =
          mtch (if_none opU dummyT :: Ts) i (j+1)
            (optmatch matchT inst (opT, opU)) (prf1, prf2)
      | mtch Ts i j inst (prf1, Abst (_, opU, prf2)) =
          mtch (if_none opU dummyT :: Ts) i (j+1) inst
            (incr_pboundvars 0 1 prf1 %> Bound 0, prf2)
      | mtch Ts i j inst (AbsP (_, opt, prf1), AbsP (_, opu, prf2)) =
          mtch Ts (i+1) j (optmatch (matcht Ts j) inst (opt, opu)) (prf1, prf2)
      | mtch Ts i j inst (prf1, AbsP (_, _, prf2)) =
          mtch Ts (i+1) j inst (incr_pboundvars 1 0 prf1 %% PBound 0, prf2)
      | mtch Ts i j inst (PThm ((name1, _), _, prop1, opTs),
            PThm ((name2, _), _, prop2, opUs)) =
          if name1=name2 andalso prop1=prop2 then
            optmatch matchTs inst (opTs, opUs)
          else raise PMatch
      | mtch Ts i j inst (PAxm (s1, _, opTs), PAxm (s2, _, opUs)) =
          if s1=s2 then optmatch matchTs inst (opTs, opUs)
          else raise PMatch
      | mtch _ _ _ inst (PBound i, PBound j) = if i = j then inst else raise PMatch
      | mtch _ _ _ _ _ = raise PMatch
  in mtch Ts 0 0 end;

fun prf_subst (pinst, (tyinsts, insts)) =
  let
    val substT = typ_subst_TVars_Vartab tyinsts;

    fun subst' lev (t as Var (ixn, _)) = (case assoc (insts, ixn) of
          None => t
        | Some u => incr_boundvars lev u)
      | subst' lev (Const (s, T)) = Const (s, substT T)
      | subst' lev (Free (s, T)) = Free (s, substT T)
      | subst' lev (Abs (a, T, body)) = Abs (a, substT T, subst' (lev+1) body)
      | subst' lev (f $ t) = subst' lev f $ subst' lev t
      | subst' _ t = t;

    fun subst plev tlev (AbsP (a, t, body)) =
          AbsP (a, apsome (subst' tlev) t, subst (plev+1) tlev body)
      | subst plev tlev (Abst (a, T, body)) =
          Abst (a, apsome substT T, subst plev (tlev+1) body)
      | subst plev tlev (prf %% prf') = subst plev tlev prf %% subst plev tlev prf'
      | subst plev tlev (prf % t) = subst plev tlev prf % apsome (subst' tlev) t
      | subst plev tlev (prf as Hyp (Var (ixn, _))) = (case assoc (pinst, ixn) of
          None => prf
        | Some prf' => incr_pboundvars plev tlev prf')
      | subst _ _ (PThm (id, prf, prop, Ts)) =
          PThm (id, prf, prop, apsome (map substT) Ts)
      | subst _ _ (PAxm (id, prop, Ts)) =
          PAxm (id, prop, apsome (map substT) Ts)
      | subst _ _ t = t
  in subst 0 0 end;

(*A fast unification filter: true unless the two terms cannot be unified. 
  Terms must be NORMAL.  Treats all Vars as distinct. *)
fun could_unify prf1 prf2 =
  let
    fun matchrands (prf1 %% prf2) (prf1' %% prf2') =
          could_unify prf2 prf2' andalso matchrands prf1 prf1'
      | matchrands (prf % Some t) (prf' % Some t') =
          Term.could_unify (t, t') andalso matchrands prf prf'
      | matchrands (prf % _) (prf' % _) = matchrands prf prf'
      | matchrands _ _ = true

    fun head_of (prf %% _) = head_of prf
      | head_of (prf % _) = head_of prf
      | head_of prf = prf

  in case (head_of prf1, head_of prf2) of
        (_, Hyp (Var _)) => true
      | (Hyp (Var _), _) => true
      | (PThm ((a, _), _, propa, _), PThm ((b, _), _, propb, _)) =>
          a = b andalso propa = propb andalso matchrands prf1 prf2
      | (PAxm (a, _, _), PAxm (b, _, _)) => a = b andalso matchrands prf1 prf2
      | (PBound i, PBound j) =>  i = j andalso matchrands prf1 prf2
      | (AbsP _, _) =>  true   (*because of possible eta equality*)
      | (Abst _, _) =>  true
      | (_, AbsP _) =>  true
      | (_, Abst _) =>  true
      | _ => false
  end;

(**** rewriting on proof terms ****)

val skel0 = PBound 0;

fun rewrite_prf tymatch (rules, procs) prf =
  let
    fun rew _ (Abst (_, _, body) % Some t) = Some (prf_subst_bounds [t] body, skel0)
      | rew _ (AbsP (_, _, body) %% prf) = Some (prf_subst_pbounds [prf] body, skel0)
      | rew Ts prf = (case get_first (fn (_, r) => r Ts prf) procs of
          Some prf' => Some (prf', skel0)
        | None => get_first (fn (prf1, prf2) => Some (prf_subst
            (match_proof Ts tymatch ([], (Vartab.empty, [])) (prf1, prf)) prf2, prf2)
               handle PMatch => None) (filter (could_unify prf o fst) rules));

    fun rew0 Ts (prf as AbsP (_, _, prf' %% PBound 0)) =
          if prf_loose_Pbvar1 prf' 0 then rew Ts prf
          else
            let val prf'' = incr_pboundvars (~1) 0 prf'
            in Some (if_none (rew Ts prf'') (prf'', skel0)) end
      | rew0 Ts (prf as Abst (_, _, prf' % Some (Bound 0))) =
          if prf_loose_bvar1 prf' 0 then rew Ts prf
          else
            let val prf'' = incr_pboundvars 0 (~1) prf'
            in Some (if_none (rew Ts prf'') (prf'', skel0)) end
      | rew0 Ts prf = rew Ts prf;

    fun rew1 _ (Hyp (Var _)) _ = None
      | rew1 Ts skel prf = (case rew2 Ts skel prf of
          Some prf1 => (case rew0 Ts prf1 of
              Some (prf2, skel') => Some (if_none (rew1 Ts skel' prf2) prf2)
            | None => Some prf1)
        | None => (case rew0 Ts prf of
              Some (prf1, skel') => Some (if_none (rew1 Ts skel' prf1) prf1)
            | None => None))

    and rew2 Ts skel (prf % Some t) = (case prf of
            Abst (_, _, body) =>
              let val prf' = prf_subst_bounds [t] body
              in Some (if_none (rew2 Ts skel0 prf') prf') end
          | _ => (case rew1 Ts (case skel of skel' % _ => skel' | _ => skel0) prf of
              Some prf' => Some (prf' % Some t)
            | None => None))
      | rew2 Ts skel (prf % None) = apsome (fn prf' => prf' % None)
          (rew1 Ts (case skel of skel' % _ => skel' | _ => skel0) prf)
      | rew2 Ts skel (prf1 %% prf2) = (case prf1 of
            AbsP (_, _, body) =>
              let val prf' = prf_subst_pbounds [prf2] body
              in Some (if_none (rew2 Ts skel0 prf') prf') end
          | _ =>
            let val (skel1, skel2) = (case skel of
                skel1 %% skel2 => (skel1, skel2)
              | _ => (skel0, skel0))
            in case rew1 Ts skel1 prf1 of
                Some prf1' => (case rew1 Ts skel2 prf2 of
                    Some prf2' => Some (prf1' %% prf2')
                  | None => Some (prf1' %% prf2))
              | None => (case rew1 Ts skel2 prf2 of
                    Some prf2' => Some (prf1 %% prf2')
                  | None => None)
            end)
      | rew2 Ts skel (Abst (s, T, prf)) = (case rew1 (if_none T dummyT :: Ts)
              (case skel of Abst (_, _, skel') => skel' | _ => skel0) prf of
            Some prf' => Some (Abst (s, T, prf'))
          | None => None)
      | rew2 Ts skel (AbsP (s, t, prf)) = (case rew1 Ts
              (case skel of AbsP (_, _, skel') => skel' | _ => skel0) prf of
            Some prf' => Some (AbsP (s, t, prf'))
          | None => None)
      | rew2 _ _ _ = None

  in if_none (rew1 [] skel0 prf) prf end;

fun rewrite_proof tsig = rewrite_prf (fn (tab, f) =>
  Type.typ_match tsig (tab, f ()) handle Type.TYPE_MATCH => raise PMatch);

fun rewrite_proof_notypes rews = rewrite_prf fst rews;

(**** theory data ****)

(* data kind 'Pure/proof' *)

structure ProofArgs =
struct
  val name = "Pure/proof";
  type T = ((proof * proof) list *
    (string * (typ list -> proof -> proof option)) list);

  val empty = ([], []);
  val copy = I;
  val prep_ext = I;
  fun merge ((rules1, procs1), (rules2, procs2)) =
    (merge_lists rules1 rules2, merge_alists procs1 procs2);
  fun print _ _ = ();
end;

structure ProofData = TheoryDataFun(ProofArgs);

val init = ProofData.init;

fun add_prf_rrules rs thy =
  let val r = ProofData.get thy
  in ProofData.put (rs @ fst r, snd r) thy end;

fun add_prf_rprocs ps thy =
  let val r = ProofData.get thy
  in ProofData.put (fst r, ps @ snd r) thy end;

fun thm_proof sign (name, tags) hyps prop prf =
  let
    val prop = Logic.list_implies (hyps, prop);
    val nvs = needed_vars prop;
    val args = map (fn (v as Var (ixn, _)) =>
        if ixn mem nvs then Some v else None) (vars_of prop) @
      map Some (sort (make_ord atless) (term_frees prop));
    val opt_prf = if ! proofs = 2 then
        #4 (shrink [] 0 (rewrite_prf fst (ProofData.get_sg sign)
          (foldr (uncurry implies_intr_proof) (hyps, prf))))
      else MinProof (mk_min_proof ([], prf));
    val head = (case strip_combt (fst (strip_combP prf)) of
        (PThm ((old_name, _), prf', prop', None), args') =>
          if (old_name="" orelse old_name=name) andalso
             prop = prop' andalso args = args' then
            PThm ((name, tags), prf', prop, None)
          else
            PThm ((name, tags), opt_prf, prop, None)
      | _ => PThm ((name, tags), opt_prf, prop, None))
  in
    proof_combP (proof_combt' (head, args), map Hyp hyps)
  end;

fun get_name_tags hyps prop prf =
  let val prop = Logic.list_implies (hyps, prop) in
    (case strip_combt (fst (strip_combP prf)) of
      (PThm ((name, tags), _, prop', _), _) =>
        if prop=prop' then (name, tags) else ("", [])
    | (PAxm (name, prop', _), _) =>
        if prop=prop' then (name, []) else ("", [])
    | _ => ("", []))
  end;

end;

structure BasicProofterm : BASIC_PROOFTERM = Proofterm;
open BasicProofterm;
