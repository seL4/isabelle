(*  Title:      HOL/Integ/presburger.ML
    ID:         $Id$
    Author:     Amine Chaieb and Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Tactic for solving arithmetical Goals in Presburger Arithmetic
*)

signature PRESBURGER = 
sig
 val presburger_tac : bool -> int -> tactic
 val presburger_method : bool -> int -> Proof.method
 val setup : (theory -> theory) list
 val trace : bool ref
end;

structure Presburger: PRESBURGER =
struct

val trace = ref false;
fun trace_msg s = if !trace then tracing s else ();

(*-----------------------------------------------------------------*)
(*cooper_pp: provefunction for the one-exstance quantifier elimination*)
(* Here still only one problem : The proof for the arithmetical transformations done on the dvd atomic formulae*)
(*-----------------------------------------------------------------*)

val presburger_ss = simpset_of (theory "Presburger");

fun cooper_pp sg vrl (fm as e$Abs(xn,xT,p)) = 
  let val (xn1,p1) = variant_abs (xn,xT,p)
  in (CooperProof.cooper_prv sg (Free (xn1, xT)) p1 vrl) end;

fun mnnf_pp sg fm = CooperProof.proof_of_cnnf sg fm
  (CooperProof.proof_of_evalc sg);

fun mproof_of_int_qelim sg fm =
  Qelim.proof_of_mlift_qelim sg CooperDec.is_arith_rel
    (CooperProof.proof_of_linform sg) (mnnf_pp sg) (cooper_pp sg) fm;

(* Theorems to be used in this tactic*)

val zdvd_int = thm "zdvd_int";
val zdiff_int_split = thm "zdiff_int_split";
val all_nat = thm "all_nat";
val ex_nat = thm "ex_nat";
val number_of1 = thm "number_of1";
val number_of2 = thm "number_of2";
val split_zdiv = thm "split_zdiv";
val split_zmod = thm "split_zmod";
val mod_div_equality' = thm "mod_div_equality'";
val split_div' = thm "split_div'";
val Suc_plus1 = thm "Suc_plus1";
val imp_le_cong = thm "imp_le_cong";
val conj_le_cong = thm "conj_le_cong";

(* extract all the constants in a term*)
fun add_term_typed_consts (Const (c, T), cs) = (c,T) ins cs
  | add_term_typed_consts (t $ u, cs) =
      add_term_typed_consts (t, add_term_typed_consts (u, cs))
  | add_term_typed_consts (Abs (_, _, t), cs) = add_term_typed_consts (t, cs)
  | add_term_typed_consts (_, cs) = cs;

fun term_typed_consts t = add_term_typed_consts(t,[]);

(* put a term into eta long beta normal form *)
fun eta_long Ts (Abs (s, T, t)) = Abs (s, T, eta_long (T :: Ts) t)
  | eta_long Ts t = (case strip_comb t of
      (Abs _, _) => eta_long Ts (Envir.beta_norm t)
    | (u, ts) => 
      let val Us = binder_types (fastype_of1 (Ts, t))
      in list_abs (map (pair "x") Us, Unify.combound
        (list_comb (u, map (eta_long Ts) ts), 0, length Us))
      end);

(* Some Types*)
val bT = HOLogic.boolT;
val iT = HOLogic.intT;
val binT = HOLogic.binT;
val nT = HOLogic.natT;

(* Allowed Consts in formulae for presburger tactic*)

val allowed_consts =
  [("All", (iT --> bT) --> bT),
   ("Ex", (iT --> bT) --> bT),
   ("All", (nT --> bT) --> bT),
   ("Ex", (nT --> bT) --> bT),

   ("op &", bT --> bT --> bT),
   ("op |", bT --> bT --> bT),
   ("op -->", bT --> bT --> bT),
   ("op =", bT --> bT --> bT),
   ("Not", bT --> bT),

   ("op <=", iT --> iT --> bT),
   ("op =", iT --> iT --> bT),
   ("op <", iT --> iT --> bT),
   ("Divides.op dvd", iT --> iT --> bT),
   ("Divides.op div", iT --> iT --> iT),
   ("Divides.op mod", iT --> iT --> iT),
   ("op +", iT --> iT --> iT),
   ("op -", iT --> iT --> iT),
   ("op *", iT --> iT --> iT), 
   ("HOL.abs", iT --> iT),
   ("uminus", iT --> iT),

   ("op <=", nT --> nT --> bT),
   ("op =", nT --> nT --> bT),
   ("op <", nT --> nT --> bT),
   ("Divides.op dvd", nT --> nT --> bT),
   ("Divides.op div", nT --> nT --> nT),
   ("Divides.op mod", nT --> nT --> nT),
   ("op +", nT --> nT --> nT),
   ("op -", nT --> nT --> nT),
   ("op *", nT --> nT --> nT), 
   ("Suc", nT --> nT),

   ("Numeral.bin.Bit", binT --> bT --> binT),
   ("Numeral.bin.Pls", binT),
   ("Numeral.bin.Min", binT),
   ("Numeral.number_of", binT --> iT),
   ("Numeral.number_of", binT --> nT),
   ("0", nT),
   ("0", iT),
   ("1", nT),
   ("1", iT),

   ("False", bT),
   ("True", bT)];

(*returns true if the formula is relevant for presburger arithmetic tactic*)
fun relevant t = (term_typed_consts t) subset allowed_consts;

(* Preparation of the formula to be sent to the Integer quantifier *)
(* elimination procedure                                           *)
(* Transforms meta implications and meta quantifiers to object     *)
(* implications and object quantifiers                             *)

fun prepare_for_presburger q fm = 
  let
    val ps = Logic.strip_params fm
    val hs = map HOLogic.dest_Trueprop (Logic.strip_assums_hyp fm)
    val c = HOLogic.dest_Trueprop (Logic.strip_assums_concl fm)
    val _ = if relevant c then () else raise CooperDec.COOPER
    fun mk_all ((s, T), (P,n)) =
      if 0 mem loose_bnos P then
        (HOLogic.all_const T $ Abs (s, T, P), n)
      else (incr_boundvars ~1 P, n-1)
    fun mk_all2 (v, t) = HOLogic.all_const (fastype_of v) $ lambda v t;
    val (rhs,irhs) = partition relevant hs
    val np = length ps
    val (fm',np) =  foldr (fn ((x, T), (fm,n)) => mk_all ((x, T), (fm,n)))
      (ps,(foldr HOLogic.mk_imp (rhs, c), np))
    val (vs, _) = partition (fn t => q orelse (type_of t) = nT)
      (term_frees fm' @ term_vars fm');
    val fm2 = foldr mk_all2 (vs, fm')
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if (n=0) then th else (spec_step (n-1) th) RS spec ;

(* object implication to meta---*)
fun mp_step n th = if (n=0) then th else (mp_step (n-1) th) RS mp;

(* the presburger tactic*)
fun presburger_tac q i st =
  let
    val g = BasisLibrary.List.nth (prems_of st, i - 1);
    val sg = sign_of_thm st;
    (* Transform the term*)
    val (t,np,nh) = prepare_for_presburger q g
    (* Some simpsets for dealing with mod div abs and nat*)

    val simpset0 = HOL_basic_ss
      addsimps [mod_div_equality', Suc_plus1]
      addsplits [split_zdiv, split_zmod, split_div']
    (* Simp rules for changing (n::int) to int n *)
    val simpset1 = HOL_basic_ss
      addsimps [nat_number_of_def, zdvd_int] @ map (fn r => r RS sym)
        [int_int_eq, zle_int, zless_int, zadd_int, zmult_int]
      addsplits [zdiff_int_split]
    (*simp rules for elimination of int n*)

    val simpset2 = HOL_basic_ss
      addsimps [nat_0_le, all_nat, ex_nat, number_of1, number_of2, int_0, int_1]
      addcongs [conj_le_cong, imp_le_cong]
    (* simp rules for elimination of abs *)

    val simpset3 = HOL_basic_ss addsplits [zabs_split]
	      
    val ct = cterm_of sg (HOLogic.mk_Trueprop t)

    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac simpset0 i,
       TRY (simp_tac simpset1 i), TRY (simp_tac simpset2 i),
       TRY (simp_tac simpset3 i), TRY (simp_tac presburger_ss i)]
      (trivial ct))

    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i);

    (* The result of the quantifier elimination *)
    val (th, tac) = case (prop_of pre_thm) of
        Const ("==>", _) $ (Const ("Trueprop", _) $ t1) $ _ =>
          (trace_msg ("calling procedure with term:\n" ^
             Sign.string_of_term sg t1);
           ((mproof_of_int_qelim sg (eta_long [] t1) RS iffD2) RS pre_thm,
            assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i)))
      | _ => (pre_thm, assm_tac i)
  in (rtac (((mp_step nh) o (spec_step np)) th) i THEN tac) st
  end handle Subscript => no_tac st | CooperDec.COOPER => no_tac st;

fun presburger_args meth =
  Method.simple_args (Scan.optional (Args.$$$ "no_quantify" >> K false) true)
    (fn q => fn _ => meth q 1);

fun presburger_method q i = Method.METHOD (fn facts =>
  Method.insert_tac facts 1 THEN presburger_tac q i)

val setup =
  [Method.add_method ("presburger",
     presburger_args presburger_method,
     "decision procedure for Presburger arithmetic"),
   ArithTheoryData.map (fn {splits, inj_consts, discrete, presburger} =>
     {splits = splits, inj_consts = inj_consts, discrete = discrete,
      presburger = Some (presburger_tac true)})];

end;

val presburger_tac = Presburger.presburger_tac true;
