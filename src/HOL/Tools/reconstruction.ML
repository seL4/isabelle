(*  Title:      HOL/Reconstruction.thy
    ID: $Id$
    Author:     Lawrence C Paulson and Claire Quigley
    Copyright   2004  University of Cambridge
*)

(*Attributes for reconstructing external resolution proofs*)

structure Reconstruction =
let open Attrib
in
struct

(**************************************************************)
(* extra functions necessary for factoring and paramodulation *)
(**************************************************************)

fun mksubstlist [] sublist = sublist
  | mksubstlist ((a,b)::rest) sublist = 
      let val vartype = type_of b
          val avar = Var(a,vartype)
          val newlist = ((avar,b)::sublist) 
      in mksubstlist rest newlist end;


fun get_unif_comb t eqterm =
    if ((type_of t) = (type_of eqterm))
    then t
    else
        let val _ $ rand = t
        in get_unif_comb rand eqterm end;

fun get_unif_lit t eqterm =
    if (can HOLogic.dest_eq t)
    then
	let val (lhs,rhs) = HOLogic.dest_eq(HOLogic.dest_Trueprop eqterm)
	in lhs end
    else
	get_unif_comb t eqterm;



(**** attributes ****)

(** Binary resolution **)

fun binary_rule ((cl1, lit1), (cl2 , lit2)) =
     select_literal (lit1 + 1) cl1
     RSN ((lit2 + 1), cl2);

fun binary_syntax ((i, B), j) (x, A) = (x, binary_rule ((A,i), (B,j)));

fun gen_BINARY thm = syntax
      ((Scan.lift Args.nat -- thm -- Scan.lift Args.nat) >> binary_syntax);
val BINARY_global = gen_BINARY global_thm;
val BINARY_local = gen_BINARY local_thm;

(*I have not done the MRR rule because it seems to be identifical to 
BINARY*)


fun inst_single sign t1 t2 cl =
    let val ct1 = cterm_of sign t1 and ct2 = cterm_of sign t2
    in  hd (Seq.list_of(distinct_subgoals_tac
			    (cterm_instantiate [(ct1,ct2)] cl)))  
    end;

fun inst_subst sign substs cl =
    if (is_Var (fst(hd(substs))))
    then inst_single sign (fst (hd substs)) (snd (hd substs)) cl
    else if (is_Var (snd(hd(substs))))
    then inst_single sign (snd (hd substs)) (fst (hd substs)) cl
    else raise THM ("inst_subst", 0, [cl]);

(*Grabs the environment from the result of Unify.unifiers*)
fun getnewenv thisseq = fst (hd (Seq.list_of thisseq));

(** Factoring **)

fun factor_rule (cl, lit1, lit2) =
    let
       val prems = prems_of cl
       val fac1 = List.nth (prems,lit1)
       val fac2 = List.nth (prems,lit2)
       val sign = sign_of_thm cl
       val unif_env = Unify.unifiers (sign, Envir.empty 0, [(fac1, fac2)])
       val newenv = getnewenv unif_env
       val envlist = Envir.alist_of newenv
     in
       inst_subst sign (mksubstlist envlist []) cl
    end;

fun factor_syntax (i, j) (x, A) = (x, factor_rule (A,i,j));

fun FACTOR x = syntax ((Scan.lift (Args.nat -- Args.nat)) >> factor_syntax) x;


(** Paramodulation **)

(*Get rid of a Not if it is present*)
fun maybe_dest_not (Const ("Not", _) $ t) = t
  | maybe_dest_not t = t;

fun paramod_rule ((cl1, lit1), (cl2 , lit2)) =
    let val prems1 = prems_of cl1
	val prems2 = prems_of cl2
        val sign = Sign.merge (sign_of_thm cl1, sign_of_thm cl2)
	(* want to get first element of equality *)

	val fac1 = List.nth (prems1,lit1) 
	val (lhs, rhs) = HOLogic.dest_eq(maybe_dest_not
					     (HOLogic.dest_Trueprop fac1))
	(* get other literal involved in the paramodulation *)
	val fac2 = List.nth (prems2,lit2) 

       (* get bit of th2 to unify with lhs of cl1 *)
	val unif_lit = get_unif_lit (HOLogic.dest_Trueprop fac2) lhs
	val unif_env = Unify.unifiers (sign, Envir.empty 0, [(unif_lit, lhs)])
	val newenv = getnewenv unif_env
	val envlist = Envir.alist_of newenv
       (* instantiate cl2 with unifiers *)

	val newth1 = inst_subst sign (mksubstlist envlist []) cl1
       (*rewrite cl2 with the equality bit of cl2 i.e. lit2 *)
	  val facthm' = select_literal (lit1 + 1) newth1
	  val equal_lit = concl_of facthm'
	  val cterm_eq = cterm_of sign equal_lit
	  val eq_thm = assume cterm_eq
	  val meta_eq_thm = mk_meta_eq eq_thm
	  val newth2= rewrite_rule [meta_eq_thm] cl2
       (*thin lit2 from cl2 *)
       (* get cl1 with lit1 as concl, then resolve with thin_rl *)
	  val thm' = facthm' RS thin_rl
       (* now resolve cl2 with last premise of thm' *)
	  val newthm = newth2  RSN ((length prems1), thm')
     in newthm end


fun paramod_syntax ((i, B), j) (x, A) = (x, paramod_rule ((A,i), (B,j)));

fun gen_PARAMOD thm = syntax
      ((Scan.lift Args.nat -- thm -- Scan.lift Args.nat) >> paramod_syntax);
val PARAMOD_global = gen_PARAMOD global_thm;
val PARAMOD_local = gen_PARAMOD local_thm;


(** Demodulation, i.e. rewriting **)

fun demod_rule (cl1,lit1,cl2) =
    let  val eq_lit_th = select_literal (lit1+1) cl1
	 val equal_lit = concl_of eq_lit_th
         val sign = Sign.merge (sign_of_thm cl1, sign_of_thm cl2)
	 val cterm_eq = cterm_of sign equal_lit
	 val eq_thm = assume cterm_eq
	 val meta_eq_thm = mk_meta_eq eq_thm
	 val newth2= rewrite_rule [meta_eq_thm] cl2
    in newth2 end;

fun demod_syntax (i, B) (x, A) = (x, demod_rule (A,i,B));

fun gen_DEMOD thm = syntax ((Scan.lift Args.nat -- thm) >> demod_syntax);
val DEMOD_global = gen_DEMOD global_thm;
val DEMOD_local = gen_DEMOD local_thm;


(** theory setup **)

val setup =
  [Attrib.add_attributes
     [("BINARY", (BINARY_global, BINARY_local), "binary resolution"),
      ("PARAMOD", (PARAMOD_global, PARAMOD_local), "paramodulation"),
      ("DEMOD", (DEMOD_global, DEMOD_local), "demodulation"),
      ("FACTOR", (FACTOR, FACTOR), "factoring")]];

end
end


