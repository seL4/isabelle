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

fun gen_binary thm = syntax
      ((Scan.lift Args.nat -- thm -- Scan.lift Args.nat) >> binary_syntax);
val binary_global = gen_binary global_thm;
val binary_local = gen_binary local_thm;

(*I have not done the MRR rule because it seems to be identifical to 
binary*)


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

fun factor x = syntax ((Scan.lift (Args.nat -- Args.nat)) >> factor_syntax) x;


(** Paramodulation **)

(*subst with premises exchanged: that way, side literals of the equality will appear
  as the second to last premises of the result.*)
val rev_subst = rotate_prems 1 subst;

fun paramod_rule ((cl1, lit1), (cl2, lit2)) =
    let  val eq_lit_th = select_literal (lit1+1) cl1
         val mod_lit_th = select_literal (lit2+1) cl2
         val eqsubst = eq_lit_th RSN (2,rev_subst)
         val newth = Seq.hd (biresolution false [(false, mod_lit_th)] 1 eqsubst)
         val newth' = Seq.hd (flexflex_rule newth)
    in negated_asm_of_head newth' end;


fun paramod_syntax ((i, B), j) (x, A) = (x, paramod_rule ((A,i), (B,j)));

fun gen_paramod thm = syntax
      ((Scan.lift Args.nat -- thm -- Scan.lift Args.nat) >> paramod_syntax);
val paramod_global = gen_paramod global_thm;
val paramod_local = gen_paramod local_thm;


(** Demodulation: rewriting of a single literal (Non-Unit Rewriting, SPASS) **)

fun demod_rule ((cl1, lit1), (cl2 , lit2)) = 
    let  val eq_lit_th = select_literal (lit1+1) cl1
         val mod_lit_th = select_literal (lit2+1) cl2
	 val (fmod_th,thaw) = Drule.freeze_thaw_robust mod_lit_th
         val eqsubst = eq_lit_th RSN (2,rev_subst)
         val newth = Seq.hd(biresolution false [(false, fmod_th)] 1 eqsubst)
         val offset = #maxidx(rep_thm newth) + 1
	                  (*ensures "renaming apart" even when Vars are frozen*)
    in negated_asm_of_head (thaw offset newth) end;

fun demod_syntax ((i, B), j) (x, A) = (x, demod_rule ((A,i), (B,j)));

fun gen_demod thm = syntax
      ((Scan.lift Args.nat -- thm -- Scan.lift Args.nat) >> demod_syntax);
val demod_global = gen_demod global_thm;
val demod_local = gen_demod local_thm;


(** Conversion of a theorem into clauses **)

local

  (*Cache for clauses: could be a hash table if we provided them.*)
  val cc = ref (Symtab.empty : (thm * thm list) Symtab.table)

  fun memo_cnf th =
    case Thm.name_of_thm th of
        "" => ResAxioms.meta_cnf_axiom th (*no name, so can't cache*)
      | s  => case Symtab.lookup (!cc,s) of
      	        NONE => 
      	        	let val cls = ResAxioms.meta_cnf_axiom th
      	        	in  cc := Symtab.update ((s, (th,cls)), !cc); cls
      	        	end
      	      | SOME(th',cls) =>
      	      	    if eq_thm(th,th') then cls
      	      	    else (*New theorem stored under the same name? Possible??*)
      	      	      let val cls = ResAxioms.meta_cnf_axiom th
      	        	  in  cc := Symtab.update ((s, (th,cls)), !cc); cls
      	        	  end;

in
fun clausify_rule (A,i) = List.nth (memo_cnf A,i)
end;

fun clausify_syntax i (x, A) = (x, clausify_rule (A,i));

fun clausify x = syntax ((Scan.lift Args.nat) >> clausify_syntax) x;


(** theory setup **)

val setup =
  [Attrib.add_attributes
     [("binary", (binary_global, binary_local), "binary resolution"),
      ("paramod", (paramod_global, paramod_local), "paramodulation"),
      ("demod", (demod_global, demod_local), "demodulation"),
      ("factor", (factor, factor), "factoring"),
      ("clausify", (clausify, clausify), "conversion to clauses")]];

end
end


