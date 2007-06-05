(*  Title:      HOL/Tools/Groebner_Basis/misc.ML
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Very basic stuff for cterms.
*)

structure Misc =
struct

open Conv;

val is_comb = can Thm.dest_comb;
val concl = cprop_of #> Thm.dest_arg;

fun is_binop ct ct' = ct aconvc (Thm.dest_fun2 ct')
  handle CTERM _ => false;

fun dest_binop ct ct' =
  if is_binop ct ct' then Thm.dest_binop ct'
  else raise CTERM ("dest_binop: bad binop", [ct,ct'])

(* INFERENCE *)
fun conji th th' = 
let val p = concl th val q = concl th' 
in implies_elim (implies_elim (instantiate' [] (map SOME [p,q]) conjI) th) th' end;
fun conjunct1' th = th RS conjunct1;
fun conjunct2' th = th RS conjunct2;
fun conj_pair th = (conjunct1' th, conjunct2' th);
val conjuncts =
 let fun CJ th acc =
      ((let val (th1,th2) = conj_pair th
      in CJ th2 (CJ th1 acc) end)
         handle THM _ => th::acc)
 in fn th => rev (CJ th [])
 end;

fun inst_thm inst = Thm.instantiate ([], inst);

end;
