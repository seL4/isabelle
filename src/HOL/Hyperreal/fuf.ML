(*  Title       : HOL/Real/Hyperreal/fuf.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
                  1999  University of Edinburgh

Simple tactics to help proofs involving our free ultrafilter
(FreeUltrafilterNat). We rely on the fact that filters satisfy the
finite intersection property.
*)

local

exception FUFempty;

fun get_fuf_hyps [] zs = zs
|   get_fuf_hyps (x::xs) zs =
        case (concl_of x) of
        (_ $ (Const ("Not",_) $ (Const ("op :",_) $ _ $
             Const ("HyperDef.FreeUltrafilterNat",_)))) =>  get_fuf_hyps xs
                                              ((x RS FreeUltrafilterNat_Compl_mem)::zs)
       |(_ $ (Const ("op :",_) $ _ $
             Const ("HyperDef.FreeUltrafilterNat",_)))  =>  get_fuf_hyps xs (x::zs)
       | _ => get_fuf_hyps xs zs;

fun inter_prems [] = raise FUFempty
|   inter_prems [x] = x
|   inter_prems (x::y::ys) =
      inter_prems (([x,y] MRS FreeUltrafilterNat_Int) :: ys);

in

(*---------------------------------------------------------------
   solves goals of the form
    [| A1: FUF; A2: FUF; ...; An: FUF |] ==> B : FUF
   where A1 Int A2 Int ... Int An <= B
 ---------------------------------------------------------------*)

fun fuf_tac css i = METAHYPS(fn prems =>
                    (rtac ((inter_prems (get_fuf_hyps prems [])) RS
                           FreeUltrafilterNat_subset) 1) THEN
                    auto_tac css) i;

fun Fuf_tac i = fuf_tac (clasimpset ()) i;


(*---------------------------------------------------------------
   solves goals of the form
    [| A1: FUF; A2: FUF; ...; An: FUF |] ==> P
   where A1 Int A2 Int ... Int An <= {} since {} ~: FUF
   (i.e. uses fact that FUF is a proper filter)
 ---------------------------------------------------------------*)

fun fuf_empty_tac css i = METAHYPS (fn prems =>
  rtac ((inter_prems (get_fuf_hyps prems [])) RS
    (FreeUltrafilterNat_subset RS (FreeUltrafilterNat_empty RS notE))) 1
                     THEN auto_tac css) i;

fun Fuf_empty_tac i = fuf_empty_tac (clasimpset ()) i;


(*---------------------------------------------------------------
   In fact could make this the only tactic: just need to
   use contraposition and then look for empty set.
 ---------------------------------------------------------------*)

fun ultra_tac css i = rtac ccontr i THEN fuf_empty_tac css i;
fun Ultra_tac i = ultra_tac (clasimpset ()) i;

end;
