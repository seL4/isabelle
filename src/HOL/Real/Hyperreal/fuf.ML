(*  Title       : HOL/Real/Hyperreal/fuf.ml
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
                  1999  University of Edinburgh
    Description : Simple tactics to help proofs involving our 
                  free ultrafilter (FreeUltrafilterNat). We rely
                  on the fact that filters satisfy the  finite 
                  intersection property.
*)

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

fun Intprems [] = raise FUFempty
|   Intprems [x] = x
|   Intprems (x::y::ys) = 
      Intprems (([x,y] MRS FreeUltrafilterNat_Int) :: ys);

(*---------------------------------------------------------------  
   solves goals of the form 
    [| A1: FUF; A2: FUF; ...; An: FUF |] ==> B : FUF   
   where A1 Int A2 Int ... Int An <= B 
 ---------------------------------------------------------------*)

val Fuf_tac = METAHYPS(fn prems =>
                    (rtac ((Intprems (get_fuf_hyps prems [])) RS
                           FreeUltrafilterNat_subset) 1) THEN 
                    Auto_tac);

fun fuf_tac (fclaset,fsimpset) i = METAHYPS(fn prems =>
                    (rtac ((Intprems (get_fuf_hyps prems [])) RS
                           FreeUltrafilterNat_subset) 1) THEN 
                    auto_tac (fclaset,fsimpset)) i;

(*---------------------------------------------------------------  
   solves goals of the form 
    [| A1: FUF; A2: FUF; ...; An: FUF |] ==> P
   where A1 Int A2 Int ... Int An <= {} since {} ~: FUF
   (i.e. uses fact that FUF is a proper filter)
 ---------------------------------------------------------------*)

val Fuf_empty_tac = METAHYPS(fn prems => 
                    (rtac ((Intprems (get_fuf_hyps prems [])) RS
                           (FreeUltrafilterNat_subset RS 
                           (FreeUltrafilterNat_empty RS notE))) 1) 
                     THEN Auto_tac);

fun fuf_empty_tac (fclaset,fsimpset) i = METAHYPS(fn prems => 
                    (rtac ((Intprems (get_fuf_hyps prems [])) RS
                           (FreeUltrafilterNat_subset RS 
                          (FreeUltrafilterNat_empty RS notE))) 1) 
                     THEN auto_tac (fclaset,fsimpset)) i;

(*---------------------------------------------------------------  
  All in one -- not really needed.
 ---------------------------------------------------------------*)

fun Fuf_auto_tac i = SOLVE (Fuf_empty_tac i) ORELSE TRY(Fuf_tac i);

fun fuf_auto_tac (fclaset,fsimpset) i = 
     SOLVE (fuf_empty_tac (fclaset,fsimpset) i) 
     ORELSE TRY(fuf_tac (fclaset,fsimpset) i);

(*---------------------------------------------------------------  
   In fact could make this the only tactic: just need to
   use contraposition and then look for empty set.
 ---------------------------------------------------------------*)

fun Ultra_tac i = rtac ccontr i THEN Fuf_empty_tac i;
fun ultra_tac (fclaset,fsimpset) i = rtac ccontr i THEN 
              fuf_empty_tac (fclaset,fsimpset) i;

