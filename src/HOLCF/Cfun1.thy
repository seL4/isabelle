(*  Title:      HOLCF/cfun1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Definition of the type ->  of continuous functions

*)

Cfun1 = Cont +


(* new type of continuous functions *)

types "->" 2        (infixr 5)

arities "->" :: (pcpo,pcpo)term         (* No properties for ->'s range *)

consts  
        Cfun    :: "('a => 'b)set"
        fapp    :: "('a -> 'b)=>('a => 'b)"     (* usually Rep_Cfun *)
                                                (* application      *)

        fabs    :: "('a => 'b)=>('a -> 'b)"     (binder "LAM " 10)
                                                (* usually Abs_Cfun *)
                                                (* abstraction      *)

        less_cfun :: "[('a -> 'b),('a -> 'b)]=>bool"

syntax  "@fapp"     :: "('a -> 'b)=>('a => 'b)" ("_`_" [999,1000] 999)

translations "f`x" == "fapp f x"

defs 
  Cfun_def      "Cfun == {f. cont(f)}"

rules

  (*faking a type definition... *)
  (* -> is isomorphic to Cfun   *)

  Rep_Cfun              "fapp fo : Cfun"
  Rep_Cfun_inverse      "fabs (fapp fo) = fo"
  Abs_Cfun_inverse      "f:Cfun ==> fapp(fabs f) = f"

defs
  (*defining the abstract constants*)
  less_cfun_def         "less_cfun fo1 fo2 == ( fapp fo1 << fapp fo2 )"

(* start 8bit 1 *)
(* end 8bit 1 *)


end

(* start 8bit 2 *)
(* end 8bit 2 *)
