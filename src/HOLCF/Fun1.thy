(*  Title:      HOLCF/Fun1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Definition of the partial ordering for the type of all functions => (fun)

REMARK: The ordering on 'a => 'b is only defined if 'b is in class po !!
*)

Fun1 = Pcpo +

instance flat<chfin (flat_imp_chfin)

(* to make << defineable: *)
instance fun  :: (term,sq_ord)sq_ord

defs
  less_fun_def "(op <<) == (%f1 f2.!x. f1 x << f2 x)"  
end




