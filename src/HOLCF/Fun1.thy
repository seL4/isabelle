(*  Title:      HOLCF/Fun1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Definition of the partial ordering for the type of all functions => (fun)

REMARK: The ordering on 'a => 'b is only defined if 'b is in class po !!
*)

theory Fun1 = Pcpo:

instance flat<chfin
apply (intro_classes)
apply (rule flat_imp_chfin)
done

(* to make << defineable: *)

instance fun  :: (type, sq_ord) sq_ord ..

defs (overloaded)
  less_fun_def: "(op <<) == (%f1 f2.!x. f1 x << f2 x)"  

(*  Title:      HOLCF/Fun1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Definition of the partial ordering for the type of all functions => (fun)
*)

(* ------------------------------------------------------------------------ *)
(* less_fun is a partial order on 'a => 'b                                  *)
(* ------------------------------------------------------------------------ *)

lemma refl_less_fun: "(f::'a::type =>'b::po) << f"
apply (unfold less_fun_def)
apply (fast intro!: refl_less)
done

lemma antisym_less_fun:
        "[|(f1::'a::type =>'b::po) << f2; f2 << f1|] ==> f1 = f2"
apply (unfold less_fun_def)
(* apply (cut_tac prems) *)
apply (subst expand_fun_eq)
apply (fast intro!: antisym_less)
done

lemma trans_less_fun:
        "[|(f1::'a::type =>'b::po) << f2; f2 << f3 |] ==> f1 << f3"
apply (unfold less_fun_def)
(* apply (cut_tac prems) *)
apply clarify
apply (rule trans_less)
apply (erule allE)
apply assumption
apply (erule allE, assumption)
done

end




