(*  Title:      HOL/IOA/example/Sender.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Impl.
*)
 
Goal 
 "New : actions(impl_sig)       &   \
\ Loc l : actions(impl_sig)       &   \
\ Free l : actions(impl_sig) ";
by (simp_tac (simpset() addsimps 
             (Impl.sig_def :: actions_def :: 
              asig_projections)) 1);
qed "in_impl_asig";
