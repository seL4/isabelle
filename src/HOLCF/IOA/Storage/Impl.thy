(*  Title:      HOL/IOA/example/Spec.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The implementation of a memory *}

theory Impl
imports IOA Action
begin

consts

impl_sig   :: "action signature"
impl_trans :: "(action, nat  * bool)transition set"
impl_ioa   :: "(action, nat * bool)ioa"

defs

sig_def: "impl_sig == (UN l.{Free l} Un {New},
                     UN l.{Loc l},
                     {})"

trans_def: "impl_trans ==
 {tr. let s = fst(tr); k = fst s; b = snd s;
          t = snd(snd(tr)); k' = fst t; b' = snd t
      in
      case fst(snd(tr))
      of
      New       => k' = k & b'  |
      Loc l     => b & l= k & k'= (Suc k) & ~b' |
      Free l    => k'=k & b'=b}"

ioa_def: "impl_ioa == (impl_sig, {(0,False)}, impl_trans,{},{})"

lemma in_impl_asig:
  "New : actions(impl_sig) &
    Loc l : actions(impl_sig) &
    Free l : actions(impl_sig) "
  by (simp add: Impl.sig_def actions_def asig_projections)

ML {* use_legacy_bindings (the_context ()) *}

end
