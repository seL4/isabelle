(*  Title:      HOL/Lambda/ParRed.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Parallel reduction and a complete developments function "cd".
*)

ParRed = Lambda + Commutation + Recdef +

consts  par_beta :: "(dB * dB) set"

syntax  "=>" :: [dB,dB] => bool (infixl 50)

translations
  "s => t" == "(s,t) : par_beta"

inductive par_beta
  intrs
    var   "Var n => Var n"
    abs   "s => t ==> Abs s => Abs t"
    app   "[| s => s'; t => t' |] ==> s @ t => s' @ t'"
    beta  "[| s => s'; t => t' |] ==> (Abs s) @ t => s'[t'/0]"

consts
  cd  :: dB => dB

recdef cd "measure size"
  "cd(Var n) = Var n"
  "cd(Var n @ t) = Var n @ cd t"
  "cd((s1 @ s2) @ t) = cd(s1 @ s2) @ cd t"
  "cd(Abs u @ t) = (cd u)[cd t/0]"
(*
  "cd(s @ t) = (case s of Var n   => (s @ cd t)
                        | s1 @ s2 => (cd s @ cd t) 
                        | Abs u   => deAbs(cd s)[cd t/0])"
*)
  "cd(Abs s) = Abs(cd s)"
(*
primrec deAbs dB
  "deAbs(Var n) = Var n"
  "deAbs(s @ t) = s @ t"
  "deAbs(Abs s) = s"*)
end
