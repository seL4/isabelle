(*  Title:      HOL/Lambda/ParRed.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Parallel reduction and a complete developments function "cd".
Follows the first two pages of

@article{Takahashi-IC-95,author="Masako Takahashi",
title="Parallel Reductions in $\lambda$-Calculus",
journal=IC,year=1995,volume=118,pages="120--127"}
*)

ParRed = Lambda + Confluence +

consts  par_beta :: "(db * db) set"

syntax  "=>" :: "[db,db] => bool" (infixl 50)

translations
  "s => t" == "(s,t) : par_beta"

inductive "par_beta"
  intrs
    var   "Var n => Var n"
    abs   "s => t ==> Fun s => Fun t"
    app   "[| s => s'; t => t' |] ==> s @ t => s' @ t'"
    beta  "[| s => s'; t => t' |] ==> (Fun s) @ t => s'[t'/0]"

consts
  cd  :: "db => db"
  deFun :: "db => db"

primrec cd db
  cd_Var "cd(Var n) = Var n"
  cd_App "cd(s @ t) = (case s of
            Var n => s @ (cd t) |
            s1 @ s2 => (cd s) @ (cd t) |
            Fun u => deFun(cd s)[cd t/0])"
  cd_Fun "cd(Fun s) = Fun(cd s)"

primrec deFun db
  deFun_Var "deFun(Var n) = Var n"
  deFun_App "deFun(s @ t) = s @ t"
  deFun_Fun "deFun(Fun s) = s"
end
