(*  Title:      CCL/types.thy
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1993  University of Cambridge

Types in CCL are defined as sets of terms.

*)

Type = Term +

consts

  Subtype       :: "['a set, 'a => o] => 'a set"
  Bool          :: "i set"
  Unit          :: "i set"
  "+"           :: "[i set, i set] => i set"         (infixr 55)
  Pi            :: "[i set, i => i set] => i set"
  Sigma         :: "[i set, i => i set] => i set"
  Nat           :: "i set"
  List          :: "i set => i set"
  Lists         :: "i set => i set"
  ILists        :: "i set => i set"
  TAll          :: "(i set => i set) => i set"       (binder "TALL " 55)
  TEx           :: "(i set => i set) => i set"       (binder "TEX " 55)
  Lift          :: "i set => i set"                  ("(3[_])")

  SPLIT         :: "[i, [i, i] => i set] => i set"

  "@Pi"         :: "[idt, i set, i set] => i set"    ("(3PROD _:_./ _)"
                                [0,0,60] 60)

  "@Sigma"      :: "[idt, i set, i set] => i set"    ("(3SUM _:_./ _)"
                                [0,0,60] 60)
  
  "@->"         :: "[i set, i set] => i set"         ("(_ ->/ _)"  [54, 53] 53)
  "@*"          :: "[i set, i set] => i set"         ("(_ */ _)" [56, 55] 55)
  "@Subtype"    :: "[idt, 'a set, o] => 'a set"      ("(1{_: _ ./ _})")

translations
  "PROD x:A. B" => "Pi(A, %x. B)"
  "A -> B"      => "Pi(A, _K(B))"
  "SUM x:A. B"  => "Sigma(A, %x. B)"
  "A * B"       => "Sigma(A, _K(B))"
  "{x: A. B}"   == "Subtype(A, %x. B)"

rules

  Subtype_def "{x:A.P(x)} == {x.x:A & P(x)}"
  Unit_def          "Unit == {x.x=one}"
  Bool_def          "Bool == {x.x=true | x=false}"
  Plus_def           "A+B == {x. (EX a:A.x=inl(a)) | (EX b:B.x=inr(b))}"
  Pi_def         "Pi(A,B) == {x.EX b.x=lam x.b(x) & (ALL x:A.b(x):B(x))}"
  Sigma_def   "Sigma(A,B) == {x.EX a:A.EX b:B(a).x=<a,b>}"
  Nat_def            "Nat == lfp(% X.Unit + X)"
  List_def       "List(A) == lfp(% X.Unit + A*X)"

  Lists_def     "Lists(A) == gfp(% X.Unit + A*X)"
  ILists_def   "ILists(A) == gfp(% X.{} + A*X)"

  Tall_def   "TALL X.B(X) == Inter({X.EX Y.X=B(Y)})"
  Tex_def     "TEX X.B(X) == Union({X.EX Y.X=B(Y)})"
  Lift_def           "[A] == A Un {bot}"

  SPLIT_def   "SPLIT(p,B) == Union({A.EX x y.p=<x,y> & A=B(x,y)})"

end


ML

val print_translation =
  [("Pi", dependent_tr' ("@Pi", "@->")),
   ("Sigma", dependent_tr' ("@Sigma", "@*"))];

