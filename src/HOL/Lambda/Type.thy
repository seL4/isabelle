(*  Title:      HOL/Lambda/Type.thy
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   2000 TU Muenchen

Simply-typed lambda terms.
*)

Type = InductTermi +

datatype typ = Atom nat
             | Fun typ typ (infixr "=>" 200)

consts
  typing :: "((nat => typ) * dB * typ) set"

syntax
  "@type" :: "[nat => typ, dB, typ] => bool" ("_ |- _ : _" [50,50,50] 50)
  "=>>"   :: "[typ list, typ] => typ" (infixl 150)

translations
  "env |- t : T" == "(env, t, T) : typing"
  "Ts =>> T" == "foldr Fun Ts T"

inductive typing
intrs
  VAR  "env x = T ==> env |- Var x : T"
  ABS  "(nat_case T env) |- t : U ==> env |- (Abs t) : (T => U)"
  APP  "[| env |- s : T => U; env |- t : T |] ==> env |- (s $ t) : U"

consts
  "types" :: "[nat => typ, dB list, typ list] => bool"

primrec
  "types e [] Ts = (Ts = [])"
  "types e (t # ts) Ts = (case Ts of
      [] => False
    | T # Ts => e |- t : T & types e ts Ts)"

end
