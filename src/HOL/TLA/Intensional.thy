(* 
    File:	 TLA/Intensional.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: Intensional
    Logic Image: HOL

Define a framework for "intensional" (possible-world based) logics
on top of HOL, with lifting of constants and functions.
*)

Intensional  =  Prod +

classes
    world < logic    (* Type class of "possible worlds". Concrete types
                        will be provided by children theories. *)

types
    ('a,'w) term = "'w => 'a"    (* Intention: 'w::world *)
    'w form = "'w => bool"

consts
  TrueInt  :: "('w::world form) => prop"             ("(_)" 5)

  (* Holds at *)
  holdsAt  :: "['w::world, 'w form] => bool"   ("(_ |= _)" [100,9] 8)

  (* Lifting base functions to "intensional" level *)
  con      :: "'a => ('w::world => 'a)"               ("(#_)" [100] 99)
  lift     :: "['a => 'b, 'w::world => 'a] => ('w => 'b)"  ("(_[_])")
  lift2    :: "['a => ('b => 'c), 'w::world => 'a, 'w => 'b] => ('w => 'c)" ("(_[_,/ _])")
  lift3    :: "['a => 'b => 'c => 'd, 'w::world => 'a, 'w => 'b, 'w => 'c] => ('w => 'd)" ("(_[_,/ _,/ _])")

  (* Lifted infix functions *)
  IntEqu   :: "['w::world => 'a, 'w => 'a] => 'w form"  ("(_ .=/ _)" [50,51] 50)
  IntNeq   :: "['w::world => 'a, 'w => 'a] => 'w form"  ("(_ .~=/ _)" [50,51] 50)
  NotInt   :: "('w::world) form => 'w form"               ("(.~ _)" [40] 40)
  AndInt   :: "[('w::world) form, 'w form] => 'w form"    ("(_ .&/ _)" [36,35] 35)
  OrInt    :: "[('w::world) form, 'w form] => 'w form"    ("(_ .|/ _)" [31,30] 30)
  ImpInt   :: "[('w::world) form, 'w form] => 'w form"    ("(_ .->/ _)" [26,25] 25)
  IfInt    :: "[('w::world) form, ('a,'w) term, ('a,'w) term] => ('a,'w) term" ("(.if (_)/ .then (_)/ .else (_))" 10)
  PlusInt  :: "[('w::world) => ('a::plus), 'w => 'a] => ('w => 'a)"  ("(_ .+/ _)" [66,65] 65)
  MinusInt :: "[('w::world) => ('a::minus), 'w => 'a] => ('w => 'a)"  ("(_ .-/ _)" [66,65] 65)
  TimesInt :: "[('w::world) => ('a::times), 'w => 'a] => ('w => 'a)"  ("(_ .*/ _)" [71,70] 70)

  LessInt  :: "['w::world => 'a::ord, 'w => 'a] => 'w form"        ("(_/ .< _)"  [50, 51] 50)
  LeqInt   :: "['w::world => 'a::ord, 'w => 'a] => 'w form"        ("(_/ .<= _)" [50, 51] 50)

  (* lifted set membership *)
  memInt   :: "[('a,'w::world) term, ('a set,'w) term] => 'w form"  ("(_/ .: _)" [50, 51] 50)

  (* "Rigid" quantification *)
  RAll     :: "('a => 'w::world form) => 'w form"     (binder "RALL " 10)
  REx      :: "('a => 'w::world form) => 'w form"     (binder "REX " 10)

syntax
  "@tupleInt"    :: "args => ('a * 'b, 'w) term"  ("(1{[_]})")

translations

  "{[x,y,z]}"   == "{[x, {[y,z]} ]}"
  "{[x,y]}"     == "Pair [x, y]"
  "{[x]}"       => "x"

  "u .= v" == "op =[u,v]"
  "u .~= v" == ".~(u .= v)"
  ".~ A"   == "Not[A]"
  "A .& B" == "op &[A,B]"
  "A .| B"  == "op |[A,B]"
  "A .-> B" == "op -->[A,B]"
  ".if A .then u .else v" == "If[A,u,v]"
  "u .+ v"  == "op +[u,v]"
  "u .- v" == "op -[u,v]"
  "u .* v" == "op *[u,v]"

  "a .< b"  == "op < [a,b]"
  "a .<= b" == "op <= [a,b]"
  "a .: A"  == "op :[a,A]"

  "holdsAt w (lift f x)"      == "lift f x w"
  "holdsAt w (lift2 f x y)"   == "lift2 f x y w"
  "holdsAt w (lift3 f x y z)" == "lift3 f x y z w"

  "w |= A"              => "A(w)"

rules
  inteq_reflection   "(x .= y) ==> (x == y)"

  int_valid   "TrueInt(A) == (!! w. w |= A)"

  unl_con     "(#c) w == c"             (* constants *)
  unl_lift    "(f[x]) w == f(x w)"
  unl_lift2   "(f[x,y]) w == f (x w) (y w)"
  unl_lift3   "(f[x, y, z]) w == f (x w) (y w) (z w)"

  unl_Rall    "(RALL x. A(x)) w == ALL x. (w |= A(x))"
  unl_Rex     "(REX x. A(x)) w == EX x. (w |= A(x))"
end

ML
