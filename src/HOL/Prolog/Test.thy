(*  Title:    HOL/Prolog/Test.thy
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

header {* Basic examples *}

theory Test
imports HOHH
begin

typedecl nat

typedecl 'a list

consts
  Nil   :: "'a list"                                  ("[]")
  Cons  :: "'a => 'a list => 'a list"                 (infixr "#"  65)

syntax
  (* list Enumeration *)
  "_list"     :: "args => 'a list"                          ("[(_)]")

translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

typedecl person

consts
  append  :: "['a list, 'a list, 'a list]            => bool"
  reverse :: "['a list, 'a list]                     => bool"

  mappred :: "[('a => 'b => bool), 'a list, 'b list] => bool"
  mapfun  :: "[('a => 'b), 'a list, 'b list]         => bool"

  bob     :: person
  sue     :: person
  ned     :: person

  nat23   :: nat          ("23")
  nat24   :: nat          ("24")
  nat25   :: nat          ("25")

  age     :: "[person, nat]                          => bool"

  eq      :: "['a, 'a]                               => bool"

  empty   :: "['b]                                   => bool"
  add     :: "['a, 'b, 'b]                           => bool"
  remove  :: "['a, 'b, 'b]                           => bool"
  bag_appl:: "['a, 'a, 'a, 'a]                       => bool"

axioms
        append:  "append  []    xs  xs    ..
                  append (x#xs) ys (x#zs) :- append xs ys zs"
        reverse: "reverse L1 L2 :- (!rev_aux.
                  (!L.          rev_aux  []    L  L )..
                  (!X L1 L2 L3. rev_aux (X#L1) L2 L3 :- rev_aux L1 L2 (X#L3))
                  => rev_aux L1 L2 [])"

        mappred: "mappred P  []     []    ..
                  mappred P (x#xs) (y#ys) :- P x y  &  mappred P xs ys"
        mapfun:  "mapfun f  []     []      ..
                  mapfun f (x#xs) (f x#ys) :- mapfun f xs ys"

        age:     "age bob 24 ..
                  age sue 23 ..
                  age ned 23"

        eq:      "eq x x"

(* actual definitions of empty and add is hidden -> yields abstract data type *)

        bag_appl: "bag_appl A B X Y:- (? S1 S2 S3 S4 S5.
                                empty    S1    &
                                add A    S1 S2 &
                                add B    S2 S3 &
                                remove X S3 S4 &
                                remove Y S4 S5 &
                                empty    S5)"

lemmas prog_Test = append reverse mappred mapfun age eq bag_appl

schematic_lemma "append ?x ?y [a,b,c,d]"
  apply (prolog prog_Test)
  back
  back
  back
  back
  done

schematic_lemma "append [a,b] y ?L"
  apply (prolog prog_Test)
  done

schematic_lemma "!y. append [a,b] y (?L y)"
  apply (prolog prog_Test)
  done

schematic_lemma "reverse [] ?L"
  apply (prolog prog_Test)
  done

schematic_lemma "reverse [23] ?L"
  apply (prolog prog_Test)
  done

schematic_lemma "reverse [23,24,?x] ?L"
  apply (prolog prog_Test)
  done

schematic_lemma "reverse ?L [23,24,?x]"
  apply (prolog prog_Test)
  done

schematic_lemma "mappred age ?x [23,24]"
  apply (prolog prog_Test)
  back
  done

schematic_lemma "mappred (%x y. ? z. age z y) ?x [23,24]"
  apply (prolog prog_Test)
  done

schematic_lemma "mappred ?P [bob,sue] [24,23]"
  apply (prolog prog_Test)
  done

schematic_lemma "mapfun f [bob,bob,sue] [?x,?y,?z]"
  apply (prolog prog_Test)
  done

schematic_lemma "mapfun (%x. h x 25) [bob,sue] ?L"
  apply (prolog prog_Test)
  done

schematic_lemma "mapfun ?F [24,25] [h bob 24,h bob 25]"
  apply (prolog prog_Test)
  done

schematic_lemma "mapfun ?F [24] [h 24 24]"
  apply (prolog prog_Test)
  back
  back
  back
  done

lemma "True"
  apply (prolog prog_Test)
  done

schematic_lemma "age ?x 24 & age ?y 23"
  apply (prolog prog_Test)
  back
  done

schematic_lemma "age ?x 24 | age ?x 23"
  apply (prolog prog_Test)
  back
  back
  done

lemma "? x y. age x y"
  apply (prolog prog_Test)
  done

lemma "!x y. append [] x x"
  apply (prolog prog_Test)
  done

schematic_lemma "age sue 24 .. age bob 23 => age ?x ?y"
  apply (prolog prog_Test)
  back
  back
  back
  back
  done

(*set trace_DEPTH_FIRST;*)
lemma "age bob 25 :- age bob 24 => age bob 25"
  apply (prolog prog_Test)
  done
(*reset trace_DEPTH_FIRST;*)

schematic_lemma "(!x. age x 25 :- age x 23) => age ?x 25 & age ?y 25"
  apply (prolog prog_Test)
  back
  back
  back
  done

lemma "!x. ? y. eq x y"
  apply (prolog prog_Test)
  done

schematic_lemma "? P. P & eq P ?x"
  apply (prolog prog_Test)
(*
  back
  back
  back
  back
  back
  back
  back
  back
*)
  done

lemma "? P. eq P (True & True) & P"
  apply (prolog prog_Test)
  done

lemma "? P. eq P op | & P k True"
  apply (prolog prog_Test)
  done

lemma "? P. eq P (Q => True) & P"
  apply (prolog prog_Test)
  done

(* P flexible: *)
lemma "(!P k l. P k l :- eq P Q) => Q a b"
  apply (prolog prog_Test)
  done
(*
loops:
lemma "(!P k l. P k l :- eq P (%x y. x | y)) => a | b"
*)

(* implication and disjunction in atom: *)
lemma "? Q. (!p q. R(q :- p) => R(Q p q)) & Q (t | s) (s | t)"
  by fast

(* disjunction in atom: *)
lemma "(!P. g P :- (P => b | a)) => g(a | b)"
  apply (tactic "step_tac (put_claset HOL_cs @{context}) 1")
  apply (tactic "step_tac (put_claset HOL_cs @{context}) 1")
  apply (tactic "step_tac (put_claset HOL_cs @{context}) 1")
   prefer 2
   apply fast
  apply fast
  done

(*
hangs:
lemma "(!P. g P :- (P => b | a)) => g(a | b)"
  by fast
*)

schematic_lemma "!Emp Stk.(
                       empty    (Emp::'b) .. 
         (!(X::nat) S. add    X (S::'b)         (Stk X S)) .. 
         (!(X::nat) S. remove X ((Stk X S)::'b) S))
 => bag_appl 23 24 ?X ?Y"
  oops

schematic_lemma "!Qu. ( 
          (!L.            empty    (Qu L L)) .. 
          (!(X::nat) L K. add    X (Qu L (X#K)) (Qu L K)) ..
          (!(X::nat) L K. remove X (Qu (X#L) K) (Qu L K)))
 => bag_appl 23 24 ?X ?Y"
  oops

lemma "D & (!y. E) :- (!x. True & True) :- True => D"
  apply (prolog prog_Test)
  done

schematic_lemma "P x .. P y => P ?X"
  apply (prolog prog_Test)
  back
  done

end
