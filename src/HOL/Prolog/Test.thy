(*  Title:    HOL/Prolog/Test.thy
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

section \<open>Basic examples\<close>

theory Test
imports HOHH
begin

typedecl nat

typedecl 'a list

consts
  Nil   :: "'a list"                                  (\<open>[]\<close>)
  Cons  :: "'a => 'a list => 'a list"                 (infixr \<open>#\<close>  65)

text \<open>List enumeration\<close>

syntax
  "_list" :: "args => 'a list"  (\<open>(\<open>indent=1 notation=\<open>mixfix list enumeration\<close>\<close>[_])\<close>)
syntax_consts
  "_list" \<rightleftharpoons> Cons
translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"

typedecl person

axiomatization
  append  :: "['a list, 'a list, 'a list]            => bool" and
  reverse :: "['a list, 'a list]                     => bool" and

  mappred :: "[('a => 'b => bool), 'a list, 'b list] => bool" and
  mapfun  :: "[('a => 'b), 'a list, 'b list]         => bool" and

  bob     :: person and
  sue     :: person and
  ned     :: person and

  nat23   :: nat          (\<open>23\<close>) and
  nat24   :: nat          (\<open>24\<close>) and
  nat25   :: nat          (\<open>25\<close>) and

  age     :: "[person, nat]                          => bool" and

  eq      :: "['a, 'a]                               => bool" and

  empty   :: "['b]                                   => bool" and
  add     :: "['a, 'b, 'b]                           => bool" and
  remove  :: "['a, 'b, 'b]                           => bool" and
  bag_appl:: "['a, 'a, 'a, 'a]                       => bool"
where
        append:  "\<And>x xs ys zs. append  []    xs  xs    ..
                  append (x#xs) ys (x#zs) :- append xs ys zs" and
        reverse: "\<And>L1 L2. reverse L1 L2 :- (\<forall>rev_aux.
                  (\<forall>L.          rev_aux  []    L  L )..
                  (\<forall>X L1 L2 L3. rev_aux (X#L1) L2 L3 :- rev_aux L1 L2 (X#L3))
                  => rev_aux L1 L2 [])" and

        mappred: "\<And>x xs y ys P. mappred P  []     []    ..
                  mappred P (x#xs) (y#ys) :- P x y  &  mappred P xs ys" and
        mapfun:  "\<And>x xs ys f. mapfun f  []     []      ..
                  mapfun f (x#xs) (f x#ys) :- mapfun f xs ys" and

        age:     "age bob 24 ..
                  age sue 23 ..
                  age ned 23" and

        eq:      "\<And>x. eq x x" and

(* actual definitions of empty and add is hidden -> yields abstract data type *)

        bag_appl: "\<And>A B X Y. bag_appl A B X Y:- (\<exists>S1 S2 S3 S4 S5.
                                empty    S1    &
                                add A    S1 S2 &
                                add B    S2 S3 &
                                remove X S3 S4 &
                                remove Y S4 S5 &
                                empty    S5)"

lemmas prog_Test = append reverse mappred mapfun age eq bag_appl

schematic_goal "append ?x ?y [a,b,c,d]"
  apply (prolog prog_Test)
  back
  back
  back
  back
  done

schematic_goal "append [a,b] y ?L"
  apply (prolog prog_Test)
  done

schematic_goal "\<forall>y. append [a,b] y (?L y)"
  apply (prolog prog_Test)
  done

schematic_goal "reverse [] ?L"
  apply (prolog prog_Test)
  done

schematic_goal "reverse [23] ?L"
  apply (prolog prog_Test)
  done

schematic_goal "reverse [23,24,?x] ?L"
  apply (prolog prog_Test)
  done

schematic_goal "reverse ?L [23,24,?x]"
  apply (prolog prog_Test)
  done

schematic_goal "mappred age ?x [23,24]"
  apply (prolog prog_Test)
  back
  done

schematic_goal "mappred (\<lambda>x y. \<exists>z. age z y) ?x [23,24]"
  apply (prolog prog_Test)
  done

schematic_goal "mappred ?P [bob,sue] [24,23]"
  apply (prolog prog_Test)
  done

schematic_goal "mapfun f [bob,bob,sue] [?x,?y,?z]"
  apply (prolog prog_Test)
  done

schematic_goal "mapfun (%x. h x 25) [bob,sue] ?L"
  apply (prolog prog_Test)
  done

schematic_goal "mapfun ?F [24,25] [h bob 24,h bob 25]"
  apply (prolog prog_Test)
  done

schematic_goal "mapfun ?F [24] [h 24 24]"
  apply (prolog prog_Test)
  back
  back
  back
  done

lemma "True"
  apply (prolog prog_Test)
  done

schematic_goal "age ?x 24 & age ?y 23"
  apply (prolog prog_Test)
  back
  done

schematic_goal "age ?x 24 | age ?x 23"
  apply (prolog prog_Test)
  back
  back
  done

lemma "\<exists>x y. age x y"
  apply (prolog prog_Test)
  done

lemma "\<forall>x y. append [] x x"
  apply (prolog prog_Test)
  done

schematic_goal "age sue 24 .. age bob 23 => age ?x ?y"
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

schematic_goal "(\<forall>x. age x 25 :- age x 23) => age ?x 25 & age ?y 25"
  apply (prolog prog_Test)
  back
  back
  back
  done

lemma "\<forall>x. \<exists>y. eq x y"
  apply (prolog prog_Test)
  done

schematic_goal "\<exists>P. P \<and> eq P ?x"
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

lemma "\<exists>P. eq P (True & True) \<and> P"
  apply (prolog prog_Test)
  done

lemma "\<exists>P. eq P (\<or>) \<and> P k True"
  apply (prolog prog_Test)
  done

lemma "\<exists>P. eq P (Q => True) \<and> P"
  apply (prolog prog_Test)
  done

(* P flexible: *)
lemma "(\<forall>P k l. P k l :- eq P Q) => Q a b"
  apply (prolog prog_Test)
  done
(*
loops:
lemma "(!P k l. P k l :- eq P (%x y. x | y)) => a | b"
*)

(* implication and disjunction in atom: *)
lemma "\<exists>Q. (\<forall>p q. R(q :- p) => R(Q p q)) \<and> Q (t | s) (s | t)"
  by fast

(* disjunction in atom: *)
lemma "(\<forall>P. g P :- (P => b \<or> a)) => g(a \<or> b)"
  apply (tactic "step_tac (put_claset HOL_cs \<^context>) 1")
  apply (tactic "step_tac (put_claset HOL_cs \<^context>) 1")
  apply (tactic "step_tac (put_claset HOL_cs \<^context>) 1")
   prefer 2
   apply fast
  apply fast
  done

(*
hangs:
lemma "(!P. g P :- (P => b | a)) => g(a | b)"
  by fast
*)

schematic_goal "\<forall>Emp Stk.(
                       empty    (Emp::'b) .. 
         (\<forall>(X::nat) S. add    X (S::'b)         (Stk X S)) .. 
         (\<forall>(X::nat) S. remove X ((Stk X S)::'b) S))
 => bag_appl 23 24 ?X ?Y"
  oops

schematic_goal "\<forall>Qu. ( 
          (\<forall>L.            empty    (Qu L L)) .. 
          (\<forall>(X::nat) L K. add    X (Qu L (X#K)) (Qu L K)) ..
          (\<forall>(X::nat) L K. remove X (Qu (X#L) K) (Qu L K)))
 => bag_appl 23 24 ?X ?Y"
  oops

lemma "D \<and> (\<forall>y. E) :- (\<forall>x. True \<and> True) :- True => D"
  apply (prolog prog_Test)
  done

schematic_goal "P x .. P y => P ?X"
  apply (prolog prog_Test)
  back
  done

end
