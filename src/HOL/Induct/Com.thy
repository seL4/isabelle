(*  Title:      HOL/Induct/Com
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Example of Mutual Induction via Iteratived Inductive Definitions: Commands
*)

Com = Arith +

types loc
      state = "loc => nat"
      n2n2n = "nat => nat => nat"

arities loc :: term

(*To avoid a mutually recursive datatype declaration, expressions and commands
  are combined to form a single datatype.*)
datatype
  exp = N nat
      | X loc
      | Op n2n2n exp exp
      | valOf exp exp          ("VALOF _ RESULTIS _"  60)
      | SKIP
      | ":="  loc exp          (infixl  60)
      | Semi  exp exp          ("_;;_"  [60, 60] 60)
      | Cond  exp exp exp      ("IF _ THEN _ ELSE _"  60)
      | While exp exp          ("WHILE _ DO _"  60)

(** Execution of commands **)
consts  exec    :: "((exp*state) * (nat*state)) set => ((exp*state)*state)set"
       "@exec"  :: "((exp*state) * (nat*state)) set => 
                    [exp*state,state] => bool"     ("_/ -[_]-> _" [50,0,50] 50)

translations  "csig -[eval]-> s" == "(csig,s) : exec eval"

syntax  eval'   :: "[exp*state,nat*state] => 
		    ((exp*state) * (nat*state)) set => bool"
						   ("_/ -|[_]-> _" [50,0,50] 50)
translations
    "esig -|[eval]-> ns" => "(esig,ns) : eval"

constdefs assign :: [state,nat,loc] => state    ("_[_'/_]" [95,0,0] 95)
  "s[m/x] ==  (%y. if y=x then m else s y)"


(*Command execution.  Natural numbers represent Booleans: 0=True, 1=False*)
inductive "exec eval"
  intrs
    Skip    "(SKIP,s) -[eval]-> s"

    Assign  "(e,s) -|[eval]-> (v,s') ==> (x := e, s) -[eval]-> s'[v/x]"

    Semi    "[| (c0,s) -[eval]-> s2; (c1,s2) -[eval]-> s1 |] 
            ==> (c0 ;; c1, s) -[eval]-> s1"

    IfTrue "[| (e,s) -|[eval]-> (0,s');  (c0,s') -[eval]-> s1 |] 
            ==> (IF e THEN c0 ELSE c1, s) -[eval]-> s1"

    IfFalse "[| (e,s) -|[eval]->  (1,s');  (c1,s') -[eval]-> s1 |] 
             ==> (IF e THEN c0 ELSE c1, s) -[eval]-> s1"

    WhileFalse "(e,s) -|[eval]-> (1,s1) ==> (WHILE e DO c, s) -[eval]-> s1"

    WhileTrue  "[| (e,s) -|[eval]-> (0,s1);
                (c,s1) -[eval]-> s2;  (WHILE e DO c, s2) -[eval]-> s3 |] 
                ==> (WHILE e DO c, s) -[eval]-> s3"

constdefs
    Unique   :: "['a, 'b, ('a*'b) set] => bool"
    "Unique x y r == ALL y'. (x,y'): r --> y = y'"

    Function :: "('a*'b) set => bool"
    "Function r == ALL x y. (x,y): r --> Unique x y r"
end
