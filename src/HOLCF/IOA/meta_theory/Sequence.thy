(*  Title:      HOLCF/IOA/meta_theory/Sequence.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Sequences over flat domains with lifted elements

*)  

Sequence = Seq + 

default term

types 'a Seq = ('a::term lift)seq

consts

  Consq            ::"'a            => 'a Seq -> 'a Seq"
  Filter           ::"('a => bool)  => 'a Seq -> 'a Seq"
  Map              ::"('a => 'b)    => 'a Seq -> 'b Seq"
  Forall           ::"('a => bool)  => 'a Seq => bool"
  Last             ::"'a Seq        -> 'a lift"
  Dropwhile,
  Takewhile        ::"('a => bool)  => 'a Seq -> 'a Seq" 
  Zip              ::"'a Seq        -> 'b Seq -> ('a * 'b) Seq"
  Flat             ::"('a Seq) seq   -> 'a Seq"

  Filter2          ::"('a => bool)  => 'a Seq -> 'a Seq"

syntax

 "@Consq"         ::"'a => 'a Seq => 'a Seq"       ("(_/>>_)"  [66,65] 65)
 (* list Enumeration *)
  "_totlist"      :: args => 'a Seq                          ("[(_)!]")
  "_partlist"     :: args => 'a Seq                          ("[(_)?]")


syntax (symbols)

 "@Consq"     ::"'a => 'a Seq => 'a Seq"       ("(_\\<leadsto>_)"  [66,65] 65)
 

translations

  "a>>s"         == "Consq a$s"
  "[x, xs!]"     == "x>>[xs!]"
  "[x!]"         == "x>>nil"
  "[x, xs?]"     == "x>>[xs?]"
  "[x?]"         == "x>>UU" 

defs


Consq_def     "Consq a == LAM s. Def a ## s"

Filter_def    "Filter P == sfilter$(flift2 P)"

Map_def       "Map f  == smap$(flift2 f)"

Forall_def    "Forall P == sforall (flift2 P)"

Last_def      "Last == slast"

Dropwhile_def "Dropwhile P == sdropwhile$(flift2 P)"

Takewhile_def "Takewhile P == stakewhile$(flift2 P)"

Flat_def      "Flat == sflat"

Zip_def
  "Zip == (fix$(LAM h t1 t2. case t1 of 
               nil   => nil
             | x##xs => (case t2 of 
                          nil => UU 
                        | y##ys => (case x of 
                                      UU  => UU
                                    | Def a => (case y of 
                                                  UU => UU
                                                | Def b => Def (a,b)##(h$xs$ys))))))"

Filter2_def    "Filter2 P == (fix$(LAM h t. case t of 
            nil => nil
	  | x##xs => (case x of UU => UU | Def y => (if P y                                 
                     then x##(h$xs)
                     else     h$xs))))" 

rules


(* for test purposes should be deleted FIX !! *)
adm_all    "adm f"


end