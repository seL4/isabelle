(*  Title:      HOLCF/IOA/meta_theory/Seq.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Partial, Finite and Infinite Sequences (lazy lists), modeled as domain.
*)  


Seq = HOLCF + 

domain 'a seq = nil | "##" (HD::'a) (lazy TL::'a seq)  (infixr 65) 


consts    
   sfilter       :: "('a -> tr) -> 'a seq -> 'a seq"  
   smap          :: "('a -> 'b) -> 'a seq -> 'b seq"
   sforall       :: "('a -> tr) => 'a seq => bool"
   sforall2      :: "('a -> tr) -> 'a seq -> tr"
   slast         :: "'a seq     -> 'a"
   sconc         :: "'a seq     -> 'a seq -> 'a seq"
   sdropwhile,
   stakewhile    ::"('a -> tr)  -> 'a seq -> 'a seq"  
   szip          ::"'a seq      -> 'b seq -> ('a*'b) seq"  
   sflat        :: "('a seq) seq  -> 'a seq"

   sfinite       :: "'a seq set"
   Partial       ::"'a seq => bool"
   Infinite      ::"'a seq => bool"

   nproj        :: "nat => 'a seq => 'a"
   sproj        :: "nat => 'a seq => 'a seq"

syntax
   "@@"		:: "'a seq => 'a seq => 'a seq"	(infixr 65)
   "Finite"     :: "'a seq => bool"

translations
   "xs @@ ys" == "sconc`xs`ys"
   "Finite x" == "x:sfinite"
   "~(Finite x)" =="x~:sfinite"

defs 



(* f not possible at lhs, as "pattern matching" only for % x arguments,
   f cannot be written at rhs in front, as fix_eq3 does not apply later *)
smap_def
  "smap == (fix`(LAM h f tr. case tr of 
      nil   => nil
    | x##xs => f`x ## h`f`xs))"

sfilter_def       
  "sfilter == (fix`(LAM h P t. case t of 
	   nil => nil
	 | x##xs => If P`x                                 
                    then x##(h`P`xs)
                    else     h`P`xs
                    fi))" 
sforall_def
  "sforall P t == (sforall2`P`t ~=FF)" 


sforall2_def
  "sforall2 == (fix`(LAM h P t. case t of 
	   nil => TT
	 | x##xs => P`x andalso h`P`xs))"
  
sconc_def
  "sconc == (fix`(LAM h t1 t2. case t1 of 
               nil       => t2
             | x##xs => x##(h`xs`t2)))"

slast_def
  "slast == (fix`(LAM h t. case t of 
	   nil => UU
	 | x##xs => (If is_nil`xs                              
                          then x
                         else h`xs fi)))"

stakewhile_def      
  "stakewhile == (fix`(LAM h P t. case t of 
	   nil => nil
	 | x##xs => If P`x                                 
                    then x##(h`P`xs)
                    else nil
                    fi))" 
sdropwhile_def
  "sdropwhile == (fix`(LAM h P t. case t of 
	   nil => nil
	 | x##xs => If P`x                                 
                    then h`P`xs
                    else t
                    fi))" 
sflat_def
  "sflat == (fix`(LAM h t. case t of 
	   nil => nil
	 | x##xs => x @@ (h`xs)))"

szip_def
  "szip == (fix`(LAM h t1 t2. case t1 of 
               nil   => nil
             | x##xs => (case t2 of 
                          nil => UU 
                        | y##ys => <x,y>##(h`xs`ys))))"
 

nproj_def 
 "nproj == (%n tr.HD`(iterate n TL tr))"   


sproj_def 
 "sproj == (%n tr.iterate n TL tr)"   



Partial_def
  "Partial x  == (seq_finite x) & ~(Finite x)"

Infinite_def
  "Infinite x == ~(seq_finite x)"


inductive "sfinite" 
   intrs  
    sfinite_0  "nil:sfinite"
    sfinite_n  "[|tr:sfinite;a~=UU|] ==> (a##tr) : sfinite"


end
