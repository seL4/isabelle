(*  Title:      HOLCF/IOA/meta_theory/Automata.thy
    ID:         $Id$
    Author:     Olaf Müller, Konrad Slind, Tobias Nipkow

The I/O automata of Lynch and Tuttle in HOLCF.
*)   

		       
Automata = Asig +

default type
 
types
   ('a,'s)transition       =    "'s * 'a * 's"
   ('a,'s)ioa              =    "'a signature * 's set * ('a,'s)transition set * 
                                 (('a set) set) * (('a set) set)"

consts
 
  (* IO automata *)

  asig_of        ::"('a,'s)ioa => 'a signature"
  starts_of      ::"('a,'s)ioa => 's set"
  trans_of       ::"('a,'s)ioa => ('a,'s)transition set"
  wfair_of       ::"('a,'s)ioa => ('a set) set"
  sfair_of       ::"('a,'s)ioa => ('a set) set"

  is_asig_of     ::"('a,'s)ioa => bool"
  is_starts_of	 ::"('a,'s)ioa => bool"
  is_trans_of	 ::"('a,'s)ioa => bool"
  input_enabled	 ::"('a,'s)ioa => bool"
  IOA	         ::"('a,'s)ioa => bool"

  (* constraints for fair IOA *)

  fairIOA        ::"('a,'s)ioa => bool"
  input_resistant::"('a,'s)ioa => bool"

  (* enabledness of actions and action sets *)

  enabled        ::"('a,'s)ioa => 'a => 's => bool"
  Enabled    ::"('a,'s)ioa => 'a set => 's => bool"

  (* action set keeps enabled until probably disabled by itself *) 

  en_persistent  :: "('a,'s)ioa => 'a set => bool"

 (* post_conditions for actions and action sets *)

  was_enabled        ::"('a,'s)ioa => 'a => 's => bool"
  set_was_enabled    ::"('a,'s)ioa => 'a set => 's => bool"

  (* reachability and invariants *)
  reachable     :: "('a,'s)ioa => 's set"
  invariant     :: "[('a,'s)ioa, 's=>bool] => bool"

  (* binary composition of action signatures and automata *)
  asig_comp    ::"['a signature, 'a signature] => 'a signature"
  compatible   ::"[('a,'s)ioa, ('a,'t)ioa] => bool"
  "||"         ::"[('a,'s)ioa, ('a,'t)ioa] => ('a,'s*'t)ioa"  (infixr 10)

  (* hiding and restricting *)
  hide_asig     :: "['a signature, 'a set] => 'a signature"
  hide          :: "[('a,'s)ioa, 'a set] => ('a,'s)ioa"
  restrict_asig :: "['a signature, 'a set] => 'a signature"
  restrict      :: "[('a,'s)ioa, 'a set] => ('a,'s)ioa"

  (* renaming *)
  rename_set    :: "'a set => ('c => 'a option) => 'c set"
  rename        :: "('a, 'b)ioa => ('c => 'a option) => ('c,'b)ioa"


syntax 

  "_trans_of"  :: "'s => 'a => ('a,'s)ioa => 's => bool"  ("_ -_--_-> _" [81,81,81,81] 100)
  "reachable"  :: "[('a,'s)ioa, 's] => bool"
  "act"        :: "('a,'s)ioa => 'a set"
  "ext"        :: "('a,'s)ioa => 'a set"
  "int"        :: "('a,'s)ioa => 'a set"
  "inp"        :: "('a,'s)ioa => 'a set"
  "out"        :: "('a,'s)ioa => 'a set"
  "local"      :: "('a,'s)ioa => 'a set"


syntax (xsymbols)

  "_trans_of"  :: "'s => 'a => ('a,'s)ioa => 's => bool"  
                  ("_ \\<midarrow>_\\<midarrow>_\\<longrightarrow> _" [81,81,81,81] 100)
  "op ||"         ::"[('a,'s)ioa, ('a,'t)ioa] => ('a,'s*'t)ioa"  (infixr "\\<parallel>" 10)


inductive "reachable C" 
   intrs  
    reachable_0  "s:(starts_of C) ==> s : reachable C"
    reachable_n  "[|s:reachable C; (s,a,t):trans_of C|] ==> t:reachable C"


translations
  "s -a--A-> t"   == "(s,a,t):trans_of A"
  "reachable A s" == "s:reachable A"
  "act A"         == "actions (asig_of A)"
  "ext A"         == "externals (asig_of A)"
  "int A"         == "internals (asig_of A)"
  "inp A"         == "inputs (asig_of A)"
  "out A"         == "outputs (asig_of A)"
  "local A"       == "locals (asig_of A)"



defs

(* --------------------------------- IOA ---------------------------------*)



asig_of_def   "asig_of == fst"
starts_of_def "starts_of == (fst o snd)"
trans_of_def  "trans_of == (fst o snd o snd)"
wfair_of_def  "wfair_of == (fst o snd o snd o snd)"
sfair_of_def  "sfair_of == (snd o snd o snd o snd)"

is_asig_of_def
  "is_asig_of A == is_asig (asig_of A)" 

is_starts_of_def 
  "is_starts_of A ==  (~ starts_of A = {})"

is_trans_of_def
  "is_trans_of A == 
    (!triple. triple:(trans_of A) --> fst(snd(triple)):actions(asig_of A))"

input_enabled_def
  "input_enabled A ==
    (!a. (a:inputs(asig_of A)) --> (!s1. ? s2. (s1,a,s2):(trans_of A)))" 


ioa_def
  "IOA A == (is_asig_of A    &                            
             is_starts_of A  &                            
             is_trans_of A   &
             input_enabled A)"


invariant_def "invariant A P == (!s. reachable A s --> P(s))"


(* ------------------------- parallel composition --------------------------*)


compatible_def
  "compatible A B ==  
  (((out A Int out B) = {}) &                              
   ((int A Int act B) = {}) &                            
   ((int B Int act A) = {}))"

asig_comp_def
  "asig_comp a1 a2 ==                                                   
     (((inputs(a1) Un inputs(a2)) - (outputs(a1) Un outputs(a2)),      
       (outputs(a1) Un outputs(a2)),                                   
       (internals(a1) Un internals(a2))))"

par_def
  "(A || B) ==                                                    
      (asig_comp (asig_of A) (asig_of B),                        
       {pr. fst(pr):starts_of(A) & snd(pr):starts_of(B)},        
       {tr. let s = fst(tr); a = fst(snd(tr)); t = snd(snd(tr))        
            in (a:act A | a:act B) & 
               (if a:act A then                       
                  (fst(s),a,fst(t)):trans_of(A)                     
                else fst(t) = fst(s))                                  
               &                                                       
               (if a:act B then                       
                  (snd(s),a,snd(t)):trans_of(B)                     
                else snd(t) = snd(s))},
        wfair_of A Un wfair_of B,
        sfair_of A Un sfair_of B)"


(* ------------------------ hiding -------------------------------------------- *)

restrict_asig_def
  "restrict_asig asig actns ==                                          
    (inputs(asig) Int actns, 
     outputs(asig) Int actns,                  
     internals(asig) Un (externals(asig) - actns))"

(* Notice that for wfair_of and sfair_of nothing has to be changed, as 
   changes from the outputs to the internals does not touch the locals as 
   a whole, which is of importance for fairness only *)

restrict_def
  "restrict A actns ==                                               
    (restrict_asig (asig_of A) actns, 
     starts_of A, 
     trans_of A,
     wfair_of A,
     sfair_of A)"

hide_asig_def
  "hide_asig asig actns ==                                          
    (inputs(asig) - actns, 
     outputs(asig) - actns,                  
     internals(asig) Un actns)"

hide_def
  "hide A actns ==                                               
    (hide_asig (asig_of A) actns, 
     starts_of A, 
     trans_of A,
     wfair_of A,
     sfair_of A)"

(* ------------------------- renaming ------------------------------------------- *)
  
rename_set_def
  "rename_set A ren == {b. ? x. Some x = ren b & x : A}" 

rename_def 
"rename ioa ren ==  
  ((rename_set (inp ioa) ren,         
    rename_set (out ioa) ren,        
    rename_set (int ioa) ren),     
   starts_of ioa,                                            
   {tr. let s = fst(tr); a = fst(snd(tr));  t = snd(snd(tr))    
        in                                                      
        ? x. Some(x) = ren(a) & (s,x,t):trans_of ioa},
   {rename_set s ren | s. s: wfair_of ioa},
   {rename_set s ren | s. s: sfair_of ioa})"

(* ------------------------- fairness ----------------------------- *)

fairIOA_def
  "fairIOA A == (! S : wfair_of A. S<= local A) & 
                (! S : sfair_of A. S<= local A)"

input_resistant_def
  "input_resistant A == ! W : sfair_of A. ! s a t. 
                        reachable A s & reachable A t & a:inp A &
                        Enabled A W s & s -a--A-> t
                        --> Enabled A W t"

enabled_def
  "enabled A a s == ? t. s-a--A-> t"

Enabled_def
  "Enabled A W s == ? w:W. enabled A w s"

en_persistent_def
  "en_persistent A W == ! s a t. Enabled A W s & 
                                 a ~:W & 
                                 s -a--A-> t 
                                 --> Enabled A W t"
was_enabled_def
  "was_enabled A a t == ? s. s-a--A-> t"

set_was_enabled_def
  "set_was_enabled A W t == ? w:W. was_enabled A w t"


end

