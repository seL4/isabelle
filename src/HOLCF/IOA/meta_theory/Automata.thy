(*  Title:      HOLCF/IOA/meta_theory/Automata.thy
    ID:        
    Author:     Olaf M"uller, Konrad Slind, Tobias Nipkow
    Copyright   1995, 1996  TU Muenchen

The I/O automata of Lynch and Tuttle in HOLCF.
*)   

		       
Automata = Option + Asig +  

default term
 
types
   ('a,'s)transition       =    "'s * 'a * 's"
   ('a,'s)ioa              =    "'a signature * 's set * ('a,'s)transition set"

consts
 
  (* IO automata *)
  state_trans::"['a signature, ('a,'s)transition set] => bool"
  asig_of    ::"('a,'s)ioa => 'a signature"
  starts_of  ::"('a,'s)ioa => 's set"
  trans_of   ::"('a,'s)ioa => ('a,'s)transition set"
  IOA	     ::"('a,'s)ioa => bool"

  (* reachability and invariants *)
  reachable     :: "('a,'s)ioa => 's set"
  invariant     :: "[('a,'s)ioa, 's=>bool] => bool"

  (* binary composition of action signatures and automata *)
  compat_asigs ::"['a signature, 'a signature] => bool"
  asig_comp    ::"['a signature, 'a signature] => 'a signature"
  compat_ioas  ::"[('a,'s)ioa, ('a,'t)ioa] => bool"
  "||"         ::"[('a,'s)ioa, ('a,'t)ioa] => ('a,'s*'t)ioa"  (infixr 10)

  (* hiding *)
  restrict_asig :: "['a signature, 'a set] => 'a signature"
  restrict      :: "[('a,'s)ioa, 'a set] => ('a,'s)ioa"

  (* renaming *)
  rename:: "('a, 'b)ioa => ('c => 'a option) => ('c,'b)ioa"


syntax 

  "_trans_of"  :: "'s => 'a => ('a,'s)ioa => 's => bool"  ("_ -_--_-> _" [81,81,81,81] 100)
  "reachable"  :: "[('a,'s)ioa, 's] => bool"
  "act"        :: "('a,'s)ioa => 'a set"
  "ext"        :: "('a,'s)ioa => 'a set"
  "int"        :: "('a,'s)ioa => 'a set"
  "inp"        :: "('a,'s)ioa => 'a set"
  "out"        :: "('a,'s)ioa => 'a set"


syntax (symbols)

  "_trans_of"  :: "'s => 'a => ('a,'s)ioa => 's => bool"  
                  ("_ \\<midarrow>_\\<midarrow>_\\<midarrow>\\<rightarrow> _" [81,81,81,81] 100)
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


defs

(* --------------------------------- IOA ---------------------------------*)

state_trans_def
  "state_trans asig R == 
    (!triple. triple:R --> fst(snd(triple)):actions(asig)) & 
    (!a. (a:inputs(asig)) --> (!s1. ? s2. (s1,a,s2):R))"


asig_of_def   "asig_of == fst"
starts_of_def "starts_of == (fst o snd)"
trans_of_def  "trans_of == (snd o snd)"

ioa_def
  "IOA(ioa) == (is_asig(asig_of(ioa))      &                            
                (~ starts_of(ioa) = {})    &                            
               state_trans (asig_of ioa) (trans_of ioa))"


invariant_def "invariant A P == (!s. reachable A s --> P(s))"


(* ------------------------- parallel composition --------------------------*)

compat_asigs_def
  "compat_asigs a1 a2 ==                                                
  (((outputs(a1) Int outputs(a2)) = {}) &                              
   ((internals(a1) Int actions(a2)) = {}) &                            
   ((internals(a2) Int actions(a1)) = {}))"


compat_ioas_def
  "compat_ioas ioa1 ioa2 == compat_asigs (asig_of(ioa1)) (asig_of(ioa2))"


asig_comp_def
  "asig_comp a1 a2 ==                                                   
     (((inputs(a1) Un inputs(a2)) - (outputs(a1) Un outputs(a2)),      
       (outputs(a1) Un outputs(a2)),                                   
       (internals(a1) Un internals(a2))))"


par_def
  "(ioa1 || ioa2) ==                                                    
      (asig_comp (asig_of ioa1) (asig_of ioa2),                        
       {pr. fst(pr):starts_of(ioa1) & snd(pr):starts_of(ioa2)},        
       {tr. let s = fst(tr); a = fst(snd(tr)); t = snd(snd(tr))        
            in (a:act ioa1 | a:act ioa2) & 
               (if a:act ioa1 then                       
                  (fst(s),a,fst(t)):trans_of(ioa1)                     
                else fst(t) = fst(s))                                  
               &                                                       
               (if a:act ioa2 then                       
                  (snd(s),a,snd(t)):trans_of(ioa2)                     
                else snd(t) = snd(s))})"

(* ------------------------ hiding -------------------------------------------- *)

restrict_asig_def
  "restrict_asig asig actns ==                                          
    (inputs(asig) Int actns, outputs(asig) Int actns,                  
     internals(asig) Un (externals(asig) - actns))"


restrict_def
  "restrict ioa actns ==                                               
    (restrict_asig (asig_of ioa) actns, starts_of(ioa), trans_of(ioa))"

(* ------------------------- renaming ------------------------------------------- *)
  
rename_def 
"rename ioa ren ==  
  (({b. ? x. Some(x)= ren(b) & x : inp ioa},         
    {b. ? x. Some(x)= ren(b) & x : out ioa},        
    {b. ? x. Some(x)= ren(b) & x : int ioa}),     
              starts_of(ioa)   ,                                            
   {tr. let s = fst(tr); a = fst(snd(tr));  t = snd(snd(tr))    
        in                                                      
        ? x. Some(x) = ren(a) & (s,x,t):trans_of(ioa)})"


end

