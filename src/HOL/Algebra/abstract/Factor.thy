(*
    Factorisation within a factorial domain
    $Id$
    Author: Clemens Ballarin, started 25 November 1997
*)

theory Factor imports Ring2 begin

definition
  Factorisation :: "['a::ring, 'a list, 'a] => bool" where
  (* factorisation of x into a list of irred factors and a unit u *)
  "Factorisation x factors u \<longleftrightarrow>
     x = foldr op* factors u &
     (ALL a : set factors. irred a) & u dvd 1"

lemma irred_dvd_lemma: "!! c::'a::factorial.
   [| irred c; irred a; irred b; c dvd a*b |] ==> c assoc a | c assoc b"
  apply (unfold assoc_def)
  apply (frule factorial_prime)
  apply (unfold irred_def prime_def)
  apply blast
  done

lemma irred_dvd_list_lemma: "!! c::'a::factorial.
   [| irred c; a dvd 1 |] ==>  
   (ALL b : set factors. irred b) & c dvd foldr op* factors a -->  
   (EX d. c assoc d & d : set factors)"
  apply (unfold assoc_def)
  apply (induct_tac factors)
  (* Base case: c dvd a contradicts irred c *)
   apply (simp add: irred_def)
   apply (blast intro: dvd_trans_ring)
  (* Induction step *)
  apply (frule factorial_prime)
  apply (simp add: irred_def prime_def)
  apply blast
  done

lemma irred_dvd_list: "!! c::'a::factorial.  
   [| irred c; ALL b : set factors. irred b; a dvd 1;  
     c dvd foldr op* factors a |] ==>  
   EX d. c assoc d & d : set factors"
  apply (rule irred_dvd_list_lemma [THEN mp])
    apply auto
  done

lemma Factorisation_dvd: "!! c::'a::factorial.  
   [| irred c; Factorisation x factors u; c dvd x |] ==>  
   EX d. c assoc d & d : set factors"
  apply (unfold Factorisation_def)
  apply (rule irred_dvd_list_lemma [THEN mp])
    apply auto
  done

lemma Factorisation_irred: "!! c::'a::factorial.
    [| Factorisation x factors u; a : set factors |] ==> irred a"
  unfolding Factorisation_def by blast

end
