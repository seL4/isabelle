(*  Title:      ZF/Update.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Function updates: like theory Map, but for ordinary functions
*)

theory Update = func:

constdefs
  update  :: "[i,i,i] => i"
   "update(f,a,b) == lam x: cons(a, domain(f)). if(x=a, b, f`x)"

nonterminals
  updbinds  updbind

syntax

  (* Let expressions *)

  "_updbind"    :: "[i, i] => updbind"               ("(2_ :=/ _)")
  ""            :: "updbind => updbinds"             ("_")
  "_updbinds"   :: "[updbind, updbinds] => updbinds" ("_,/ _")
  "_Update"     :: "[i, updbinds] => i"              ("_/'((_)')" [900,0] 900)

translations
  "_Update (f, _updbinds(b,bs))"  == "_Update (_Update(f,b), bs)"
  "f(x:=y)"                       == "update(f,x,y)"


lemma update_apply [simp]: "f(x:=y) ` z = (if z=x then y else f`z)"
apply (simp add: update_def)
apply (rule_tac P="z \<in> domain(f)" in case_split_thm)   
apply (simp_all add: apply_0)
done

lemma update_idem: "[| f`x = y;  f: Pi(A,B);  x: A |] ==> f(x:=y) = f"
apply (unfold update_def)
apply (simp add: domain_of_fun cons_absorb)
apply (rule fun_extension)
apply (best intro: apply_type if_type lam_type, assumption, simp)
done


(* [| f: Pi(A, B); x:A |] ==> f(x := f`x) = f *)
declare refl [THEN update_idem, simp]

lemma domain_update [simp]: "domain(f(x:=y)) = cons(x, domain(f))"
by (unfold update_def, simp)

lemma update_type: "[| f: A -> B;  x : A;  y: B |] ==> f(x:=y) : A -> B"
apply (unfold update_def)
apply (simp add: domain_of_fun cons_absorb apply_funtype lam_type)
done

ML
{*
val update_def = thm "update_def";
val update_apply = thm "update_apply";
val update_idem = thm "update_idem";
val domain_update = thm "domain_update";
val update_type = thm "update_type";
*}


end
