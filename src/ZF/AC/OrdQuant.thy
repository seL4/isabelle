(*  Title: 	ZF/AC/OrdQuant.thy
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

Quantifiers and union operator for ordinals. 
*)

OrdQuant = Ordinal +

consts
  
  (* Ordinal Quantifiers *)
  Oall, Oex   :: "[i, i => o] => o"
  (* General Union and Intersection *)
  OUnion      :: "[i, i => i] => i"
  
syntax
  
  "@OUNION"   :: "[idt, i, i] => i"        ("(3UN _<_./ _)" 10)
  "@Oall"     :: "[idt, i, o] => o"        ("(3ALL _<_./ _)" 10)
  "@Oex"      :: "[idt, i, o] => o"        ("(3EX _<_./ _)" 10)

translations
  
  "UN x<a. B"   == "OUnion(a, %x. B)"
  "ALL x<a. P"  == "Oall(a, %x. P)"
  "EX x<a. P"   == "Oex(a, %x. P)"

rules
  
  OUnion_iff     "A : OUnion(a, %z. B(z)) <-> (EX x<a. A: B(x))"

defs
  
  (* Ordinal Quantifiers *)
  Oall_def      "Oall(A, P) == ALL x. x<A --> P(x)"
  Oex_def       "Oex(A, P) == EX x. x<A & P(x)"

end
