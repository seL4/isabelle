(*  Title:      ZF/AC/OrdQuant.thy
    ID:         $Id$
    Authors:    Krzysztof Grabczewski and L C Paulson

Quantifiers and union operator for ordinals. 
*)

OrdQuant = Ordinal +

consts
  
  (* Ordinal Quantifiers *)
  oall, oex   :: [i, i => o] => o

  (* Ordinal Union *)
  OUnion      :: [i, i => i] => i
  
syntax
  "@oall"     :: [idt, i, o] => o        ("(3ALL _<_./ _)" 10)
  "@oex"      :: [idt, i, o] => o        ("(3EX _<_./ _)" 10)
  "@OUNION"   :: [idt, i, i] => i        ("(3UN _<_./ _)" 10)

translations
  "ALL x<a. P"  == "oall(a, %x. P)"
  "EX x<a. P"   == "oex(a, %x. P)"
  "UN x<a. B"   == "OUnion(a, %x. B)"

syntax (xsymbols)
  "@oall"     :: [idt, i, o] => o        ("(3\\<forall>_<_./ _)" 10)
  "@oex"      :: [idt, i, o] => o        ("(3\\<exists>_<_./ _)" 10)
  "@OUNION"   :: [idt, i, i] => i        ("(3\\<Union>_<_./ _)" 10)

defs
  
  (* Ordinal Quantifiers *)
  oall_def      "oall(A, P) == ALL x. x<A --> P(x)"
  oex_def       "oex(A, P) == EX x. x<A & P(x)"

  OUnion_def     "OUnion(i,B) == {z: UN x:i. B(x). Ord(i)}"
  
end
