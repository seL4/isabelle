(*  Title:      SubUnion.thy
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

SubUnion = Redex +

consts
  Ssub,Scomp,Sreg  :: i
  "<==","~"        :: [i,i]=>o (infixl 70)
  un               :: [i,i]=>i (infixl 70)
  regular          :: i=>o
  
translations
  "a<==b"        == "<a,b>:Ssub"
  "a ~ b"        == "<a,b>:Scomp"
  "regular(a)"   == "a:Sreg"

inductive
  domains       "Ssub" <= "redexes*redexes"
  intrs
    Sub_Var     "n:nat ==> Var(n)<== Var(n)"
    Sub_Fun     "[|u<== v|]==> Fun(u)<== Fun(v)"
    Sub_App1    "[|u1<== v1; u2<== v2; b:bool|]==>   
                     App(0,u1,u2)<== App(b,v1,v2)"
    Sub_App2    "[|u1<== v1; u2<== v2|]==>   
                     App(1,u1,u2)<== App(1,v1,v2)"
  type_intrs    "redexes.intrs@bool_typechecks"

inductive
  domains       "Scomp" <= "redexes*redexes"
  intrs
    Comp_Var    "n:nat ==> Var(n) ~ Var(n)"
    Comp_Fun    "[|u ~ v|]==> Fun(u) ~ Fun(v)"
    Comp_App    "[|u1 ~ v1; u2 ~ v2; b1:bool; b2:bool|]==>   
                     App(b1,u1,u2) ~ App(b2,v1,v2)"
  type_intrs    "redexes.intrs@bool_typechecks"

inductive
  domains       "Sreg" <= "redexes"
  intrs
    Reg_Var     "n:nat ==> regular(Var(n))"
    Reg_Fun     "[|regular(u)|]==> regular(Fun(u))"
    Reg_App1    "[|regular(Fun(u)); regular(v) 
                     |]==>regular(App(1,Fun(u),v))"
    Reg_App2    "[|regular(u); regular(v) 
                     |]==>regular(App(0,u,v))"
  type_intrs    "redexes.intrs@bool_typechecks"

defs
  union_def  "u un v == redex_rec(u,   
         %i.lam t:redexes.redexes_case(%j.Var(i), %x.0, %b x y.0, t),   
      %x m.lam t:redexes.redexes_case(%j.0, %y.Fun(m`y), %b y z.0, t),   
%b x y m p.lam t:redexes.redexes_case(%j.0, %y.0,   
                                       %c z u. App(b or c, m`z, p`u), t))`v"
end

