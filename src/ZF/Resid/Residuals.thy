(*  Title: 	Residuals.thy
    ID:         $Id$
    Author: 	Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF

*)

Residuals = Substitution+

consts
  Sres		:: "i"
  residuals	:: "[i,i,i]=>i"
  "|>"		:: "[i,i]=>i"     (infixl 70)
  
translations
  "residuals(u,v,w)"  == "<u,v,w>:Sres"

inductive
  domains       "Sres" <= "redexes*redexes*redexes"
  intrs
    Res_Var	"n:nat ==> residuals(Var(n),Var(n),Var(n))"
    Res_Fun	"[|residuals(u,v,w)|]==>   \
\		     residuals(Fun(u),Fun(v),Fun(w))"
    Res_App	"[|residuals(u1,v1,w1);   \
\		   residuals(u2,v2,w2); b:bool|]==>   \
\		 residuals(App(b,u1,u2),App(0,v1,v2),App(b,w1,w2))"
    Res_redex	"[|residuals(u1,v1,w1);   \
\		   residuals(u2,v2,w2); b:bool|]==>   \
\		 residuals(App(b,Fun(u1),u2),App(1,Fun(v1),v2),w2/w1)"
  type_intrs	"[subst_type]@nat_typechecks@redexes.intrs@bool_typechecks"

rules
  res_func_def  "u |> v == THE w.residuals(u,v,w)"
end

