(*  Title:      HOL/ex/mt.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Based upon the article
    Robin Milner and Mads Tofte,
    Co-induction in Relational Semantics,
    Theoretical Computer Science 87 (1991), pages 209-220.

Written up as
    Jacob Frost, A Case Study of Co_induction in Isabelle/HOL
    Report 308, Computer Lab, University of Cambridge (1993).
*)

MT = Gfp + Sum + 

types 
  Const

  ExVar
  Ex

  TyConst
  Ty

  Clos
  Val

  ValEnv
  TyEnv

arities 
  Const :: term

  ExVar :: term
  Ex :: term

  TyConst :: term
  Ty :: term

  Clos :: term
  Val :: term

  ValEnv :: term
  TyEnv :: term

consts
  c_app :: [Const, Const] => Const

  e_const :: Const => Ex
  e_var :: ExVar => Ex
  e_fn :: [ExVar, Ex] => Ex ("fn _ => _" [0,51] 1000)
  e_fix :: [ExVar, ExVar, Ex] => Ex ("fix _ ( _ ) = _" [0,51,51] 1000)
  e_app :: [Ex, Ex] => Ex ("_ @ _" [51,51] 1000)
  e_const_fst :: Ex => Const

  t_const :: TyConst => Ty
  t_fun :: [Ty, Ty] => Ty ("_ -> _" [51,51] 1000)

  v_const :: Const => Val
  v_clos :: Clos => Val
  
  ve_emp :: ValEnv
  ve_owr :: [ValEnv, ExVar, Val] => ValEnv ("_ + { _ |-> _ }" [36,0,0] 50)
  ve_dom :: ValEnv => ExVar set
  ve_app :: [ValEnv, ExVar] => Val

  clos_mk :: [ExVar, Ex, ValEnv] => Clos ("<| _ , _ , _ |>" [0,0,0] 1000)

  te_emp :: TyEnv
  te_owr :: [TyEnv, ExVar, Ty] => TyEnv ("_ + { _ |=> _ }" [36,0,0] 50)
  te_app :: [TyEnv, ExVar] => Ty
  te_dom :: TyEnv => ExVar set

  eval_fun :: "((ValEnv * Ex) * Val) set => ((ValEnv * Ex) * Val) set"
  eval_rel :: "((ValEnv * Ex) * Val) set"
  eval :: [ValEnv, Ex, Val] => bool ("_ |- _ ---> _" [36,0,36] 50)

  elab_fun :: "((TyEnv * Ex) * Ty) set => ((TyEnv * Ex) * Ty) set"
  elab_rel :: "((TyEnv * Ex) * Ty) set"
  elab :: [TyEnv, Ex, Ty] => bool ("_ |- _ ===> _" [36,0,36] 50)
  
  isof :: [Const, Ty] => bool ("_ isof _" [36,36] 50)
  isof_env :: [ValEnv,TyEnv] => bool ("_ isofenv _")

  hasty_fun :: "(Val * Ty) set => (Val * Ty) set"
  hasty_rel :: "(Val * Ty) set"
  hasty :: [Val, Ty] => bool ("_ hasty _" [36,36] 50)
  hasty_env :: [ValEnv,TyEnv] => bool ("_ hastyenv _ " [36,36] 35)

rules

(* 
  Expression constructors must be injective, distinct and it must be possible
  to do induction over expressions.
*)

(* All the constructors are injective *)

  e_const_inj "e_const(c1) = e_const(c2) ==> c1 = c2"
  e_var_inj "e_var(ev1) = e_var(ev2) ==> ev1 = ev2"
  e_fn_inj "fn ev1 => e1 = fn ev2 => e2 ==> ev1 = ev2 & e1 = e2"
  e_fix_inj 
    " fix ev11e(v12) = e1 = fix ev21(ev22) = e2 ==> 
     ev11 = ev21 & ev12 = ev22 & e1 = e2 
   "
  e_app_inj "e11 @ e12 = e21 @ e22 ==> e11 = e21 & e12 = e22"

(* All constructors are distinct *)

  e_disj_const_var "~e_const(c) = e_var(ev)"
  e_disj_const_fn "~e_const(c) = fn ev => e"
  e_disj_const_fix "~e_const(c) = fix ev1(ev2) = e"
  e_disj_const_app "~e_const(c) = e1 @ e2"
  e_disj_var_fn "~e_var(ev1) = fn ev2 => e"
  e_disj_var_fix "~e_var(ev) = fix ev1(ev2) = e"
  e_disj_var_app "~e_var(ev) = e1 @ e2"
  e_disj_fn_fix "~fn ev1 => e1 = fix ev21(ev22) = e2"
  e_disj_fn_app "~fn ev1 => e1 = e21 @ e22"
  e_disj_fix_app "~fix ev11(ev12) = e1 = e21 @ e22"

(* Strong elimination, induction on expressions  *)

  e_ind 
    " [|  !!ev. P(e_var(ev)); 
         !!c. P(e_const(c)); 
         !!ev e. P(e) ==> P(fn ev => e); 
         !!ev1 ev2 e. P(e) ==> P(fix ev1(ev2) = e); 
         !!e1 e2. P(e1) ==> P(e2) ==> P(e1 @ e2) 
     |] ==> 
   P(e) 
   "

(* Types - same scheme as for expressions *)

(* All constructors are injective *) 

  t_const_inj "t_const(c1) = t_const(c2) ==> c1 = c2"
  t_fun_inj "t11 -> t12 = t21 -> t22 ==> t11 = t21 & t12 = t22"

(* All constructors are distinct, not needed so far ... *)

(* Strong elimination, induction on types *)

 t_ind 
    "[| !!p. P(t_const p); !!t1 t2. P(t1) ==> P(t2) ==> P(t_fun t1 t2) |] 
    ==> P(t)"


(* Values - same scheme again *)

(* All constructors are injective *) 

  v_const_inj "v_const(c1) = v_const(c2) ==> c1 = c2"
  v_clos_inj 
    " v_clos(<|ev1,e1,ve1|>) = v_clos(<|ev2,e2,ve2|>) ==> 
     ev1 = ev2 & e1 = e2 & ve1 = ve2"
  
(* All constructors are distinct *)

  v_disj_const_clos "~v_const(c) = v_clos(cl)"

(* Strong elimination, induction on values, not needed yet ... *)


(* 
  Value environments bind variables to values. Only the following trivial
  properties are needed.
*)

  ve_dom_owr "ve_dom(ve + {ev |-> v}) = ve_dom(ve) Un {ev}"
 
  ve_app_owr1 "ve_app (ve + {ev |-> v}) ev=v"
  ve_app_owr2 "~ev1=ev2 ==> ve_app (ve+{ev1 |-> v}) ev2=ve_app ve ev2"


(* Type Environments bind variables to types. The following trivial
properties are needed.  *)

  te_dom_owr "te_dom(te + {ev |=> t}) = te_dom(te) Un {ev}"
 
  te_app_owr1 "te_app (te + {ev |=> t}) ev=t"
  te_app_owr2 "~ev1=ev2 ==> te_app (te+{ev1 |=> t}) ev2=te_app te ev2"


(* The dynamic semantics is defined inductively by a set of inference
rules.  These inference rules allows one to draw conclusions of the form ve
|- e ---> v, read the expression e evaluates to the value v in the value
environment ve.  Therefore the relation _ |- _ ---> _ is defined in Isabelle
as the least fixpoint of the functor eval_fun below.  From this definition
introduction rules and a strong elimination (induction) rule can be
derived.  
*)

  eval_fun_def 
    " eval_fun(s) == 
     { pp. 
       (? ve c. pp=((ve,e_const(c)),v_const(c))) | 
       (? ve x. pp=((ve,e_var(x)),ve_app ve x) & x:ve_dom(ve)) |
       (? ve e x. pp=((ve,fn x => e),v_clos(<|x,e,ve|>)))| 
       ( ? ve e x f cl. 
           pp=((ve,fix f(x) = e),v_clos(cl)) & 
           cl=<|x, e, ve+{f |-> v_clos(cl)} |>  
       ) | 
       ( ? ve e1 e2 c1 c2. 
           pp=((ve,e1 @ e2),v_const(c_app c1 c2)) & 
           ((ve,e1),v_const(c1)):s & ((ve,e2),v_const(c2)):s 
       ) | 
       ( ? ve vem e1 e2 em xm v v2. 
           pp=((ve,e1 @ e2),v) & 
           ((ve,e1),v_clos(<|xm,em,vem|>)):s & 
           ((ve,e2),v2):s & 
           ((vem+{xm |-> v2},em),v):s 
       ) 
     }"

  eval_rel_def "eval_rel == lfp(eval_fun)"
  eval_def "ve |- e ---> v == ((ve,e),v):eval_rel"

(* The static semantics is defined in the same way as the dynamic
semantics.  The relation te |- e ===> t express the expression e has the
type t in the type environment te.
*)

  elab_fun_def 
  "elab_fun(s) == 
  { pp. 
    (? te c t. pp=((te,e_const(c)),t) & c isof t) | 
    (? te x. pp=((te,e_var(x)),te_app te x) & x:te_dom(te)) | 
    (? te x e t1 t2. pp=((te,fn x => e),t1->t2) & ((te+{x |=> t1},e),t2):s) | 
    (? te f x e t1 t2. 
       pp=((te,fix f(x)=e),t1->t2) & ((te+{f |=> t1->t2}+{x |=> t1},e),t2):s 
    ) | 
    (? te e1 e2 t1 t2. 
       pp=((te,e1 @ e2),t2) & ((te,e1),t1->t2):s & ((te,e2),t1):s 
    ) 
  }"

  elab_rel_def "elab_rel == lfp(elab_fun)"
  elab_def "te |- e ===> t == ((te,e),t):elab_rel"

(* The original correspondence relation *)

  isof_env_def 
    " ve isofenv te == 
     ve_dom(ve) = te_dom(te) & 
     ( ! x. 
         x:ve_dom(ve) --> 
         (? c.ve_app ve x = v_const(c) & c isof te_app te x) 
     ) 
   "

  isof_app "[| c1 isof t1->t2; c2 isof t1 |] ==> c_app c1 c2 isof t2"

(* The extented correspondence relation *)

  hasty_fun_def
    " hasty_fun(r) == 
     { p. 
       ( ? c t. p = (v_const(c),t) & c isof t) | 
       ( ? ev e ve t te. 
           p = (v_clos(<|ev,e,ve|>),t) & 
           te |- fn ev => e ===> t & 
           ve_dom(ve) = te_dom(te) & 
           (! ev1.ev1:ve_dom(ve) --> (ve_app ve ev1,te_app te ev1) : r) 
       ) 
     } 
   "

  hasty_rel_def "hasty_rel == gfp(hasty_fun)"
  hasty_def "v hasty t == (v,t) : hasty_rel"
  hasty_env_def 
    " ve hastyenv te == 
     ve_dom(ve) = te_dom(te) & 
     (! x. x: ve_dom(ve) --> ve_app ve x hasty te_app te x)"

end
