(*  Title:      HOL/ex/MT.thy
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

section {* Milner-Tofte: Co-induction in Relational Semantics *}

theory MT
imports Main
begin

typedecl Const

typedecl ExVar
typedecl Ex

typedecl TyConst
typedecl Ty

typedecl Clos
typedecl Val

typedecl ValEnv
typedecl TyEnv

consts
  c_app :: "[Const, Const] => Const"

  e_const :: "Const => Ex"
  e_var :: "ExVar => Ex"
  e_fn :: "[ExVar, Ex] => Ex" ("fn _ => _" [0,51] 1000)
  e_fix :: "[ExVar, ExVar, Ex] => Ex" ("fix _ ( _ ) = _" [0,51,51] 1000)
  e_app :: "[Ex, Ex] => Ex" ("_ @@ _" [51,51] 1000)
  e_const_fst :: "Ex => Const"

  t_const :: "TyConst => Ty"
  t_fun :: "[Ty, Ty] => Ty" ("_ -> _" [51,51] 1000)

  v_const :: "Const => Val"
  v_clos :: "Clos => Val"

  ve_emp :: ValEnv
  ve_owr :: "[ValEnv, ExVar, Val] => ValEnv" ("_ + { _ |-> _ }" [36,0,0] 50)
  ve_dom :: "ValEnv => ExVar set"
  ve_app :: "[ValEnv, ExVar] => Val"

  clos_mk :: "[ExVar, Ex, ValEnv] => Clos" ("<| _ , _ , _ |>" [0,0,0] 1000)

  te_emp :: TyEnv
  te_owr :: "[TyEnv, ExVar, Ty] => TyEnv" ("_ + { _ |=> _ }" [36,0,0] 50)
  te_app :: "[TyEnv, ExVar] => Ty"
  te_dom :: "TyEnv => ExVar set"

  eval_fun :: "((ValEnv * Ex) * Val) set => ((ValEnv * Ex) * Val) set"
  eval_rel :: "((ValEnv * Ex) * Val) set"
  eval :: "[ValEnv, Ex, Val] => bool" ("_ |- _ ---> _" [36,0,36] 50)

  elab_fun :: "((TyEnv * Ex) * Ty) set => ((TyEnv * Ex) * Ty) set"
  elab_rel :: "((TyEnv * Ex) * Ty) set"
  elab :: "[TyEnv, Ex, Ty] => bool" ("_ |- _ ===> _" [36,0,36] 50)

  isof :: "[Const, Ty] => bool" ("_ isof _" [36,36] 50)
  isof_env :: "[ValEnv,TyEnv] => bool" ("_ isofenv _")

  hasty_fun :: "(Val * Ty) set => (Val * Ty) set"
  hasty_rel :: "(Val * Ty) set"
  hasty :: "[Val, Ty] => bool" ("_ hasty _" [36,36] 50)
  hasty_env :: "[ValEnv,TyEnv] => bool" ("_ hastyenv _ " [36,36] 35)

(*
  Expression constructors must be injective, distinct and it must be possible
  to do induction over expressions.
*)

(* All the constructors are injective *)
axiomatization where
  e_const_inj: "e_const(c1) = e_const(c2) ==> c1 = c2" and
  e_var_inj: "e_var(ev1) = e_var(ev2) ==> ev1 = ev2" and
  e_fn_inj: "fn ev1 => e1 = fn ev2 => e2 ==> ev1 = ev2 & e1 = e2" and
  e_fix_inj:
    " fix ev11e(v12) = e1 = fix ev21(ev22) = e2 ==>
     ev11 = ev21 & ev12 = ev22 & e1 = e2" and
  e_app_inj: "e11 @@ e12 = e21 @@ e22 ==> e11 = e21 & e12 = e22"

(* All constructors are distinct *)

axiomatization where
  e_disj_const_var: "~e_const(c) = e_var(ev)" and
  e_disj_const_fn: "~e_const(c) = fn ev => e" and
  e_disj_const_fix: "~e_const(c) = fix ev1(ev2) = e" and
  e_disj_const_app: "~e_const(c) = e1 @@ e2" and
  e_disj_var_fn: "~e_var(ev1) = fn ev2 => e" and
  e_disj_var_fix: "~e_var(ev) = fix ev1(ev2) = e" and
  e_disj_var_app: "~e_var(ev) = e1 @@ e2" and
  e_disj_fn_fix: "~fn ev1 => e1 = fix ev21(ev22) = e2" and
  e_disj_fn_app: "~fn ev1 => e1 = e21 @@ e22" and
  e_disj_fix_app: "~fix ev11(ev12) = e1 = e21 @@ e22"

(* Strong elimination, induction on expressions  *)

axiomatization where
  e_ind:
    " [|  !!ev. P(e_var(ev));
         !!c. P(e_const(c));
         !!ev e. P(e) ==> P(fn ev => e);
         !!ev1 ev2 e. P(e) ==> P(fix ev1(ev2) = e);
         !!e1 e2. P(e1) ==> P(e2) ==> P(e1 @@ e2)
     |] ==>
   P(e)
   "

(* Types - same scheme as for expressions *)

(* All constructors are injective *)

axiomatization where
  t_const_inj: "t_const(c1) = t_const(c2) ==> c1 = c2" and
  t_fun_inj: "t11 -> t12 = t21 -> t22 ==> t11 = t21 & t12 = t22"

(* All constructors are distinct, not needed so far ... *)

(* Strong elimination, induction on types *)

axiomatization where
 t_ind:
    "[| !!p. P(t_const p); !!t1 t2. P(t1) ==> P(t2) ==> P(t_fun t1 t2) |]
    ==> P(t)"


(* Values - same scheme again *)

(* All constructors are injective *)

axiomatization where
  v_const_inj: "v_const(c1) = v_const(c2) ==> c1 = c2" and
  v_clos_inj:
    " v_clos(<|ev1,e1,ve1|>) = v_clos(<|ev2,e2,ve2|>) ==>
     ev1 = ev2 & e1 = e2 & ve1 = ve2"

(* All constructors are distinct *)

axiomatization where
  v_disj_const_clos: "~v_const(c) = v_clos(cl)"

(* No induction on values: they are a codatatype! ... *)


(*
  Value environments bind variables to values. Only the following trivial
  properties are needed.
*)

axiomatization where
  ve_dom_owr: "ve_dom(ve + {ev |-> v}) = ve_dom(ve) Un {ev}" and

  ve_app_owr1: "ve_app (ve + {ev |-> v}) ev=v" and
  ve_app_owr2: "~ev1=ev2 ==> ve_app (ve+{ev1 |-> v}) ev2=ve_app ve ev2"


(* Type Environments bind variables to types. The following trivial
properties are needed.  *)

axiomatization where
  te_dom_owr: "te_dom(te + {ev |=> t}) = te_dom(te) Un {ev}" and

  te_app_owr1: "te_app (te + {ev |=> t}) ev=t" and
  te_app_owr2: "~ev1=ev2 ==> te_app (te+{ev1 |=> t}) ev2=te_app te ev2"


(* The dynamic semantics is defined inductively by a set of inference
rules.  These inference rules allows one to draw conclusions of the form ve
|- e ---> v, read the expression e evaluates to the value v in the value
environment ve.  Therefore the relation _ |- _ ---> _ is defined in Isabelle
as the least fixpoint of the functor eval_fun below.  From this definition
introduction rules and a strong elimination (induction) rule can be
derived.
*)

defs
  eval_fun_def:
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
           pp=((ve,e1 @@ e2),v_const(c_app c1 c2)) &
           ((ve,e1),v_const(c1)):s & ((ve,e2),v_const(c2)):s
       ) |
       ( ? ve vem e1 e2 em xm v v2.
           pp=((ve,e1 @@ e2),v) &
           ((ve,e1),v_clos(<|xm,em,vem|>)):s &
           ((ve,e2),v2):s &
           ((vem+{xm |-> v2},em),v):s
       )
     }"

  eval_rel_def: "eval_rel == lfp(eval_fun)"
  eval_def: "ve |- e ---> v == ((ve,e),v):eval_rel"

(* The static semantics is defined in the same way as the dynamic
semantics.  The relation te |- e ===> t express the expression e has the
type t in the type environment te.
*)

  elab_fun_def:
  "elab_fun(s) ==
  { pp.
    (? te c t. pp=((te,e_const(c)),t) & c isof t) |
    (? te x. pp=((te,e_var(x)),te_app te x) & x:te_dom(te)) |
    (? te x e t1 t2. pp=((te,fn x => e),t1->t2) & ((te+{x |=> t1},e),t2):s) |
    (? te f x e t1 t2.
       pp=((te,fix f(x)=e),t1->t2) & ((te+{f |=> t1->t2}+{x |=> t1},e),t2):s
    ) |
    (? te e1 e2 t1 t2.
       pp=((te,e1 @@ e2),t2) & ((te,e1),t1->t2):s & ((te,e2),t1):s
    )
  }"

  elab_rel_def: "elab_rel == lfp(elab_fun)"
  elab_def: "te |- e ===> t == ((te,e),t):elab_rel"

(* The original correspondence relation *)

  isof_env_def:
    " ve isofenv te ==
     ve_dom(ve) = te_dom(te) &
     ( ! x.
         x:ve_dom(ve) -->
         (? c. ve_app ve x = v_const(c) & c isof te_app te x)
     )
   "

axiomatization where
  isof_app: "[| c1 isof t1->t2; c2 isof t1 |] ==> c_app c1 c2 isof t2"

defs
(* The extented correspondence relation *)

  hasty_fun_def:
    " hasty_fun(r) ==
     { p.
       ( ? c t. p = (v_const(c),t) & c isof t) |
       ( ? ev e ve t te.
           p = (v_clos(<|ev,e,ve|>),t) &
           te |- fn ev => e ===> t &
           ve_dom(ve) = te_dom(te) &
           (! ev1. ev1:ve_dom(ve) --> (ve_app ve ev1,te_app te ev1) : r)
       )
     }
   "

  hasty_rel_def: "hasty_rel == gfp(hasty_fun)"
  hasty_def: "v hasty t == (v,t) : hasty_rel"
  hasty_env_def:
    " ve hastyenv te ==
     ve_dom(ve) = te_dom(te) &
     (! x. x: ve_dom(ve) --> ve_app ve x hasty te_app te x)"


(* ############################################################ *)
(* Inference systems                                            *)
(* ############################################################ *)

ML {*
val infsys_mono_tac = REPEAT (ares_tac (@{thms basic_monos} @ [allI, impI]) 1)
*}

lemma infsys_p1: "P a b ==> P (fst (a,b)) (snd (a,b))"
  by simp

lemma infsys_p2: "P (fst (a,b)) (snd (a,b)) ==> P a b"
  by simp

lemma infsys_pp1: "P a b c ==> P (fst(fst((a,b),c))) (snd(fst ((a,b),c))) (snd ((a,b),c))"
  by simp

lemma infsys_pp2: "P (fst(fst((a,b),c))) (snd(fst((a,b),c))) (snd((a,b),c)) ==> P a b c"
  by simp


(* ############################################################ *)
(* Fixpoints                                                    *)
(* ############################################################ *)

(* Least fixpoints *)

lemma lfp_intro2: "[| mono(f); x:f(lfp(f)) |] ==> x:lfp(f)"
apply (rule subsetD)
apply (rule lfp_lemma2)
apply assumption+
done

lemma lfp_elim2:
  assumes lfp: "x:lfp(f)"
    and mono: "mono(f)"
    and r: "!!y. y:f(lfp(f)) ==> P(y)"
  shows "P(x)"
apply (rule r)
apply (rule subsetD)
apply (rule lfp_lemma3)
apply (rule mono)
apply (rule lfp)
done

lemma lfp_ind2:
  assumes lfp: "x:lfp(f)"
    and mono: "mono(f)"
    and r: "!!y. y:f(lfp(f) Int {x. P(x)}) ==> P(y)"
  shows "P(x)"
apply (rule lfp_induct_set [OF lfp mono])
apply (erule r)
done

(* Greatest fixpoints *)

(* Note : "[| x:S; S <= f(S Un gfp(f)); mono(f) |] ==> x:gfp(f)" *)

lemma gfp_coind2:
  assumes cih: "x:f({x} Un gfp(f))"
    and monoh: "mono(f)"
  shows "x:gfp(f)"
apply (rule cih [THEN [2] gfp_upperbound [THEN subsetD]])
apply (rule monoh [THEN monoD])
apply (rule UnE [THEN subsetI])
apply assumption
apply (blast intro!: cih)
apply (rule monoh [THEN monoD [THEN subsetD]])
apply (rule Un_upper2)
apply (erule monoh [THEN gfp_lemma2, THEN subsetD])
done

lemma gfp_elim2:
  assumes gfph: "x:gfp(f)"
    and monoh: "mono(f)"
    and caseh: "!!y. y:f(gfp(f)) ==> P(y)"
  shows "P(x)"
apply (rule caseh)
apply (rule subsetD)
apply (rule gfp_lemma2)
apply (rule monoh)
apply (rule gfph)
done

(* ############################################################ *)
(* Expressions                                                  *)
(* ############################################################ *)

lemmas e_injs = e_const_inj e_var_inj e_fn_inj e_fix_inj e_app_inj

lemmas e_disjs =
  e_disj_const_var
  e_disj_const_fn
  e_disj_const_fix
  e_disj_const_app
  e_disj_var_fn
  e_disj_var_fix
  e_disj_var_app
  e_disj_fn_fix
  e_disj_fn_app
  e_disj_fix_app

lemmas e_disj_si = e_disjs  e_disjs [symmetric]

lemmas e_disj_se = e_disj_si [THEN notE]

(* ############################################################ *)
(* Values                                                      *)
(* ############################################################ *)

lemmas v_disjs = v_disj_const_clos
lemmas v_disj_si = v_disjs  v_disjs [symmetric]
lemmas v_disj_se = v_disj_si [THEN notE]

lemmas v_injs = v_const_inj v_clos_inj

(* ############################################################ *)
(* Evaluations                                                  *)
(* ############################################################ *)

(* Monotonicity of eval_fun *)

lemma eval_fun_mono: "mono(eval_fun)"
unfolding mono_def eval_fun_def
apply (tactic infsys_mono_tac)
done

(* Introduction rules *)

lemma eval_const: "ve |- e_const(c) ---> v_const(c)"
unfolding eval_def eval_rel_def
apply (rule lfp_intro2)
apply (rule eval_fun_mono)
apply (unfold eval_fun_def)
        (*Naughty!  But the quantifiers are nested VERY deeply...*)
apply (blast intro!: exI)
done

lemma eval_var2:
  "ev:ve_dom(ve) ==> ve |- e_var(ev) ---> ve_app ve ev"
apply (unfold eval_def eval_rel_def)
apply (rule lfp_intro2)
apply (rule eval_fun_mono)
apply (unfold eval_fun_def)
apply (blast intro!: exI)
done

lemma eval_fn:
  "ve |- fn ev => e ---> v_clos(<|ev,e,ve|>)"
apply (unfold eval_def eval_rel_def)
apply (rule lfp_intro2)
apply (rule eval_fun_mono)
apply (unfold eval_fun_def)
apply (blast intro!: exI)
done

lemma eval_fix:
  " cl = <| ev1, e, ve + {ev2 |-> v_clos(cl)} |> ==>
    ve |- fix ev2(ev1) = e ---> v_clos(cl)"
apply (unfold eval_def eval_rel_def)
apply (rule lfp_intro2)
apply (rule eval_fun_mono)
apply (unfold eval_fun_def)
apply (blast intro!: exI)
done

lemma eval_app1:
  " [| ve |- e1 ---> v_const(c1); ve |- e2 ---> v_const(c2) |] ==>
    ve |- e1 @@ e2 ---> v_const(c_app c1 c2)"
apply (unfold eval_def eval_rel_def)
apply (rule lfp_intro2)
apply (rule eval_fun_mono)
apply (unfold eval_fun_def)
apply (blast intro!: exI)
done

lemma eval_app2:
  " [|  ve |- e1 ---> v_clos(<|xm,em,vem|>);
        ve |- e2 ---> v2;
        vem + {xm |-> v2} |- em ---> v
    |] ==>
    ve |- e1 @@ e2 ---> v"
apply (unfold eval_def eval_rel_def)
apply (rule lfp_intro2)
apply (rule eval_fun_mono)
apply (unfold eval_fun_def)
apply (blast intro!: disjI2)
done

(* Strong elimination, induction on evaluations *)

lemma eval_ind0:
  " [| ve |- e ---> v;
       !!ve c. P(((ve,e_const(c)),v_const(c)));
       !!ev ve. ev:ve_dom(ve) ==> P(((ve,e_var(ev)),ve_app ve ev));
       !!ev ve e. P(((ve,fn ev => e),v_clos(<|ev,e,ve|>)));
       !!ev1 ev2 ve cl e.
         cl = <| ev1, e, ve + {ev2 |-> v_clos(cl)} |> ==>
         P(((ve,fix ev2(ev1) = e),v_clos(cl)));
       !!ve c1 c2 e1 e2.
         [| P(((ve,e1),v_const(c1))); P(((ve,e2),v_const(c2))) |] ==>
         P(((ve,e1 @@ e2),v_const(c_app c1 c2)));
       !!ve vem xm e1 e2 em v v2.
         [|  P(((ve,e1),v_clos(<|xm,em,vem|>)));
             P(((ve,e2),v2));
             P(((vem + {xm |-> v2},em),v))
         |] ==>
         P(((ve,e1 @@ e2),v))
    |] ==>
    P(((ve,e),v))"
unfolding eval_def eval_rel_def
apply (erule lfp_ind2)
apply (rule eval_fun_mono)
apply (unfold eval_fun_def)
apply (drule CollectD)
apply safe
apply auto
done

lemma eval_ind:
  " [| ve |- e ---> v;
       !!ve c. P ve (e_const c) (v_const c);
       !!ev ve. ev:ve_dom(ve) ==> P ve (e_var ev) (ve_app ve ev);
       !!ev ve e. P ve (fn ev => e) (v_clos <|ev,e,ve|>);
       !!ev1 ev2 ve cl e.
         cl = <| ev1, e, ve + {ev2 |-> v_clos(cl)} |> ==>
         P ve (fix ev2(ev1) = e) (v_clos cl);
       !!ve c1 c2 e1 e2.
         [| P ve e1 (v_const c1); P ve e2 (v_const c2) |] ==>
         P ve (e1 @@ e2) (v_const(c_app c1 c2));
       !!ve vem evm e1 e2 em v v2.
         [|  P ve e1 (v_clos <|evm,em,vem|>);
             P ve e2 v2;
             P (vem + {evm |-> v2}) em v
         |] ==> P ve (e1 @@ e2) v
    |] ==> P ve e v"
apply (rule_tac P = "P" in infsys_pp2)
apply (rule eval_ind0)
apply (rule infsys_pp1)
apply auto
done

(* ############################################################ *)
(* Elaborations                                                 *)
(* ############################################################ *)

lemma elab_fun_mono: "mono(elab_fun)"
unfolding mono_def elab_fun_def
apply (tactic infsys_mono_tac)
done

(* Introduction rules *)

lemma elab_const:
  "c isof ty ==> te |- e_const(c) ===> ty"
apply (unfold elab_def elab_rel_def)
apply (rule lfp_intro2)
apply (rule elab_fun_mono)
apply (unfold elab_fun_def)
apply (blast intro!: exI)
done

lemma elab_var:
  "x:te_dom(te) ==> te |- e_var(x) ===> te_app te x"
apply (unfold elab_def elab_rel_def)
apply (rule lfp_intro2)
apply (rule elab_fun_mono)
apply (unfold elab_fun_def)
apply (blast intro!: exI)
done

lemma elab_fn:
  "te + {x |=> ty1} |- e ===> ty2 ==> te |- fn x => e ===> ty1->ty2"
apply (unfold elab_def elab_rel_def)
apply (rule lfp_intro2)
apply (rule elab_fun_mono)
apply (unfold elab_fun_def)
apply (blast intro!: exI)
done

lemma elab_fix:
  "te + {f |=> ty1->ty2} + {x |=> ty1} |- e ===> ty2 ==>
         te |- fix f(x) = e ===> ty1->ty2"
apply (unfold elab_def elab_rel_def)
apply (rule lfp_intro2)
apply (rule elab_fun_mono)
apply (unfold elab_fun_def)
apply (blast intro!: exI)
done

lemma elab_app:
  "[| te |- e1 ===> ty1->ty2; te |- e2 ===> ty1 |] ==>
         te |- e1 @@ e2 ===> ty2"
apply (unfold elab_def elab_rel_def)
apply (rule lfp_intro2)
apply (rule elab_fun_mono)
apply (unfold elab_fun_def)
apply (blast intro!: disjI2)
done

(* Strong elimination, induction on elaborations *)

lemma elab_ind0:
  assumes 1: "te |- e ===> t"
    and 2: "!!te c t. c isof t ==> P(((te,e_const(c)),t))"
    and 3: "!!te x. x:te_dom(te) ==> P(((te,e_var(x)),te_app te x))"
    and 4: "!!te x e t1 t2.
       [| te + {x |=> t1} |- e ===> t2; P(((te + {x |=> t1},e),t2)) |] ==>
       P(((te,fn x => e),t1->t2))"
    and 5: "!!te f x e t1 t2.
       [| te + {f |=> t1->t2} + {x |=> t1} |- e ===> t2;
          P(((te + {f |=> t1->t2} + {x |=> t1},e),t2))
       |] ==>
       P(((te,fix f(x) = e),t1->t2))"
    and 6: "!!te e1 e2 t1 t2.
       [| te |- e1 ===> t1->t2; P(((te,e1),t1->t2));
          te |- e2 ===> t1; P(((te,e2),t1))
       |] ==>
       P(((te,e1 @@ e2),t2))"
  shows "P(((te,e),t))"
apply (rule lfp_ind2 [OF 1 [unfolded elab_def elab_rel_def]])
apply (rule elab_fun_mono)
apply (unfold elab_fun_def)
apply (drule CollectD)
apply safe
apply (erule 2)
apply (erule 3)
apply (rule 4 [unfolded elab_def elab_rel_def]) apply blast+
apply (rule 5 [unfolded elab_def elab_rel_def]) apply blast+
apply (rule 6 [unfolded elab_def elab_rel_def]) apply blast+
done

lemma elab_ind:
  " [| te |- e ===> t;
        !!te c t. c isof t ==> P te (e_const c) t;
       !!te x. x:te_dom(te) ==> P te (e_var x) (te_app te x);
       !!te x e t1 t2.
         [| te + {x |=> t1} |- e ===> t2; P (te + {x |=> t1}) e t2 |] ==>
         P te (fn x => e) (t1->t2);
       !!te f x e t1 t2.
         [| te + {f |=> t1->t2} + {x |=> t1} |- e ===> t2;
            P (te + {f |=> t1->t2} + {x |=> t1}) e t2
         |] ==>
         P te (fix f(x) = e) (t1->t2);
       !!te e1 e2 t1 t2.
         [| te |- e1 ===> t1->t2; P te e1 (t1->t2);
            te |- e2 ===> t1; P te e2 t1
         |] ==>
         P te (e1 @@ e2) t2
    |] ==>
    P te e t"
apply (rule_tac P = "P" in infsys_pp2)
apply (erule elab_ind0)
apply (rule_tac [!] infsys_pp1)
apply auto
done

(* Weak elimination, case analysis on elaborations *)

lemma elab_elim0:
  assumes 1: "te |- e ===> t"
    and 2: "!!te c t. c isof t ==> P(((te,e_const(c)),t))"
    and 3: "!!te x. x:te_dom(te) ==> P(((te,e_var(x)),te_app te x))"
    and 4: "!!te x e t1 t2.
         te + {x |=> t1} |- e ===> t2 ==> P(((te,fn x => e),t1->t2))"
    and 5: "!!te f x e t1 t2.
         te + {f |=> t1->t2} + {x |=> t1} |- e ===> t2 ==>
         P(((te,fix f(x) = e),t1->t2))"
    and 6: "!!te e1 e2 t1 t2.
         [| te |- e1 ===> t1->t2; te |- e2 ===> t1 |] ==>
         P(((te,e1 @@ e2),t2))"
  shows "P(((te,e),t))"
apply (rule lfp_elim2 [OF 1 [unfolded elab_def elab_rel_def]])
apply (rule elab_fun_mono)
apply (unfold elab_fun_def)
apply (drule CollectD)
apply safe
apply (erule 2)
apply (erule 3)
apply (rule 4 [unfolded elab_def elab_rel_def]) apply blast+
apply (rule 5 [unfolded elab_def elab_rel_def]) apply blast+
apply (rule 6 [unfolded elab_def elab_rel_def]) apply blast+
done

lemma elab_elim:
  " [| te |- e ===> t;
        !!te c t. c isof t ==> P te (e_const c) t;
       !!te x. x:te_dom(te) ==> P te (e_var x) (te_app te x);
       !!te x e t1 t2.
         te + {x |=> t1} |- e ===> t2 ==> P te (fn x => e) (t1->t2);
       !!te f x e t1 t2.
         te + {f |=> t1->t2} + {x |=> t1} |- e ===> t2 ==>
         P te (fix f(x) = e) (t1->t2);
       !!te e1 e2 t1 t2.
         [| te |- e1 ===> t1->t2; te |- e2 ===> t1 |] ==>
         P te (e1 @@ e2) t2
    |] ==>
    P te e t"
apply (rule_tac P = "P" in infsys_pp2)
apply (rule elab_elim0)
apply auto
done

(* Elimination rules for each expression *)

lemma elab_const_elim_lem:
    "te |- e ===> t ==> (e = e_const(c) --> c isof t)"
apply (erule elab_elim)
apply (fast intro!: e_disj_si elim!: e_disj_se dest!: e_injs)+
done

lemma elab_const_elim: "te |- e_const(c) ===> t ==> c isof t"
apply (drule elab_const_elim_lem)
apply blast
done

lemma elab_var_elim_lem:
  "te |- e ===> t ==> (e = e_var(x) --> t=te_app te x & x:te_dom(te))"
apply (erule elab_elim)
apply (fast intro!: e_disj_si elim!: e_disj_se dest!: e_injs)+
done

lemma elab_var_elim: "te |- e_var(ev) ===> t ==> t=te_app te ev & ev : te_dom(te)"
apply (drule elab_var_elim_lem)
apply blast
done

lemma elab_fn_elim_lem:
  " te |- e ===> t ==>
    ( e = fn x1 => e1 -->
      (? t1 t2. t=t_fun t1 t2 & te + {x1 |=> t1} |- e1 ===> t2)
    )"
apply (erule elab_elim)
apply (fast intro!: e_disj_si elim!: e_disj_se dest!: e_injs)+
done

lemma elab_fn_elim: " te |- fn x1 => e1 ===> t ==>
    (? t1 t2. t=t1->t2 & te + {x1 |=> t1} |- e1 ===> t2)"
apply (drule elab_fn_elim_lem)
apply blast
done

lemma elab_fix_elim_lem:
  " te |- e ===> t ==>
    (e = fix f(x) = e1 -->
    (? t1 t2. t=t1->t2 & te + {f |=> t1->t2} + {x |=> t1} |- e1 ===> t2))"
apply (erule elab_elim)
apply (fast intro!: e_disj_si elim!: e_disj_se dest!: e_injs)+
done

lemma elab_fix_elim: " te |- fix ev1(ev2) = e1 ===> t ==>
    (? t1 t2. t=t1->t2 & te + {ev1 |=> t1->t2} + {ev2 |=> t1} |- e1 ===> t2)"
apply (drule elab_fix_elim_lem)
apply blast
done

lemma elab_app_elim_lem:
  " te |- e ===> t2 ==>
    (e = e1 @@ e2 --> (? t1 . te |- e1 ===> t1->t2 & te |- e2 ===> t1))"
apply (erule elab_elim)
apply (fast intro!: e_disj_si elim!: e_disj_se dest!: e_injs)+
done

lemma elab_app_elim: "te |- e1 @@ e2 ===> t2 ==> (? t1 . te |- e1 ===> t1->t2 & te |- e2 ===> t1)"
apply (drule elab_app_elim_lem)
apply blast
done

(* ############################################################ *)
(* The extended correspondence relation                       *)
(* ############################################################ *)

(* Monotonicity of hasty_fun *)

lemma mono_hasty_fun: "mono(hasty_fun)"
unfolding mono_def hasty_fun_def
apply (tactic infsys_mono_tac)
apply blast
done

(*
  Because hasty_rel has been defined as the greatest fixpoint of hasty_fun it
  enjoys two strong indtroduction (co-induction) rules and an elimination rule.
*)

(* First strong indtroduction (co-induction) rule for hasty_rel *)

lemma hasty_rel_const_coind: "c isof t ==> (v_const(c),t) : hasty_rel"
apply (unfold hasty_rel_def)
apply (rule gfp_coind2)
apply (unfold hasty_fun_def)
apply (rule CollectI)
apply (rule disjI1)
apply blast
apply (rule mono_hasty_fun)
done

(* Second strong introduction (co-induction) rule for hasty_rel *)

lemma hasty_rel_clos_coind:
  " [|  te |- fn ev => e ===> t;
        ve_dom(ve) = te_dom(te);
        ! ev1.
          ev1:ve_dom(ve) -->
          (ve_app ve ev1,te_app te ev1) : {(v_clos(<|ev,e,ve|>),t)} Un hasty_rel
    |] ==>
    (v_clos(<|ev,e,ve|>),t) : hasty_rel"
apply (unfold hasty_rel_def)
apply (rule gfp_coind2)
apply (unfold hasty_fun_def)
apply (rule CollectI)
apply (rule disjI2)
apply blast
apply (rule mono_hasty_fun)
done

(* Elimination rule for hasty_rel *)

lemma hasty_rel_elim0:
  " [| !! c t. c isof t ==> P((v_const(c),t));
       !! te ev e t ve.
         [| te |- fn ev => e ===> t;
            ve_dom(ve) = te_dom(te);
            !ev1. ev1:ve_dom(ve) --> (ve_app ve ev1,te_app te ev1) : hasty_rel
         |] ==> P((v_clos(<|ev,e,ve|>),t));
       (v,t) : hasty_rel
    |] ==> P(v,t)"
unfolding hasty_rel_def
apply (erule gfp_elim2)
apply (rule mono_hasty_fun)
apply (unfold hasty_fun_def)
apply (drule CollectD)
apply (fold hasty_fun_def)
apply auto
done

lemma hasty_rel_elim:
  " [| (v,t) : hasty_rel;
       !! c t. c isof t ==> P (v_const c) t;
       !! te ev e t ve.
         [| te |- fn ev => e ===> t;
            ve_dom(ve) = te_dom(te);
            !ev1. ev1:ve_dom(ve) --> (ve_app ve ev1,te_app te ev1) : hasty_rel
         |] ==> P (v_clos <|ev,e,ve|>) t
    |] ==> P v t"
apply (rule_tac P = "P" in infsys_p2)
apply (rule hasty_rel_elim0)
apply auto
done

(* Introduction rules for hasty *)

lemma hasty_const: "c isof t ==> v_const(c) hasty t"
apply (unfold hasty_def)
apply (erule hasty_rel_const_coind)
done

lemma hasty_clos:
 "te |- fn ev => e ===> t & ve hastyenv te ==> v_clos(<|ev,e,ve|>) hasty t"
apply (unfold hasty_def hasty_env_def)
apply (rule hasty_rel_clos_coind)
apply (blast del: equalityI)+
done

(* Elimination on constants for hasty *)

lemma hasty_elim_const_lem:
  "v hasty t ==> (!c.(v = v_const(c) --> c isof t))"
apply (unfold hasty_def)
apply (rule hasty_rel_elim)
apply (blast intro!: v_disj_si elim!: v_disj_se dest!: v_injs)+
done

lemma hasty_elim_const: "v_const(c) hasty t ==> c isof t"
apply (drule hasty_elim_const_lem)
apply blast
done

(* Elimination on closures for hasty *)

lemma hasty_elim_clos_lem:
  " v hasty t ==>
    ! x e ve.
      v=v_clos(<|x,e,ve|>) --> (? te. te |- fn x => e ===> t & ve hastyenv te)"
apply (unfold hasty_env_def hasty_def)
apply (rule hasty_rel_elim)
apply (blast intro!: v_disj_si elim!: v_disj_se dest!: v_injs)+
done

lemma hasty_elim_clos: "v_clos(<|ev,e,ve|>) hasty t ==>
        ? te. te |- fn ev => e ===> t & ve hastyenv te "
apply (drule hasty_elim_clos_lem)
apply blast
done

(* ############################################################ *)
(* The pointwise extension of hasty to environments             *)
(* ############################################################ *)

lemma hasty_env1: "[| ve hastyenv te; v hasty t |] ==>
         ve + {ev |-> v} hastyenv te + {ev |=> t}"
apply (unfold hasty_env_def)
apply (simp del: mem_simps add: ve_dom_owr te_dom_owr)
apply (tactic {* safe_tac (put_claset HOL_cs @{context}) *})
apply (case_tac "ev=x")
apply (simp (no_asm_simp) add: ve_app_owr1 te_app_owr1)
apply (simp add: ve_app_owr2 te_app_owr2)
done

(* ############################################################ *)
(* The Consistency theorem                                      *)
(* ############################################################ *)

lemma consistency_const: "[| ve hastyenv te ; te |- e_const(c) ===> t |] ==> v_const(c) hasty t"
apply (drule elab_const_elim)
apply (erule hasty_const)
done

lemma consistency_var:
  "[| ev : ve_dom(ve); ve hastyenv te ; te |- e_var(ev) ===> t |] ==>
        ve_app ve ev hasty t"
apply (unfold hasty_env_def)
apply (drule elab_var_elim)
apply blast
done

lemma consistency_fn: "[| ve hastyenv te ; te |- fn ev => e ===> t |] ==>
        v_clos(<| ev, e, ve |>) hasty t"
apply (rule hasty_clos)
apply blast
done

lemma consistency_fix:
  "[| cl = <| ev1, e, ve + { ev2 |-> v_clos(cl) } |>;
       ve hastyenv te ;
       te |- fix ev2  ev1  = e ===> t
    |] ==>
    v_clos(cl) hasty t"
apply (unfold hasty_env_def hasty_def)
apply (drule elab_fix_elim)
apply (tactic {* safe_tac (put_claset HOL_cs @{context}) *})
(*Do a single unfolding of cl*)
apply (frule ssubst) prefer 2 apply assumption
apply (rule hasty_rel_clos_coind)
apply (erule elab_fn)
apply (simp (no_asm_simp) add: ve_dom_owr te_dom_owr)

apply (simp (no_asm_simp) del: mem_simps add: ve_dom_owr)
apply (tactic {* safe_tac (put_claset HOL_cs @{context}) *})
apply (case_tac "ev2=ev1a")
apply (simp (no_asm_simp) del: mem_simps add: ve_app_owr1 te_app_owr1)
apply blast
apply (simp add: ve_app_owr2 te_app_owr2)
done

lemma consistency_app1: "[| ! t te. ve hastyenv te --> te |- e1 ===> t --> v_const(c1) hasty t;
       ! t te. ve hastyenv te  --> te |- e2 ===> t --> v_const(c2) hasty t;
       ve hastyenv te ; te |- e1 @@ e2 ===> t
    |] ==>
    v_const(c_app c1 c2) hasty t"
apply (drule elab_app_elim)
apply safe
apply (rule hasty_const)
apply (rule isof_app)
apply (rule hasty_elim_const)
apply blast
apply (rule hasty_elim_const)
apply blast
done

lemma consistency_app2: "[| ! t te.
         ve hastyenv te  -->
         te |- e1 ===> t --> v_clos(<|evm, em, vem|>) hasty t;
       ! t te. ve hastyenv te  --> te |- e2 ===> t --> v2 hasty t;
       ! t te.
         vem + { evm |-> v2 } hastyenv te  --> te |- em ===> t --> v hasty t;
       ve hastyenv te ;
       te |- e1 @@ e2 ===> t
    |] ==>
    v hasty t"
apply (drule elab_app_elim)
apply safe
apply (erule allE, erule allE, erule impE)
apply assumption
apply (erule impE)
apply assumption
apply (erule allE, erule allE, erule impE)
apply assumption
apply (erule impE)
apply assumption
apply (drule hasty_elim_clos)
apply safe
apply (drule elab_fn_elim)
apply (blast intro: hasty_env1 dest!: t_fun_inj)
done

lemma consistency: "ve |- e ---> v ==>
   (! t te. ve hastyenv te --> te |- e ===> t --> v hasty t)"

(* Proof by induction on the structure of evaluations *)

apply (erule eval_ind)
apply safe
apply (blast intro: consistency_const consistency_var consistency_fn consistency_fix consistency_app1 consistency_app2)+
done

(* ############################################################ *)
(* The Basic Consistency theorem                                *)
(* ############################################################ *)

lemma basic_consistency_lem:
  "ve isofenv te ==> ve hastyenv te"
apply (unfold isof_env_def hasty_env_def)
apply safe
apply (erule allE)
apply (erule impE)
apply assumption
apply (erule exE)
apply (erule conjE)
apply (drule hasty_const)
apply (simp (no_asm_simp))
done

lemma basic_consistency:
  "[| ve isofenv te; ve |- e ---> v_const(c); te |- e ===> t |] ==> c isof t"
apply (rule hasty_elim_const)
apply (drule consistency)
apply (blast intro!: basic_consistency_lem)
done

end
