(*  Title:      HOLCF/Cfun1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Definition of the type ->  of continuous functions.

*)

theory Cfun1 = Cont:

defaultsort cpo

typedef (CFun)  ('a, 'b) "->" (infixr 0) = "{f::'a => 'b. cont f}"
by (rule exI, rule CfunI)

(* to make << defineable *)
instance "->"  :: (cpo,cpo)sq_ord ..

syntax
	Rep_CFun  :: "('a -> 'b) => ('a => 'b)" ("_$_" [999,1000] 999)
                                                (* application      *)
        Abs_CFun  :: "('a => 'b) => ('a -> 'b)" (binder "LAM " 10)
                                                (* abstraction      *)
        less_cfun :: "[('a -> 'b),('a -> 'b)]=>bool"

syntax (xsymbols)
  "->"		:: "[type, type] => type"      ("(_ \<rightarrow>/ _)" [1,0]0)
  "LAM "	:: "[idts, 'a => 'b] => ('a -> 'b)"
					("(3\<Lambda>_./ _)" [0, 10] 10)
  Rep_CFun      :: "('a -> 'b) => ('a => 'b)"  ("(_\<cdot>_)" [999,1000] 999)

syntax (HTML output)
  Rep_CFun      :: "('a -> 'b) => ('a => 'b)"  ("(_\<cdot>_)" [999,1000] 999)

defs (overloaded)
  less_cfun_def: "(op <<) == (% fo1 fo2. Rep_CFun fo1 << Rep_CFun fo2 )"

(*  Title:      HOLCF/Cfun1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The type ->  of continuous functions.
*)

(* ------------------------------------------------------------------------ *)
(* derive old type definition rules for Abs_CFun & Rep_CFun
    *)
(* Rep_CFun and Abs_CFun should be replaced by Rep_Cfun anf Abs_Cfun in future
    *)
(* ------------------------------------------------------------------------ *)

lemma Rep_Cfun: "Rep_CFun fo : CFun"
apply (rule Rep_CFun)
done

lemma Rep_Cfun_inverse: "Abs_CFun (Rep_CFun fo) = fo"
apply (rule Rep_CFun_inverse)
done

lemma Abs_Cfun_inverse: "f:CFun==>Rep_CFun(Abs_CFun f)=f"
apply (erule Abs_CFun_inverse)
done

(* ------------------------------------------------------------------------ *)
(* less_cfun is a partial order on type 'a -> 'b                            *)
(* ------------------------------------------------------------------------ *)

lemma refl_less_cfun: "(f::'a->'b) << f"

apply (unfold less_cfun_def)
apply (rule refl_less)
done

lemma antisym_less_cfun: 
        "[|(f1::'a->'b) << f2; f2 << f1|] ==> f1 = f2"
apply (unfold less_cfun_def)
apply (rule injD)
apply (rule_tac [2] antisym_less)
prefer 3 apply (assumption)
prefer 2 apply (assumption)
apply (rule inj_on_inverseI)
apply (rule Rep_Cfun_inverse)
done

lemma trans_less_cfun: 
        "[|(f1::'a->'b) << f2; f2 << f3|] ==> f1 << f3"
apply (unfold less_cfun_def)
apply (erule trans_less)
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* lemmas about application of continuous functions                         *)
(* ------------------------------------------------------------------------ *)

lemma cfun_cong: "[| f=g; x=y |] ==> f$x = g$y"
apply (simp (no_asm_simp))
done

lemma cfun_fun_cong: "f=g ==> f$x = g$x"
apply (simp (no_asm_simp))
done

lemma cfun_arg_cong: "x=y ==> f$x = f$y"
apply (simp (no_asm_simp))
done


(* ------------------------------------------------------------------------ *)
(* additional lemma about the isomorphism between -> and Cfun               *)
(* ------------------------------------------------------------------------ *)

lemma Abs_Cfun_inverse2: "cont f ==> Rep_CFun (Abs_CFun f) = f"
apply (rule Abs_Cfun_inverse)
apply (unfold CFun_def)
apply (erule mem_Collect_eq [THEN ssubst])
done

(* ------------------------------------------------------------------------ *)
(* simplification of application                                            *)
(* ------------------------------------------------------------------------ *)

lemma Cfunapp2: "cont f ==> (Abs_CFun f)$x = f x"
apply (erule Abs_Cfun_inverse2 [THEN fun_cong])
done

(* ------------------------------------------------------------------------ *)
(* beta - equality for continuous functions                                 *)
(* ------------------------------------------------------------------------ *)

lemma beta_cfun: "cont(c1) ==> (LAM x .c1 x)$u = c1 u"
apply (rule Cfunapp2)
apply assumption
done

end
