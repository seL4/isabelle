(*  Title:      HOLCF/cfun1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Definition of the type ->  of continuous functions

*)

Cfun1 = Cont +

typedef (CFun)  ('a, 'b) "->" (infixr 0) = "{f. cont f}" (CfunI)

consts  
        fapp      :: "('a -> 'b)=>('a => 'b)"   (* usually Rep_Cfun *)
                                                (* application      *)
        fabs      :: "('a => 'b)=>('a -> 'b)"     (binder "LAM " 10)
                                                (* usually Abs_Cfun *)
                                                (* abstraction      *)
        less_cfun :: "[('a -> 'b),('a -> 'b)]=>bool"

syntax  "@fapp"   :: "('a -> 'b)=>('a => 'b)" ("_`_" [999,1000] 999)

translations "f`x" == "fapp f x"

syntax (symbols)
  "->"		:: [type, type] => type	("(_ \\<rightarrow>/ _)" [6,5]5)
  "LAM "	:: "[idts, 'a => 'b] => ('a -> 'b)"
					("(3\\<Lambda>_./ _)" [0, 10] 10)
defs 
  fabs_def	"fabs==Abs_CFun"
  fapp_def	"fapp==Rep_CFun"

  less_cfun_def "less == (% fo1 fo2. fapp fo1 << fapp fo2 )"

end
