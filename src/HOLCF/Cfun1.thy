(*  Title:      HOLCF/Cfun1.thy
    ID:         $Id$
    Author:     Franz Regensburger

Definition of the type ->  of continuous functions.

*)

Cfun1 = Cont +

default cpo

typedef (CFun)  ('a, 'b) "->" (infixr 0) = "{f::'a => 'b. cont f}" (CfunI)

(* to make << defineable *)
instance "->"  :: (cpo,cpo)sq_ord

syntax
	Rep_CFun  :: "('a -> 'b) => ('a => 'b)" ("_$_" [999,1000] 999)
                                                (* application      *)
        Abs_CFun  :: "('a => 'b) => ('a -> 'b)" (binder "LAM " 10)
                                                (* abstraction      *)
        less_cfun :: "[('a -> 'b),('a -> 'b)]=>bool"

syntax (xsymbols)
  "->"		:: [type, type] => type	("(_ \\<rightarrow>/ _)" [1,0]0)
  "LAM "	:: "[idts, 'a => 'b] => ('a -> 'b)"
					("(3\\<Lambda>_./ _)" [0, 10] 10)
  Rep_CFun      :: "('a -> 'b) => ('a => 'b)"  ("(_\\<cdot>_)" [999,1000] 999)

syntax (HTML output)
  Rep_CFun      :: "('a -> 'b) => ('a => 'b)"  ("(_\\<cdot>_)" [999,1000] 999)

defs 
  less_cfun_def "(op <<) == (% fo1 fo2. Rep_CFun fo1 << Rep_CFun fo2 )"

end
