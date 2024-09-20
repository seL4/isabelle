(*  Title:      HOL/NanoJava/Term.thy
    Author:     David von Oheimb, Technische Universitaet Muenchen
*)

section "Statements and expression emulations"

theory Term imports Main begin

typedecl cname  \<comment> \<open>class    name\<close>
typedecl mname  \<comment> \<open>method   name\<close>
typedecl fname  \<comment> \<open>field    name\<close>
typedecl vname  \<comment> \<open>variable name\<close>

axiomatization
  This \<comment> \<open>This pointer\<close>
  Par  \<comment> \<open>method parameter\<close>
  Res  :: vname \<comment> \<open>method result\<close>
 \<comment> \<open>Inequality axioms are not required for the meta theory.\<close>
(*
where
  This_neq_Par [simp]: "This \<noteq> Par"
  Par_neq_Res  [simp]: "Par \<noteq> Res"
  Res_neq_This [simp]: "Res \<noteq> This"
*)

datatype stmt
  = Skip                   \<comment> \<open>empty statement\<close>
  | Comp       stmt stmt   (\<open>_;; _\<close>             [91,90   ] 90)
  | Cond expr  stmt stmt   (\<open>If '(_') _ Else _\<close> [ 3,91,91] 91)
  | Loop vname stmt        (\<open>While '(_') _\<close>     [ 3,91   ] 91)
  | LAss vname expr        (\<open>_ :== _\<close>           [99,   95] 94) \<comment> \<open>local assignment\<close>
  | FAss expr  fname expr  (\<open>_.._:==_\<close>          [95,99,95] 94) \<comment> \<open>field assignment\<close>
  | Meth "cname \<times> mname"   \<comment> \<open>virtual method\<close>
  | Impl "cname \<times> mname"   \<comment> \<open>method implementation\<close>
and expr
  = NewC cname       (\<open>new _\<close>        [   99] 95) \<comment> \<open>object creation\<close>
  | Cast cname expr                              \<comment> \<open>type cast\<close>
  | LAcc vname                                   \<comment> \<open>local access\<close>
  | FAcc expr  fname (\<open>_.._\<close>         [95,99] 95) \<comment> \<open>field access\<close>
  | Call cname expr mname expr                   
                     (\<open>{_}_.._'(_')\<close> [99,95,99,95] 95) \<comment> \<open>method call\<close>

end

