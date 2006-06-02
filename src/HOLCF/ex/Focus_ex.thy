(* $Id$ *)

(* Specification of the following loop back device


          g
           --------------------
          |      -------       |
       x  |     |       |      |  y
    ------|---->|       |------| ----->
          |  z  |   f   | z    |
          |  -->|       |---   |
          | |   |       |   |  |
          | |    -------    |  |
          | |               |  |
          |  <--------------   |
          |                    |
           --------------------


First step: Notation in Agent Network Description Language (ANDL)
-----------------------------------------------------------------

agent f
        input  channel i1:'b i2: ('b,'c) tc
        output channel o1:'c o2: ('b,'c) tc
is
        Rf(i1,i2,o1,o2)  (left open in the example)
end f

agent g
        input  channel x:'b
        output channel y:'c
is network
        <y,z> = f$<x,z>
end network
end g


Remark: the type of the feedback depends at most on the types of the input and
        output of g. (No type miracles inside g)

Second step: Translation of ANDL specification to HOLCF Specification
---------------------------------------------------------------------

Specification of agent f ist translated to predicate is_f

is_f :: ('b stream * ('b,'c) tc stream ->
                'c stream * ('b,'c) tc stream) => bool

is_f f  = !i1 i2 o1 o2.
        f$<i1,i2> = <o1,o2> --> Rf(i1,i2,o1,o2)

Specification of agent g is translated to predicate is_g which uses
predicate is_net_g

is_net_g :: ('b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream) =>
            'b stream => 'c stream => bool

is_net_g f x y =
        ? z. <y,z> = f$<x,z> &
        !oy hz. <oy,hz> = f$<x,hz> --> z << hz


is_g :: ('b stream -> 'c stream) => bool

is_g g  = ? f. is_f f  & (!x y. g$x = y --> is_net_g f x y

Third step: (show conservativity)
-----------

Suppose we have a model for the theory TH1 which contains the axiom

        ? f. is_f f

In this case there is also a model for the theory TH2 that enriches TH1 by
axiom

        ? g. is_g g

The result is proved by showing that there is a definitional extension
that extends TH1 by a definition of g.


We define:

def_g g  =
         (? f. is_f f  &
              g = (LAM x. cfst$(f$<x,fix$(LAM k.csnd$(f$<x,k>))>)) )

Now we prove:

        (? f. is_f f ) --> (? g. is_g g)

using the theorems

loopback_eq)    def_g = is_g                    (real work)

L1)             (? f. is_f f ) --> (? g. def_g g)  (trivial)

*)

theory Focus_ex
imports Stream
begin

typedecl ('a, 'b) tc
arities tc:: (pcpo, pcpo) pcpo

consts
  Rf :: "('b stream * ('b,'c) tc stream * 'c stream * ('b,'c) tc stream) => bool"

definition
  is_f :: "('b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream) => bool"
  "is_f f = (!i1 i2 o1 o2. f$<i1,i2> = <o1,o2> --> Rf(i1,i2,o1,o2))"

  is_net_g :: "('b stream *('b,'c) tc stream -> 'c stream * ('b,'c) tc stream) =>
    'b stream => 'c stream => bool"
  "is_net_g f x y == (? z.
                        <y,z> = f$<x,z> &
                        (!oy hz. <oy,hz> = f$<x,hz> --> z << hz))"

  is_g :: "('b stream -> 'c stream) => bool"
  "is_g g  == (? f. is_f f  & (!x y. g$x = y --> is_net_g f x y))"

  def_g :: "('b stream -> 'c stream) => bool"
  "def_g g == (? f. is_f f  & g = (LAM x. cfst$(f$<x,fix$(LAM  k. csnd$(f$<x,k>))>)))"


(* first some logical trading *)

lemma lemma1:
"is_g(g) =
  (? f. is_f(f) &  (!x.(? z. <g$x,z> = f$<x,z> &
                   (! w y. <y,w> = f$<x,w>  --> z << w))))"
apply (simp add: is_g_def is_net_g_def)
apply fast
done

lemma lemma2:
"(? f. is_f(f) &  (!x. (? z. <g$x,z> = f$<x,z> &
                  (!w y. <y,w> = f$<x,w>  --> z << w))))
  =
  (? f. is_f(f) &  (!x. ? z.
        g$x = cfst$(f$<x,z>) &
          z = csnd$(f$<x,z>) &
        (! w y.  <y,w> = f$<x,w> --> z << w)))"
apply (rule iffI)
apply (erule exE)
apply (rule_tac x = "f" in exI)
apply (erule conjE)+
apply (erule conjI)
apply (intro strip)
apply (erule allE)
apply (erule exE)
apply (rule_tac x = "z" in exI)
apply (erule conjE)+
apply (rule conjI)
apply (rule_tac [2] conjI)
prefer 3 apply (assumption)
apply (drule sym)
apply (tactic "asm_simp_tac HOLCF_ss 1")
apply (drule sym)
apply (tactic "asm_simp_tac HOLCF_ss 1")
apply (erule exE)
apply (rule_tac x = "f" in exI)
apply (erule conjE)+
apply (erule conjI)
apply (intro strip)
apply (erule allE)
apply (erule exE)
apply (rule_tac x = "z" in exI)
apply (erule conjE)+
apply (rule conjI)
prefer 2 apply (assumption)
apply (rule trans)
apply (rule_tac [2] surjective_pairing_Cprod2)
apply (erule subst)
apply (erule subst)
apply (rule refl)
done

lemma lemma3: "def_g(g) --> is_g(g)"
apply (tactic {* simp_tac (HOL_ss addsimps [thm "def_g_def", thm "lemma1", thm "lemma2"]) 1 *})
apply (rule impI)
apply (erule exE)
apply (rule_tac x = "f" in exI)
apply (erule conjE)+
apply (erule conjI)
apply (intro strip)
apply (rule_tac x = "fix$ (LAM k. csnd$ (f$<x,k>))" in exI)
apply (rule conjI)
 apply (tactic "asm_simp_tac HOLCF_ss 1")
 apply (rule trans)
  apply (rule_tac [2] surjective_pairing_Cprod2)
 apply (rule cfun_arg_cong)
 apply (rule trans)
  apply (rule fix_eq)
 apply (simp (no_asm))
apply (intro strip)
apply (rule fix_least)
apply (simp (no_asm))
apply (erule exE)
apply (drule sym)
back
apply simp
done

lemma lemma4: "is_g(g) --> def_g(g)"
apply (tactic {* simp_tac (HOL_ss delsimps (thms "ex_simps" @ thms "all_simps")
  addsimps [thm "lemma1", thm "lemma2", thm "def_g_def"]) 1 *})
apply (rule impI)
apply (erule exE)
apply (rule_tac x = "f" in exI)
apply (erule conjE)+
apply (erule conjI)
apply (rule ext_cfun)
apply (erule_tac x = "x" in allE)
apply (erule exE)
apply (erule conjE)+
apply (subgoal_tac "fix$ (LAM k. csnd$ (f$<x, k>)) = z")
 apply simp
apply (subgoal_tac "! w y. f$<x, w> = <y, w> --> z << w")
apply (rule sym)
apply (rule fix_eqI)
apply simp
apply (rule allI)
apply (tactic "simp_tac HOLCF_ss 1")
apply (intro strip)
apply (subgoal_tac "f$<x, za> = <cfst$ (f$<x,za>) ,za>")
apply fast
apply (rule trans)
apply (rule surjective_pairing_Cprod2 [symmetric])
apply (erule cfun_arg_cong)
apply (intro strip)
apply (erule allE)+
apply (erule mp)
apply (erule sym)
done

(* now we assemble the result *)

lemma loopback_eq: "def_g = is_g"
apply (rule ext)
apply (rule iffI)
apply (erule lemma3 [THEN mp])
apply (erule lemma4 [THEN mp])
done

lemma L2:
"(? f.
  is_f(f::'b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream))
  -->
  (? g. def_g(g::'b stream -> 'c stream ))"
apply (simp add: def_g_def)
done

theorem conservative_loopback:
"(? f.
  is_f(f::'b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream))
  -->
  (? g. is_g(g::'b stream -> 'c stream ))"
apply (rule loopback_eq [THEN subst])
apply (rule L2)
done

end
