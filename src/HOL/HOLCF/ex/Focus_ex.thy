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
        (y,z) = f$(x,z)
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
        f$(i1,i2) = (o1,o2) --> Rf(i1,i2,o1,o2)

Specification of agent g is translated to predicate is_g which uses
predicate is_net_g

is_net_g :: ('b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream) =>
            'b stream => 'c stream => bool

is_net_g f x y =
        ? z. (y,z) = f$(x,z) &
        !oy hz. (oy,hz) = f$(x,hz) --> z << hz


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
              g = (LAM x. fst (f$(x,fix$(LAM k. snd (f$(x,k)))))) )

Now we prove:

        (? f. is_f f ) --> (? g. is_g g)

using the theorems

loopback_eq)    def_g = is_g                    (real work)

L1)             (? f. is_f f ) --> (? g. def_g g)  (trivial)

*)

theory Focus_ex
imports "HOLCF-Library.Stream"
begin

typedecl ('a, 'b) tc
axiomatization where tc_arity: "OFCLASS(('a::pcpo, 'b::pcpo) tc, pcop_class)"
instance tc :: (pcpo, pcpo) pcpo by (rule tc_arity)

axiomatization
  Rf :: "('b stream * ('b,'c) tc stream * 'c stream * ('b,'c) tc stream) \<Rightarrow> bool"

definition
  is_f :: "('b stream * ('b,'c) tc stream \<rightarrow> 'c stream * ('b,'c) tc stream) \<Rightarrow> bool" where
  "is_f f \<longleftrightarrow> (\<forall>i1 i2 o1 o2. f\<cdot>(i1, i2) = (o1, o2) \<longrightarrow> Rf (i1, i2, o1, o2))"

definition
  is_net_g :: "('b stream * ('b,'c) tc stream \<rightarrow> 'c stream * ('b,'c) tc stream) \<Rightarrow>
    'b stream \<Rightarrow> 'c stream \<Rightarrow> bool" where
  "is_net_g f x y \<equiv> (\<exists>z.
                        (y, z) = f\<cdot>(x,z) \<and>
                        (\<forall>oy hz. (oy, hz) = f\<cdot>(x, hz) \<longrightarrow> z << hz))"

definition
  is_g :: "('b stream \<rightarrow> 'c stream) \<Rightarrow> bool" where
  "is_g g \<equiv> (\<exists>f. is_f f \<and> (\<forall>x y. g\<cdot>x = y \<longrightarrow> is_net_g f x y))"

definition
  def_g :: "('b stream \<rightarrow> 'c stream) => bool" where
  "def_g g \<equiv> (\<exists>f. is_f f \<and> g = (LAM x. fst (f\<cdot>(x, fix\<cdot>(LAM  k. snd (f\<cdot>(x, k)))))))"


(* first some logical trading *)

lemma lemma1:
  "is_g g \<longleftrightarrow>
    (\<exists>f. is_f(f) \<and> (\<forall>x.(\<exists>z. (g\<cdot>x,z) = f\<cdot>(x,z) \<and> (\<forall>w y. (y, w) = f\<cdot>(x, w) \<longrightarrow> z << w))))"
apply (simp add: is_g_def is_net_g_def)
apply fast
done

lemma lemma2:
  "(\<exists>f. is_f f \<and> (\<forall>x. (\<exists>z. (g\<cdot>x, z) = f\<cdot>(x, z) \<and> (\<forall>w y. (y, w) = f\<cdot>(x,w) \<longrightarrow> z << w)))) \<longleftrightarrow>
  (\<exists>f. is_f f \<and> (\<forall>x. \<exists>z.
        g\<cdot>x = fst (f\<cdot>(x, z)) \<and>
          z = snd (f\<cdot>(x, z)) \<and>
        (\<forall>w y. (y, w) = f\<cdot>(x, w) \<longrightarrow> z << w)))"
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
apply (simp)
apply (drule sym)
apply (simp)
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
apply (rule prod_eqI)
apply simp
apply simp
done

lemma lemma3: "def_g g \<longrightarrow> is_g g"
apply (tactic \<open>simp_tac (put_simpset HOL_ss \<^context>
  addsimps [@{thm def_g_def}, @{thm lemma1}, @{thm lemma2}]) 1\<close>)
apply (rule impI)
apply (erule exE)
apply (rule_tac x = "f" in exI)
apply (erule conjE)+
apply (erule conjI)
apply (intro strip)
apply (rule_tac x = "fix\<cdot>(LAM k. snd (f\<cdot>(x, k)))" in exI)
apply (rule conjI)
 apply (simp)
 apply (rule prod_eqI, simp, simp)
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

lemma lemma4: "is_g g \<longrightarrow> def_g g"
apply (tactic \<open>simp_tac (\<^context> |> put_simpset HOL_ss
  |> Simplifier.del_simps @{thms HOL.ex_simps HOL.all_simps}
  |> Simplifier.add_simps @{thms lemma1 lemma2 def_g_def}) 1\<close>)
apply (rule impI)
apply (erule exE)
apply (rule_tac x = "f" in exI)
apply (erule conjE)+
apply (erule conjI)
apply (rule cfun_eqI)
apply (erule_tac x = "x" in allE)
apply (erule exE)
apply (erule conjE)+
apply (subgoal_tac "fix\<cdot>(LAM k. snd (f\<cdot>(x, k))) = z")
 apply simp
apply (subgoal_tac "\<forall>w y. f\<cdot>(x, w) = (y, w) \<longrightarrow> z << w")
apply (rule fix_eqI)
apply simp
apply (subgoal_tac "f\<cdot>(x, za) = (fst (f\<cdot>(x, za)), za)")
apply fast
apply (rule prod_eqI, simp, simp)
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
  "(\<exists>f. is_f (f::'b stream * ('b,'c) tc stream \<rightarrow> 'c stream * ('b,'c) tc stream)) \<longrightarrow>
    (\<exists>g. def_g (g::'b stream \<rightarrow> 'c stream))"
apply (simp add: def_g_def)
done

theorem conservative_loopback:
  "(\<exists>f. is_f (f::'b stream * ('b,'c) tc stream \<rightarrow> 'c stream * ('b,'c) tc stream)) \<longrightarrow>
    (\<exists>g. is_g (g::'b stream \<rightarrow> 'c stream))"
apply (rule loopback_eq [THEN subst])
apply (rule L2)
done

end
