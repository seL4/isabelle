(*  Title:      HOL/Hoare/Separation.thy
    Author:     Tobias Nipkow
    Copyright   2003 TUM

A first attempt at a nice syntactic embedding of separation logic.
Already builds on the theory for list abstractions.

If we suppress the H parameter for "List", we have to hardwired this
into parser and pretty printer, which is not very modular.
Alternative: some syntax like <P> which stands for P H. No more
compact, but avoids the funny H.
*)

section \<open>Separation logic\<close>

theory Separation
  imports Hoare_Logic_Abort SepLogHeap
begin

text\<open>The semantic definition of a few connectives:\<close>

definition ortho :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 55)
  where "h1 \<bottom> h2 \<longleftrightarrow> dom h1 \<inter> dom h2 = {}"

definition is_empty :: "heap \<Rightarrow> bool"
  where "is_empty h \<longleftrightarrow> h = Map.empty"

definition singl:: "heap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "singl h x y \<longleftrightarrow> dom h = {x} & h x = Some y"

definition star:: "(heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool)"
  where "star P Q = (\<lambda>h. \<exists>h1 h2. h = h1++h2 \<and> h1 \<bottom> h2 \<and> P h1 \<and> Q h2)"

definition wand:: "(heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool)"
  where "wand P Q = (\<lambda>h. \<forall>h'. h' \<bottom> h \<and> P h' \<longrightarrow> Q(h++h'))"

text\<open>This is what assertions look like without any syntactic sugar:\<close>

lemma "VARS x y z w h
 {star (%h. singl h x y) (%h. singl h z w) h}
 SKIP
 {x \<noteq> z}"
apply vcg
apply(auto simp:star_def ortho_def singl_def)
done

text\<open>Now we add nice input syntax.  To suppress the heap parameter
of the connectives, we assume it is always called H and add/remove it
upon parsing/printing. Thus every pointer program needs to have a
program variable H, and assertions should not contain any locally
bound Hs - otherwise they may bind the implicit H.\<close>

syntax
 "_emp" :: "bool" ("emp")
 "_singl" :: "nat \<Rightarrow> nat \<Rightarrow> bool" ("[_ \<mapsto> _]")
 "_star" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "**" 60)
 "_wand" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "-*" 60)

(* FIXME does not handle "_idtdummy" *)
ML \<open>
\<comment> \<open>\<open>free_tr\<close> takes care of free vars in the scope of separation logic connectives:
    they are implicitly applied to the heap\<close>
fun free_tr(t as Free _) = t $ Syntax.free "H"
\<^cancel>\<open>| free_tr((list as Free("List",_))$ p $ ps) = list $ Syntax.free "H" $ p $ ps\<close>
  | free_tr t = t

fun emp_tr [] = Syntax.const \<^const_syntax>\<open>is_empty\<close> $ Syntax.free "H"
  | emp_tr ts = raise TERM ("emp_tr", ts);
fun singl_tr [p, q] = Syntax.const \<^const_syntax>\<open>singl\<close> $ Syntax.free "H" $ p $ q
  | singl_tr ts = raise TERM ("singl_tr", ts);
fun star_tr [P,Q] = Syntax.const \<^const_syntax>\<open>star\<close> $
      absfree ("H", dummyT) (free_tr P) $ absfree ("H", dummyT) (free_tr Q) $
      Syntax.free "H"
  | star_tr ts = raise TERM ("star_tr", ts);
fun wand_tr [P, Q] = Syntax.const \<^const_syntax>\<open>wand\<close> $
      absfree ("H", dummyT) P $ absfree ("H", dummyT) Q $ Syntax.free "H"
  | wand_tr ts = raise TERM ("wand_tr", ts);
\<close>

parse_translation \<open>
 [(\<^syntax_const>\<open>_emp\<close>, K emp_tr),
  (\<^syntax_const>\<open>_singl\<close>, K singl_tr),
  (\<^syntax_const>\<open>_star\<close>, K star_tr),
  (\<^syntax_const>\<open>_wand\<close>, K wand_tr)]
\<close>

text\<open>Now it looks much better:\<close>

lemma "VARS H x y z w
 {[x\<mapsto>y] ** [z\<mapsto>w]}
 SKIP
 {x \<noteq> z}"
apply vcg
apply(auto simp:star_def ortho_def singl_def)
done

lemma "VARS H x y z w
 {emp ** emp}
 SKIP
 {emp}"
apply vcg
apply(auto simp:star_def ortho_def is_empty_def)
done

text\<open>But the output is still unreadable. Thus we also strip the heap
parameters upon output:\<close>

ML \<open>
local

fun strip (Abs(_,_,(t as Const("_free",_) $ Free _) $ Bound 0)) = t
  | strip (Abs(_,_,(t as Free _) $ Bound 0)) = t
\<^cancel>\<open>| strip (Abs(_,_,((list as Const("List",_))$ Bound 0 $ p $ ps))) = list$p$ps\<close>
  | strip (Abs(_,_,(t as Const("_var",_) $ Var _) $ Bound 0)) = t
  | strip (Abs(_,_,P)) = P
  | strip (Const(\<^const_syntax>\<open>is_empty\<close>,_)) = Syntax.const \<^syntax_const>\<open>_emp\<close>
  | strip t = t;

in

fun is_empty_tr' [_] = Syntax.const \<^syntax_const>\<open>_emp\<close>
fun singl_tr' [_,p,q] = Syntax.const \<^syntax_const>\<open>_singl\<close> $ p $ q
fun star_tr' [P,Q,_] = Syntax.const \<^syntax_const>\<open>_star\<close> $ strip P $ strip Q
fun wand_tr' [P,Q,_] = Syntax.const \<^syntax_const>\<open>_wand\<close> $ strip P $ strip Q

end
\<close>

print_translation \<open>
 [(\<^const_syntax>\<open>is_empty\<close>, K is_empty_tr'),
  (\<^const_syntax>\<open>singl\<close>, K singl_tr'),
  (\<^const_syntax>\<open>star\<close>, K star_tr'),
  (\<^const_syntax>\<open>wand\<close>, K wand_tr')]
\<close>

text\<open>Now the intermediate proof states are also readable:\<close>

lemma "VARS H x y z w
 {[x\<mapsto>y] ** [z\<mapsto>w]}
 y := w
 {x \<noteq> z}"
apply vcg
apply(auto simp:star_def ortho_def singl_def)
done

lemma "VARS H x y z w
 {emp ** emp}
 SKIP
 {emp}"
apply vcg
apply(auto simp:star_def ortho_def is_empty_def)
done

text\<open>So far we have unfolded the separation logic connectives in
proofs. Here comes a simple example of a program proof that uses a law
of separation logic instead.\<close>

\<comment> \<open>a law of separation logic\<close>
lemma star_comm: "P ** Q = Q ** P"
  by(auto simp add:star_def ortho_def dest: map_add_comm)

lemma "VARS H x y z w
 {P ** Q}
 SKIP
 {Q ** P}"
apply vcg
apply(simp add: star_comm)
done


lemma "VARS H
 {p\<noteq>0 \<and> [p \<mapsto> x] ** List H q qs}
 H := H(p \<mapsto> q)
 {List H p (p#qs)}"
apply vcg
apply(simp add: star_def ortho_def singl_def)
apply clarify
apply(subgoal_tac "p \<notin> set qs")
 prefer 2
 apply(blast dest:list_in_heap)
apply simp
done

lemma "VARS H p q r
  {List H p Ps ** List H q Qs}
  WHILE p \<noteq> 0
  INV {\<exists>ps qs. (List H p ps ** List H q qs) \<and> rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := the(H p); H := H(r \<mapsto> q); q := r OD
  {List H q (rev Ps @ Qs)}"
apply vcg
apply(simp_all add: star_def ortho_def singl_def)

apply fastforce

apply (clarsimp simp add:List_non_null)
apply(rename_tac ps')
apply(rule_tac x = ps' in exI)
apply(rule_tac x = "p#qs" in exI)
apply simp
apply(rule_tac x = "h1(p:=None)" in exI)
apply(rule_tac x = "h2(p\<mapsto>q)" in exI)
apply simp
apply(rule conjI)
 apply(rule ext)
 apply(simp add:map_add_def split:option.split)
apply(rule conjI)
 apply blast
apply(simp add:map_add_def split:option.split)
apply(rule conjI)
apply(subgoal_tac "p \<notin> set qs")
 prefer 2
 apply(blast dest:list_in_heap)
apply(simp)
apply fast

apply(fastforce)
done

end
