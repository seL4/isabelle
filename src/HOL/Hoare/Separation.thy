(*  Title:      HOL/Hoare/Separation.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2003 TUM

A first attempt at a nice syntactic embedding of separation logic.
*)

theory Separation = HoareAbort:

types heap = "(nat \<Rightarrow> nat option)"

text{* The semantic definition of a few connectives: *}

constdefs
 ortho:: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 55)
"h1 \<bottom> h2 == dom h1 \<inter> dom h2 = {}"

 is_empty :: "heap \<Rightarrow> bool"
"is_empty h == h = empty"

 singl:: "heap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
"singl h x y == dom h = {x} & h x = Some y"

 star:: "(heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool)"
"star P Q == \<lambda>h. \<exists>h1 h2. h = h1++h2 \<and> h1 \<bottom> h2 \<and> P h1 \<and> Q h2"

 wand:: "(heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool)"
"wand P Q == \<lambda>h. \<forall>h'. h' \<bottom> h \<and> P h' \<longrightarrow> Q(h++h')"

text{*This is what assertions look like without any syntactic sugar: *}

lemma "VARS x y z w h
 {star (%h. singl h x y) (%h. singl h z w) h}
 SKIP
 {x \<noteq> z}"
apply vcg
apply(auto simp:star_def ortho_def singl_def)
done

text{* Now we add nice input syntax.  To suppress the heap parameter
of the connectives, we assume it is always called H and add/remove it
upon parsing/printing. Thus every pointer program needs to have a
program variable H, and assertions should not contain any locally
bound Hs - otherwise they may bind the implicit H. *}

syntax
 "@emp" :: "bool" ("emp")
 "@singl" :: "nat \<Rightarrow> nat \<Rightarrow> bool" ("[_ \<mapsto> _]")
 "@star" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "**" 60)
 "@wand" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "-*" 60)

ML{*
(* free_tr takes care of free vars in the scope of sep. logic connectives:
   they are implicitly applied to the heap *)
fun free_tr(t as Free _) = t $ Syntax.free "H"
  | free_tr t = t

fun emp_tr [] = Syntax.const "is_empty" $ Syntax.free "H"
  | emp_tr ts = raise TERM ("emp_tr", ts);
fun singl_tr [p,q] = Syntax.const "singl" $ Syntax.free "H" $ p $ q
  | singl_tr ts = raise TERM ("singl_tr", ts);
fun star_tr [P,Q] = Syntax.const "star" $
      absfree("H",dummyT,free_tr P) $ absfree("H",dummyT,free_tr Q) $
      Syntax.free "H"
  | star_tr ts = raise TERM ("star_tr", ts);
fun wand_tr [P,Q] = Syntax.const "wand" $
      absfree("H",dummyT,P) $ absfree("H",dummyT,Q) $ Syntax.free "H"
  | wand_tr ts = raise TERM ("wand_tr", ts);
*}

parse_translation
 {* [("@emp", emp_tr), ("@singl", singl_tr),
     ("@star", star_tr), ("@wand", wand_tr)] *}

text{* Now it looks much better: *}

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

text{* But the output is still unreadable. Thus we also strip the heap
parameters upon output: *}

(* debugging code:
fun sot(Free(s,_)) = s
  | sot(Var((s,i),_)) = "?" ^ s ^ string_of_int i
  | sot(Const(s,_)) = s
  | sot(Bound i) = "B." ^ string_of_int i
  | sot(s $ t) = "(" ^ sot s ^ " " ^ sot t ^ ")"
  | sot(Abs(_,_,t)) = "(% " ^ sot t ^ ")";
*)

ML{*
local
fun strip (Abs(_,_,(t as Const("_free",_) $ Free _) $ Bound 0)) = t
  | strip (Abs(_,_,(t as Free _) $ Bound 0)) = t
  | strip (Abs(_,_,(t as Const("_var",_) $ Var _) $ Bound 0)) = t
  | strip (Abs(_,_,P)) = P
  | strip (Const("is_empty",_)) = Syntax.const "@emp"
  | strip t = t;
in
fun is_empty_tr' [_] = Syntax.const "@emp"
fun singl_tr' [_,p,q] = Syntax.const "@singl" $ p $ q
fun star_tr' [P,Q,_] = Syntax.const "@star" $ strip P $ strip Q
fun wand_tr' [P,Q,_] = Syntax.const "@wand" $ strip P $ strip Q
end
*}

print_translation
 {* [("is_empty", is_empty_tr'),("singl", singl_tr'),
     ("star", star_tr'),("wand", wand_tr')] *}

text{* Now the intermediate proof states are also readable: *}

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

text{* So far we have unfolded the separation logic connectives in
proofs. Here comes a simple example of a program proof that uses a law
of separation logic instead. *}

(* move to Map.thy *)
lemma override_comm: "dom m1 \<inter> dom m2 = {} \<Longrightarrow> m1++m2 = m2++m1"
apply(rule ext)
apply(fastsimp simp:override_def split:option.split)
done

(* a law of separation logic *)
lemma star_comm: "P ** Q = Q ** P"
apply(simp add:star_def ortho_def)
apply(blast intro:override_comm)
done

lemma "VARS H x y z w
 {P ** Q}
 SKIP
 {Q ** P}"
apply vcg
apply(simp add: star_comm)
done

end
