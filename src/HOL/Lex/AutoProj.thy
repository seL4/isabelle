(*  Title:      HOL/Lex/AutoProj.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Is there an optimal order of arguments for `next'?
Currently we can have laws like `delta A (a#w) = delta A w o delta A a'
Otherwise we could have `acceps A == fin A o delta A (start A)'
and use foldl instead of foldl2.
*)

theory AutoProj = Main:

constdefs
 start :: "'a * 'b * 'c => 'a"
"start A == fst A"
 "next" :: "'a * 'b * 'c => 'b"
"next A == fst(snd(A))"
 fin :: "'a * 'b * 'c => 'c"
"fin A == snd(snd(A))"

lemma [simp]: "start(q,d,f) = q"
by(simp add:start_def)

lemma [simp]: "next(q,d,f) = d"
by(simp add:next_def)

lemma [simp]: "fin(q,d,f) = f"
by(simp add:fin_def)

end
