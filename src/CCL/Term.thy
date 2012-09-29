(*  Title:      CCL/Term.thy
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

header {* Definitions of usual program constructs in CCL *}

theory Term
imports CCL
begin

consts

  one        :: "i"

  "if"       :: "[i,i,i]=>i"           ("(3if _/ then _/ else _)" [0,0,60] 60)

  inl        :: "i=>i"
  inr        :: "i=>i"
  when       :: "[i,i=>i,i=>i]=>i"

  split      :: "[i,[i,i]=>i]=>i"
  fst        :: "i=>i"
  snd        :: "i=>i"
  thd        :: "i=>i"

  zero       :: "i"
  succ       :: "i=>i"
  ncase      :: "[i,i,i=>i]=>i"
  nrec       :: "[i,i,[i,i]=>i]=>i"

  nil        :: "i"                        ("([])")
  cons       :: "[i,i]=>i"                 (infixr "$" 80)
  lcase      :: "[i,i,[i,i]=>i]=>i"
  lrec       :: "[i,i,[i,i,i]=>i]=>i"

  "let"      :: "[i,i=>i]=>i"
  letrec     :: "[[i,i=>i]=>i,(i=>i)=>i]=>i"
  letrec2    :: "[[i,i,i=>i=>i]=>i,(i=>i=>i)=>i]=>i"
  letrec3    :: "[[i,i,i,i=>i=>i=>i]=>i,(i=>i=>i=>i)=>i]=>i"

syntax
  "_let"     :: "[id,i,i]=>i"             ("(3let _ be _/ in _)"
                        [0,0,60] 60)

  "_letrec"  :: "[id,id,i,i]=>i"         ("(3letrec _ _ be _/ in _)"
                        [0,0,0,60] 60)

  "_letrec2" :: "[id,id,id,i,i]=>i"     ("(3letrec _ _ _ be _/ in _)"
                        [0,0,0,0,60] 60)

  "_letrec3" :: "[id,id,id,id,i,i]=>i" ("(3letrec _ _ _ _ be _/ in _)"
                        [0,0,0,0,0,60] 60)

ML {*
(** Quantifier translations: variable binding **)

(* FIXME does not handle "_idtdummy" *)
(* FIXME should use Syntax_Trans.mark_bound, Syntax_Trans.variant_abs' *)

fun let_tr [Free x, a, b] = Const(@{const_syntax let},dummyT) $ a $ absfree x b;
fun let_tr' [a,Abs(id,T,b)] =
     let val (id',b') = Syntax_Trans.variant_abs(id,T,b)
     in Const(@{syntax_const "_let"},dummyT) $ Free(id',T) $ a $ b' end;

fun letrec_tr [Free f, Free x, a, b] =
      Const(@{const_syntax letrec}, dummyT) $ absfree x (absfree f a) $ absfree f b;
fun letrec2_tr [Free f, Free x, Free y, a, b] =
      Const(@{const_syntax letrec2}, dummyT) $ absfree x (absfree y (absfree f a)) $ absfree f b;
fun letrec3_tr [Free f, Free x, Free y, Free z, a, b] =
      Const(@{const_syntax letrec3}, dummyT) $
        absfree x (absfree y (absfree z (absfree f a))) $ absfree f b;

fun letrec_tr' [Abs(x,T,Abs(f,S,a)),Abs(ff,SS,b)] =
     let val (f',b') = Syntax_Trans.variant_abs(ff,SS,b)
         val (_,a'') = Syntax_Trans.variant_abs(f,S,a)
         val (x',a') = Syntax_Trans.variant_abs(x,T,a'')
     in Const(@{syntax_const "_letrec"},dummyT) $ Free(f',SS) $ Free(x',T) $ a' $ b' end;
fun letrec2_tr' [Abs(x,T,Abs(y,U,Abs(f,S,a))),Abs(ff,SS,b)] =
     let val (f',b') = Syntax_Trans.variant_abs(ff,SS,b)
         val ( _,a1) = Syntax_Trans.variant_abs(f,S,a)
         val (y',a2) = Syntax_Trans.variant_abs(y,U,a1)
         val (x',a') = Syntax_Trans.variant_abs(x,T,a2)
     in Const(@{syntax_const "_letrec2"},dummyT) $ Free(f',SS) $ Free(x',T) $ Free(y',U) $ a' $ b'
      end;
fun letrec3_tr' [Abs(x,T,Abs(y,U,Abs(z,V,Abs(f,S,a)))),Abs(ff,SS,b)] =
     let val (f',b') = Syntax_Trans.variant_abs(ff,SS,b)
         val ( _,a1) = Syntax_Trans.variant_abs(f,S,a)
         val (z',a2) = Syntax_Trans.variant_abs(z,V,a1)
         val (y',a3) = Syntax_Trans.variant_abs(y,U,a2)
         val (x',a') = Syntax_Trans.variant_abs(x,T,a3)
     in Const(@{syntax_const "_letrec3"},dummyT) $ Free(f',SS) $ Free(x',T) $ Free(y',U) $ Free(z',V) $ a' $ b'
      end;

*}

parse_translation {*
 [(@{syntax_const "_let"}, let_tr),
  (@{syntax_const "_letrec"}, letrec_tr),
  (@{syntax_const "_letrec2"}, letrec2_tr),
  (@{syntax_const "_letrec3"}, letrec3_tr)]
*}

print_translation {*
 [(@{const_syntax let}, let_tr'),
  (@{const_syntax letrec}, letrec_tr'),
  (@{const_syntax letrec2}, letrec2_tr'),
  (@{const_syntax letrec3}, letrec3_tr')]
*}

consts
  napply     :: "[i=>i,i,i]=>i"            ("(_ ^ _ ` _)" [56,56,56] 56)

defs
  one_def:                    "one == true"
  if_def:     "if b then t else u  == case(b,t,u,% x y. bot,%v. bot)"
  inl_def:                 "inl(a) == <true,a>"
  inr_def:                 "inr(b) == <false,b>"
  when_def:           "when(t,f,g) == split(t,%b x. if b then f(x) else g(x))"
  split_def:           "split(t,f) == case(t,bot,bot,f,%u. bot)"
  fst_def:                 "fst(t) == split(t,%x y. x)"
  snd_def:                 "snd(t) == split(t,%x y. y)"
  thd_def:                 "thd(t) == split(t,%x p. split(p,%y z. z))"
  zero_def:                  "zero == inl(one)"
  succ_def:               "succ(n) == inr(n)"
  ncase_def:         "ncase(n,b,c) == when(n,%x. b,%y. c(y))"
  nrec_def:          " nrec(n,b,c) == letrec g x be ncase(x,b,%y. c(y,g(y))) in g(n)"
  nil_def:                     "[] == inl(one)"
  cons_def:                   "h$t == inr(<h,t>)"
  lcase_def:         "lcase(l,b,c) == when(l,%x. b,%y. split(y,c))"
  lrec_def:           "lrec(l,b,c) == letrec g x be lcase(x,b,%h t. c(h,t,g(t))) in g(l)"

  let_def:  "let x be t in f(x) == case(t,f(true),f(false),%x y. f(<x,y>),%u. f(lam x. u(x)))"
  letrec_def:
  "letrec g x be h(x,g) in b(g) == b(%x. fix(%f. lam x. h(x,%y. f`y))`x)"

  letrec2_def:  "letrec g x y be h(x,y,g) in f(g)==
               letrec g' p be split(p,%x y. h(x,y,%u v. g'(<u,v>)))
                          in f(%x y. g'(<x,y>))"

  letrec3_def:  "letrec g x y z be h(x,y,z,g) in f(g) ==
             letrec g' p be split(p,%x xs. split(xs,%y z. h(x,y,z,%u v w. g'(<u,<v,w>>))))
                          in f(%x y z. g'(<x,<y,z>>))"

  napply_def: "f ^n` a == nrec(n,a,%x g. f(g))"


lemmas simp_can_defs = one_def inl_def inr_def
  and simp_ncan_defs = if_def when_def split_def fst_def snd_def thd_def
lemmas simp_defs = simp_can_defs simp_ncan_defs

lemmas ind_can_defs = zero_def succ_def nil_def cons_def
  and ind_ncan_defs = ncase_def nrec_def lcase_def lrec_def
lemmas ind_defs = ind_can_defs ind_ncan_defs

lemmas data_defs = simp_defs ind_defs napply_def
  and genrec_defs = letrec_def letrec2_def letrec3_def


subsection {* Beta Rules, including strictness *}

lemma letB: "~ t=bot ==> let x be t in f(x) = f(t)"
  apply (unfold let_def)
  apply (erule rev_mp)
  apply (rule_tac t = "t" in term_case)
      apply (simp_all add: caseBtrue caseBfalse caseBpair caseBlam)
  done

lemma letBabot: "let x be bot in f(x) = bot"
  apply (unfold let_def)
  apply (rule caseBbot)
  done

lemma letBbbot: "let x be t in bot = bot"
  apply (unfold let_def)
  apply (rule_tac t = t in term_case)
      apply (rule caseBbot)
     apply (simp_all add: caseBtrue caseBfalse caseBpair caseBlam)
  done

lemma applyB: "(lam x. b(x)) ` a = b(a)"
  apply (unfold apply_def)
  apply (simp add: caseBtrue caseBfalse caseBpair caseBlam)
  done

lemma applyBbot: "bot ` a = bot"
  apply (unfold apply_def)
  apply (rule caseBbot)
  done

lemma fixB: "fix(f) = f(fix(f))"
  apply (unfold fix_def)
  apply (rule applyB [THEN ssubst], rule refl)
  done

lemma letrecB:
    "letrec g x be h(x,g) in g(a) = h(a,%y. letrec g x be h(x,g) in g(y))"
  apply (unfold letrec_def)
  apply (rule fixB [THEN ssubst], rule applyB [THEN ssubst], rule refl)
  done

lemmas rawBs = caseBs applyB applyBbot

method_setup beta_rl = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (CHANGED o
      simp_tac (simpset_of ctxt addsimps @{thms rawBs} setloop (stac @{thm letrecB}))))
*}

lemma ifBtrue: "if true then t else u = t"
  and ifBfalse: "if false then t else u = u"
  and ifBbot: "if bot then t else u = bot"
  unfolding data_defs by beta_rl+

lemma whenBinl: "when(inl(a),t,u) = t(a)"
  and whenBinr: "when(inr(a),t,u) = u(a)"
  and whenBbot: "when(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma splitB: "split(<a,b>,h) = h(a,b)"
  and splitBbot: "split(bot,h) = bot"
  unfolding data_defs by beta_rl+

lemma fstB: "fst(<a,b>) = a"
  and fstBbot: "fst(bot) = bot"
  unfolding data_defs by beta_rl+

lemma sndB: "snd(<a,b>) = b"
  and sndBbot: "snd(bot) = bot"
  unfolding data_defs by beta_rl+

lemma thdB: "thd(<a,<b,c>>) = c"
  and thdBbot: "thd(bot) = bot"
  unfolding data_defs by beta_rl+

lemma ncaseBzero: "ncase(zero,t,u) = t"
  and ncaseBsucc: "ncase(succ(n),t,u) = u(n)"
  and ncaseBbot: "ncase(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma nrecBzero: "nrec(zero,t,u) = t"
  and nrecBsucc: "nrec(succ(n),t,u) = u(n,nrec(n,t,u))"
  and nrecBbot: "nrec(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma lcaseBnil: "lcase([],t,u) = t"
  and lcaseBcons: "lcase(x$xs,t,u) = u(x,xs)"
  and lcaseBbot: "lcase(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma lrecBnil: "lrec([],t,u) = t"
  and lrecBcons: "lrec(x$xs,t,u) = u(x,xs,lrec(xs,t,u))"
  and lrecBbot: "lrec(bot,t,u) = bot"
  unfolding data_defs by beta_rl+

lemma letrec2B:
  "letrec g x y be h(x,y,g) in g(p,q) = h(p,q,%u v. letrec g x y be h(x,y,g) in g(u,v))"
  unfolding data_defs letrec2_def by beta_rl+

lemma letrec3B:
  "letrec g x y z be h(x,y,z,g) in g(p,q,r) =
    h(p,q,r,%u v w. letrec g x y z be h(x,y,z,g) in g(u,v,w))"
  unfolding data_defs letrec3_def by beta_rl+

lemma napplyBzero: "f^zero`a = a"
  and napplyBsucc: "f^succ(n)`a = f(f^n`a)"
  unfolding data_defs by beta_rl+

lemmas termBs = letB applyB applyBbot splitB splitBbot fstB fstBbot
  sndB sndBbot thdB thdBbot ifBtrue ifBfalse ifBbot whenBinl whenBinr
  whenBbot ncaseBzero ncaseBsucc ncaseBbot nrecBzero nrecBsucc
  nrecBbot lcaseBnil lcaseBcons lcaseBbot lrecBnil lrecBcons lrecBbot
  napplyBzero napplyBsucc


subsection {* Constructors are injective *}

lemma term_injs:
  "(inl(a) = inl(a')) <-> (a=a')"
  "(inr(a) = inr(a')) <-> (a=a')"
  "(succ(a) = succ(a')) <-> (a=a')"
  "(a$b = a'$b') <-> (a=a' & b=b')"
  by (inj_rl applyB splitB whenBinl whenBinr ncaseBsucc lcaseBcons)


subsection {* Constructors are distinct *}

ML {*
bind_thms ("term_dstncts",
  mkall_dstnct_thms @{theory} @{thms data_defs} (@{thms ccl_injs} @ @{thms term_injs})
    [["bot","inl","inr"], ["bot","zero","succ"], ["bot","nil","cons"]]);
*}


subsection {* Rules for pre-order @{text "[="} *}

lemma term_porews:
  "inl(a) [= inl(a') <-> a [= a'"
  "inr(b) [= inr(b') <-> b [= b'"
  "succ(n) [= succ(n') <-> n [= n'"
  "x$xs [= x'$xs' <-> x [= x'  & xs [= xs'"
  by (simp_all add: data_defs ccl_porews)


subsection {* Rewriting and Proving *}

ML {*
  bind_thms ("term_injDs", XH_to_Ds @{thms term_injs});
*}

lemmas term_rews = termBs term_injs term_dstncts ccl_porews term_porews

lemmas [simp] = term_rews
lemmas [elim!] = term_dstncts [THEN notE]
lemmas [dest!] = term_injDs

end
