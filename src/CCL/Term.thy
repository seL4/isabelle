(*  Title:      CCL/terms.thy
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1993  University of Cambridge

Definitions of usual program constructs in CCL.

*)

Term = CCL +

consts

  one        :: "i"

  if         :: "[i,i,i]=>i"           ("(3if _/ then _/ else _)" [0,0,60] 60)

  inl,inr    :: "i=>i"
  when       :: "[i,i=>i,i=>i]=>i" 

  split      :: "[i,[i,i]=>i]=>i"
  fst,snd,   
  thd        :: "i=>i"

  zero       :: "i"
  succ       :: "i=>i"
  ncase      :: "[i,i,i=>i]=>i"
  nrec       :: "[i,i,[i,i]=>i]=>i"

  nil        :: "i"                        ("([])")
  "$"        :: "[i,i]=>i"                 (infixr 80)
  lcase      :: "[i,i,[i,i]=>i]=>i"
  lrec       :: "[i,i,[i,i,i]=>i]=>i"

  let        :: "[i,i=>i]=>i"
  letrec     :: "[[i,i=>i]=>i,(i=>i)=>i]=>i"
  letrec2    :: "[[i,i,i=>i=>i]=>i,(i=>i=>i)=>i]=>i"
  letrec3    :: "[[i,i,i,i=>i=>i=>i]=>i,(i=>i=>i=>i)=>i]=>i"  

syntax
  "@let"     :: "[idt,i,i]=>i"             ("(3let _ be _/ in _)"
                        [0,0,60] 60)

  "@letrec"  :: "[idt,idt,i,i]=>i"         ("(3letrec _ _ be _/ in _)"
                        [0,0,0,60] 60)

  "@letrec2" :: "[idt,idt,idt,i,i]=>i"     ("(3letrec _ _ _ be _/ in _)"
                        [0,0,0,0,60] 60)

  "@letrec3" :: "[idt,idt,idt,idt,i,i]=>i" ("(3letrec _ _ _ _ be _/ in _)"
                        [0,0,0,0,0,60] 60)

consts
  napply     :: "[i=>i,i,i]=>i"            ("(_ ^ _ ` _)" [56,56,56] 56)

rules

  one_def                    "one == true"
  if_def     "if b then t else u  == case(b,t,u,% x y. bot,%v. bot)"
  inl_def                 "inl(a) == <true,a>"
  inr_def                 "inr(b) == <false,b>"
  when_def           "when(t,f,g) == split(t,%b x. if b then f(x) else g(x))"
  split_def           "split(t,f) == case(t,bot,bot,f,%u. bot)"
  fst_def                 "fst(t) == split(t,%x y. x)"
  snd_def                 "snd(t) == split(t,%x y. y)"
  thd_def                 "thd(t) == split(t,%x p. split(p,%y z. z))"
  zero_def                  "zero == inl(one)"
  succ_def               "succ(n) == inr(n)"
  ncase_def         "ncase(n,b,c) == when(n,%x. b,%y. c(y))"
  nrec_def          " nrec(n,b,c) == letrec g x be ncase(x,b,%y. c(y,g(y))) in g(n)"
  nil_def                     "[] == inl(one)"
  cons_def                   "h$t == inr(<h,t>)"
  lcase_def         "lcase(l,b,c) == when(l,%x. b,%y. split(y,c))"
  lrec_def           "lrec(l,b,c) == letrec g x be lcase(x,b,%h t. c(h,t,g(t))) in g(l)"

  let_def  "let x be t in f(x) == case(t,f(true),f(false),%x y. f(<x,y>),%u. f(lam x. u(x)))"
  letrec_def    
  "letrec g x be h(x,g) in b(g) == b(%x. fix(%f. lam x. h(x,%y. f`y))`x)"

  letrec2_def  "letrec g x y be h(x,y,g) in f(g)== 
               letrec g' p be split(p,%x y. h(x,y,%u v. g'(<u,v>))) 
                          in f(%x y. g'(<x,y>))"

  letrec3_def  "letrec g x y z be h(x,y,z,g) in f(g) == 
             letrec g' p be split(p,%x xs. split(xs,%y z. h(x,y,z,%u v w. g'(<u,<v,w>>)))) 
                          in f(%x y z. g'(<x,<y,z>>))"

  napply_def "f ^n` a == nrec(n,a,%x g. f(g))"

end

ML

(** Quantifier translations: variable binding **)

(* FIXME should use Syntax.mark_bound(T), Syntax.variant_abs' *)

fun let_tr [Free(id,T),a,b] = Const("let",dummyT) $ a $ absfree(id,T,b);
fun let_tr' [a,Abs(id,T,b)] =
     let val (id',b') = variant_abs(id,T,b)
     in Const("@let",dummyT) $ Free(id',T) $ a $ b' end;

fun letrec_tr [Free(f,S),Free(x,T),a,b] = 
      Const("letrec",dummyT) $ absfree(x,T,absfree(f,S,a)) $ absfree(f,S,b);
fun letrec2_tr [Free(f,S),Free(x,T),Free(y,U),a,b] = 
      Const("letrec2",dummyT) $ absfree(x,T,absfree(y,U,absfree(f,S,a))) $ absfree(f,S,b);
fun letrec3_tr [Free(f,S),Free(x,T),Free(y,U),Free(z,V),a,b] = 
      Const("letrec3",dummyT) $ absfree(x,T,absfree(y,U,absfree(z,U,absfree(f,S,a)))) $ absfree(f,S,b);

fun letrec_tr' [Abs(x,T,Abs(f,S,a)),Abs(ff,SS,b)] =
     let val (f',b')  = variant_abs(ff,SS,b)
         val (_,a'') = variant_abs(f,S,a)
         val (x',a')  = variant_abs(x,T,a'')
     in Const("@letrec",dummyT) $ Free(f',SS) $ Free(x',T) $ a' $ b' end;
fun letrec2_tr' [Abs(x,T,Abs(y,U,Abs(f,S,a))),Abs(ff,SS,b)] =
     let val (f',b') = variant_abs(ff,SS,b)
         val ( _,a1) = variant_abs(f,S,a)
         val (y',a2) = variant_abs(y,U,a1)
         val (x',a') = variant_abs(x,T,a2)
     in Const("@letrec2",dummyT) $ Free(f',SS) $ Free(x',T) $ Free(y',U) $ a' $ b'
      end;
fun letrec3_tr' [Abs(x,T,Abs(y,U,Abs(z,V,Abs(f,S,a)))),Abs(ff,SS,b)] =
     let val (f',b') = variant_abs(ff,SS,b)
         val ( _,a1) = variant_abs(f,S,a)
         val (z',a2) = variant_abs(z,V,a1)
         val (y',a3) = variant_abs(y,U,a2)
         val (x',a') = variant_abs(x,T,a3)
     in Const("@letrec3",dummyT) $ Free(f',SS) $ Free(x',T) $ Free(y',U) $ Free(z',V) $ a' $ b'
      end;

val  parse_translation=
    [("@let",       let_tr),
     ("@letrec",    letrec_tr),
     ("@letrec2",   letrec2_tr),
     ("@letrec3",   letrec3_tr)
    ];
val print_translation=
    [("let",       let_tr'),
     ("letrec",    letrec_tr'),
     ("letrec2",   letrec2_tr'),
     ("letrec3",   letrec3_tr')
    ];
