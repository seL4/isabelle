(*  Title: 	HOL/IMP/Hoare.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

Semantic embedding of Hoare logic
*)

Hoare = Denotation +
consts
  spec :: [state=>bool,com,state=>bool] => bool
(* syntax "@spec" :: [bool,com,bool] => bool *)
          ("{{(1_)}}/ (_)/ {{(1_)}}" 10)
defs
  spec_def "spec P c Q == !s t. (s,t) : C(c) --> P s --> Q t"
end
(* Pretty-printing of assertions.
   Not very helpful as long as programs are not pretty-printed.
ML

local open Syntax

fun is_loc a = let val ch = hd(explode a)
               in ord "A" <= ord ch andalso ord ch <= ord "Z" end;

fun tr(s$t,i) = tr(s,i)$tr(t,i)
  | tr(Abs(x,T,u),i) = Abs(x,T,tr(u,i+1))
  | tr(t as Free(a,T),i) = if is_loc a then Bound(i) $ free(a) else t
  | tr(t,_) = t;

fun cond_tr(p) = Abs("",dummyT,tr(p,0))

fun spec_tr[p,c,q] = const"spec" $ cond_tr p $ c $ cond_tr q;

fun tr'(t as (Bound j $ (u as Free(a,_))),i) = if i=j then u else t
  | tr'(s$t,i) = tr'(s,i)$tr'(t,i)
  | tr'(Abs(x,T,u),i) = Abs(x,T,tr'(u,i+1))
  | tr'(t,_) = t;

fun spec_tr'[Abs(_,_,p),c,Abs(_,_,q)] =
  const"@spec" $ tr'(p,0) $ c $ tr'(q,0);

in

val parse_translation = [("@spec", spec_tr)];
val print_translation = [("spec", spec_tr')];

end
*)
