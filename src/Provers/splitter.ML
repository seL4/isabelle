(*  Title:      Provers/splitter
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995  TU Munich

Generic case-splitter, suitable for most logics.

Use:

val split_tac = mk_case_split_tac iffD;

by(case_split_tac splits i);

where splits = [P(elim(...)) == rhs, ...]
      iffD  = [| P <-> Q; Q |] ==> P (* is called iffD2 in HOL *)

*)

fun mk_case_split_tac iffD =
let

val lift =
  let val ct = read_cterm (#sign(rep_thm iffD))
           ("[| !!x::'b::logic. Q(x) == R(x) |] ==> \
            \P(%x.Q(x)) == P(%x.R(x))::'a::logic",propT)
  in prove_goalw_cterm [] ct
     (fn [prem] => [rewtac prem, rtac reflexive_thm 1])
  end;

val trlift = lift RS transitive_thm;
val _ $ (Var(P,PT)$_) $ _ = concl_of trlift;


fun mk_cntxt Ts t pos T maxi =
  let fun var (t,i) = Var(("X",i),type_of1(Ts,t));
      fun down [] t i = Bound 0
        | down (p::ps) t i =
            let val (h,ts) = strip_comb t
                val v1 = map var (take(p,ts) ~~ (i upto (i+p-1)))
                val u::us = drop(p,ts)
                val v2 = map var (us ~~ ((i+p) upto (i+length(ts)-2)))
      in list_comb(h,v1@[down ps u (i+length ts)]@v2) end;
  in Abs("", T, down (rev pos) t maxi) end;

fun add_lbnos(is,t) = add_loose_bnos(t,0,is);

(* check if the innermost quantifier that needs to be removed
   has a body of type T; otherwise the expansion thm will fail later on
*)
fun type_test(T,lbnos,apsns) =
  let val (_,U,_) = nth_elem(min lbnos,apsns)
  in T=U end;

fun mk_split_pack(thm,T,n,ts,apsns) =
  if n > length ts then []
  else let val lev = length apsns
           val lbnos = foldl add_lbnos ([],take(n,ts))
           val flbnos = filter (fn i => i < lev) lbnos
       in if null flbnos then [(thm,[])]
          else if type_test(T,flbnos,apsns) then [(thm, rev apsns)] else []
       end;

fun split_posns cmap Ts t =
  let fun posns Ts pos apsns (Abs(_,T,t)) =
            let val U = fastype_of1(T::Ts,t)
            in posns (T::Ts) (0::pos) ((T,U,pos)::apsns) t end
        | posns Ts pos apsns t =
            let val (h,ts) = strip_comb t
                fun iter((i,a),t) = (i+1, (posns Ts (i::pos) apsns t) @ a);
                val a = case h of
                  Const(c,_) =>
                    (case assoc(cmap,c) of
                       Some(thm,T,n) => mk_split_pack(thm,T,n,ts,apsns)
                     | None => [])
                | _ => []
             in snd(foldl iter ((0,a),ts)) end
  in posns Ts [] [] t end;

fun nth_subgoal i thm = nth_elem(i-1,prems_of thm);

fun shorter((_,ps),(_,qs)) = length ps <= length qs;

fun select cmap state i =
  let val goali = nth_subgoal i state
      val Ts = rev(map #2 (Logic.strip_params goali))
      val _ $ t $ _ = Logic.strip_assums_concl goali;
  in (Ts,t,sort shorter (split_posns cmap Ts t)) end;

fun inst_lift Ts t (T,U,pos) state lift i =
  let val sg = #sign(rep_thm state)
      val tsig = #tsig(Sign.rep_sg sg)
      val cntxt = mk_cntxt Ts t pos (T-->U) (#maxidx(rep_thm lift))
      val cu = cterm_of sg cntxt
      val uT = #T(rep_cterm cu)
      val cP' = cterm_of sg (Var(P,uT))
      val ixnTs = Type.typ_match tsig ([],(PT,uT));
      val ixncTs = map (fn (x,y) => (x,ctyp_of sg y)) ixnTs;
  in instantiate (ixncTs, [(cP',cu)]) lift end;


fun split_tac [] i = no_tac
  | split_tac splits i =
  let fun const(thm) = let val _$(t as _$lhs)$_ = concl_of thm
                           val (Const(a,_),args) = strip_comb lhs
                       in (a,(thm,fastype_of t,length args)) end
      val cmap = map const splits;
      fun lift Ts t p state = rtac (inst_lift Ts t p state trlift i) i
      fun lift_split state =
            let val (Ts,t,splits) = select cmap state i
            in case splits of
                 [] => no_tac
               | (thm,apsns)::_ =>
                   (case apsns of
                      [] => rtac thm i
                    | p::_ => EVERY[STATE(lift Ts t p),
                                    rtac reflexive_thm (i+1),
                                    STATE lift_split])
            end
  in STATE(fn thm =>
       if i <= nprems_of thm then rtac iffD i THEN STATE lift_split
       else no_tac)
  end;

in split_tac end;
