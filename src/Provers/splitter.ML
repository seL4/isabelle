(*  Title:      Provers/splitter
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  TU Munich

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

fun contains cmap =
  let fun isin i (Abs(_,_,b)) = isin 0 b
        | isin i (s$t) = isin (i+1) s orelse isin 0 t
        | isin i (Const(c,_)) = (case assoc(cmap,c) of
                                   Some(n,_) => n <= i
                                 | None => false)
        | isin _ _ = false
  in isin 0 end;

fun mk_context cmap Ts maxi t =
  let fun var (t,i) = Var(("X",i),type_of1(Ts,t))

      fun mka((None,i,ts),t) = if contains cmap t
            then let val (u,T,j) = mk(t,i) in (Some(T),j,ts@[u]) end
            else (None,i+1,ts@[var(t,i)])
        | mka((some,i,ts),t) = (some,i+1,ts@[var(t,i)])
      and mk(t as Abs _, i) = (Bound 0,type_of1(Ts,t),i)
        | mk(t,i) =
            let val (f,ts) = strip_comb t
                val (Some(T),j,us) = foldl mka ((None,i,[]),ts)
            in (list_comb(f,us),T,j) end

      val (u,T,_) = mk(t,maxi+1)
  in Abs("",T,u) end;

fun nth_subgoal i thm = nth_elem(i-1,prems_of thm);

fun goal_concl i thm = Logic.strip_assums_concl(nth_subgoal i thm);

fun inst_lift cmap state lift i =
  let val sg = #sign(rep_thm state)
      val tsig = #tsig(Sign.rep_sg sg)
      val goali = nth_subgoal i state
      val Ts = map #2 (Logic.strip_params goali)
      val _ $ t $ _ = Logic.strip_assums_concl goali;
      val cntxt = mk_context cmap (rev Ts) (#maxidx(rep_thm lift)) t
      val cu = cterm_of sg cntxt
      val uT = #T(rep_cterm cu)
      val cP' = cterm_of sg (Var(P,uT))
      val ixnTs = Type.typ_match tsig ([],(PT,uT));
      val ixncTs = map (fn (x,y) => (x,ctyp_of sg y)) ixnTs;
  in instantiate (ixncTs, [(cP',cu)]) lift end;

fun splittable al i thm =
  let val tm = goal_concl i thm
      fun nobound j k (Abs(_,_,t)) = nobound j (k+1) t
        | nobound j k (s$t) = nobound j k s andalso nobound j k t
        | nobound j k (Bound n) = n < k orelse k+j <= n
        | nobound _ _ _ = true;
      fun find j (None,t) = (case t of
            Abs(_,_,t) => find (j+1) (None,t)
          | _ => let val (h,args) = strip_comb t
                     fun no() = foldl (find j) (None,args)
                 in case h of
                      Const(c,_) =>
                        (case assoc(al,c) of
                           Some(n,thm) =>
                             if length args < n then no()
                             else if forall (nobound j 0) (take(n,args))
                                  then Some(thm)
                                  else no()
                         | None => no())
                    | _ => no()
                 end)
        | find _ (some,_) = some
  in find 0 (None,tm) end;

fun split_tac [] i = no_tac
  | split_tac splits i =
  let fun const(thm) = let val _$(_$lhs)$_ = concl_of thm
                           val (Const(a,_),args) = strip_comb lhs
                       in (a,(length args,thm)) end
      val cmap = map const splits;
      fun lift thm = rtac (inst_lift cmap thm trlift i) i
      fun lift_split thm =
            case splittable cmap i thm of
              Some(split) => rtac split i
            | None => EVERY[STATE lift, rtac reflexive_thm (i+1),
                            STATE lift_split]
  in STATE(fn thm =>
       if (i <= nprems_of thm)  andalso  contains cmap (goal_concl i thm)
       then EVERY[rtac iffD i, STATE lift_split]
       else no_tac)
  end;

in split_tac end;
