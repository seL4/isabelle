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

local

fun mk_case_split_tac_2 iffD order =
let


(************************************************************
   Create lift-theorem "trlift" :

   [| !! x. Q(x)==R(x) ; P(R) == C |] ==> P(Q)==C

*************************************************************)
 
val lift =
  let val ct = read_cterm (#sign(rep_thm iffD))
           ("[| !!x::'b::logic. Q(x) == R(x) |] ==> \
            \P(%x. Q(x)) == P(%x. R(x))::'a::logic",propT)
  in prove_goalw_cterm [] ct
     (fn [prem] => [rewtac prem, rtac reflexive_thm 1])
  end;

val trlift = lift RS transitive_thm;
val _ $ (Var(P,PT)$_) $ _ = concl_of trlift;


(************************************************************************ 
   Set up term for instantiation of P in the lift-theorem
   
   Ts    : types of parameters (i.e. variables bound by meta-quantifiers)
   t     : lefthand side of meta-equality in subgoal
           the lift theorem is applied to (see select)
   pos   : "path" leading to abstraction, coded as a list
   T     : type of body of P(...)
   maxi  : maximum index of Vars
*************************************************************************)

fun mk_cntxt Ts t pos T maxi =
  let fun var (t,i) = Var(("X",i),type_of1(Ts,t));
      fun down [] t i = Bound 0
        | down (p::ps) t i =
            let val (h,ts) = strip_comb t
                val v1 = ListPair.map var (take(p,ts), i upto (i+p-1))
                val u::us = drop(p,ts)
                val v2 = ListPair.map var (us, (i+p) upto (i+length(ts)-2))
      in list_comb(h,v1@[down ps u (i+length ts)]@v2) end;
  in Abs("", T, down (rev pos) t maxi) end;


(************************************************************************ 
   Set up term for instantiation of P in the split-theorem
   P(...) == rhs

   Ts    : types of parameters (i.e. variables bound by meta-quantifiers)
   t     : lefthand side of meta-equality in subgoal
           the split theorem is applied to (see select)
   T     : type of body of P(...)
   tt    : the term  Const(..,..) $ ...
   maxi  : maximum index of Vars

   lev   : abstraction level
*************************************************************************)

fun mk_cntxt_splitthm Ts t tt T maxi =
  let fun down lev (Abs(v,T2,t)) = Abs(v,T2,down (lev+1) t)
        | down lev (Bound i) = if i >= lev
                               then Var(("X",maxi+i-lev),nth_elem(i-lev,Ts))
                               else Bound i 
        | down lev t = 
            let val (h,ts) = strip_comb t
                val h2 = (case h of Bound _ => down lev h | _ => h)
            in if incr_bv(lev,0,tt)=t 
               then
                 Bound (lev)
               else
                 list_comb(h2,map (down lev) ts)
            end;
  in Abs("",T,down 0 t) end;


(* add all loose bound variables in t to list is *)
fun add_lbnos(is,t) = add_loose_bnos(t,0,is);

(* check if the innermost quantifier that needs to be removed
   has a body of type T; otherwise the expansion thm will fail later on
*)
fun type_test(T,lbnos,apsns) =
  let val (_,U,_) = nth_elem(foldl Int.min (hd lbnos, tl lbnos), apsns)
  in T=U end;

(*************************************************************************
   Create a "split_pack".

   thm   : the relevant split-theorem, i.e. P(...) == rhs , where P(...)
           is of the form
           P( Const(key,...) $ t_1 $ ... $ t_n )      (e.g. key = "if")
   T     : type of P(...)
   n     : number of arguments expected by Const(key,...)
   ts    : list of arguments actually found
   apsns : list of tuples of the form (T,U,pos), one tuple for each
           abstraction that is encountered on the way to the position where 
           Const(key, ...) $ ...  occurs, where
           T   : type of the variable bound by the abstraction
           U   : type of the abstraction's body
           pos : "path" leading to the body of the abstraction
   pos   : "path" leading to the position where Const(key, ...) $ ...  occurs.
   TB    : type of  Const(key,...) $ t_1 $ ... $ t_n
   t     : the term Const(key,...) $ t_1 $ ... $ t_n

   A split pack is a tuple of the form
   (thm, apsns, pos, TB)
   Note : apsns is reversed, so that the outermost quantifier's position
          comes first ! If the terms in ts don't contain variables bound
          by other than meta-quantifiers, apsns is empty, because no further
          lifting is required before applying the split-theorem.
******************************************************************************) 

fun mk_split_pack(thm,T,n,ts,apsns,pos,TB,t) =
  if n > length ts then []
  else let val lev = length apsns
           val lbnos = foldl add_lbnos ([],take(n,ts))
           val flbnos = filter (fn i => i < lev) lbnos
           val tt = incr_bv(~lev,0,t)
       in if null flbnos then [(thm,[],pos,TB,tt)]
          else if type_test(T,flbnos,apsns) then [(thm, rev apsns,pos,TB,tt)] 
               else []
       end;


(****************************************************************************
   Recursively scans term for occurences of Const(key,...) $ ...
   Returns a list of "split-packs" (one for each occurence of Const(key,...) )

   cmap : association list of split-theorems that should be tried.
          The elements have the format (key,(thm,T,n)) , where
          key : the theorem's key constant ( Const(key,...) $ ... )
          thm : the theorem itself
          T   : type of P( Const(key,...) $ ... )
          n   : number of arguments expected by Const(key,...)
   Ts   : types of parameters
   t    : the term to be scanned
******************************************************************************)

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
                       Some(thm,T,n) => mk_split_pack(thm,T,n,ts,apsns,pos,type_of1(Ts,t),t)
                     | None => [])
                | _ => []
             in snd(foldl iter ((0,a),ts)) end
  in posns Ts [] [] t end;


fun nth_subgoal i thm = nth_elem(i-1,prems_of thm);

fun shorter((_,ps,pos,_,_),(_,qs,qos,_,_)) =
  let val ms = length ps and ns = length qs
  in ms < ns orelse (ms = ns andalso order(length pos,length qos)) end;


(************************************************************
   call split_posns with appropriate parameters
*************************************************************)

fun select cmap state i =
  let val goali = nth_subgoal i state
      val Ts = rev(map #2 (Logic.strip_params goali))
      val _ $ t $ _ = Logic.strip_assums_concl goali;
  in (Ts,t,sort shorter (split_posns cmap Ts t)) end;


(*************************************************************
   instantiate lift theorem

   if t is of the form
   ... ( Const(...,...) $ Abs( .... ) ) ...
   then
   P = %a.  ... ( Const(...,...) $ a ) ...
   where a has type T --> U

   Ts      : types of parameters
   t       : lefthand side of meta-equality in subgoal
             the split theorem is applied to (see cmap)
   T,U,pos : see mk_split_pack
   state   : current proof state
   lift    : the lift theorem
   i       : no. of subgoal
**************************************************************)

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


(*************************************************************
   instantiate split theorem

   Ts    : types of parameters
   t     : lefthand side of meta-equality in subgoal
           the split theorem is applied to (see cmap)
   pos   : "path" to the body of P(...)
   thm   : the split theorem
   TB    : type of body of P(...)
   state : current proof state
**************************************************************)

fun inst_split Ts t tt thm TB state =
  let val _$((Var(P2,PT2))$_)$_ = concl_of thm
      val sg = #sign(rep_thm state)
      val tsig = #tsig(Sign.rep_sg sg)
      val cntxt = mk_cntxt_splitthm Ts t tt TB (#maxidx(rep_thm thm))
      val cu = cterm_of sg cntxt
      val uT = #T(rep_cterm cu)
      val cP' = cterm_of sg (Var(P2,uT))
      val ixnTs = Type.typ_match tsig ([],(PT2,uT));
      val ixncTs = map (fn (x,y) => (x,ctyp_of sg y)) ixnTs;
  in instantiate (ixncTs, [(cP',cu)]) thm end;


(*****************************************************************************
   The split-tactic
   
   splits : list of split-theorems to be tried
   i      : number of subgoal the tactic should be applied to
*****************************************************************************)

fun split_tac [] i = no_tac
  | split_tac splits i =
  let fun const(thm) = let val _$(t as _$lhs)$_ = concl_of thm
                           val (Const(a,_),args) = strip_comb lhs
                       in (a,(thm,fastype_of t,length args)) end
      val cmap = map const splits;
      fun lift_tac Ts t p st = (rtac (inst_lift Ts t p st trlift i) i) st
      fun lift_split_tac st = st |>
            let val (Ts,t,splits) = select cmap st i
            in case splits of
                 [] => no_tac
               | (thm,apsns,pos,TB,tt)::_ =>
                   (case apsns of
                      [] => (fn state => state |>
			           rtac (inst_split Ts t tt thm TB state) i)
                    | p::_ => EVERY[lift_tac Ts t p,
                                    rtac reflexive_thm (i+1),
                                    lift_split_tac])
            end
  in COND (has_fewer_prems i) no_tac 
          (rtac iffD i THEN lift_split_tac)
  end;

in split_tac end;

in

fun mk_case_split_tac iffD = mk_case_split_tac_2 iffD (op <=) ;

fun mk_case_split_inside_tac iffD = mk_case_split_tac_2 iffD (op >=) ;

end;
