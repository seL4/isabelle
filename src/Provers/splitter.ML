(*  Title:      Provers/splitter
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995  TU Munich

Generic case-splitter, suitable for most logics.
*)

infix 4 addsplits delsplits;

signature SPLITTER_DATA =
sig
  structure Simplifier: SIMPLIFIER
  val mk_eq         : thm -> thm
  val meta_eq_to_iff: thm (* "x == y ==> x = y"                    *)
  val iffD          : thm (* "[| P = Q; Q |] ==> P"                *)
  val disjE         : thm (* "[| P | Q; P ==> R; Q ==> R |] ==> R" *)
  val conjE         : thm (* "[| P & Q; [| P; Q |] ==> R |] ==> R" *)
  val exE           : thm (* "[|  x. P x; !!x. P x ==> Q |] ==> Q" *)
  val contrapos     : thm (* "[| ~ Q; P ==> Q |] ==> ~ P"          *)
  val contrapos2    : thm (* "[| Q; ~ P ==> ~ Q |] ==> P"          *)
  val notnotD       : thm (* "~ ~ P ==> P"                         *)
end

signature SPLITTER =
sig
  type simpset
  val split_tac       : thm list -> int -> tactic
  val split_inside_tac: thm list -> int -> tactic
  val split_asm_tac   : thm list -> int -> tactic
  val addsplits       : simpset * thm list -> simpset
  val delsplits       : simpset * thm list -> simpset
  val Addsplits       : thm list -> unit
  val Delsplits       : thm list -> unit
  val split_add_global: theory attribute
  val split_del_global: theory attribute
  val split_add_local: Proof.context attribute
  val split_del_local: Proof.context attribute
  val split_modifiers : (Args.T list -> (Method.modifier * Args.T list)) list
  val setup: (theory -> theory) list
end;

functor SplitterFun(Data: SPLITTER_DATA): SPLITTER =
struct 

structure Simplifier = Data.Simplifier;
type simpset = Simplifier.simpset;

val Const ("==>", _) $ (Const ("Trueprop", _) $
         (Const (const_not, _) $ _    )) $ _ = #prop (rep_thm(Data.notnotD));

val Const ("==>", _) $ (Const ("Trueprop", _) $
         (Const (const_or , _) $ _ $ _)) $ _ = #prop (rep_thm(Data.disjE));

fun split_format_err() = error("Wrong format for split rule");

fun split_thm_info thm = case concl_of (Data.mk_eq thm) of
     Const("==", _)$(Var _$t)$c =>
        (case strip_comb t of
           (Const(a,_),_) => (a,case c of (Const(s,_)$_)=>s=const_not|_=> false)
         | _              => split_format_err())
   | _ => split_format_err();

fun mk_case_split_tac order =
let


(************************************************************
   Create lift-theorem "trlift" :

   [| !!x. Q x == R x; P(%x. R x) == C |] ==> P (%x. Q x) == C

*************************************************************)

val meta_iffD = Data.meta_eq_to_iff RS Data.iffD;
val lift =
  let val ct = read_cterm (#sign(rep_thm Data.iffD))
           ("[| !!x::'b::logic. Q(x) == R(x) |] ==> \
            \P(%x. Q(x)) == P(%x. R(x))::'a::logic",propT)
  in prove_goalw_cterm [] ct
     (fn [prem] => [rewtac prem, rtac reflexive_thm 1])
  end;

val trlift = lift RS transitive_thm;
val _ $ (P $ _) $ _ = concl_of trlift;


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

   t     : lefthand side of meta-equality in subgoal
           the split theorem is applied to (see select)
   T     : type of body of P(...)
   tt    : the term  Const(key,..) $ ...
*************************************************************************)

fun mk_cntxt_splitthm t tt T =
  let fun repl lev t =
    if incr_boundvars lev tt aconv t then Bound lev
    else case t of
        (Abs (v, T2, t)) => Abs (v, T2, repl (lev+1) t)
      | (Bound i) => Bound (if i>=lev then i+1 else i)
      | (t1 $ t2) => (repl lev t1) $ (repl lev t2)
      | t => t
  in Abs("", T, repl 0 t) end;


(* add all loose bound variables in t to list is *)
fun add_lbnos(is,t) = add_loose_bnos(t,0,is);

(* check if the innermost abstraction that needs to be removed
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
   T'    : type of term to be scanned
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
   (thm, apsns, pos, TB, tt)
   Note : apsns is reversed, so that the outermost quantifier's position
          comes first ! If the terms in ts don't contain variables bound
          by other than meta-quantifiers, apsns is empty, because no further
          lifting is required before applying the split-theorem.
******************************************************************************) 

fun mk_split_pack(thm, T, T', n, ts, apsns, pos, TB, t) =
  if n > length ts then []
  else let val lev = length apsns
           val lbnos = foldl add_lbnos ([],take(n,ts))
           val flbnos = filter (fn i => i < lev) lbnos
           val tt = incr_boundvars (~lev) t
       in if null flbnos then
            if T = T' then [(thm,[],pos,TB,tt)] else []
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

fun split_posns cmap sg Ts t =
  let
    val T' = fastype_of1 (Ts, t);
    fun posns Ts pos apsns (Abs (_, T, t)) =
          let val U = fastype_of1 (T::Ts,t)
          in posns (T::Ts) (0::pos) ((T, U, pos)::apsns) t end
      | posns Ts pos apsns t =
          let
            val (h, ts) = strip_comb t
            fun iter((i, a), t) = (i+1, (posns Ts (i::pos) apsns t) @ a);
            val a = case h of
              Const(c, cT) =>
                let fun find [] = []
                      | find ((gcT, thm, T, n)::tups) =
                          if Sign.typ_instance sg (cT, gcT)
                          then
                            let val t2 = list_comb (h, take (n, ts))
                            in mk_split_pack(thm,T,T',n,ts,apsns,pos,type_of1(Ts,t2),t2)
                            end
                          else find tups
                in find (assocs cmap c) end
            | _ => []
          in snd(foldl iter ((0, a), ts)) end
  in posns Ts [] [] t end;


fun nth_subgoal i thm = nth_elem(i-1,prems_of thm);

fun shorter((_,ps,pos,_,_),(_,qs,qos,_,_)) =
  prod_ord (int_ord o pairself length) (order o pairself length)
    ((ps, pos), (qs, qos));



(************************************************************
   call split_posns with appropriate parameters
*************************************************************)

fun select cmap state i =
  let val sg = #sign(rep_thm state)
      val goali = nth_subgoal i state
      val Ts = rev(map #2 (Logic.strip_params goali))
      val _ $ t $ _ = Logic.strip_assums_concl goali;
  in (Ts,t, sort shorter (split_posns cmap sg Ts t)) end;


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

fun inst_lift Ts t (T, U, pos) state i =
  let
    val cert = cterm_of (sign_of_thm state);
    val cntxt = mk_cntxt Ts t pos (T --> U) (#maxidx(rep_thm trlift));    
  in cterm_instantiate [(cert P, cert cntxt)] trlift
  end;


(*************************************************************
   instantiate split theorem

   Ts    : types of parameters
   t     : lefthand side of meta-equality in subgoal
           the split theorem is applied to (see cmap)
   tt    : the term  Const(key,..) $ ...
   thm   : the split theorem
   TB    : type of body of P(...)
   state : current proof state
   i     : number of subgoal
**************************************************************)

fun inst_split Ts t tt thm TB state i =
  let 
    val thm' = Thm.lift_rule (state, i) thm;
    val (P, _) = strip_comb (fst (Logic.dest_equals
      (Logic.strip_assums_concl (#prop (rep_thm thm')))));
    val cert = cterm_of (sign_of_thm state);
    val cntxt = mk_cntxt_splitthm t tt TB;
    val abss = foldl (fn (t, T) => Abs ("", T, t));
  in cterm_instantiate [(cert P, cert (abss (cntxt, Ts)))] thm'
  end;


(*****************************************************************************
   The split-tactic
   
   splits : list of split-theorems to be tried
   i      : number of subgoal the tactic should be applied to
*****************************************************************************)

fun split_tac [] i = no_tac
  | split_tac splits i =
  let val splits = map Data.mk_eq splits;
      fun add_thm(cmap,thm) =
            (case concl_of thm of _$(t as _$lhs)$_ =>
               (case strip_comb lhs of (Const(a,aT),args) =>
                  let val info = (aT,thm,fastype_of t,length args)
                  in case assoc(cmap,a) of
                       Some infos => overwrite(cmap,(a,info::infos))
                     | None => (a,[info])::cmap
                  end
                | _ => split_format_err())
             | _ => split_format_err())
      val cmap = foldl add_thm ([],splits);
      fun lift_tac Ts t p st = rtac (inst_lift Ts t p st i) i st
      fun lift_split_tac state =
            let val (Ts, t, splits) = select cmap state i
            in case splits of
                 [] => no_tac state
               | (thm, apsns, pos, TB, tt)::_ =>
                   (case apsns of
                      [] => compose_tac (false, inst_split Ts t tt thm TB state i, 0) i state
                    | p::_ => EVERY [lift_tac Ts t p,
                                     rtac reflexive_thm (i+1),
                                     lift_split_tac] state)
            end
  in COND (has_fewer_prems i) no_tac 
          (rtac meta_iffD i THEN lift_split_tac)
  end;

in split_tac end;


val split_tac        = mk_case_split_tac              int_ord;

val split_inside_tac = mk_case_split_tac (rev_order o int_ord);


(*****************************************************************************
   The split-tactic for premises
   
   splits : list of split-theorems to be tried
****************************************************************************)
fun split_asm_tac []     = K no_tac
  | split_asm_tac splits = 

  let val cname_list = map (fst o split_thm_info) splits;
      fun is_case (a,_) = a mem cname_list;
      fun tac (t,i) = 
	  let val n = find_index (exists_Const is_case) 
				 (Logic.strip_assums_hyp t);
	      fun first_prem_is_disj (Const ("==>", _) $ (Const ("Trueprop", _)
				 $ (Const (s, _) $ _ $ _ )) $ _ ) = (s=const_or)
	      |   first_prem_is_disj (Const("all",_)$Abs(_,_,t)) = 
					first_prem_is_disj t
	      |   first_prem_is_disj _ = false;
      (* does not work properly if the split variable is bound by a quantfier *)
	      fun flat_prems_tac i = SUBGOAL (fn (t,i) => 
			   (if first_prem_is_disj t
			    then EVERY[etac Data.disjE i,rotate_tac ~1 i,
				       rotate_tac ~1  (i+1),
				       flat_prems_tac (i+1)]
			    else all_tac) 
			   THEN REPEAT (eresolve_tac [Data.conjE,Data.exE] i)
			   THEN REPEAT (dresolve_tac [Data.notnotD]   i)) i;
	  in if n<0 then no_tac else DETERM (EVERY'
		[rotate_tac n, etac Data.contrapos2,
		 split_tac splits, 
		 rotate_tac ~1, etac Data.contrapos, rotate_tac ~1, 
		 flat_prems_tac] i)
	  end;
  in SUBGOAL tac
  end;



(** declare split rules **)

(* addsplits / delsplits *)

fun split_name name asm = "split " ^ name ^ (if asm then " asm" else "");

fun ss addsplits splits =
  let fun addsplit (ss,split) =
        let val (name,asm) = split_thm_info split
        in Simplifier.addloop(ss,(split_name name asm,
		       (if asm then split_asm_tac else split_tac) [split])) end
  in foldl addsplit (ss,splits) end;

fun ss delsplits splits =
  let fun delsplit(ss,split) =
        let val (name,asm) = split_thm_info split
        in Simplifier.delloop(ss,split_name name asm)
  end in foldl delsplit (ss,splits) end;

fun Addsplits splits = (Simplifier.simpset_ref() := 
			Simplifier.simpset() addsplits splits);
fun Delsplits splits = (Simplifier.simpset_ref() := 
			Simplifier.simpset() delsplits splits);


(* attributes *)

val splitN = "split";

val split_add_global = Simplifier.change_global_ss (op addsplits);
val split_del_global = Simplifier.change_global_ss (op delsplits);
val split_add_local = Simplifier.change_local_ss (op addsplits);
val split_del_local = Simplifier.change_local_ss (op delsplits);

val split_attr =
 (Attrib.add_del_args split_add_global split_del_global,
  Attrib.add_del_args split_add_local split_del_local);


(* methods *)

val split_modifiers =
 [Args.$$$ splitN -- Args.colon >> K ((I, split_add_local): Method.modifier),
  Args.$$$ splitN -- Args.add -- Args.colon >> K (I, split_add_local),
  Args.$$$ splitN -- Args.del -- Args.colon >> K (I, split_del_local)];

val split_args = #2 oo Method.syntax (Args.mode "asm" -- Attrib.local_thms);

fun split_meth (asm, ths) =
  Method.SIMPLE_METHOD' HEADGOAL (if asm then split_asm_tac ths else split_tac ths);



(** theory setup **)

val setup =
 [Attrib.add_attributes [(splitN, split_attr, "declaration of case split rule")],
  Method.add_methods [(splitN, split_meth oo split_args, "apply case split rule")]];

end;
