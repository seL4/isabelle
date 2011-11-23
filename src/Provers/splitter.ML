(*  Title:      Provers/splitter.ML
    Author:     Tobias Nipkow
    Copyright   1995  TU Munich

Generic case-splitter, suitable for most logics.
Deals with equalities of the form ?P(f args) = ...
where "f args" must be a first-order term without duplicate variables.
*)

signature SPLITTER_DATA =
sig
  val thy           : theory
  val mk_eq         : thm -> thm
  val meta_eq_to_iff: thm (* "x == y ==> x = y"                      *)
  val iffD          : thm (* "[| P = Q; Q |] ==> P"                  *)
  val disjE         : thm (* "[| P | Q; P ==> R; Q ==> R |] ==> R"   *)
  val conjE         : thm (* "[| P & Q; [| P; Q |] ==> R |] ==> R"   *)
  val exE           : thm (* "[| EX x. P x; !!x. P x ==> Q |] ==> Q" *)
  val contrapos     : thm (* "[| ~ Q; P ==> Q |] ==> ~ P"            *)
  val contrapos2    : thm (* "[| Q; ~ P ==> ~ Q |] ==> P"            *)
  val notnotD       : thm (* "~ ~ P ==> P"                           *)
end

signature SPLITTER =
sig
  (* somewhat more internal functions *)
  val cmap_of_split_thms: thm list -> (string * (typ * term * thm * typ * int) list) list
  val split_posns: (string * (typ * term * thm * typ * int) list) list ->
    theory -> typ list -> term -> (thm * (typ * typ * int list) list * int list * typ * term) list
    (* first argument is a "cmap", returns a list of "split packs" *)
  (* the "real" interface, providing a number of tactics *)
  val split_tac       : thm list -> int -> tactic
  val split_inside_tac: thm list -> int -> tactic
  val split_asm_tac   : thm list -> int -> tactic
  val add_split: thm -> simpset -> simpset
  val del_split: thm -> simpset -> simpset
  val split_add: attribute
  val split_del: attribute
  val split_modifiers : Method.modifier parser list
  val setup: theory -> theory
end;

functor Splitter(Data: SPLITTER_DATA): SPLITTER =
struct

val Const (const_not, _) $ _ =
  Object_Logic.drop_judgment Data.thy
    (#1 (Logic.dest_implies (Thm.prop_of Data.notnotD)));

val Const (const_or , _) $ _ $ _ =
  Object_Logic.drop_judgment Data.thy
    (#1 (Logic.dest_implies (Thm.prop_of Data.disjE)));

val const_Trueprop = Object_Logic.judgment_name Data.thy;


fun split_format_err () = error "Wrong format for split rule";

fun split_thm_info thm = case concl_of (Data.mk_eq thm) of
     Const("==", _) $ (Var _ $ t) $ c => (case strip_comb t of
       (Const p, _) => (p, case c of (Const (s, _) $ _) => s = const_not | _ => false)
     | _ => split_format_err ())
   | _ => split_format_err ();

fun cmap_of_split_thms thms =
let
  val splits = map Data.mk_eq thms
  fun add_thm thm cmap =
    (case concl_of thm of _ $ (t as _ $ lhs) $ _ =>
       (case strip_comb lhs of (Const(a,aT),args) =>
          let val info = (aT,lhs,thm,fastype_of t,length args)
          in case AList.lookup (op =) cmap a of
               SOME infos => AList.update (op =) (a, info::infos) cmap
             | NONE => (a,[info])::cmap
          end
        | _ => split_format_err())
     | _ => split_format_err())
in
  fold add_thm splits []
end;

(* ------------------------------------------------------------------------- *)
(* mk_case_split_tac                                                         *)
(* ------------------------------------------------------------------------- *)

fun mk_case_split_tac order =
let

(************************************************************
   Create lift-theorem "trlift" :

   [| !!x. Q x == R x; P(%x. R x) == C |] ==> P (%x. Q x) == C

*************************************************************)

val meta_iffD = Data.meta_eq_to_iff RS Data.iffD;  (* (P == Q) ==> Q ==> P *)

val lift = Goal.prove_global Pure.thy ["P", "Q", "R"]
  [Syntax.read_prop_global Pure.thy "!!x :: 'b. Q(x) == R(x) :: 'c"]
  (Syntax.read_prop_global Pure.thy "P(%x. Q(x)) == P(%x. R(x))")
  (fn {prems, ...} => rewrite_goals_tac prems THEN rtac reflexive_thm 1)

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
                val v1 = ListPair.map var (take p ts, i upto (i+p-1))
                val u::us = drop p ts
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
    if Pattern.aeconv(incr_boundvars lev tt, t) then Bound lev
    else case t of
        (Abs (v, T2, t)) => Abs (v, T2, repl (lev+1) t)
      | (Bound i) => Bound (if i>=lev then i+1 else i)
      | (t1 $ t2) => (repl lev t1) $ (repl lev t2)
      | t => t
  in Abs("", T, repl 0 t) end;


(* add all loose bound variables in t to list is *)
fun add_lbnos t is = add_loose_bnos (t, 0, is);

(* check if the innermost abstraction that needs to be removed
   has a body of type T; otherwise the expansion thm will fail later on
*)
fun type_test (T, lbnos, apsns) =
  let val (_, U: typ, _) = nth apsns (foldl1 Int.min lbnos)
  in T = U end;

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

fun mk_split_pack (thm, T: typ, T', n, ts, apsns, pos, TB, t) =
  if n > length ts then []
  else let val lev = length apsns
           val lbnos = fold add_lbnos (take n ts) []
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

(* Simplified first-order matching;
   assumes that all Vars in the pattern are distinct;
   see Pure/pattern.ML for the full version;
*)
local
  exception MATCH
in
  fun typ_match thy (tyenv, TU) = Sign.typ_match thy TU tyenv
    handle Type.TYPE_MATCH => raise MATCH;

  fun fomatch thy args =
    let
      fun mtch tyinsts = fn
          (Ts, Var(_,T), t) =>
            typ_match thy (tyinsts, (T, fastype_of1(Ts,t)))
        | (_, Free (a,T), Free (b,U)) =>
            if a=b then typ_match thy (tyinsts,(T,U)) else raise MATCH
        | (_, Const (a,T), Const (b,U)) =>
            if a=b then typ_match thy (tyinsts,(T,U)) else raise MATCH
        | (_, Bound i, Bound j) =>
            if i=j then tyinsts else raise MATCH
        | (Ts, Abs(_,T,t), Abs(_,U,u)) =>
            mtch (typ_match thy (tyinsts,(T,U))) (U::Ts,t,u)
        | (Ts, f$t, g$u) =>
            mtch (mtch tyinsts (Ts,f,g)) (Ts, t, u)
        | _ => raise MATCH
    in (mtch Vartab.empty args; true) handle MATCH => false end;
end;

fun split_posns (cmap : (string * (typ * term * thm * typ * int) list) list) thy Ts t =
  let
    val T' = fastype_of1 (Ts, t);
    fun posns Ts pos apsns (Abs (_, T, t)) =
          let val U = fastype_of1 (T::Ts,t)
          in posns (T::Ts) (0::pos) ((T, U, pos)::apsns) t end
      | posns Ts pos apsns t =
          let
            val (h, ts) = strip_comb t
            fun iter t (i, a) = (i+1, (posns Ts (i::pos) apsns t) @ a);
            val a =
              case h of
                Const(c, cT) =>
                  let fun find [] = []
                        | find ((gcT, pat, thm, T, n)::tups) =
                            let val t2 = list_comb (h, take n ts) in
                              if Sign.typ_instance thy (cT, gcT) andalso fomatch thy (Ts, pat, t2)
                              then mk_split_pack(thm,T,T',n,ts,apsns,pos,type_of1(Ts,t2),t2)
                              else find tups
                            end
                  in find (these (AList.lookup (op =) cmap c)) end
              | _ => []
          in snd (fold iter ts (0, a)) end
  in posns Ts [] [] t end;

fun shorter ((_,ps,pos,_,_), (_,qs,qos,_,_)) =
  prod_ord (int_ord o pairself length) (order o pairself length)
    ((ps, pos), (qs, qos));


(************************************************************
   call split_posns with appropriate parameters
*************************************************************)

fun select cmap state i =
  let
    val thy = Thm.theory_of_thm state
    val goal = term_of (Thm.cprem_of state i);
    val Ts = rev (map #2 (Logic.strip_params goal));
    val _ $ t $ _ = Logic.strip_assums_concl goal;
  in (Ts, t, sort shorter (split_posns cmap thy Ts t)) end;

fun exported_split_posns cmap thy Ts t =
  sort shorter (split_posns cmap thy Ts t);

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
    val cert = cterm_of (Thm.theory_of_thm state);
    val cntxt = mk_cntxt Ts t pos (T --> U) (Thm.maxidx_of trlift);
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
    val thm' = Thm.lift_rule (Thm.cprem_of state i) thm;
    val (P, _) = strip_comb (fst (Logic.dest_equals
      (Logic.strip_assums_concl (Thm.prop_of thm'))));
    val cert = cterm_of (Thm.theory_of_thm state);
    val cntxt = mk_cntxt_splitthm t tt TB;
    val abss = fold (fn T => fn t => Abs ("", T, t));
  in cterm_instantiate [(cert P, cert (abss Ts cntxt))] thm'
  end;


(*****************************************************************************
   The split-tactic

   splits : list of split-theorems to be tried
   i      : number of subgoal the tactic should be applied to
*****************************************************************************)

fun split_tac [] i = no_tac
  | split_tac splits i =
  let val cmap = cmap_of_split_thms splits
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

in (split_tac, exported_split_posns) end;  (* mk_case_split_tac *)


val (split_tac, split_posns) = mk_case_split_tac int_ord;

val (split_inside_tac, _) = mk_case_split_tac (rev_order o int_ord);


(*****************************************************************************
   The split-tactic for premises

   splits : list of split-theorems to be tried
****************************************************************************)
fun split_asm_tac [] = K no_tac
  | split_asm_tac splits =

  let val cname_list = map (fst o fst o split_thm_info) splits;
      fun tac (t,i) =
          let val n = find_index (exists_Const (member (op =) cname_list o #1))
                                 (Logic.strip_assums_hyp t);
              fun first_prem_is_disj (Const ("==>", _) $ (Const (c, _)
                    $ (Const (s, _) $ _ $ _ )) $ _ ) = c = const_Trueprop andalso s = const_or
              |   first_prem_is_disj (Const("all",_)$Abs(_,_,t)) =
                                        first_prem_is_disj t
              |   first_prem_is_disj _ = false;
      (* does not work properly if the split variable is bound by a quantifier *)
              fun flat_prems_tac i = SUBGOAL (fn (t,i) =>
                           (if first_prem_is_disj t
                            then EVERY[etac Data.disjE i,rotate_tac ~1 i,
                                       rotate_tac ~1  (i+1),
                                       flat_prems_tac (i+1)]
                            else all_tac)
                           THEN REPEAT (eresolve_tac [Data.conjE,Data.exE] i)
                           THEN REPEAT (dresolve_tac [Data.notnotD]   i)) i;
          in if n<0 then  no_tac  else (DETERM (EVERY'
                [rotate_tac n, etac Data.contrapos2,
                 split_tac splits,
                 rotate_tac ~1, etac Data.contrapos, rotate_tac ~1,
                 flat_prems_tac] i))
          end;
  in SUBGOAL tac
  end;

fun gen_split_tac [] = K no_tac
  | gen_split_tac (split::splits) =
      let val (_,asm) = split_thm_info split
      in (if asm then split_asm_tac else split_tac) [split] ORELSE'
         gen_split_tac splits
      end;


(** declare split rules **)

(* add_split / del_split *)

fun string_of_typ (Type (s, Ts)) =
      (if null Ts then "" else enclose "(" ")" (commas (map string_of_typ Ts))) ^ s
  | string_of_typ _ = "_";

fun split_name (name, T) asm = "split " ^
  (if asm then "asm " else "") ^ name ^ " :: " ^ string_of_typ T;

fun add_split split ss =
  let
    val (name, asm) = split_thm_info split
    val tac = (if asm then split_asm_tac else split_tac) [split]
  in Simplifier.addloop (ss, (split_name name asm, tac)) end;

fun del_split split ss =
  let val (name, asm) = split_thm_info split
  in Simplifier.delloop (ss, split_name name asm) end;


(* attributes *)

val splitN = "split";

val split_add = Simplifier.attrib add_split;
val split_del = Simplifier.attrib del_split;


(* methods *)

val split_modifiers =
 [Args.$$$ splitN -- Args.colon >> K ((I, split_add): Method.modifier),
  Args.$$$ splitN -- Args.add -- Args.colon >> K (I, split_add),
  Args.$$$ splitN -- Args.del -- Args.colon >> K (I, split_del)];


(* theory setup *)

val setup =
  Attrib.setup @{binding split}
    (Attrib.add_del split_add split_del) "declare case split rule" #>
  Method.setup @{binding split}
    (Attrib.thms >> (fn ths => K (SIMPLE_METHOD' (CHANGED_PROP o gen_split_tac ths))))
    "apply case split rule";

end;
