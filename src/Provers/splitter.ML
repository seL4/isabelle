(*  Title:      Provers/splitter.ML
    Author:     Tobias Nipkow
    Copyright   1995  TU Munich

Generic case-splitter, suitable for most logics.
Deals with equalities of the form ?P(f args) = ...
where "f args" must be a first-order term without duplicate variables.
*)

signature SPLITTER_DATA =
sig
  val context       : Proof.context
  val mk_eq         : thm -> thm
  val meta_eq_to_iff: thm (* "x == y ==> x = y"                      *)
  val iffD          : thm (* "[| P = Q; Q |] ==> P"                  *)
  val disjE         : thm (* "[| P | Q; P ==> R; Q ==> R |] ==> R"   *)
  val conjE         : thm (* "[| P & Q; [| P; Q |] ==> R |] ==> R"   *)
  val exE           : thm (* "[| EX x. P x; !!x. P x ==> Q |] ==> Q" *)
  val contrapos     : thm (* "[| ~ Q; P ==> Q |] ==> ~ P"            *)
  val contrapos2    : thm (* "[| Q; ~ P ==> ~ Q |] ==> P"            *)
  val notnotD       : thm (* "~ ~ P ==> P"                           *)
  val safe_tac      : Proof.context -> tactic
end

signature SPLITTER =
sig
  (* somewhat more internal functions *)
  val cmap_of_split_thms: thm list -> (string * (typ * term * thm * typ * int) list) list
  val split_posns: (string * (typ * term * thm * typ * int) list) list ->
    theory -> typ list -> term -> (thm * (typ * typ * int list) list * int list * typ * term) list
    (* first argument is a "cmap", returns a list of "split packs" *)
  (* the "real" interface, providing a number of tactics *)
  val split_tac       : Proof.context -> thm list -> int -> tactic
  val split_inside_tac: Proof.context -> thm list -> int -> tactic
  val split_asm_tac   : Proof.context -> thm list -> int -> tactic
  val add_split: thm -> Proof.context -> Proof.context
  val add_split_bang: thm -> Proof.context -> Proof.context
  val del_split: thm -> Proof.context -> Proof.context
  val split_modifiers : Method.modifier parser list
end;

functor Splitter(Data: SPLITTER_DATA): SPLITTER =
struct

val Const (const_not, _) $ _ =
  Object_Logic.drop_judgment Data.context
    (#1 (Logic.dest_implies (Thm.prop_of Data.notnotD)));

val Const (const_or , _) $ _ $ _ =
  Object_Logic.drop_judgment Data.context
    (#1 (Logic.dest_implies (Thm.prop_of Data.disjE)));

val const_Trueprop = Object_Logic.judgment_name Data.context;


fun split_format_err () = error "Wrong format for split rule";

fun split_thm_info thm =
  (case Thm.concl_of (Data.mk_eq thm) of
    \<^Const_>\<open>Pure.eq _ for \<open>Var _ $ t\<close> c\<close> =>
      (case strip_comb t of
        (Const p, _) => (p, case c of (Const (s, _) $ _) => s = const_not | _ => false)
      | _ => split_format_err ())
  | _ => split_format_err ());

fun cmap_of_split_thms thms =
let
  val splits = map Data.mk_eq thms
  fun add_thm thm cmap =
    (case Thm.concl_of thm of _ $ (t as _ $ lhs) $ _ =>
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

val abss = fold (Term.abs o pair "");

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

val lift = Goal.prove_global \<^theory> ["P", "Q", "R"]
  [Syntax.read_prop_global \<^theory>\<open>Pure\<close> "!!x :: 'b. Q(x) == R(x) :: 'c"]
  (Syntax.read_prop_global \<^theory>\<open>Pure\<close> "P(%x. Q(x)) == P(%x. R(x))")
  (fn {context = ctxt, prems} =>
    rewrite_goals_tac ctxt prems THEN resolve_tac ctxt [reflexive_thm] 1)

val _ $ _ $ (_ $ (_ $ abs_lift) $ _) = Thm.prop_of lift;

val trlift = lift RS transitive_thm;


(************************************************************************
   Set up term for instantiation of P in the lift-theorem

   t     : lefthand side of meta-equality in subgoal
           the lift theorem is applied to (see select)
   pos   : "path" leading to abstraction, coded as a list
   T     : type of body of P(...)
*************************************************************************)

fun mk_cntxt t pos T =
  let
    fun down [] t = (Bound 0, t)
      | down (p :: ps) t =
          let
            val (h, ts) = strip_comb t
            val (ts1, u :: ts2) = chop p ts
            val (u1, u2) = down ps u
          in
            (list_comb (incr_boundvars 1 h,
               map (incr_boundvars 1) ts1 @ u1 ::
               map (incr_boundvars 1) ts2),
             u2)
          end;
    val (u1, u2) = down (rev pos) t
  in (Abs ("", T, u1), u2) end;


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
    if Envir.aeconv(incr_boundvars lev tt, t) then Bound lev
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
   Recursively scans term for occurrences of Const(key,...) $ ...
   Returns a list of "split-packs" (one for each occurrence of Const(key,...) )

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
  prod_ord (int_ord o apply2 length) (order o apply2 length)
    ((ps, pos), (qs, qos));


(************************************************************
   call split_posns with appropriate parameters
*************************************************************)

fun select thy cmap state i =
  let
    val goal = Thm.term_of (Thm.cprem_of state i);
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
   i       : no. of subgoal
**************************************************************)

fun inst_lift ctxt Ts t (T, U, pos) state i =
  let
    val (cntxt, u) = mk_cntxt t pos (T --> U);
    val trlift' = Thm.lift_rule (Thm.cprem_of state i)
      (Thm.rename_boundvars abs_lift u trlift);
    val (Var (P, _), _) =
      strip_comb (fst (Logic.dest_equals
        (Logic.strip_assums_concl (Thm.prop_of trlift'))));
  in infer_instantiate ctxt [(P, Thm.cterm_of ctxt (abss Ts cntxt))] trlift' end;


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

fun inst_split ctxt Ts t tt thm TB state i =
  let
    val thm' = Thm.lift_rule (Thm.cprem_of state i) thm;
    val (Var (P, _), _) =
      strip_comb (fst (Logic.dest_equals
        (Logic.strip_assums_concl (Thm.prop_of thm'))));
    val cntxt = mk_cntxt_splitthm t tt TB;
  in infer_instantiate ctxt [(P, Thm.cterm_of ctxt (abss Ts cntxt))] thm' end;


(*****************************************************************************
   The split-tactic

   splits : list of split-theorems to be tried
   i      : number of subgoal the tactic should be applied to
*****************************************************************************)

fun split_tac _ [] i = no_tac
  | split_tac ctxt splits i =
  let val cmap = cmap_of_split_thms splits
      fun lift_tac Ts t p st = compose_tac ctxt (false, inst_lift ctxt Ts t p st i, 2) i st
      fun lift_split_tac state =
            let val (Ts, t, splits) = select (Proof_Context.theory_of ctxt) cmap state i
            in case splits of
                 [] => no_tac state
               | (thm, apsns, pos, TB, tt)::_ =>
                   (case apsns of
                      [] =>
                        compose_tac ctxt (false, inst_split ctxt Ts t tt thm TB state i, 0) i state
                    | p::_ => EVERY [lift_tac Ts t p,
                                     resolve_tac ctxt [reflexive_thm] (i+1),
                                     lift_split_tac] state)
            end
  in COND (has_fewer_prems i) no_tac
          (resolve_tac ctxt [meta_iffD] i THEN lift_split_tac)
  end;

in (split_tac, exported_split_posns) end;  (* mk_case_split_tac *)


val (split_tac, split_posns) = mk_case_split_tac int_ord;

val (split_inside_tac, _) = mk_case_split_tac (rev_order o int_ord);


(*****************************************************************************
   The split-tactic for premises

   splits : list of split-theorems to be tried
****************************************************************************)
fun split_asm_tac _ [] = K no_tac
  | split_asm_tac ctxt splits =

  let val cname_list = map (fst o fst o split_thm_info) splits;
      fun tac (t,i) =
          let val n = find_index (exists_Const (member (op =) cname_list o #1))
                                 (Logic.strip_assums_hyp t);
              fun first_prem_is_disj (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ (Const (c, _)
                    $ (Const (s, _) $ _ $ _ )) $ _ ) = c = const_Trueprop andalso s = const_or
              |   first_prem_is_disj (Const(\<^const_name>\<open>Pure.all\<close>,_)$Abs(_,_,t)) =
                                        first_prem_is_disj t
              |   first_prem_is_disj _ = false;
      (* does not work properly if the split variable is bound by a quantifier *)
              fun flat_prems_tac i = SUBGOAL (fn (t,i) =>
                           (if first_prem_is_disj t
                            then EVERY[eresolve_tac ctxt [Data.disjE] i, rotate_tac ~1 i,
                                       rotate_tac ~1  (i+1),
                                       flat_prems_tac (i+1)]
                            else all_tac)
                           THEN REPEAT (eresolve_tac ctxt [Data.conjE,Data.exE] i)
                           THEN REPEAT (dresolve_tac ctxt [Data.notnotD]   i)) i;
          in if n<0 then  no_tac  else (DETERM (EVERY'
                [rotate_tac n, eresolve_tac ctxt [Data.contrapos2],
                 split_tac ctxt splits,
                 rotate_tac ~1, eresolve_tac ctxt [Data.contrapos], rotate_tac ~1,
                 flat_prems_tac] i))
          end;
  in SUBGOAL tac
  end;

fun gen_split_tac _ [] = K no_tac
  | gen_split_tac ctxt (split::splits) =
      let val (_,asm) = split_thm_info split
      in (if asm then split_asm_tac else split_tac) ctxt [split] ORELSE'
         gen_split_tac ctxt splits
      end;


(** declare split rules **)

(* add_split / del_split *)

fun string_of_typ (Type (s, Ts)) =
      (if null Ts then "" else enclose "(" ")" (commas (map string_of_typ Ts))) ^ s
  | string_of_typ _ = "_";

fun split_name (name, T) asm = "split " ^
  (if asm then "asm " else "") ^ name ^ " :: " ^ string_of_typ T;

fun gen_add_split bang split ctxt =
  let
    val (name, asm) = split_thm_info split
    val split0 = Thm.trim_context split
    fun tac ctxt' =
      let val split' = Thm.transfer' ctxt' split0 in
        (if asm then split_asm_tac ctxt' [split']
         else if bang
              then split_tac ctxt' [split'] THEN_ALL_NEW
                   TRY o (SELECT_GOAL (Data.safe_tac ctxt'))
              else split_tac ctxt' [split'])
      end
  in Simplifier.addloop (ctxt, (split_name name asm, tac)) end;

val add_split = gen_add_split false;
val add_split_bang = gen_add_split true;

fun del_split split ctxt =
  let val (name, asm) = split_thm_info split
  in Simplifier.delloop (ctxt, split_name name asm) end;


(* attributes *)

val splitN = "split";

fun split_add bang = Simplifier.attrib (gen_add_split bang);
val split_del = Simplifier.attrib del_split;

val add_del = Scan.lift
  (Args.bang >> K (split_add true)
   || Args.del >> K split_del
   || Scan.succeed (split_add false));

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>split\<close> add_del "declare case split rule");


(* methods *)

val split_modifiers =
 [Args.$$$ splitN -- Args.colon >> K (Method.modifier (split_add false) \<^here>),
  Args.$$$ splitN -- Args.bang_colon >> K (Method.modifier (split_add true) \<^here>),
  Args.$$$ splitN -- Args.del -- Args.colon >> K (Method.modifier split_del \<^here>)];

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>split\<close>
      (Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (CHANGED_PROP o gen_split_tac ctxt ths)))
      "apply case split rule");

end;
