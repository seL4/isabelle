(* ========================================================================= *)
(* ORDERED REWRITING FOR FIRST ORDER TERMS                                   *)
(* Copyright (c) 2003 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Rewrite :> Rewrite =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Orientations of equations.                                                *)
(* ------------------------------------------------------------------------- *)

datatype orient = LeftToRight | RightToLeft;

fun toStringOrient ort =
    case ort of
      LeftToRight => "-->"
    | RightToLeft => "<--";

val ppOrient = Print.ppMap toStringOrient Print.ppString;

fun toStringOrientOption orto =
    case orto of
      SOME ort => toStringOrient ort
    | NONE => "<->";

val ppOrientOption = Print.ppMap toStringOrientOption Print.ppString;

(* ------------------------------------------------------------------------- *)
(* A type of rewrite systems.                                                *)
(* ------------------------------------------------------------------------- *)

type reductionOrder = Term.term * Term.term -> order option;

type equationId = int;

type equation = Rule.equation;

datatype rewrite =
    Rewrite of
      {order : reductionOrder,
       known : (equation * orient option) IntMap.map,
       redexes : (equationId * orient) TermNet.termNet,
       subterms : (equationId * bool * Term.path) TermNet.termNet,
       waiting : IntSet.set};

fun updateWaiting rw waiting =
    let
      val Rewrite {order, known, redexes, subterms, waiting = _} = rw
    in
      Rewrite
        {order = order, known = known, redexes = redexes,
         subterms = subterms, waiting = waiting}
    end;

fun deleteWaiting (rw as Rewrite {waiting,...}) id =
    updateWaiting rw (IntSet.delete waiting id);

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

fun new order =
    Rewrite
      {order = order,
       known = IntMap.new (),
       redexes = TermNet.new {fifo = false},
       subterms = TermNet.new {fifo = false},
       waiting = IntSet.empty};

fun peek (Rewrite {known,...}) id = IntMap.peek known id;

fun size (Rewrite {known,...}) = IntMap.size known;

fun equations (Rewrite {known,...}) =
    IntMap.foldr (fn (_,(eqn,_),eqns) => eqn :: eqns) [] known;

val pp = Print.ppMap equations (Print.ppList Rule.ppEquation);

(*MetisTrace1
local
  fun ppEq ((x_y,_),ort) =
      Print.ppOp2 (" " ^ toStringOrientOption ort) Term.pp Term.pp x_y;

  fun ppField f ppA a =
      Print.inconsistentBlock 2
        [Print.ppString (f ^ " ="),
         Print.break,
         ppA a];

  val ppKnown =
      ppField "known"
        (Print.ppMap IntMap.toList
           (Print.ppList (Print.ppPair Print.ppInt ppEq)));

  val ppRedexes =
      ppField "redexes"
        (TermNet.pp (Print.ppPair Print.ppInt ppOrient));

  val ppSubterms =
      ppField "subterms"
        (TermNet.pp
           (Print.ppMap
              (fn (i,l,p) => (i, (if l then 0 else 1) :: p))
              (Print.ppPair Print.ppInt Term.ppPath)));

  val ppWaiting =
      ppField "waiting"
        (Print.ppMap (IntSet.toList) (Print.ppList Print.ppInt));
in
  fun pp (Rewrite {known,redexes,subterms,waiting,...}) =
      Print.inconsistentBlock 2
        [Print.ppString "Rewrite",
         Print.break,
         Print.inconsistentBlock 1
           [Print.ppString "{",
            ppKnown known,
(*MetisTrace5
            Print.ppString ",",
            Print.break,
            ppRedexes redexes,
            Print.ppString ",",
            Print.break,
            ppSubterms subterms,
            Print.ppString ",",
            Print.break,
            ppWaiting waiting,
*)
            Print.skip],
         Print.ppString "}"]
end;
*)

val toString = Print.toString pp;

(* ------------------------------------------------------------------------- *)
(* Debug functions.                                                          *)
(* ------------------------------------------------------------------------- *)

fun termReducible order known id =
    let
      fun eqnRed ((l,r),_) tm =
          case total (Subst.match Subst.empty l) tm of
            NONE => false
          | SOME sub =>
            order (tm, Subst.subst (Subst.normalize sub) r) = SOME GREATER

      fun knownRed tm (eqnId,(eqn,ort)) =
          eqnId <> id andalso
          ((ort <> SOME RightToLeft andalso eqnRed eqn tm) orelse
           (ort <> SOME LeftToRight andalso eqnRed (Rule.symEqn eqn) tm))

      fun termRed tm = IntMap.exists (knownRed tm) known orelse subtermRed tm
      and subtermRed (Term.Var _) = false
        | subtermRed (Term.Fn (_,tms)) = List.exists termRed tms
    in
      termRed
    end;

fun literalReducible order known id lit =
    List.exists (termReducible order known id) (Literal.arguments lit);

fun literalsReducible order known id lits =
    LiteralSet.exists (literalReducible order known id) lits;

fun thmReducible order known id th =
    literalsReducible order known id (Thm.clause th);

(* ------------------------------------------------------------------------- *)
(* Add equations into the system.                                            *)
(* ------------------------------------------------------------------------- *)

fun orderToOrient (SOME EQUAL) = raise Error "Rewrite.orient: reflexive"
  | orderToOrient (SOME GREATER) = SOME LeftToRight
  | orderToOrient (SOME LESS) = SOME RightToLeft
  | orderToOrient NONE = NONE;

local
  fun ins redexes redex id ort = TermNet.insert redexes (redex,(id,ort));
in
  fun addRedexes id (((l,r),_),ort) redexes =
      case ort of
        SOME LeftToRight => ins redexes l id LeftToRight
      | SOME RightToLeft => ins redexes r id RightToLeft
      | NONE => ins (ins redexes l id LeftToRight) r id RightToLeft;
end;

fun add (rw as Rewrite {known,...}) (id,eqn) =
    if IntMap.inDomain id known then rw
    else
      let
        val Rewrite {order,redexes,subterms,waiting, ...} = rw

        val ort = orderToOrient (order (fst eqn))

        val known = IntMap.insert known (id,(eqn,ort))

        val redexes = addRedexes id (eqn,ort) redexes

        val waiting = IntSet.add waiting id

        val rw =
            Rewrite
              {order = order, known = known, redexes = redexes,
               subterms = subterms, waiting = waiting}
(*MetisTrace5
        val () = Print.trace pp "Rewrite.add: result" rw
*)
      in
        rw
      end;

local
  fun uncurriedAdd (eqn,rw) = add rw eqn;
in
  fun addList rw = List.foldl uncurriedAdd rw;
end;

(* ------------------------------------------------------------------------- *)
(* Rewriting (the order must be a refinement of the rewrite order).          *)
(* ------------------------------------------------------------------------- *)

local
  fun reorder ((i,_),(j,_)) = Int.compare (j,i);
in
  fun matchingRedexes redexes tm = sort reorder (TermNet.match redexes tm);
end;

fun wellOriented NONE _ = true
  | wellOriented (SOME LeftToRight) LeftToRight = true
  | wellOriented (SOME RightToLeft) RightToLeft = true
  | wellOriented _ _ = false;

fun redexResidue LeftToRight ((l_r,_) : equation) = l_r
  | redexResidue RightToLeft ((l,r),_) = (r,l);

fun orientedEquation LeftToRight eqn = eqn
  | orientedEquation RightToLeft eqn = Rule.symEqn eqn;

fun rewrIdConv' order known redexes id tm =
    let
      fun rewr (id',lr) =
          let
            val _ = id <> id' orelse raise Error "same theorem"
            val (eqn,ort) = IntMap.get known id'
            val _ = wellOriented ort lr orelse raise Error "orientation"
            val (l,r) = redexResidue lr eqn
            val sub = Subst.normalize (Subst.match Subst.empty l tm)
            val tm' = Subst.subst sub r
            val _ = Option.isSome ort orelse
                    order (tm,tm') = SOME GREATER orelse
                    raise Error "order"
            val (_,th) = orientedEquation lr eqn
          in
            (tm', Thm.subst sub th)
          end
    in
      case first (total rewr) (matchingRedexes redexes tm) of
        NONE => raise Error "Rewrite.rewrIdConv: no matching rewrites"
      | SOME res => res
    end;

fun rewriteIdConv' order known redexes id =
    if IntMap.null known then Rule.allConv
    else Rule.repeatTopDownConv (rewrIdConv' order known redexes id);

fun mkNeqConv order lit =
    let
      val (l,r) = Literal.destNeq lit
    in
      case order (l,r) of
        NONE => raise Error "incomparable"
      | SOME LESS =>
        let
          val th = Rule.symmetryRule l r
        in
          fn tm =>
             if Term.equal tm r then (l,th) else raise Error "mkNeqConv: RL"
        end
      | SOME EQUAL => raise Error "irreflexive"
      | SOME GREATER =>
        let
          val th = Thm.assume lit
        in
          fn tm =>
             if Term.equal tm l then (r,th) else raise Error "mkNeqConv: LR"
        end
    end;

datatype neqConvs = NeqConvs of Rule.conv LiteralMap.map;

val neqConvsEmpty = NeqConvs (LiteralMap.new ());

fun neqConvsNull (NeqConvs m) = LiteralMap.null m;

fun neqConvsAdd order (neq as NeqConvs m) lit =
    case total (mkNeqConv order) lit of
      NONE => NONE
    | SOME conv => SOME (NeqConvs (LiteralMap.insert m (lit,conv)));

fun mkNeqConvs order =
    let
      fun add (lit,(neq,lits)) =
          case neqConvsAdd order neq lit of
            SOME neq => (neq,lits)
          | NONE => (neq, LiteralSet.add lits lit)
    in
      LiteralSet.foldl add (neqConvsEmpty,LiteralSet.empty)
    end;

fun neqConvsDelete (NeqConvs m) lit = NeqConvs (LiteralMap.delete m lit);

fun neqConvsToConv (NeqConvs m) =
    Rule.firstConv (LiteralMap.foldr (fn (_,c,l) => c :: l) [] m);

fun neqConvsFoldl f b (NeqConvs m) =
    LiteralMap.foldl (fn (l,_,z) => f (l,z)) b m;

fun neqConvsRewrIdLiterule order known redexes id neq =
    if IntMap.null known andalso neqConvsNull neq then Rule.allLiterule
    else
      let
        val neq_conv = neqConvsToConv neq
        val rewr_conv = rewrIdConv' order known redexes id
        val conv = Rule.orelseConv neq_conv rewr_conv
        val conv = Rule.repeatTopDownConv conv
      in
        Rule.allArgumentsLiterule conv
      end;

fun rewriteIdEqn' order known redexes id (eqn as (l_r,th)) =
    let
      val (neq,_) = mkNeqConvs order (Thm.clause th)
      val literule = neqConvsRewrIdLiterule order known redexes id neq
      val (strongEqn,lit) =
          case Rule.equationLiteral eqn of
            NONE => (true, Literal.mkEq l_r)
          | SOME lit => (false,lit)
      val (lit',litTh) = literule lit
    in
      if Literal.equal lit lit' then eqn
      else
        (Literal.destEq lit',
         if strongEqn then th
         else if not (Thm.negateMember lit litTh) then litTh
         else Thm.resolve lit th litTh)
    end
(*MetisDebug
    handle Error err => raise Error ("Rewrite.rewriteIdEqn':\n" ^ err);
*)

fun rewriteIdLiteralsRule' order known redexes id lits th =
    let
      val mk_literule = neqConvsRewrIdLiterule order known redexes id

      fun rewr_neq_lit (lit, acc as (changed,neq,lits,th)) =
          let
            val neq = neqConvsDelete neq lit
            val (lit',litTh) = mk_literule neq lit
          in
            if Literal.equal lit lit' then acc
            else
              let
                val th = Thm.resolve lit th litTh
              in
                case neqConvsAdd order neq lit' of
                  SOME neq => (true,neq,lits,th)
                | NONE => (changed, neq, LiteralSet.add lits lit', th)
              end
          end

      fun rewr_neq_lits neq lits th =
          let
            val (changed,neq,lits,th) =
                neqConvsFoldl rewr_neq_lit (false,neq,lits,th) neq
          in
            if changed then rewr_neq_lits neq lits th
            else (neq,lits,th)
          end

      val (neq,lits) = mkNeqConvs order lits

      val (neq,lits,th) = rewr_neq_lits neq lits th

      val rewr_literule = mk_literule neq

      fun rewr_lit (lit,th) =
          if Thm.member lit th then Rule.literalRule rewr_literule lit th
          else th
    in
      LiteralSet.foldl rewr_lit th lits
    end;

fun rewriteIdRule' order known redexes id th =
    rewriteIdLiteralsRule' order known redexes id (Thm.clause th) th;

(*MetisDebug
val rewriteIdRule' = fn order => fn known => fn redexes => fn id => fn th =>
    let
(*MetisTrace6
      val () = Print.trace Thm.pp "Rewrite.rewriteIdRule': th" th
*)
      val result = rewriteIdRule' order known redexes id th
(*MetisTrace6
      val () = Print.trace Thm.pp "Rewrite.rewriteIdRule': result" result
*)
      val _ = not (thmReducible order known id result) orelse
              raise Bug "rewriteIdRule: should be normalized"
    in
      result
    end
    handle Error err => raise Error ("Rewrite.rewriteIdRule:\n" ^ err);
*)

fun rewrIdConv (Rewrite {known,redexes,...}) order =
    rewrIdConv' order known redexes;

fun rewrConv rewrite order = rewrIdConv rewrite order ~1;

fun rewriteIdConv (Rewrite {known,redexes,...}) order =
    rewriteIdConv' order known redexes;

fun rewriteConv rewrite order = rewriteIdConv rewrite order ~1;

fun rewriteIdLiteralsRule (Rewrite {known,redexes,...}) order =
    rewriteIdLiteralsRule' order known redexes;

fun rewriteLiteralsRule rewrite order =
    rewriteIdLiteralsRule rewrite order ~1;

fun rewriteIdRule (Rewrite {known,redexes,...}) order =
    rewriteIdRule' order known redexes;

fun rewriteRule rewrite order = rewriteIdRule rewrite order ~1;

(* ------------------------------------------------------------------------- *)
(* Inter-reduce the equations in the system.                                 *)
(* ------------------------------------------------------------------------- *)

fun addSubterms id (((l,r),_) : equation) subterms =
    let
      fun addSubterm b ((path,tm),net) = TermNet.insert net (tm,(id,b,path))

      val subterms = List.foldl (addSubterm true) subterms (Term.subterms l)

      val subterms = List.foldl (addSubterm false) subterms (Term.subterms r)
    in
      subterms
    end;

fun sameRedexes NONE _ _ = false
  | sameRedexes (SOME LeftToRight) (l0,_) (l,_) = Term.equal l0 l
  | sameRedexes (SOME RightToLeft) (_,r0) (_,r) = Term.equal r0 r;

fun redexResidues NONE (l,r) = [(l,r,false),(r,l,false)]
  | redexResidues (SOME LeftToRight) (l,r) = [(l,r,true)]
  | redexResidues (SOME RightToLeft) (l,r) = [(r,l,true)];

fun findReducibles order known subterms id =
    let
      fun checkValidRewr (l,r,ord) id' left path =
          let
            val (((x,y),_),_) = IntMap.get known id'
            val tm = Term.subterm (if left then x else y) path
            val sub = Subst.match Subst.empty l tm
          in
            if ord then ()
            else
              let
                val tm' = Subst.subst (Subst.normalize sub) r
              in
                if order (tm,tm') = SOME GREATER then ()
                else raise Error "order"
              end
          end

      fun addRed lr ((id',left,path),todo) =
          if id <> id' andalso not (IntSet.member id' todo) andalso
             can (checkValidRewr lr id' left) path
          then IntSet.add todo id'
          else todo

      fun findRed (lr as (l,_,_), todo) =
          List.foldl (addRed lr) todo (TermNet.matched subterms l)
    in
      List.foldl findRed
    end;

fun reduce1 new id (eqn0,ort0) (rpl,spl,todo,rw,changed) =
    let
      val (eq0,_) = eqn0
      val Rewrite {order,known,redexes,subterms,waiting} = rw
      val eqn as (eq,_) = rewriteIdEqn' order known redexes id eqn0
      val identical =
          let
            val (l0,r0) = eq0
            and (l,r) = eq
          in
            Term.equal l l0 andalso Term.equal r r0
          end
      val same_redexes = identical orelse sameRedexes ort0 eq0 eq
      val rpl = if same_redexes then rpl else IntSet.add rpl id
      val spl = if new orelse identical then spl else IntSet.add spl id
      val changed =
          if not new andalso identical then changed else IntSet.add changed id
      val ort =
          if same_redexes then SOME ort0 else total orderToOrient (order eq)
    in
      case ort of
        NONE =>
        let
          val known = IntMap.delete known id
          val rw =
              Rewrite
                {order = order, known = known, redexes = redexes,
                 subterms = subterms, waiting = waiting}
        in
          (rpl,spl,todo,rw,changed)
        end
      | SOME ort =>
        let
          val todo =
              if not new andalso same_redexes then todo
              else
                findReducibles
                  order known subterms id todo (redexResidues ort eq)
          val known =
              if identical then known else IntMap.insert known (id,(eqn,ort))
          val redexes =
              if same_redexes then redexes
              else addRedexes id (eqn,ort) redexes
          val subterms =
              if new orelse not identical then addSubterms id eqn subterms
              else subterms
          val rw =
              Rewrite
                {order = order, known = known, redexes = redexes,
                 subterms = subterms, waiting = waiting}
        in
          (rpl,spl,todo,rw,changed)
        end
    end;

fun pick known set =
    let
      fun oriented id =
          case IntMap.peek known id of
            SOME (x as (_, SOME _)) => SOME (id,x)
          | _ => NONE

      fun any id =
          case IntMap.peek known id of SOME x => SOME (id,x) | _ => NONE
    in
      case IntSet.firstl oriented set of
        x as SOME _ => x
      | NONE => IntSet.firstl any set
    end;

local
  fun cleanRedexes known redexes rpl =
      if IntSet.null rpl then redexes
      else
        let
          fun filt (id,_) = not (IntSet.member id rpl)

          fun addReds (id,reds) =
              case IntMap.peek known id of
                NONE => reds
              | SOME eqn_ort => addRedexes id eqn_ort reds

          val redexes = TermNet.filter filt redexes
          val redexes = IntSet.foldl addReds redexes rpl
        in
          redexes
        end;

  fun cleanSubterms known subterms spl =
      if IntSet.null spl then subterms
      else
        let
          fun filt (id,_,_) = not (IntSet.member id spl)

          fun addSubtms (id,subtms) =
              case IntMap.peek known id of
                NONE => subtms
              | SOME (eqn,_) => addSubterms id eqn subtms

          val subterms = TermNet.filter filt subterms
          val subterms = IntSet.foldl addSubtms subterms spl
        in
          subterms
        end;
in
  fun rebuild rpl spl rw =
      let
(*MetisTrace5
        val ppPl = Print.ppMap IntSet.toList (Print.ppList Print.ppInt)
        val () = Print.trace ppPl "Rewrite.rebuild: rpl" rpl
        val () = Print.trace ppPl "Rewrite.rebuild: spl" spl
*)
        val Rewrite {order,known,redexes,subterms,waiting} = rw
        val redexes = cleanRedexes known redexes rpl
        val subterms = cleanSubterms known subterms spl
      in
        Rewrite
          {order = order,
           known = known,
           redexes = redexes,
           subterms = subterms,
           waiting = waiting}
      end;
end;

fun reduceAcc (rpl, spl, todo, rw as Rewrite {known,waiting,...}, changed) =
    case pick known todo of
      SOME (id,eqn_ort) =>
      let
        val todo = IntSet.delete todo id
      in
        reduceAcc (reduce1 false id eqn_ort (rpl,spl,todo,rw,changed))
      end
    | NONE =>
      case pick known waiting of
        SOME (id,eqn_ort) =>
        let
          val rw = deleteWaiting rw id
        in
          reduceAcc (reduce1 true id eqn_ort (rpl,spl,todo,rw,changed))
        end
      | NONE => (rebuild rpl spl rw, IntSet.toList changed);

fun isReduced (Rewrite {waiting,...}) = IntSet.null waiting;

fun reduce' rw =
    if isReduced rw then (rw,[])
    else reduceAcc (IntSet.empty,IntSet.empty,IntSet.empty,rw,IntSet.empty);

(*MetisDebug
val reduce' = fn rw =>
    let
(*MetisTrace4
      val () = Print.trace pp "Rewrite.reduce': rw" rw
*)
      val Rewrite {known,order,...} = rw
      val result as (Rewrite {known = known', ...}, _) = reduce' rw
(*MetisTrace4
      val ppResult = Print.ppPair pp (Print.ppList Print.ppInt)
      val () = Print.trace ppResult "Rewrite.reduce': result" result
*)
      val ths = List.map (fn (id,((_,th),_)) => (id,th)) (IntMap.toList known')
      val _ =
          not (List.exists (uncurry (thmReducible order known')) ths) orelse
          raise Bug "Rewrite.reduce': not fully reduced"
    in
      result
    end
    handle Error err => raise Bug ("Rewrite.reduce': shouldn't fail\n" ^ err);
*)

fun reduce rw = fst (reduce' rw);

(* ------------------------------------------------------------------------- *)
(* Rewriting as a derived rule.                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun addEqn (id_eqn,rw) = add rw id_eqn;
in
  fun orderedRewrite order ths =
    let
      val rw = List.foldl addEqn (new order) (enumerate ths)
    in
      rewriteRule rw order
    end;
end;

local
  val order : reductionOrder = K (SOME GREATER);
in
  val rewrite = orderedRewrite order;
end;

end
