(* ========================================================================= *)
(* THE ACTIVE SET OF CLAUSES                                                 *)
(* Copyright (c) 2002 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Active :> Active =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

(*MetisDebug
local
  fun mkRewrite ordering =
      let
        fun add (cl,rw) =
            let
              val {id, thm = th, ...} = Clause.dest cl
            in
              case total Thm.destUnitEq th of
                SOME l_r => Rewrite.add rw (id,(l_r,th))
              | NONE => rw
            end
      in
        List.foldl add (Rewrite.new (KnuthBendixOrder.compare ordering))
      end;

  fun allFactors red =
      let
        fun allClause cl =
            List.all red (cl :: Clause.factor cl) orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allFactors: cl" cl
            in
              false
            end
      in
        List.all allClause
      end;

  fun allResolutions red =
      let
        fun allClause2 cl_lit cl =
            let
              fun allLiteral2 lit =
                  case total (Clause.resolve cl_lit) (cl,lit) of
                    NONE => true
                  | SOME cl => allFactors red [cl]
            in
              LiteralSet.all allLiteral2 (Clause.literals cl)
            end orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allResolutions: cl2" cl
            in
              false
            end

        fun allClause1 allCls cl =
            let
              val cl = Clause.freshVars cl

              fun allLiteral1 lit = List.all (allClause2 (cl,lit)) allCls
            in
              LiteralSet.all allLiteral1 (Clause.literals cl)
            end orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allResolutions: cl1" cl
            in
              false
            end

      in
        fn [] => true
         | allCls as cl :: cls =>
           allClause1 allCls cl andalso allResolutions red cls
      end;

  fun allParamodulations red cls =
      let
        fun allClause2 cl_lit_ort_tm cl =
            let
              fun allLiteral2 lit =
                  let
                    val para = Clause.paramodulate cl_lit_ort_tm

                    fun allSubterms (path,tm) =
                        case total para (cl,lit,path,tm) of
                          NONE => true
                        | SOME cl => allFactors red [cl]
                  in
                    List.all allSubterms (Literal.nonVarTypedSubterms lit)
                  end orelse
                  let
                    val () = Print.trace Literal.pp
                               "Active.isSaturated.allParamodulations: lit2" lit
                  in
                    false
                  end
            in
              LiteralSet.all allLiteral2 (Clause.literals cl)
            end orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allParamodulations: cl2" cl
              val (_,_,ort,_) = cl_lit_ort_tm
              val () = Print.trace Rewrite.ppOrient
                         "Active.isSaturated.allParamodulations: ort1" ort
            in
              false
            end

        fun allClause1 cl =
            let
              val cl = Clause.freshVars cl

              fun allLiteral1 lit =
                  let
                    fun allCl2 x = List.all (allClause2 x) cls
                  in
                    case total Literal.destEq lit of
                      NONE => true
                    | SOME (l,r) =>
                      allCl2 (cl,lit,Rewrite.LeftToRight,l) andalso
                      allCl2 (cl,lit,Rewrite.RightToLeft,r)
                  end orelse
                  let
                    val () = Print.trace Literal.pp
                               "Active.isSaturated.allParamodulations: lit1" lit
                  in
                    false
                  end
            in
              LiteralSet.all allLiteral1 (Clause.literals cl)
            end orelse
            let
              val () = Print.trace Clause.pp
                         "Active.isSaturated.allParamodulations: cl1" cl
            in
              false
            end
      in
        List.all allClause1 cls
      end;

  fun redundant {subsume,reduce,rewrite} =
      let
        fun simp cl =
            case Clause.simplify cl of
              NONE => true
            | SOME cl =>
              Subsume.isStrictlySubsumed subsume (Clause.literals cl) orelse
              let
                val cl' = cl
                val cl' = Clause.reduce reduce cl'
                val cl' = Clause.rewrite rewrite cl'
              in
                not (Clause.equalThms cl cl') andalso
                (simp cl' orelse
                 let
                   val () = Print.trace Clause.pp
                              "Active.isSaturated.redundant: cl'" cl'
                 in
                   false
                 end)
              end
      in
        fn cl =>
           simp cl orelse
           let
             val () = Print.trace Clause.pp
                        "Active.isSaturated.redundant: cl" cl
           in
             false
           end
      end;
in
  fun isSaturated ordering subs cls =
      let
        val rd = Units.empty
        val rw = mkRewrite ordering cls
        val red = redundant {subsume = subs, reduce = rd, rewrite = rw}
      in
        (allFactors red cls andalso
         allResolutions red cls andalso
         allParamodulations red cls) orelse
        let
          val () = Print.trace Rewrite.pp "Active.isSaturated: rw" rw
          val () = Print.trace (Print.ppList Clause.pp)
                     "Active.isSaturated: clauses" cls
        in
          false
        end
      end;
end;

fun checkSaturated ordering subs cls =
    if isSaturated ordering subs cls then ()
    else raise Bug "Active.checkSaturated";
*)

(* ------------------------------------------------------------------------- *)
(* A type of active clause sets.                                             *)
(* ------------------------------------------------------------------------- *)

type simplify = {subsume : bool, reduce : bool, rewrite : bool};

type parameters =
     {clause : Clause.parameters,
      prefactor : simplify,
      postfactor : simplify};

datatype active =
    Active of
      {parameters : parameters,
       clauses : Clause.clause IntMap.map,
       units : Units.units,
       rewrite : Rewrite.rewrite,
       subsume : Clause.clause Subsume.subsume,
       literals : (Clause.clause * Literal.literal) LiteralNet.literalNet,
       equations :
         (Clause.clause * Literal.literal * Rewrite.orient * Term.term)
         TermNet.termNet,
       subterms :
         (Clause.clause * Literal.literal * Term.path * Term.term)
         TermNet.termNet,
       allSubterms : (Clause.clause * Term.term) TermNet.termNet};

fun getSubsume (Active {subsume = s, ...}) = s;

fun setRewrite active rewrite =
    let
      val Active
            {parameters,clauses,units,subsume,literals,equations,
             subterms,allSubterms,...} = active
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms, allSubterms = allSubterms}
    end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val maxSimplify : simplify = {subsume = true, reduce = true, rewrite = true};

val default : parameters =
    {clause = Clause.default,
     prefactor = maxSimplify,
     postfactor = maxSimplify};

fun empty parameters =
    let
      val {clause,...} = parameters
      val {ordering,...} = clause
    in
      Active
        {parameters = parameters,
         clauses = IntMap.new (),
         units = Units.empty,
         rewrite = Rewrite.new (KnuthBendixOrder.compare ordering),
         subsume = Subsume.new (),
         literals = LiteralNet.new {fifo = false},
         equations = TermNet.new {fifo = false},
         subterms = TermNet.new {fifo = false},
         allSubterms = TermNet.new {fifo = false}}
    end;

fun size (Active {clauses,...}) = IntMap.size clauses;

fun clauses (Active {clauses = cls, ...}) =
    let
      fun add (_,cl,acc) = cl :: acc
    in
      IntMap.foldr add [] cls
    end;

fun saturation active =
    let
      fun remove (cl,(cls,subs)) =
          let
            val lits = Clause.literals cl
          in
            if Subsume.isStrictlySubsumed subs lits then (cls,subs)
            else (cl :: cls, Subsume.insert subs (lits,()))
          end

      val cls = clauses active
      val (cls,_) = List.foldl remove ([], Subsume.new ()) cls
      val (cls,subs) = List.foldl remove ([], Subsume.new ()) cls

(*MetisDebug
      val Active {parameters,...} = active
      val {clause,...} = parameters
      val {ordering,...} = clause
      val () = checkSaturated ordering subs cls
*)
    in
      cls
    end;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val pp =
    let
      fun toStr active = "Active{" ^ Int.toString (size active) ^ "}"
    in
      Print.ppMap toStr Print.ppString
    end;

(*MetisDebug
local
  fun ppField f ppA a =
      Print.inconsistentBlock 2
        [Print.ppString (f ^ " ="),
         Print.break,
         ppA a];

  val ppClauses =
      ppField "clauses"
        (Print.ppMap IntMap.toList
           (Print.ppList (Print.ppPair Print.ppInt Clause.pp)));

  val ppRewrite = ppField "rewrite" Rewrite.pp;

  val ppSubterms =
      ppField "subterms"
        (TermNet.pp
           (Print.ppMap (fn (c,l,p,t) => ((Clause.id c, l, p), t))
              (Print.ppPair
                 (Print.ppTriple Print.ppInt Literal.pp Term.ppPath)
                 Term.pp)));
in
  fun pp (Active {clauses,rewrite,subterms,...}) =
      Print.inconsistentBlock 2
        [Print.ppString "Active",
         Print.break,
         Print.inconsistentBlock 1
           [Print.ppString "{",
            ppClauses clauses,
            Print.ppString ",",
            Print.break,
            ppRewrite rewrite,
(*MetisTrace5
            Print.ppString ",",
            Print.break,
            ppSubterms subterms,
*)
            Print.skip],
         Print.ppString "}"];
end;
*)

val toString = Print.toString pp;

(* ------------------------------------------------------------------------- *)
(* Simplify clauses.                                                         *)
(* ------------------------------------------------------------------------- *)

fun simplify simp units rewr subs =
    let
      val {subsume = s, reduce = r, rewrite = w} = simp

      fun rewrite cl =
          let
            val cl' = Clause.rewrite rewr cl
          in
            if Clause.equalThms cl cl' then SOME cl else Clause.simplify cl'
          end
    in
      fn cl =>
         case Clause.simplify cl of
           NONE => NONE
         | SOME cl =>
           case (if w then rewrite cl else SOME cl) of
             NONE => NONE
           | SOME cl =>
             let
               val cl = if r then Clause.reduce units cl else cl
             in
               if s andalso Clause.subsumes subs cl then NONE else SOME cl
             end
    end;

(*MetisDebug
val simplify = fn simp => fn units => fn rewr => fn subs => fn cl =>
    let
      fun traceCl s = Print.trace Clause.pp ("Active.simplify: " ^ s)
(*MetisTrace4
      val ppClOpt = Print.ppOption Clause.pp
      val () = traceCl "cl" cl
*)
      val cl' = simplify simp units rewr subs cl
(*MetisTrace4
      val () = Print.trace ppClOpt "Active.simplify: cl'" cl'
*)
      val () =
          case cl' of
            NONE => ()
          | SOME cl' =>
            case
              (case simplify simp units rewr subs cl' of
                 NONE => SOME ("away", K ())
               | SOME cl'' =>
                 if Clause.equalThms cl' cl'' then NONE
                 else SOME ("further", fn () => traceCl "cl''" cl'')) of
              NONE => ()
            | SOME (e,f) =>
              let
                val () = traceCl "cl" cl
                val () = traceCl "cl'" cl'
                val () = f ()
              in
                raise
                  Bug
                    ("Active.simplify: clause should have been simplified "^e)
              end
    in
      cl'
    end;
*)

fun simplifyActive simp active =
    let
      val Active {units,rewrite,subsume,...} = active
    in
      simplify simp units rewrite subsume
    end;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set.                                         *)
(* ------------------------------------------------------------------------- *)

fun addUnit units cl =
    let
      val th = Clause.thm cl
    in
      case total Thm.destUnit th of
        SOME lit => Units.add units (lit,th)
      | NONE => units
    end;

fun addRewrite rewrite cl =
    let
      val th = Clause.thm cl
    in
      case total Thm.destUnitEq th of
        SOME l_r => Rewrite.add rewrite (Clause.id cl, (l_r,th))
      | NONE => rewrite
    end;

fun addSubsume subsume cl = Subsume.insert subsume (Clause.literals cl, cl);

fun addLiterals literals cl =
    let
      fun add (lit as (_,atm), literals) =
          if Atom.isEq atm then literals
          else LiteralNet.insert literals (lit,(cl,lit))
    in
      LiteralSet.foldl add literals (Clause.largestLiterals cl)
    end;

fun addEquations equations cl =
    let
      fun add ((lit,ort,tm),equations) =
          TermNet.insert equations (tm,(cl,lit,ort,tm))
    in
      List.foldl add equations (Clause.largestEquations cl)
    end;

fun addSubterms subterms cl =
    let
      fun add ((lit,path,tm),subterms) =
          TermNet.insert subterms (tm,(cl,lit,path,tm))
    in
      List.foldl add subterms (Clause.largestSubterms cl)
    end;

fun addAllSubterms allSubterms cl =
    let
      fun add ((_,_,tm),allSubterms) =
          TermNet.insert allSubterms (tm,(cl,tm))
    in
      List.foldl add allSubterms (Clause.allSubterms cl)
    end;

fun addClause active cl =
    let
      val Active
            {parameters,clauses,units,rewrite,subsume,literals,
             equations,subterms,allSubterms} = active
      val clauses = IntMap.insert clauses (Clause.id cl, cl)
      and subsume = addSubsume subsume cl
      and literals = addLiterals literals cl
      and equations = addEquations equations cl
      and subterms = addSubterms subterms cl
      and allSubterms = addAllSubterms allSubterms cl
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms,
         allSubterms = allSubterms}
    end;

fun addFactorClause active cl =
    let
      val Active
            {parameters,clauses,units,rewrite,subsume,literals,
             equations,subterms,allSubterms} = active
      val units = addUnit units cl
      and rewrite = addRewrite rewrite cl
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms, allSubterms = allSubterms}
    end;

(* ------------------------------------------------------------------------- *)
(* Derive (unfactored) consequences of a clause.                             *)
(* ------------------------------------------------------------------------- *)

fun deduceResolution literals cl (lit as (_,atm), acc) =
    let
      fun resolve (cl_lit,acc) =
          case total (Clause.resolve cl_lit) (cl,lit) of
            SOME cl' => cl' :: acc
          | NONE => acc
(*MetisTrace4
      val () = Print.trace Literal.pp "Active.deduceResolution: lit" lit
*)
    in
      if Atom.isEq atm then acc
      else
        List.foldl resolve acc (LiteralNet.unify literals (Literal.negate lit))
    end;

fun deduceParamodulationWith subterms cl ((lit,ort,tm),acc) =
    let
      fun para (cl_lit_path_tm,acc) =
          case total (Clause.paramodulate (cl,lit,ort,tm)) cl_lit_path_tm of
            SOME cl' => cl' :: acc
          | NONE => acc
    in
      List.foldl para acc (TermNet.unify subterms tm)
    end;

fun deduceParamodulationInto equations cl ((lit,path,tm),acc) =
    let
      fun para (cl_lit_ort_tm,acc) =
          case total (Clause.paramodulate cl_lit_ort_tm) (cl,lit,path,tm) of
            SOME cl' => cl' :: acc
          | NONE => acc
    in
      List.foldl para acc (TermNet.unify equations tm)
    end;

fun deduce active cl =
    let
      val Active {parameters,literals,equations,subterms,...} = active

      val lits = Clause.largestLiterals cl
      val eqns = Clause.largestEquations cl
      val subtms =
          if TermNet.null equations then [] else Clause.largestSubterms cl
(*MetisTrace5
      val () = Print.trace LiteralSet.pp "Active.deduce: lits" lits
      val () = Print.trace
                 (Print.ppList
                    (Print.ppMap (fn (lit,ort,_) => (lit,ort))
                      (Print.ppPair Literal.pp Rewrite.ppOrient)))
                 "Active.deduce: eqns" eqns
      val () = Print.trace
                 (Print.ppList
                    (Print.ppTriple Literal.pp Term.ppPath Term.pp))
                 "Active.deduce: subtms" subtms
*)

      val acc = []
      val acc = LiteralSet.foldl (deduceResolution literals cl) acc lits
      val acc = List.foldl (deduceParamodulationWith subterms cl) acc eqns
      val acc = List.foldl (deduceParamodulationInto equations cl) acc subtms
      val acc = List.rev acc

(*MetisTrace5
      val () = Print.trace (Print.ppList Clause.pp) "Active.deduce: acc" acc
*)
    in
      acc
    end;

(* ------------------------------------------------------------------------- *)
(* Extract clauses from the active set that can be simplified.               *)
(* ------------------------------------------------------------------------- *)

local
  fun clause_rewritables active =
      let
        val Active {clauses,rewrite,...} = active

        fun rewr (id,cl,ids) =
            let
              val cl' = Clause.rewrite rewrite cl
            in
              if Clause.equalThms cl cl' then ids else IntSet.add ids id
            end
      in
        IntMap.foldr rewr IntSet.empty clauses
      end;

  fun orderedRedexResidues (((l,r),_),ort) =
      case ort of
        NONE => []
      | SOME Rewrite.LeftToRight => [(l,r,true)]
      | SOME Rewrite.RightToLeft => [(r,l,true)];

  fun unorderedRedexResidues (((l,r),_),ort) =
      case ort of
        NONE => [(l,r,false),(r,l,false)]
      | SOME _ => [];

  fun rewrite_rewritables active rewr_ids =
      let
        val Active {parameters,rewrite,clauses,allSubterms,...} = active
        val {clause = {ordering,...}, ...} = parameters
        val order = KnuthBendixOrder.compare ordering

        fun addRewr (id,acc) =
            if IntMap.inDomain id clauses then IntSet.add acc id else acc

        fun addReduce ((l,r,ord),acc) =
            let
              fun isValidRewr tm =
                  case total (Subst.match Subst.empty l) tm of
                    NONE => false
                  | SOME sub =>
                    ord orelse
                    let
                      val tm' = Subst.subst (Subst.normalize sub) r
                    in
                      order (tm,tm') = SOME GREATER
                    end

              fun addRed ((cl,tm),acc) =
                  let
(*MetisTrace5
                    val () = Print.trace Clause.pp "Active.addRed: cl" cl
                    val () = Print.trace Term.pp "Active.addRed: tm" tm
*)
                    val id = Clause.id cl
                  in
                    if IntSet.member id acc then acc
                    else if not (isValidRewr tm) then acc
                    else IntSet.add acc id
                  end

(*MetisTrace5
              val () = Print.trace Term.pp "Active.addReduce: l" l
              val () = Print.trace Term.pp "Active.addReduce: r" r
              val () = Print.trace Print.ppBool "Active.addReduce: ord" ord
*)
            in
              List.foldl addRed acc (TermNet.matched allSubterms l)
            end

        fun addEquation redexResidues (id,acc) =
            case Rewrite.peek rewrite id of
              NONE => acc
            | SOME eqn_ort => List.foldl addReduce acc (redexResidues eqn_ort)

        val addOrdered = addEquation orderedRedexResidues

        val addUnordered = addEquation unorderedRedexResidues

        val ids = IntSet.empty
        val ids = List.foldl addRewr ids rewr_ids
        val ids = List.foldl addOrdered ids rewr_ids
        val ids = List.foldl addUnordered ids rewr_ids
      in
        ids
      end;

  fun choose_clause_rewritables active ids = size active <= length ids

  fun rewritables active ids =
      if choose_clause_rewritables active ids then clause_rewritables active
      else rewrite_rewritables active ids;

(*MetisDebug
  val rewritables = fn active => fn ids =>
      let
        val clause_ids = clause_rewritables active
        val rewrite_ids = rewrite_rewritables active ids

        val () =
            if IntSet.equal rewrite_ids clause_ids then ()
            else
              let
                val ppIdl = Print.ppList Print.ppInt
                val ppIds = Print.ppMap IntSet.toList ppIdl
                val () = Print.trace pp "Active.rewritables: active" active
                val () = Print.trace ppIdl "Active.rewritables: ids" ids
                val () = Print.trace ppIds
                           "Active.rewritables: clause_ids" clause_ids
                val () = Print.trace ppIds
                           "Active.rewritables: rewrite_ids" rewrite_ids
              in
                raise Bug "Active.rewritables: ~(rewrite_ids SUBSET clause_ids)"
              end
      in
        if choose_clause_rewritables active ids then clause_ids else rewrite_ids
      end;
*)

  fun delete active ids =
      if IntSet.null ids then active
      else
        let
          fun idPred id = not (IntSet.member id ids)

          fun clausePred cl = idPred (Clause.id cl)

          val Active
                {parameters,
                 clauses,
                 units,
                 rewrite,
                 subsume,
                 literals,
                 equations,
                 subterms,
                 allSubterms} = active

          val clauses = IntMap.filter (idPred o fst) clauses
          and subsume = Subsume.filter clausePred subsume
          and literals = LiteralNet.filter (clausePred o #1) literals
          and equations = TermNet.filter (clausePred o #1) equations
          and subterms = TermNet.filter (clausePred o #1) subterms
          and allSubterms = TermNet.filter (clausePred o fst) allSubterms
        in
          Active
            {parameters = parameters,
             clauses = clauses,
             units = units,
             rewrite = rewrite,
             subsume = subsume,
             literals = literals,
             equations = equations,
             subterms = subterms,
             allSubterms = allSubterms}
        end;
in
  fun extract_rewritables (active as Active {clauses,rewrite,...}) =
      if Rewrite.isReduced rewrite then (active,[])
      else
        let
(*MetisTrace3
          val () = trace "Active.extract_rewritables: inter-reducing\n"
*)
          val (rewrite,ids) = Rewrite.reduce' rewrite
          val active = setRewrite active rewrite
          val ids = rewritables active ids
          val cls = IntSet.transform (IntMap.get clauses) ids
(*MetisTrace3
          val ppCls = Print.ppList Clause.pp
          val () = Print.trace ppCls "Active.extract_rewritables: cls" cls
*)
        in
          (delete active ids, cls)
        end
(*MetisDebug
        handle Error err =>
          raise Bug ("Active.extract_rewritables: shouldn't fail\n" ^ err);
*)
end;

(* ------------------------------------------------------------------------- *)
(* Factor clauses.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun prefactor_simplify active subsume =
      let
        val Active {parameters,units,rewrite,...} = active
        val {prefactor,...} = parameters
      in
        simplify prefactor units rewrite subsume
      end;

  fun postfactor_simplify active subsume =
      let
        val Active {parameters,units,rewrite,...} = active
        val {postfactor,...} = parameters
      in
        simplify postfactor units rewrite subsume
      end;

  val sort_utilitywise =
      let
        fun utility cl =
            case LiteralSet.size (Clause.literals cl) of
              0 => ~1
            | 1 => if Thm.isUnitEq (Clause.thm cl) then 0 else 1
            | n => n
      in
        sortMap utility Int.compare
      end;

  fun factor_add (cl, active_subsume_acc as (active,subsume,acc)) =
      case postfactor_simplify active subsume cl of
        NONE => active_subsume_acc
      | SOME cl =>
        let
          val active = addFactorClause active cl
          and subsume = addSubsume subsume cl
          and acc = cl :: acc
        in
          (active,subsume,acc)
        end;

  fun factor1 (cl, active_subsume_acc as (active,subsume,_)) =
      case prefactor_simplify active subsume cl of
        NONE => active_subsume_acc
      | SOME cl =>
        let
          val cls = sort_utilitywise (cl :: Clause.factor cl)
        in
          List.foldl factor_add active_subsume_acc cls
        end;

  fun factor' active acc [] = (active, List.rev acc)
    | factor' active acc cls =
      let
        val cls = sort_utilitywise cls
        val subsume = getSubsume active
        val (active,_,acc) = List.foldl factor1 (active,subsume,acc) cls
        val (active,cls) = extract_rewritables active
      in
        factor' active acc cls
      end;
in
  fun factor active cls = factor' active [] cls;
end;

(*MetisTrace4
val factor = fn active => fn cls =>
    let
      val ppCls = Print.ppList Clause.pp
      val () = Print.trace ppCls "Active.factor: cls" cls
      val (active,cls') = factor active cls
      val () = Print.trace ppCls "Active.factor: cls'" cls'
    in
      (active,cls')
    end;
*)

(* ------------------------------------------------------------------------- *)
(* Create a new active clause set and initialize clauses.                    *)
(* ------------------------------------------------------------------------- *)

fun new parameters {axioms,conjecture} =
    let
      val {clause,...} = parameters

      fun mk_clause th =
          Clause.mk {parameters = clause, id = Clause.newId (), thm = th}

      val active = empty parameters
      val (active,axioms) = factor active (List.map mk_clause axioms)
      val (active,conjecture) = factor active (List.map mk_clause conjecture)
    in
      (active, {axioms = axioms, conjecture = conjecture})
    end;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set and deduce all consequences.             *)
(* ------------------------------------------------------------------------- *)

fun add active cl =
    case simplifyActive maxSimplify active cl of
      NONE => (active,[])
    | SOME cl' =>
      if Clause.isContradiction cl' then (active,[cl'])
      else if not (Clause.equalThms cl cl') then factor active [cl']
      else
        let
(*MetisTrace2
          val () = Print.trace Clause.pp "Active.add: cl" cl
*)
          val active = addClause active cl
          val cl = Clause.freshVars cl
          val cls = deduce active cl
          val (active,cls) = factor active cls
(*MetisTrace2
          val ppCls = Print.ppList Clause.pp
          val () = Print.trace ppCls "Active.add: cls" cls
*)
        in
          (active,cls)
        end;

end
