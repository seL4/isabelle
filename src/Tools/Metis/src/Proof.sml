(* ========================================================================= *)
(* PROOFS IN FIRST ORDER LOGIC                                               *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Proof :> Proof =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic proofs.                                       *)
(* ------------------------------------------------------------------------- *)

datatype inference =
    Axiom of LiteralSet.set
  | Assume of Atom.atom
  | Subst of Subst.subst * Thm.thm
  | Resolve of Atom.atom * Thm.thm * Thm.thm
  | Refl of Term.term
  | Equality of Literal.literal * Term.path * Term.term;

type proof = (Thm.thm * inference) list;

(* ------------------------------------------------------------------------- *)
(* Printing.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun inferenceType (Axiom _) = Thm.Axiom
  | inferenceType (Assume _) = Thm.Assume
  | inferenceType (Subst _) = Thm.Subst
  | inferenceType (Resolve _) = Thm.Resolve
  | inferenceType (Refl _) = Thm.Refl
  | inferenceType (Equality _) = Thm.Equality;

local
  fun ppAssume pp atm = (Parser.addBreak pp (1,0); Atom.pp pp atm);

  fun ppSubst ppThm pp (sub,thm) =
      (Parser.addBreak pp (1,0);
       Parser.beginBlock pp Parser.Inconsistent 1;
       Parser.addString pp "{";
       Parser.ppBinop " =" Parser.ppString Subst.pp pp ("sub",sub);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString ppThm pp ("thm",thm);
       Parser.addString pp "}";
       Parser.endBlock pp);

  fun ppResolve ppThm pp (res,pos,neg) =
      (Parser.addBreak pp (1,0);
       Parser.beginBlock pp Parser.Inconsistent 1;
       Parser.addString pp "{";
       Parser.ppBinop " =" Parser.ppString Atom.pp pp ("res",res);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString ppThm pp ("pos",pos);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString ppThm pp ("neg",neg);
       Parser.addString pp "}";
       Parser.endBlock pp);

  fun ppRefl pp tm = (Parser.addBreak pp (1,0); Term.pp pp tm);

  fun ppEquality pp (lit,path,res) =
      (Parser.addBreak pp (1,0);
       Parser.beginBlock pp Parser.Inconsistent 1;
       Parser.addString pp "{";
       Parser.ppBinop " =" Parser.ppString Literal.pp pp ("lit",lit);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString Term.ppPath pp ("path",path);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString Term.pp pp ("res",res);
       Parser.addString pp "}";
       Parser.endBlock pp);

  fun ppInf ppAxiom ppThm pp inf =
      let
        val infString = Thm.inferenceTypeToString (inferenceType inf)
      in
        Parser.beginBlock pp Parser.Inconsistent (size infString + 1);
        Parser.ppString pp infString;
        case inf of
          Axiom cl => ppAxiom pp cl
        | Assume x => ppAssume pp x
        | Subst x => ppSubst ppThm pp x
        | Resolve x => ppResolve ppThm pp x
        | Refl x => ppRefl pp x
        | Equality x => ppEquality pp x;
        Parser.endBlock pp
      end;

  fun ppAxiom pp cl =
      (Parser.addBreak pp (1,0);
       Parser.ppMap
         LiteralSet.toList
         (Parser.ppBracket "{" "}" (Parser.ppSequence "," Literal.pp)) pp cl);
in
  val ppInference = ppInf ppAxiom Thm.pp;

  fun pp p prf =
      let
        fun thmString n = "(" ^ Int.toString n ^ ")"
                          
        val prf = enumerate prf

        fun ppThm p th =
            let
              val cl = Thm.clause th

              fun pred (_,(th',_)) = LiteralSet.equal (Thm.clause th') cl
            in
              case List.find pred prf of
                NONE => Parser.addString p "(?)"
              | SOME (n,_) => Parser.addString p (thmString n)
            end

        fun ppStep (n,(th,inf)) =
            let
              val s = thmString n
            in
              Parser.beginBlock p Parser.Consistent (1 + size s);
              Parser.addString p (s ^ " ");
              Thm.pp p th;
              Parser.addBreak p (2,0);
              Parser.ppBracket "[" "]" (ppInf (K (K ())) ppThm) p inf;
              Parser.endBlock p;
              Parser.addNewline p
            end
      in
        Parser.beginBlock p Parser.Consistent 0;
        Parser.addString p "START OF PROOF";
        Parser.addNewline p;
        app ppStep prf;
        Parser.addString p "END OF PROOF";
        Parser.addNewline p;
        Parser.endBlock p
      end
(*DEBUG
      handle Error err => raise Bug ("Proof.pp: shouldn't fail:\n" ^ err);
*)

end;

val inferenceToString = Parser.toString ppInference;

val toString = Parser.toString pp;

(* ------------------------------------------------------------------------- *)
(* Reconstructing single inferences.                                         *)
(* ------------------------------------------------------------------------- *)

fun parents (Axiom _) = []
  | parents (Assume _) = []
  | parents (Subst (_,th)) = [th]
  | parents (Resolve (_,th,th')) = [th,th']
  | parents (Refl _) = []
  | parents (Equality _) = [];

fun inferenceToThm (Axiom cl) = Thm.axiom cl
  | inferenceToThm (Assume atm) = Thm.assume (true,atm)
  | inferenceToThm (Subst (sub,th)) = Thm.subst sub th
  | inferenceToThm (Resolve (atm,th,th')) = Thm.resolve (true,atm) th th'
  | inferenceToThm (Refl tm) = Thm.refl tm
  | inferenceToThm (Equality (lit,path,r)) = Thm.equality lit path r;

local
  fun reconstructSubst cl cl' =
      let
        fun recon [] =
            let
(*TRACE3
              val () = Parser.ppTrace LiteralSet.pp "reconstructSubst: cl" cl
              val () = Parser.ppTrace LiteralSet.pp "reconstructSubst: cl'" cl'
*)
            in
              raise Bug "can't reconstruct Subst rule"
            end
          | recon (([],sub) :: others) =
            if LiteralSet.equal (LiteralSet.subst sub cl) cl' then sub
            else recon others
          | recon ((lit :: lits, sub) :: others) =
            let
              fun checkLit (lit',acc) =
                  case total (Literal.match sub lit) lit' of
                    NONE => acc
                  | SOME sub => (lits,sub) :: acc
            in
              recon (LiteralSet.foldl checkLit others cl')
            end
      in
        Subst.normalize (recon [(LiteralSet.toList cl, Subst.empty)])
      end
(*DEBUG
      handle Error err =>
        raise Bug ("Proof.recontructSubst: shouldn't fail:\n" ^ err);
*)

  fun reconstructResolvant cl1 cl2 cl =
      (if not (LiteralSet.subset cl1 cl) then
         LiteralSet.pick (LiteralSet.difference cl1 cl)
       else if not (LiteralSet.subset cl2 cl) then
         Literal.negate (LiteralSet.pick (LiteralSet.difference cl2 cl))
       else
         (* A useless resolution, but we must reconstruct it anyway *)
         let
           val cl1' = LiteralSet.negate cl1
           and cl2' = LiteralSet.negate cl2
           val lits = LiteralSet.intersectList [cl1,cl1',cl2,cl2']
         in
           if not (LiteralSet.null lits) then LiteralSet.pick lits
           else raise Bug "can't reconstruct Resolve rule"
         end)
(*DEBUG
      handle Error err =>
        raise Bug ("Proof.recontructResolvant: shouldn't fail:\n" ^ err);
*)

  fun reconstructEquality cl =
      let
(*TRACE3
        val () = Parser.ppTrace LiteralSet.pp "Proof.reconstructEquality: cl" cl
*)

        fun sync s t path (f,a) (f',a') =
            if f <> f' orelse length a <> length a' then NONE
            else
              case List.filter (op<> o snd) (enumerate (zip a a')) of
                [(i,(tm,tm'))] =>
                let
                  val path = i :: path
                in
                  if tm = s andalso tm' = t then SOME (rev path)
                  else 
                    case (tm,tm') of
                      (Term.Fn f_a, Term.Fn f_a') => sync s t path f_a f_a'
                    | _ => NONE
                end
              | _ => NONE

        fun recon (neq,(pol,atm),(pol',atm')) =
            if pol = pol' then NONE
            else
              let
                val (s,t) = Literal.destNeq neq

                val path =
                    if s <> t then sync s t [] atm atm'
                    else if atm <> atm' then NONE
                    else Atom.find (equal s) atm
              in
                case path of
                  SOME path => SOME ((pol',atm),path,t)
                | NONE => NONE
              end

        val candidates =
            case List.partition Literal.isNeq (LiteralSet.toList cl) of
              ([l1],[l2,l3]) => [(l1,l2,l3),(l1,l3,l2)]
            | ([l1,l2],[l3]) => [(l1,l2,l3),(l1,l3,l2),(l2,l1,l3),(l2,l3,l1)]
            | ([l1],[l2]) => [(l1,l1,l2),(l1,l2,l1)]
            | _ => raise Bug "reconstructEquality: malformed"

(*TRACE3
        val ppCands =
            Parser.ppList (Parser.ppTriple Literal.pp Literal.pp Literal.pp)
        val () = Parser.ppTrace ppCands
                   "Proof.reconstructEquality: candidates" candidates
*)
      in
        case first recon candidates of
          SOME info => info
        | NONE => raise Bug "can't reconstruct Equality rule"
      end
(*DEBUG
      handle Error err =>
        raise Bug ("Proof.recontructEquality: shouldn't fail:\n" ^ err);
*)

  fun reconstruct cl (Thm.Axiom,[]) = Axiom cl
    | reconstruct cl (Thm.Assume,[]) =
      (case LiteralSet.findl Literal.positive cl of
         SOME (_,atm) => Assume atm
       | NONE => raise Bug "malformed Assume inference")
    | reconstruct cl (Thm.Subst,[th]) =
      Subst (reconstructSubst (Thm.clause th) cl, th)
    | reconstruct cl (Thm.Resolve,[th1,th2]) =
      let
        val cl1 = Thm.clause th1
        and cl2 = Thm.clause th2
        val (pol,atm) = reconstructResolvant cl1 cl2 cl
      in
        if pol then Resolve (atm,th1,th2) else Resolve (atm,th2,th1)
      end
    | reconstruct cl (Thm.Refl,[]) =
      (case LiteralSet.findl (K true) cl of
         SOME lit => Refl (Literal.destRefl lit)
       | NONE => raise Bug "malformed Refl inference")
    | reconstruct cl (Thm.Equality,[]) = Equality (reconstructEquality cl)
    | reconstruct _ _ = raise Bug "malformed inference";
in
  fun thmToInference th =
      let
(*TRACE3
        val () = Parser.ppTrace Thm.pp "Proof.thmToInference: th" th
*)

        val cl = Thm.clause th

        val thmInf = Thm.inference th

(*TRACE3
        val ppThmInf = Parser.ppPair Thm.ppInferenceType (Parser.ppList Thm.pp)
        val () = Parser.ppTrace ppThmInf "Proof.thmToInference: thmInf" thmInf
*)

        val inf = reconstruct cl thmInf

(*TRACE3
        val () = Parser.ppTrace ppInference "Proof.thmToInference: inf" inf
*)
(*DEBUG
        val () =
            let
              val th' = inferenceToThm inf
            in
              if LiteralSet.equal (Thm.clause th') cl then ()
              else
                raise
                  Bug
                    ("Proof.thmToInference: bad inference reconstruction:" ^
                     "\n  th = " ^ Thm.toString th ^
                     "\n  inf = " ^ inferenceToString inf ^
                     "\n  inf th = " ^ Thm.toString th')
            end
*)
      in
        inf
      end
(*DEBUG
      handle Error err =>
        raise Bug ("Proof.thmToInference: shouldn't fail:\n" ^ err);
*)
end;

(* ------------------------------------------------------------------------- *)
(* Reconstructing whole proofs.                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun thmCompare (th1,th2) =
      LiteralSet.compare (Thm.clause th1, Thm.clause th2);

  fun buildProof (th,(m,l)) =
      if Map.inDomain th m then (m,l)
      else
        let
          val (_,deps) = Thm.inference th
          val (m,l) = foldl buildProof (m,l) deps
        in
          if Map.inDomain th m then (m,l)
          else
            let
              val l = (th, thmToInference th) :: l
            in
              (Map.insert m (th,l), l)
            end
        end;
in
  fun proof th =
      let
(*TRACE3
        val () = Parser.ppTrace Thm.pp "Proof.proof: th" th
*)
        val (m,_) = buildProof (th, (Map.new thmCompare, []))
(*TRACE3
        val () = Parser.ppTrace Parser.ppInt "Proof.proof: size" (Map.size m)
*)
      in
        case Map.peek m th of
          SOME l => rev l
        | NONE => raise Bug "Proof.proof"
      end;
end;

end
