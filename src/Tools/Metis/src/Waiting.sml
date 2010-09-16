(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* Copyright (c) 2002 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Waiting :> Waiting =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type weight = real;

type modelParameters =
     {model : Model.parameters,
      initialPerturbations : int,
      maxChecks : int option,
      perturbations : int,
      weight : weight}

type parameters =
     {symbolsWeight : weight,
      variablesWeight : weight,
      literalsWeight : weight,
      models : modelParameters list};

type distance = real;

datatype waiting =
    Waiting of
      {parameters : parameters,
       clauses : (weight * (distance * Clause.clause)) Heap.heap,
       models : Model.model list};

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val defaultModels : modelParameters list =
    [{model = Model.default,
      initialPerturbations = 100,
      maxChecks = SOME 20,
      perturbations = 0,
      weight = 1.0}];

val default : parameters =
     {symbolsWeight = 1.0,
      literalsWeight = 1.0,
      variablesWeight = 1.0,
      models = defaultModels};

fun size (Waiting {clauses,...}) = Heap.size clauses;

val pp =
    Print.ppMap
      (fn w => "Waiting{" ^ Int.toString (size w) ^ "}")
      Print.ppString;

(*MetisDebug
val pp =
    Print.ppMap
      (fn Waiting {clauses,...} =>
          map (fn (w,(_,cl)) => (w, Clause.id cl, cl)) (Heap.toList clauses))
      (Print.ppList (Print.ppTriple Print.ppReal Print.ppInt Clause.pp));
*)

(* ------------------------------------------------------------------------- *)
(* Perturbing the models.                                                    *)
(* ------------------------------------------------------------------------- *)

type modelClause = NameSet.set * Thm.clause;

fun mkModelClause cl =
    let
      val lits = Clause.literals cl
      val fvs = LiteralSet.freeVars lits
    in
      (fvs,lits)
    end;

val mkModelClauses = map mkModelClause;

fun perturbModel M cls =
    if null cls then K ()
    else
      let
        val N = {size = Model.size M}

        fun perturbClause (fv,cl) =
            let
              val V = Model.randomValuation N fv
            in
              if Model.interpretClause M V cl then ()
              else Model.perturbClause M V cl
            end

        fun perturbClauses () = app perturbClause cls
      in
        fn n => funpow n perturbClauses ()
      end;

fun initialModel axioms conjecture parm =
    let
      val {model,initialPerturbations,...} : modelParameters = parm
      val m = Model.new model
      val () = perturbModel m conjecture initialPerturbations
      val () = perturbModel m axioms initialPerturbations
    in
      m
    end;

fun checkModels parms models (fv,cl) =
    let
      fun check ((parm,model),z) =
          let
            val {maxChecks,weight,...} : modelParameters = parm
            val n = {maxChecks = maxChecks}
            val {T,F} = Model.check Model.interpretClause n model fv cl
          in
            Math.pow (1.0 + Real.fromInt T / Real.fromInt (T + F), weight) * z
          end
    in
      List.foldl check 1.0 (zip parms models)
    end;

fun perturbModels parms models cls =
    let
      fun perturb (parm,model) =
          let
            val {perturbations,...} : modelParameters = parm
          in
            perturbModel model cls perturbations
          end
    in
      app perturb (zip parms models)
    end;

(* ------------------------------------------------------------------------- *)
(* Clause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun clauseSymbols cl = Real.fromInt (LiteralSet.typedSymbols cl);

  fun clauseVariables cl =
      Real.fromInt (NameSet.size (LiteralSet.freeVars cl) + 1);

  fun clauseLiterals cl = Real.fromInt (LiteralSet.size cl);

  fun clausePriority cl = 1e~12 * Real.fromInt (Clause.id cl);
in
  fun clauseWeight (parm : parameters) mods dist mcl cl =
      let
(*MetisTrace3
        val () = Print.trace Clause.pp "Waiting.clauseWeight: cl" cl
*)
        val {symbolsWeight,variablesWeight,literalsWeight,models,...} = parm
        val lits = Clause.literals cl
        val symbolsW = Math.pow (clauseSymbols lits, symbolsWeight)
        val variablesW = Math.pow (clauseVariables lits, variablesWeight)
        val literalsW = Math.pow (clauseLiterals lits, literalsWeight)
        val modelsW = checkModels models mods mcl
(*MetisTrace4
        val () = trace ("Waiting.clauseWeight: dist = " ^
                        Real.toString dist ^ "\n")
        val () = trace ("Waiting.clauseWeight: symbolsW = " ^
                        Real.toString symbolsW ^ "\n")
        val () = trace ("Waiting.clauseWeight: variablesW = " ^
                        Real.toString variablesW ^ "\n")
        val () = trace ("Waiting.clauseWeight: literalsW = " ^
                        Real.toString literalsW ^ "\n")
        val () = trace ("Waiting.clauseWeight: modelsW = " ^
                        Real.toString modelsW ^ "\n")
*)
        val weight = dist * symbolsW * variablesW * literalsW * modelsW
        val weight = weight + clausePriority cl
(*MetisTrace3
        val () = trace ("Waiting.clauseWeight: weight = " ^
                        Real.toString weight ^ "\n")
*)
      in
        weight
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

fun add' waiting dist mcls cls =
    let
      val Waiting {parameters,clauses,models} = waiting
      val {models = modelParameters, ...} = parameters

      val dist = dist + Math.ln (Real.fromInt (length cls))

      fun addCl ((mcl,cl),acc) =
          let
            val weight = clauseWeight parameters models dist mcl cl
          in
            Heap.add acc (weight,(dist,cl))
          end

      val clauses = List.foldl addCl clauses (zip mcls cls)

      val () = perturbModels modelParameters models mcls
    in
      Waiting {parameters = parameters, clauses = clauses, models = models}
    end;

fun add waiting (_,[]) = waiting
  | add waiting (dist,cls) =
    let
(*MetisTrace3
      val () = Print.trace pp "Waiting.add: waiting" waiting
      val () = Print.trace (Print.ppList Clause.pp) "Waiting.add: cls" cls
*)

      val waiting = add' waiting dist (mkModelClauses cls) cls

(*MetisTrace3
      val () = Print.trace pp "Waiting.add: waiting" waiting
*)
    in
      waiting
    end;

local
  fun cmp ((w1,_),(w2,_)) = Real.compare (w1,w2);

  fun empty parameters axioms conjecture =
      let
        val {models = modelParameters, ...} = parameters
        val clauses = Heap.new cmp
        and models = map (initialModel axioms conjecture) modelParameters
      in
        Waiting {parameters = parameters, clauses = clauses, models = models}
      end;
in
  fun new parameters {axioms,conjecture} =
      let
        val mAxioms = mkModelClauses axioms
        and mConjecture = mkModelClauses conjecture

        val waiting = empty parameters mAxioms mConjecture
      in
        add' waiting 0.0 (mAxioms @ mConjecture) (axioms @ conjecture)
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

fun remove (Waiting {parameters,clauses,models}) =
    if Heap.null clauses then NONE
    else
      let
        val ((_,dcl),clauses) = Heap.remove clauses
        val waiting =
            Waiting
              {parameters = parameters, clauses = clauses, models = models}
      in
        SOME (dcl,waiting)
      end;

end
