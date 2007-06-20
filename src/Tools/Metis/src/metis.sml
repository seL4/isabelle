(* ========================================================================= *)
(* METIS FIRST ORDER PROVER                                                  *)
(*                                                                           *)
(* Copyright (c) 2001-2007 Joe Hurd                                          *)
(*                                                                           *)
(* Metis is free software; you can redistribute it and/or modify             *)
(* it under the terms of the GNU General Public License as published by      *)
(* the Free Software Foundation; either version 2 of the License, or         *)
(* (at your option) any later version.                                       *)
(*                                                                           *)
(* Metis is distributed in the hope that it will be useful,                  *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of            *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the             *)
(* GNU General Public License for more details.                              *)
(*                                                                           *)
(* You should have received a copy of the GNU General Public License         *)
(* along with Metis; if not, write to the Free Software                      *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA *)
(* ========================================================================= *)

open Useful;

(* ------------------------------------------------------------------------- *)
(* The program name.                                                         *)
(* ------------------------------------------------------------------------- *)

val PROGRAM = "metis";

(* ------------------------------------------------------------------------- *)
(* Program options.                                                          *)
(* ------------------------------------------------------------------------- *)

val QUIET = ref false;

val TEST = ref false;

val ITEMS = ["name","goal","clauses","size","category","proof","saturated"];

val show_items = map (fn s => (s, ref false)) ITEMS;

fun show_ref s =
    case List.find (equal s o fst) show_items of
      NONE => raise Bug ("item " ^ s ^ " not found")
    | SOME (_,r) => r;

fun showing s = not (!QUIET) andalso (s = "status" orelse !(show_ref s));

fun notshowing s = not (showing s);

fun showing_any () = List.exists showing ITEMS;

fun notshowing_any () = not (showing_any ());

fun show s = case show_ref s of r => r := true;

fun hide s = case show_ref s of r => r := false;

local
  open Useful Options;
in
  val specialOptions =
    [{switches = ["--show"], arguments = ["ITEM"],
      description = "show ITEM (see below for list)",
      processor =
        beginOpt (enumOpt ITEMS endOpt) (fn _ => fn s => show s)},
     {switches = ["--hide"], arguments = ["ITEM"],
      description = "hide ITEM (see below for list)",
      processor =
        beginOpt (enumOpt ITEMS endOpt) (fn _ => fn s => hide s)},
     {switches = ["-q","--quiet"], arguments = [],
      description = "Run quietly; indicate provability with return value",
      processor = beginOpt endOpt (fn _ => QUIET := true)},
     {switches = ["--test"], arguments = [],
      description = "Skip the proof search for the input problems",
      processor = beginOpt endOpt (fn _ => TEST := true)}];
end;

val VERSION = "2.0";

val versionString = PROGRAM^" version "^VERSION^" (release 20070609)"^"\n";

val programOptions =
    {name    = PROGRAM,
     version = versionString,
     header  = "usage: "^PROGRAM^" [option ...] problem.tptp ...\n" ^
               "Proves the input TPTP problem files.\n",
     footer  = "Possible ITEMs are {" ^ join "," ITEMS ^ "}.\n" ^
               "Problems can be read from standard input using the " ^
               "special - filename.\n",
     options = specialOptions @ Options.basicOptions};

fun exit x : unit = Options.exit programOptions x;
fun succeed () = Options.succeed programOptions;
fun fail mesg = Options.fail programOptions mesg;
fun usage mesg = Options.usage programOptions mesg;

val (opts,work) =
    Options.processOptions programOptions (CommandLine.arguments ());

val () = if null work then usage "no input problem files" else ();

(* ------------------------------------------------------------------------- *)
(* The core application.                                                     *)
(* ------------------------------------------------------------------------- *)

local
  fun display_sep () =
      if notshowing_any () then ()
      else print (nChars #"-" (!Parser.lineLength) ^ "\n");

  fun display_name filename =
      if notshowing "name" then ()
      else print ("Problem: " ^ filename ^ "\n\n");

  fun display_goal goal =
      if notshowing "goal" then ()
      else print ("Goal:\n" ^ Formula.toString goal ^ "\n\n");

  fun display_clauses cls =
      if notshowing "clauses" then ()
      else print ("Clauses:\n" ^ Problem.toString cls ^ "\n\n");

  fun display_size cls =
      if notshowing "size" then ()
      else
        let
          fun plural 1 s = "1 " ^ s
            | plural n s = Int.toString n ^ " " ^ s ^ "s"
                           
          val {clauses,literals,symbols,typedSymbols} = Problem.size cls
        in
          print
            ("Size: " ^
             plural clauses "clause" ^ ", " ^
             plural literals "literal" ^ ", " ^
             plural symbols "symbol" ^ ", " ^
             plural typedSymbols "typed symbol" ^ ".\n\n")
        end;
        
  fun display_category cls =
      if notshowing "category" then ()
      else
        let
          val cat = Problem.categorize cls
        in
          print ("Category: " ^ Problem.categoryToString cat ^ ".\n\n")
        end;

  fun display_proof filename th = 
      if notshowing "proof" then ()
      else
        (print ("SZS output start CNFRefutation for " ^ filename ^ "\n");
         print (Proof.toString (Proof.proof th));
         print ("SZS output end CNFRefutation for " ^ filename ^ "\n\n"));

  fun display_saturated filename ths =
      if notshowing "saturated" then ()
      else
        (print ("SZS output start Saturated for " ^ filename ^ "\n");
         app (fn th => print (Thm.toString th ^ "\n")) ths;
         print ("SZS output end Saturated for " ^ filename ^ "\n\n"));

  fun display_result filename result =
      case result of
        Resolution.Contradiction th => display_proof filename th
      | Resolution.Satisfiable ths => display_saturated filename ths;

  fun display_status filename status =
      if notshowing "status" then ()
      else print ("SZS status " ^ status ^ " for " ^ filename ^ "\n");

  fun display_problem filename cls =
      let
(*DEBUG
        val () = Tptp.write {filename = "cnf.tptp"} (Tptp.fromProblem cls)
*)
        val () = display_clauses cls
        val () = display_size cls
        val () = display_category cls
      in
        ()
      end;

  fun display_problems filename problems =
      List.app (display_problem filename) problems;

  fun refute cls =
      Resolution.loop (Resolution.new Resolution.default (map Thm.axiom cls));

  fun refutable filename cls =
      let
        val () = display_problem filename cls
      in
        case refute cls of
          Resolution.Contradiction th => (display_proof filename th; true)
        | Resolution.Satisfiable ths => (display_saturated filename ths; false)
      end;
in
  fun prove filename =
      let
        val () = display_sep ()
        val () = display_name filename
        val tptp = Tptp.read {filename = filename}
      in
        case Tptp.toGoal tptp of
          Tptp.Cnf prob =>
          let
            val () = display_problem filename prob
          in
            if !TEST then
              (display_status filename "Unknown";
               true)
            else
              case refute prob of
                Resolution.Contradiction th =>
                (display_status filename "Unsatisfiable";
                 if showing "proof" then print "\n" else ();
                 display_proof filename th;
                 true)
              | Resolution.Satisfiable ths =>
                (display_status filename "Satisfiable";
                 if showing "saturated" then print "\n" else ();
                 display_saturated filename ths;
                 false)
          end
        | Tptp.Fof goal =>
          let
            val () = display_goal goal
            val problems = Problem.fromGoal goal
            val result =
                if !TEST then (display_problems filename problems; true)
                else List.all (refutable filename) problems
            val status =
                if !TEST then "Unknown"
                else if Tptp.hasConjecture tptp then
                  if result then "Theorem" else "CounterSatisfiable"
                else
                  if result then "Unsatisfiable" else "Satisfiable"
            val () = display_status filename status
          in
            result
          end
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Top level.                                                                *)
(* ------------------------------------------------------------------------- *)

val () =
let
(*DEBUG
  val () = print "Running in DEBUG mode.\n"
*)
  val success = List.all prove work
  val return = not (!QUIET) orelse success
in
  exit {message = NONE, usage = false, success = return}
end
handle Error s => die (PROGRAM^" failed:\n" ^ s)
     | Bug s => die ("BUG found in "^PROGRAM^" program:\n" ^ s);
