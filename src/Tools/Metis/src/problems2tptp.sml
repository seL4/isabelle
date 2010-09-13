(* ========================================================================= *)
(* SOME SAMPLE PROBLEMS TO TEST PROOF PROCEDURES                             *)
(* Copyright (c) 2001 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

open Useful;

(* ------------------------------------------------------------------------- *)
(* The program name.                                                         *)
(* ------------------------------------------------------------------------- *)

val PROGRAM = "problems2tptp";

(* ------------------------------------------------------------------------- *)
(* Problem data.                                                             *)
(* ------------------------------------------------------------------------- *)

use "problems.sml";

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun addSlash "" = ""
  | addSlash dir =
    if String.sub (dir, size dir - 1) = #"/" then dir
    else dir ^ "/";

fun checkProblems (problems : problem list) =
    let
      fun dups [] = ()
        | dups [_] = ()
        | dups (x :: (xs as x' :: _)) =
          if x <> x' then dups xs
          else raise Error ("duplicate problem name: " ^ x)

      val names = sort String.compare (map #name problems)
    in
      dups names
    end;

fun listProblem {name, comments = _, goal = _} = print (name ^ "\n");

fun outputProblem outputDir {name,comments,goal} =
    let
      val filename = name ^ ".tptp"
      val filename =
          case outputDir of
            NONE => filename
          | SOME dir => addSlash dir ^ filename

      val comment_bar = nChars #"-" 77
      val comment_footer =
          ["TPTP file created by " ^ host () ^ " at " ^
           time () ^ " on " ^ date () ^ "."]
      val comments =
          [comment_bar] @
          ["Name: " ^ name] @
          (if null comments then [] else "" :: comments) @
          (if null comment_footer then [] else "" :: comment_footer) @
          [comment_bar]

      val includes = []

      val formulas =
          let
            val name = Tptp.FormulaName "goal"
            val role = Tptp.ConjectureRole
            val body = Tptp.FofFormulaBody (Formula.parse goal)
            val source = Tptp.NoFormulaSource
          in
            [Tptp.Formula
               {name = name,
                role = role,
                body = body,
                source = source}]
          end

      val problem =
          Tptp.Problem
            {comments = comments,
             includes = includes,
             formulas = formulas}

      val mapping = Tptp.defaultMapping

      val () =
          Tptp.write
            {problem = problem,
             mapping = mapping,
             filename = filename}
    in
      ()
    end;

(* ------------------------------------------------------------------------- *)
(* Program options.                                                          *)
(* ------------------------------------------------------------------------- *)

datatype mode = OutputMode | ListMode;

val MODE : mode ref = ref OutputMode;

val COLLECTION : string option ref = ref NONE;

val OUTPUT_DIRECTORY : string option ref = ref NONE;

local
  open Useful Options;
in
  val specialOptions =
      [{switches = ["--collection"], arguments = ["C"],
        description = "restrict to the problems in collection C",
        processor =
          beginOpt
            (stringOpt endOpt)
            (fn _ => fn c => COLLECTION := SOME c)},
       {switches = ["--list"], arguments = [],
        description = "just list the problems",
        processor = beginOpt endOpt (fn _ => MODE := ListMode)},
       {switches = ["--output-dir"], arguments = ["DIR"],
        description = "the output directory",
        processor =
          beginOpt
            (stringOpt endOpt)
            (fn _ => fn d => OUTPUT_DIRECTORY := SOME d)}];
end;

val VERSION = "1.0";

val versionString = PROGRAM^" v"^VERSION^"\n";

val programOptions =
    {name    = PROGRAM,
     version = versionString,
     header  = "usage: "^PROGRAM^" [option ...]\n" ^
               "Outputs the set of sample problems in TPTP format.\n",
     footer  = "",
     options = specialOptions @ Options.basicOptions};

fun succeed () = Options.succeed programOptions;
fun fail mesg = Options.fail programOptions mesg;
fun usage mesg = Options.usage programOptions mesg;

val (opts,work) =
    Options.processOptions programOptions (CommandLine.arguments ());

val () = if null work then () else usage "too many arguments";

(* ------------------------------------------------------------------------- *)
(* Top level.                                                                *)
(* ------------------------------------------------------------------------- *)

val () =
let
  val problems =
      case !COLLECTION of
        NONE => problems
      | SOME c => List.filter (isCollection c) problems

  val () = checkProblems problems

  val () =
      case !MODE of
        ListMode => app listProblem problems
      | OutputMode => app (outputProblem (!OUTPUT_DIRECTORY)) problems
in
  succeed ()
end
handle Error s => die (PROGRAM^" failed:\n" ^ s)
     | Bug s => die ("BUG found in "^PROGRAM^" program:\n" ^ s);
