(* ========================================================================= *)
(* SOME SAMPLE PROBLEMS TO TEST PROOF PROCEDURES                             *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
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

      val goal = Formula.parse goal
      val formulas =
          [Tptp.FofFormula {name = "goal", role = "conjecture", formula = goal}]

      val problem = {comments = comments, formulas = formulas}
    in
      Tptp.write {filename = filename} problem
    end;

(* ------------------------------------------------------------------------- *)
(* Program options.                                                          *)
(* ------------------------------------------------------------------------- *)

val OUTPUT_DIRECTORY : string option ref = ref NONE;

local
  open Useful Options;
in
  val specialOptions =
      [{switches = ["--output"], arguments = ["DIR"],
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
  val () = checkProblems problems

  val () = app (outputProblem (!OUTPUT_DIRECTORY)) problems
in
  succeed ()
end
handle Error s => die (PROGRAM^" failed:\n" ^ s)
     | Bug s => die ("BUG found in "^PROGRAM^" program:\n" ^ s);
