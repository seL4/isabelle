(* ========================================================================= *)
(* PROCESSING COMMAND LINE OPTIONS                                           *)
(* Copyright (c) 2003-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Options =
sig

(* ------------------------------------------------------------------------- *)
(* Option processors take an option with its associated arguments.           *)
(* ------------------------------------------------------------------------- *)

type proc = string * string list -> unit

type ('a,'x) mkProc = ('x -> proc) -> ('a -> 'x) -> proc

(* ------------------------------------------------------------------------- *)
(* One command line option: names, arguments, description and a processor.   *)
(* ------------------------------------------------------------------------- *)

type opt =
     {switches : string list, arguments : string list,
      description : string, processor : proc}

(* ------------------------------------------------------------------------- *)
(* Option processors may raise an OptionExit exception.                      *)
(* ------------------------------------------------------------------------- *)

type optionExit = {message : string option, usage : bool, success : bool}

exception OptionExit of optionExit

(* ------------------------------------------------------------------------- *)
(* Constructing option processors.                                           *)
(* ------------------------------------------------------------------------- *)

val beginOpt : (string,'x) mkProc

val endOpt : unit -> proc

val stringOpt : (string,'x) mkProc

val intOpt : int option * int option -> (int,'x) mkProc

val realOpt : real option * real option -> (real,'x) mkProc

val enumOpt : string list -> (string,'x) mkProc

val optionOpt : string * ('a,'x) mkProc -> ('a option,'x) mkProc

(* ------------------------------------------------------------------------- *)
(* Basic options useful for all programs.                                    *)
(* ------------------------------------------------------------------------- *)

val basicOptions : opt list

(* ------------------------------------------------------------------------- *)
(* All the command line options of a program.                                *)
(* ------------------------------------------------------------------------- *)

type allOptions =
     {name : string, version : string, header : string,
      footer : string, options : opt list}

(* ------------------------------------------------------------------------- *)
(* Usage information.                                                        *)
(* ------------------------------------------------------------------------- *)

val versionInformation : allOptions -> string

val usageInformation : allOptions -> string

(* ------------------------------------------------------------------------- *)
(* Exit the program gracefully.                                              *)
(* ------------------------------------------------------------------------- *)

val exit : allOptions -> optionExit -> 'exit

val succeed : allOptions -> 'exit

val fail : allOptions -> string -> 'exit

val usage : allOptions -> string -> 'exit

val version : allOptions -> 'exit

(* ------------------------------------------------------------------------- *)
(* Process the command line options passed to the program.                   *)
(* ------------------------------------------------------------------------- *)

val processOptions : allOptions -> string list -> string list * string list

end
