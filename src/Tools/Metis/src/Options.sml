(* ========================================================================= *)
(* PROCESSING COMMAND LINE OPTIONS                                           *)
(* Copyright (c) 2003 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Options :> Options =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* One command line option: names, arguments, description and a processor    *)
(* ------------------------------------------------------------------------- *)

type proc = string * string list -> unit;

type ('a,'x) mkProc = ('x -> proc) -> ('a -> 'x) -> proc;

type opt = {switches : string list, arguments : string list,
            description : string, processor : proc};

(* ------------------------------------------------------------------------- *)
(* Option processors may raise an OptionExit exception                       *)
(* ------------------------------------------------------------------------- *)

type optionExit = {message : string option, usage : bool, success : bool};

exception OptionExit of optionExit;

(* ------------------------------------------------------------------------- *)
(* Wrappers for option processors                                            *)
(* ------------------------------------------------------------------------- *)

fun beginOpt f p (s : string, l : string list) : unit = f (p s) (s,l);

fun endOpt () (_ : string, [] : string list) = ()
  | endOpt _ (_, _ :: _) = raise Bug "endOpt";

fun stringOpt _ _ (_ : string, []) = raise Bug "stringOpt"
  | stringOpt f p (s, (h : string) :: t) : unit = f (p h) (s,t);

local
  fun range NONE NONE = "Z"
    | range (SOME i) NONE = "{n IN Z | " ^ Int.toString i ^ " <= n}"
    | range NONE (SOME j) = "{n IN Z | n <= " ^ Int.toString j ^ "}"
    | range (SOME i) (SOME j) =
    "{n IN Z | " ^ Int.toString i ^ " <= n <= " ^ Int.toString j ^ "}";
  fun oLeq (SOME x) (SOME y) = x <= y | oLeq _ _ = true;
  fun argToInt arg omin omax x =
    (case Int.fromString x of
       SOME i =>
       if oLeq omin (SOME i) andalso oLeq (SOME i) omax then i else
         raise OptionExit
           {success = false, usage = false, message =
            SOME (arg ^ " option needs an integer argument in the range "
                  ^ range omin omax ^ " (not " ^ x ^ ")")}
     | NONE =>
       raise OptionExit
         {success = false, usage = false, message =
          SOME (arg ^ " option needs an integer argument (not \"" ^ x ^ "\")")})
    handle Overflow =>
       raise OptionExit
         {success = false, usage = false, message =
          SOME (arg ^ " option suffered integer overflow on argument " ^ x)};
in
  fun intOpt _ _ _ (_,[]) = raise Bug "intOpt"
    | intOpt (omin,omax) f p (s:string, h :: (t : string list)) : unit =
      f (p (argToInt s omin omax h)) (s,t);
end;

local
  fun range NONE NONE = "R"
    | range (SOME i) NONE = "{n IN R | " ^ Real.toString i ^ " <= n}"
    | range NONE (SOME j) = "{n IN R | n <= " ^ Real.toString j ^ "}"
    | range (SOME i) (SOME j) =
    "{n IN R | " ^ Real.toString i ^ " <= n <= " ^ Real.toString j ^ "}";
  fun oLeq (SOME (x:real)) (SOME y) = x <= y | oLeq _ _ = true;
  fun argToReal arg omin omax x =
    (case Real.fromString x of
       SOME i =>
       if oLeq omin (SOME i) andalso oLeq (SOME i) omax then i else
         raise OptionExit
           {success = false, usage = false, message =
            SOME (arg ^ " option needs an real argument in the range "
                  ^ range omin omax ^ " (not " ^ x ^ ")")}
     | NONE =>
       raise OptionExit
         {success = false, usage = false, message =
          SOME (arg ^ " option needs an real argument (not \"" ^ x ^ "\")")})
in
  fun realOpt _ _ _ (_,[]) = raise Bug "realOpt"
    | realOpt (omin,omax) f p (s:string, h :: (t : string list)) : unit =
      f (p (argToReal s omin omax h)) (s,t);
end;

fun enumOpt _ _ _ (_,[]) = raise Bug "enumOpt"
  | enumOpt (choices : string list) f p (s : string, h :: t) : unit =
    if mem h choices then f (p h) (s,t) else
      raise OptionExit
        {success = false, usage = false,
         message = SOME ("follow parameter " ^ s ^ " with one of {" ^
                         join "," choices ^ "}, not \"" ^ h ^ "\"")};

fun optionOpt _ _ _ (_,[]) = raise Bug "optionOpt"
  | optionOpt (x : string, p) f q (s : string, l as h :: t) : unit =
    if h = x then f (q NONE) (s,t) else p f (q o SOME) (s,l);

(* ------------------------------------------------------------------------- *)
(* Basic options useful for all programs                                     *)
(* ------------------------------------------------------------------------- *)

val basicOptions : opt list =
  [{switches = ["--"], arguments = [],
    description = "no more options",
    processor = fn _ => raise Fail "basicOptions: --"},
   {switches = ["-?","-h","--help"], arguments = [],
    description = "display option information and exit",
    processor = fn _ => raise OptionExit
    {message = SOME "displaying option information",
     usage = true, success = true}},
   {switches = ["-v", "--version"], arguments = [],
    description = "display version information",
    processor = fn _ => raise Fail "basicOptions: -v, --version"}];

(* ------------------------------------------------------------------------- *)
(* All the command line options of a program                                 *)
(* ------------------------------------------------------------------------- *)

type allOptions =
     {name : string, version : string, header : string,
      footer : string, options : opt list};

(* ------------------------------------------------------------------------- *)
(* Usage information                                                         *)
(* ------------------------------------------------------------------------- *)

fun versionInformation ({version, ...} : allOptions) = version;

fun usageInformation ({name,version,header,footer,options} : allOptions) =
  let
    fun listOpts {switches = n, arguments = r, description = s,
                  processor = _} =
        let
          fun indent (s, "" :: l) = indent (s ^ "  ", l) | indent x = x
          val (res,n) = indent ("  ",n)
          val res = res ^ join ", " n
          val res = List.foldl (fn (x,y) => y ^ " " ^ x) res r
        in
          [res ^ " ...", " " ^ s]
        end

    val alignment =
        [{leftAlign = true, padChar = #"."},
         {leftAlign = true, padChar = #" "}]

    val table = alignTable alignment (List.map listOpts options)
  in
    header ^ join "\n" table ^ "\n" ^ footer
  end;

(* ------------------------------------------------------------------------- *)
(* Exit the program gracefully                                               *)
(* ------------------------------------------------------------------------- *)

fun exit (allopts : allOptions) (optexit : optionExit) =
  let
    val {name, options, ...} = allopts
    val {message, usage, success} = optexit
    fun err s = TextIO.output (TextIO.stdErr, s)
  in
    case message of NONE => () | SOME m => err (name ^ ": " ^ m ^ "\n");
    if usage then err (usageInformation allopts) else ();
    OS.Process.exit (if success then OS.Process.success else OS.Process.failure)
  end;

fun succeed allopts =
    exit allopts {message = NONE, usage = false, success = true};

fun fail allopts mesg =
    exit allopts {message = SOME mesg, usage = false, success = false};

fun usage allopts mesg =
    exit allopts {message = SOME mesg, usage = true, success = false};

fun version allopts =
    (TextIO.print (versionInformation allopts);
     exit allopts {message = NONE, usage = false, success = true});

(* ------------------------------------------------------------------------- *)
(* Process the command line options passed to the program                    *)
(* ------------------------------------------------------------------------- *)

fun processOptions (allopts : allOptions) =
  let
    fun findOption x =
      case List.find (fn {switches = n, ...} => mem x n) (#options allopts) of
        NONE => raise OptionExit
                        {message = SOME ("unknown switch \"" ^ x ^ "\""),
                         usage = true, success = false}
      | SOME {arguments = r, processor = f, ...} => (r,f)

    fun getArgs x r xs =
      let
        fun f 1 = "a following argument"
          | f m = Int.toString m ^ " following arguments"
        val m = length r
        val () =
          if m <= length xs then () else
            raise OptionExit
              {usage = false, success = false, message = SOME
               (x ^ " option needs " ^ f m ^ ": " ^ join " " r)}
      in
        divide xs m
      end

    fun process [] = ([], [])
      | process ("--" :: xs) = ([("--",[])], xs)
      | process ("-v" :: _) = version allopts
      | process ("--version" :: _) = version allopts
      | process (x :: xs) =
      if x = "" orelse x = "-" orelse hd (String.explode x) <> #"-" then
        ([], x :: xs)
      else
        let
          val (r,f) = findOption x
          val (ys,xs) = getArgs x r xs
          val () = f (x,ys)

          val (xys,xs) = process xs
        in
          ((x,ys) :: xys, xs)
        end
  in
    fn l =>
       let
         val (a,b) = process l

         val a = List.foldl (fn ((x,xs),ys) => x :: xs @ ys) [] (List.rev a)
       in
         (a,b)
       end
       handle OptionExit x => exit allopts x
  end;

end
