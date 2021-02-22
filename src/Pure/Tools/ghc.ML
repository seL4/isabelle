(*  Title:      Pure/Tools/ghc.ML
    Author:     Makarius

Support for GHC: Glasgow Haskell Compiler.
*)

signature GHC =
sig
  val print_codepoint: UTF8.codepoint -> string
  val print_symbol: Symbol.symbol -> string
  val print_string: string -> string
  val project_template: {depends: string list, modules: string list} -> string
  val new_project: Path.T -> {name: string, depends: string list, modules: string list} -> unit
end;

structure GHC: GHC =
struct

(** string literals **)

fun print_codepoint c =
  (case c of
    34 => "\\\""
  | 39 => "\\'"
  | 92 => "\\\\"
  | 7 => "\\a"
  | 8 => "\\b"
  | 9 => "\\t"
  | 10 => "\\n"
  | 11 => "\\v"
  | 12 => "\\f"
  | 13 => "\\r"
  | c =>
      if c >= 32 andalso c < 127 then chr c
      else "\\" ^ string_of_int c ^ "\\&");

fun print_symbol sym =
  (case Symbol.decode sym of
    Symbol.Char s => print_codepoint (ord s)
  | Symbol.UTF8 s => UTF8.decode_permissive s |> map print_codepoint |> implode
  | Symbol.Sym s => "\\092<" ^ s ^ ">"
  | Symbol.Control s => "\\092<^" ^ s ^ ">"
  | _ => translate_string (print_codepoint o ord) sym);

val print_string = quote o implode o map print_symbol o Symbol.explode;



(** project setup **)

fun project_template {depends, modules} =
  \<^verbatim>\<open>{-# START_FILE {{name}}.cabal #-}
name:                {{name}}
version:             0.1.0.0
homepage:            default
license:             BSD3
author:              default
maintainer:          default
category:            default
build-type:          Simple
cabal-version:       >=1.10

executable {{name}}
  hs-source-dirs:      src
  main-is:             Main.hs
  default-language:    Haskell2010
  build-depends:       \<close> ^ commas ("base >= 4.7 && < 5" :: depends) ^
  \<^verbatim>\<open>
  other-modules:       \<close> ^ commas modules ^
  \<^verbatim>\<open>
{-# START_FILE Setup.hs #-}
import Distribution.Simple
main = defaultMain

{-# START_FILE src/Main.hs #-}
module Main where

main :: IO ()
main = return ()
\<close>;

fun new_project dir {name, depends, modules} =
  let
    val template_path = dir + (Path.basic name |> Path.ext "hsfiles");
    val _ = File.write template_path (project_template {depends = depends, modules = modules});
    val _ =
      Isabelle_System.bash_process
        ("cd " ^ File.bash_path dir ^ "; isabelle ghc_stack new " ^ Bash.string name ^
          " --bare " ^ File.bash_platform_path template_path)
      |> Process_Result.check;
  in () end;

end;
