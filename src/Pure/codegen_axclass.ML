(*  Title:      Pure/codegen.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Stub code generator for (axiomatic) type classes
*)

(*!!! for now, only experimental scratch code !!!*)

type theory = unit;
type constname = string;
type typerepr = string;
type clsname = string;
type typname = string;
type defname = string;
type constdef = constname * typerepr;
type instdecl = typname * clsname list * defname list;

signature CODEGEN_AXCLASS =
sig
  val gen_clsdict_typ: theory -> clsname -> clsname list -> constdef list -> string; 
  val gen_clsdict_insts: theory -> clsname -> clsname list -> instdecl list -> constdef list -> string; 
  val gen_clsdicts: theory -> clsname -> clsname list -> instdecl list -> constdef list -> string -> string; 
end;

structure CodegenAxclass : CODEGEN_AXCLASS =
struct

fun enumerate ls = "  " ^ (space_implode ",\n  " ls) ^ "\n"

fun get_dictidf thy cls = cls ^ "_dict";

fun get_dictidf_inst thy cls ty = cls ^ "_" ^ ty ^ "_dict";

fun get_clsidf thy cls = cls ^ "_class";

fun get_memidf thy const = const;

fun gen_clsdict_typ thy cls supclss consts =
  "type 'a " ^ (get_dictidf thy cls) ^ " = {\n"
  ^ (((supclss |> map (fn supcls => (get_clsidf thy supcls) ^ ": 'a " ^ (get_dictidf thy supcls)))
      @ (consts |> map (fn (cname, ctyp) => (get_memidf thy cname) ^ ": " ^ ctyp)))
      |> enumerate)
  ^ "};\n";

fun gen_clsdict_mem thy cls consts =
  consts |> map (fn (cname, _) =>
    "fun " ^ (get_memidf thy cname) ^ " (cdict:'a " ^ (get_dictidf thy cls) ^ ") = #" ^ (get_memidf thy cname) ^ " cdict;\n")
  |> space_implode "";

fun gen_clsdict_inst thy cls supclss (ty, clsargs, constdefs) consts =
  "val " ^ (get_dictidf_inst thy cls ty) ^ " = {\n"
  ^ (((supclss |> map (fn supcls => (get_clsidf thy cls) ^ " = " ^ (get_dictidf_inst thy supcls ty)))
      @ ((fst (split_list consts) ~~ constdefs) |>
        map (fn (cname, dname) => (get_memidf thy cname) ^ " = " ^ dname)))
      |> enumerate)
  ^ "};\n";

fun gen_clsdict_insts thy cls supclss insts consts =
  insts |> map (fn inst => gen_clsdict_inst thy cls supclss inst consts) |> cat_lines

fun gen_clsdicts thy cls supclss insts consts constdefs =
  gen_clsdict_typ thy cls supclss consts ^ "\n"
  ^ gen_clsdict_mem thy cls consts ^ "\n"
  ^ constdefs ^ "\n"
  ^ (insts |> map (fn inst => gen_clsdict_inst thy cls supclss inst consts) |> cat_lines);

end;

open CodegenAxclass;

val ex_list =
"fun list_le _ _ [] _  = true\n" ^ 
"  | list_le _ _ _  [] = false\n" ^ 
"  | list_le (cdict:'a list ord_dict) (cdict1:'a ord_dict) (x::xs) (y::ys) = #lt cdict1 x y orelse #eq (#eq_class cdict1) x y andalso list_le cdict cdict1 xs ys;\n\n" ^
"fun list_lt _ _ [] [] = false\n" ^ 
"  | list_lt _ _ [] _  = true\n" ^ 
"  | list_lt _ _ _  [] = false\n" ^ 
"  | list_lt (cdict:'a list ord_dict) (cdict1:'a ord_dict) (x::xs) (y::ys) = #lt cdict1 x y orelse #eq (#eq_class cdict1) x y andalso list_lt cdict cdict1 xs ys;\n\n"

val ex_eq = gen_clsdicts ()
    "eq" []
    [("int", [], ["(op =)"]),
     ("char", [], ["(op =)"]),
     ("list", [], ["(op =)"])]
    [("eq", "'a -> 'a -> bool")]
    "";

val ex_ord = gen_clsdicts ()
    "ord" ["eq"]
    [("int", [], ["(op <=)", "(op <)"]),
     ("char", [], ["(op <=)", "(op <)"]),
     ("list", ["ord"], ["list_le", "list_lt"])]
    [("le", "'a -> 'a -> bool"), ("lt", "'a -> 'a -> bool")]
    ex_list;

fun ex _ = TextIO.output (TextIO.stdOut, cat_lines [ex_eq, ex_ord]);

(* TODO:
- Dependency: dicttypdecl, members, (instancedef, instance)+
- Nahtstelle ausfindig machen
*)