val thy = mk_base [Thy "Ord"] "Set2g" true;

structure Set2g =
struct

local
 val parse_ast_translation = [];
 val parse_translation = [];
 val print_translation = [];
 val print_ast_translation = [];
in



val thy = thy

|> add_trfuns
(parse_ast_translation, parse_translation, print_translation, print_ast_translation)

|> add_types
[("set", 1, NoSyn)]

|> add_tyabbrs
[]

|> add_consts
[("Ball", "'a set ë ('a ë bool) ë bool", NoSyn)]

|> add_syntax
[("GBall", "pttrn ë 'a set ë bool ë bool", Mixfix ("(3Â _ Î _ ./ _)", [], 10))]

|> add_trrules
[("logic", "Â x Î A . P") <-> ("logic", "Ball A (³x. P)")]

|> add_thyname "Set2g";

val _ = store_theory (thy, "Set2g");




end;
end;
