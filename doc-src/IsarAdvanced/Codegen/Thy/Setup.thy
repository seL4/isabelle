theory Setup
imports Complex_Main
uses "../../../antiquote_setup.ML"
begin

ML {* no_document use_thys ["Efficient_Nat", "Code_Char_chr"] *}

ML_val {* Code_Target.code_width := 74 *}

ML {*
fun pr_class ctxt = enclose "\\isa{" "}" o Sign.extern_class (ProofContext.theory_of ctxt)
  o Sign.read_class (ProofContext.theory_of ctxt);
*}

ML {*
val _ = ThyOutput.add_commands
  [("class", ThyOutput.args (Scan.lift Args.name) (K pr_class))]
*}

ML {*
val verbatim_line = space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|";
val verbatim_lines = rev
  #> dropwhile (fn s => s = "")
  #> rev
  #> map verbatim_line #> space_implode "\\newline%\n"
  #> prefix "\\isaverbatim%\n\\noindent%\n"
*}

ML {*
local

  val parse_const_terms = Scan.repeat1 Args.term
    >> (fn ts => fn thy => map (Code_Unit.check_const thy) ts);
  val parse_consts = Scan.lift (Args.parens (Args.$$$ "consts")) |-- parse_const_terms
    >> (fn mk_cs => fn thy => map (Code_Name.const thy) (mk_cs thy));
  val parse_types = Scan.lift (Args.parens (Args.$$$ "types") |-- Scan.repeat1 Args.name)
    >> (fn tycos => fn thy => map (Code_Name.tyco thy o Sign.intern_type thy) tycos);
  val parse_classes = Scan.lift (Args.parens (Args.$$$ "classes") |-- Scan.repeat1 Args.name)
    >> (fn classes => fn thy => map (Code_Name.class thy o Sign.intern_class thy) classes);
  val parse_instances = Scan.lift (Args.parens (Args.$$$ "instances") |-- Scan.repeat1 (Args.name --| Args.$$$ "::" -- Args.name))
    >> (fn insts => fn thy => map (Code_Name.instance thy o apsnd (Sign.intern_type thy) o apfst (Sign.intern_class thy) o swap) insts);
  val parse_names = parse_consts || parse_types || parse_classes || parse_instances; 

  fun code_stmts src ctxt ((mk_cs, mk_stmtss), target) =
    Code_Target.code_of (ProofContext.theory_of ctxt)
      target "Example" (mk_cs (ProofContext.theory_of ctxt))
        (maps (fn f => f (ProofContext.theory_of ctxt)) mk_stmtss)
    |> split_lines
    |> verbatim_lines;

in

val _ = ThyOutput.add_commands
  [("code_stmts", ThyOutput.args
      (parse_const_terms -- Scan.repeat parse_names -- Scan.lift (Args.parens Args.name))
        code_stmts)]

end
*}

end
