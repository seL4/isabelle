(*  Title:      HOL/Datatype_Benchmark/Verilog.thy

Example from Daryl: a Verilog grammar.
*)

theory Verilog imports Main begin

datatype
  Source_text
     = module string "string list" "Module_item list"
     | Source_textMeta string
and
  Module_item
     = "declaration" Declaration
     | initial Statement
     | always Statement
     | assign Lvalue Expression
     | Module_itemMeta string
and
  Declaration
     = reg_declaration "Range option" "string list"
     | net_declaration "Range option" "string list"
     | input_declaration "Range option" "string list"
     | output_declaration "Range option" "string list"
     | DeclarationMeta string
and
  Range = range Expression Expression | RangeMeta string
and
  Statement
     = clock_statement Clock Statement_or_null
     | blocking_assignment Lvalue Expression
     | non_blocking_assignment Lvalue Expression
     | conditional_statement
          Expression Statement_or_null "Statement_or_null option"
     | case_statement Expression "Case_item list"
     | while_loop Expression Statement
     | repeat_loop Expression Statement
     | for_loop
          Lvalue Expression Expression Lvalue Expression Statement
     | forever_loop Statement
     | disable string
     | seq_block "string option" "Statement list"
     | StatementMeta string
and
  Statement_or_null
     = statement Statement | null_statement | Statement_or_nullMeta string
and
  Clock
     = posedge string
     | negedge string
     | clock string
     | ClockMeta string
and
  Case_item
     = case_item "Expression list" Statement_or_null
     | default_case_item Statement_or_null
     | Case_itemMeta string
and
  Expression
     = plus Expression Expression
     | minus Expression Expression
     | lshift Expression Expression
     | rshift Expression Expression
     | lt Expression Expression
     | leq Expression Expression
     | gt Expression Expression
     | geq Expression Expression
     | logeq Expression Expression
     | logneq Expression Expression
     | caseeq Expression Expression
     | caseneq Expression Expression
     | bitand Expression Expression
     | bitxor Expression Expression
     | bitor Expression Expression
     | logand Expression Expression
     | logor Expression Expression
     | conditional Expression Expression Expression
     | positive Primary
     | negative Primary
     | lognot Primary
     | bitnot Primary
     | reducand Primary
     | reducxor Primary
     | reducor Primary
     | reducnand Primary
     | reducxnor Primary
     | reducnor Primary
     | primary Primary
     | ExpressionMeta string
and
  Primary
     = primary_number Number
     | primary_IDENTIFIER string
     | primary_bit_select string Expression
     | primary_part_select string Expression Expression
     | primary_gen_bit_select Expression Expression
     | primary_gen_part_select Expression Expression Expression
     | primary_concatenation Concatenation
     | primary_multiple_concatenation Multiple_concatenation
     | brackets Expression
     | PrimaryMeta string
and
  Lvalue
     = lvalue string
     | lvalue_bit_select string Expression
     | lvalue_part_select string Expression Expression
     | lvalue_concatenation Concatenation
     | LvalueMeta string
and
  Number
     = decimal string
     | based "string option" string
     | NumberMeta string
and
  Concatenation
     = concatenation "Expression list" | ConcatenationMeta string
and
  Multiple_concatenation
     = multiple_concatenation Expression "Expression list"
     | Multiple_concatenationMeta string
and
  meta
     = Meta_Source_text Source_text
     | Meta_Module_item Module_item
     | Meta_Declaration Declaration
     | Meta_Range Range
     | Meta_Statement Statement
     | Meta_Statement_or_null Statement_or_null
     | Meta_Clock Clock
     | Meta_Case_item Case_item
     | Meta_Expression Expression
     | Meta_Primary Primary
     | Meta_Lvalue Lvalue
     | Meta_Number Number
     | Meta_Concatenation Concatenation
     | Meta_Multiple_concatenation Multiple_concatenation

end
