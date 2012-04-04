open TPTP_Syntax

exception UNRECOGNISED_SYMBOL of string * string

exception UNRECOGNISED_ROLE of string
fun classify_role role =
  case role of
    "axiom" => Role_Axiom
  | "hypothesis" => Role_Hypothesis
  | "definition" => Role_Definition
  | "assumption" => Role_Assumption
  | "lemma" => Role_Lemma
  | "theorem" => Role_Theorem
  | "conjecture" => Role_Conjecture
  | "negated_conjecture" => Role_Negated_Conjecture
  | "plain" => Role_Plain
  | "fi_domain" => Role_Fi_Domain
  | "fi_functors" => Role_Fi_Functors
  | "fi_predicates" => Role_Fi_Predicates
  | "type" => Role_Type
  | "unknown" => Role_Unknown
  | thing => raise (UNRECOGNISED_ROLE thing)

fun extract_quant_info (Quant (quantifier, vars, tptp_formula)) =
  (quantifier, vars, tptp_formula)

%%
%name TPTP
%term AMPERSAND | AT_SIGN | CARET | COLON | COMMA | EQUALS | EXCLAMATION
  | LET | ARROW | FI | IFF | IMPLIES | INCLUDE
  | LAMBDA | LBRKT | LPAREN | MAP_TO | MMINUS | NAND
  | NEQUALS | XOR | NOR | PERIOD | PPLUS | QUESTION | RBRKT | RPAREN
  | TILDE | TOK_FALSE | TOK_I | TOK_O | TOK_INT | TOK_REAL | TOK_RAT | TOK_TRUE
  | TOK_TYPE | VLINE | EOF | DTHF | DFOF | DCNF | DFOT | DTFF | REAL of string
  | RATIONAL of string | SIGNED_INTEGER of string | UNSIGNED_INTEGER of string
  | DOT_DECIMAL of string | SINGLE_QUOTED of string | UPPER_WORD of string
  | LOWER_WORD of string | COMMENT of string
  | DISTINCT_OBJECT of string
  | DUD | INDEF_CHOICE | DEFIN_CHOICE
  | OPERATOR_FORALL | OPERATOR_EXISTS
  | PLUS | TIMES | GENTZEN_ARROW | DEP_SUM | DEP_PROD
  | DOLLAR_WORD of string | DOLLAR_DOLLAR_WORD of string
  | SUBTYPE | LET_TERM
  | THF | TFF | FOF | CNF
  | ITE_F | ITE_T
  | LET_TF | LET_FF | LET_FT | LET_TT

%nonterm
    annotations of annotation option
  | name of string
  | name_list of string list
  | formula_selection of string list
  | optional_info of general_term list
  | general_list of general_list | general_terms of general_term list
  | general_term of general_term

  | atomic_word of string
  | general_data of general_data | variable_ of string
  | number of number_kind * string | formula_data of general_data
  | integer of string
  | identifier of string
  | general_function of general_data | useful_info of general_list
  | file_name of string
  | functor_ of symbol
  | term of tptp_term
  | arguments of tptp_term list
  | defined_functor of symbol
  | system_functor of symbol
  | system_constant of symbol
  | system_term of symbol * tptp_term list
  | defined_constant of symbol
  | defined_plain_term of symbol * tptp_term list
  | defined_atomic_term of tptp_term
  | defined_atom of tptp_term
  | defined_term of tptp_term
  | constant of symbol
  | plain_term of symbol * tptp_term list
  | function_term of tptp_term
  | conditional_term of tptp_term
  | system_atomic_formula of tptp_formula
  | infix_equality of symbol
  | infix_inequality of symbol
  | defined_infix_pred of symbol
  | defined_infix_formula of tptp_formula
  | defined_prop of string
  | defined_pred of string
  | defined_plain_formula of tptp_formula
  | defined_atomic_formula of tptp_formula
  | plain_atomic_formula of tptp_formula
  | atomic_formula of tptp_formula
  | unary_connective of symbol

  | defined_type of tptp_base_type
  | system_type of string
  | assoc_connective of symbol
  | binary_connective of symbol
  | fol_quantifier of quantifier
  | thf_unary_connective of symbol
  | thf_pair_connective of symbol
  | thf_quantifier of quantifier
  | fol_infix_unary of tptp_formula
  | thf_conn_term of symbol
  | literal of tptp_formula
  | disjunction of tptp_formula
  | cnf_formula of tptp_formula
  | fof_tuple_list of tptp_formula list
  | fof_tuple of tptp_formula list
  | fof_sequent of tptp_formula
  | fof_unary_formula of tptp_formula
  | fof_variable_list of string list
  | fof_quantified_formula of tptp_formula
  | fof_unitary_formula of tptp_formula
  | fof_and_formula of tptp_formula
  | fof_or_formula of tptp_formula
  | fof_binary_assoc of tptp_formula
  | fof_binary_nonassoc of tptp_formula
  | fof_binary_formula of tptp_formula
  | fof_logic_formula of tptp_formula
  | fof_formula of tptp_formula
  | tff_tuple of tptp_formula list
  | tff_tuple_list of tptp_formula list
  | tff_sequent of tptp_formula
  | tff_conditional of tptp_formula
  | tff_xprod_type of tptp_type
  | tff_mapping_type of tptp_type
  | tff_atomic_type of tptp_type
  | tff_unitary_type of tptp_type
  | tff_top_level_type of tptp_type
  | tff_untyped_atom of symbol * tptp_type option
  | tff_typed_atom of symbol * tptp_type option
  | tff_unary_formula of tptp_formula
  | tff_typed_variable of string * tptp_type option
  | tff_variable of string * tptp_type option
  | tff_variable_list of (string * tptp_type option) list
  | tff_quantified_formula of tptp_formula
  | tff_unitary_formula of tptp_formula
  | tff_and_formula of tptp_formula
  | tff_or_formula of tptp_formula
  | tff_binary_assoc of tptp_formula
  | tff_binary_nonassoc of tptp_formula
  | tff_binary_formula of tptp_formula
  | tff_logic_formula of tptp_formula
  | tff_formula of tptp_formula

  | thf_tuple of tptp_formula list
  | thf_tuple_list of tptp_formula list
  | thf_sequent of tptp_formula
  | thf_conditional of tptp_formula
  | thf_let of tptp_formula
  | thf_atom of tptp_formula
  | thf_union_type of tptp_type
  | thf_xprod_type of tptp_type
  | thf_mapping_type of tptp_type
  | thf_binary_type of tptp_type
  | thf_unitary_type of tptp_type
  | thf_top_level_type of tptp_type
  | thf_subtype of tptp_type
  | thf_typeable_formula of tptp_formula
  | thf_type_formula of tptp_formula * tptp_type
  | thf_unary_formula of tptp_formula
  | thf_typed_variable of string * tptp_type option
  | thf_variable of string * tptp_type option
  | thf_variable_list of (string * tptp_type option) list
  | thf_quantified_formula of tptp_formula
  | thf_unitary_formula of tptp_formula
  | thf_apply_formula of tptp_formula
  | thf_and_formula of tptp_formula
  | thf_or_formula of tptp_formula
  | thf_binary_tuple of tptp_formula
  | thf_binary_pair of tptp_formula
  | thf_binary_formula of tptp_formula
  | thf_logic_formula of tptp_formula
  | thf_formula of tptp_formula
  | formula_role of role

  | cnf_annotated of tptp_line
  | fof_annotated of tptp_line
  | tff_annotated of tptp_line
  | thf_annotated of tptp_line
  | annotated_formula of tptp_line
  | include_ of tptp_line
  | tptp_input of tptp_line
  | tptp_file of tptp_problem
  | tptp of tptp_problem

  | thf_let_defn of tptp_let list
  | tff_let of tptp_formula
  | tff_let_term_defn of tptp_let list
  | tff_let_formula_defn of tptp_let list
  | tff_quantified_type of tptp_type
  | tff_monotype of tptp_type
  | tff_type_arguments of tptp_type list
  | let_term of tptp_term
  | atomic_defined_word of string
  | atomic_system_word of string

%pos int
%eop EOF
%noshift EOF
%arg (file_name) : string

%nonassoc LET
%nonassoc RPAREN
%nonassoc DUD
%right COMMA
%left COLON

%left AT_SIGN
%nonassoc IFF XOR
%right IMPLIES FI
%nonassoc EQUALS NEQUALS
%right VLINE NOR
%left AMPERSAND NAND
%right ARROW
%left PLUS
%left TIMES

%right OPERATOR_FORALL OPERATOR_EXISTS

%nonassoc EXCLAMATION QUESTION LAMBDA CARET
%nonassoc TILDE
%pure
%start tptp
%verbose
%%

(*  Title:      HOL/TPTP/TPTP_Parser/tptp.yacc
    Author:     Nik Sultana, Cambridge University Computer Laboratory

 Parser for TPTP languages. Latest version of the language spec can
 be obtained from http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html
 This implements version 5.3.0.
*)

tptp : tptp_file (( tptp_file ))

tptp_file : tptp_input tptp_file (( tptp_input :: tptp_file ))
          | COMMENT tptp_file    (( tptp_file ))
          |                      (( [] ))

tptp_input : annotated_formula (( annotated_formula ))
           | include_           (( include_ ))

annotated_formula : thf_annotated (( thf_annotated ))
                  | tff_annotated (( tff_annotated ))
                  | fof_annotated (( fof_annotated ))
                  | cnf_annotated (( cnf_annotated ))

thf_annotated : THF LPAREN name COMMA formula_role COMMA thf_formula annotations RPAREN PERIOD ((
  Annotated_Formula ((file_name, THFleft + 1, THFright + 1),
   THF, name, formula_role, thf_formula, annotations)
))

tff_annotated : TFF LPAREN name COMMA formula_role COMMA tff_formula annotations RPAREN PERIOD ((
  Annotated_Formula ((file_name, TFFleft + 1, TFFright + 1),
   TFF, name, formula_role, tff_formula, annotations)
))

fof_annotated : FOF LPAREN name COMMA formula_role COMMA fof_formula annotations RPAREN PERIOD ((
  Annotated_Formula ((file_name, FOFleft + 1, FOFright + 1),
   FOF, name, formula_role, fof_formula, annotations)
))

cnf_annotated : CNF LPAREN name COMMA formula_role COMMA cnf_formula annotations RPAREN PERIOD ((
  Annotated_Formula ((file_name, CNFleft + 1, CNFright + 1),
   CNF, name, formula_role, cnf_formula, annotations)
))

annotations : COMMA general_term optional_info (( SOME (general_term, optional_info) ))
            |                                  (( NONE ))

formula_role : LOWER_WORD (( classify_role LOWER_WORD ))


(* THF formulas *)

thf_formula : thf_logic_formula (( thf_logic_formula ))
            | thf_sequent       (( thf_sequent ))

thf_logic_formula : thf_binary_formula   (( thf_binary_formula ))
                  | thf_unitary_formula  (( thf_unitary_formula ))
                  | thf_type_formula     (( THF_typing thf_type_formula ))
                  | thf_subtype          (( THF_type thf_subtype ))

thf_binary_formula : thf_binary_pair   (( thf_binary_pair ))
                   | thf_binary_tuple  (( thf_binary_tuple ))
                   | thf_binary_type   (( THF_type thf_binary_type ))

thf_binary_pair : thf_unitary_formula thf_pair_connective thf_unitary_formula ((
  Fmla (thf_pair_connective, [thf_unitary_formula1, thf_unitary_formula2])
))

thf_binary_tuple : thf_or_formula    (( thf_or_formula ))
                 | thf_and_formula   (( thf_and_formula ))
                 | thf_apply_formula (( thf_apply_formula ))

thf_or_formula : thf_unitary_formula VLINE thf_unitary_formula (( Fmla (Interpreted_Logic Or, [thf_unitary_formula1, thf_unitary_formula2]) ))
               | thf_or_formula VLINE thf_unitary_formula      (( Fmla (Interpreted_Logic Or, [thf_or_formula, thf_unitary_formula]) ))

thf_and_formula : thf_unitary_formula AMPERSAND thf_unitary_formula (( Fmla (Interpreted_Logic And, [thf_unitary_formula1, thf_unitary_formula2]) ))
                | thf_and_formula AMPERSAND thf_unitary_formula     (( Fmla (Interpreted_Logic And, [thf_and_formula, thf_unitary_formula]) ))

thf_apply_formula : thf_unitary_formula AT_SIGN thf_unitary_formula (( Fmla (Interpreted_ExtraLogic Apply, [thf_unitary_formula1, thf_unitary_formula2]) ))
                  | thf_apply_formula AT_SIGN thf_unitary_formula   (( Fmla (Interpreted_ExtraLogic Apply, [thf_apply_formula, thf_unitary_formula]) ))

thf_unitary_formula : thf_quantified_formula (( thf_quantified_formula ))
                    | thf_unary_formula      (( thf_unary_formula ))
                    | thf_atom               (( thf_atom ))
                    | thf_conditional        (( thf_conditional ))
                    | thf_let                (( thf_let ))
                    | LPAREN thf_logic_formula RPAREN  (( thf_logic_formula ))

thf_quantified_formula : thf_quantifier LBRKT thf_variable_list RBRKT COLON thf_unitary_formula ((
  Quant (thf_quantifier, thf_variable_list, thf_unitary_formula)
))

thf_variable_list : thf_variable                          (( [thf_variable] ))
                  | thf_variable COMMA thf_variable_list  (( thf_variable :: thf_variable_list ))

thf_variable : thf_typed_variable (( thf_typed_variable ))
             | variable_          (( (variable_, NONE) ))

thf_typed_variable : variable_ COLON thf_top_level_type (( (variable_, SOME thf_top_level_type) ))

thf_unary_formula : thf_unary_connective LPAREN thf_logic_formula RPAREN ((
  Fmla (thf_unary_connective, [thf_logic_formula])
))

thf_atom : term          (( Atom (THF_Atom_term term) ))
         | thf_conn_term (( Atom (THF_Atom_conn_term thf_conn_term) ))

thf_conditional : ITE_F LPAREN thf_logic_formula COMMA thf_logic_formula COMMA thf_logic_formula RPAREN ((
  Conditional (thf_logic_formula1, thf_logic_formula2, thf_logic_formula3)
))

thf_let : LET_TF LPAREN thf_let_defn COMMA thf_formula RPAREN ((
  Let (thf_let_defn, thf_formula)
))

(*FIXME here could check that fmla is of right form (TPTP BNF L130-134)*)
thf_let_defn : thf_quantified_formula ((
  let
    val (_, vars, fmla) = extract_quant_info thf_quantified_formula
  in [Let_fmla (hd vars, fmla)]
  end
))

thf_type_formula : thf_typeable_formula COLON thf_top_level_type (( (thf_typeable_formula, thf_top_level_type) ))

thf_typeable_formula : thf_atom                         (( thf_atom ))
                     | LPAREN thf_logic_formula RPAREN  (( thf_logic_formula ))

thf_subtype : constant SUBTYPE constant (( Subtype(constant1, constant2) ))

thf_top_level_type : thf_logic_formula (( Fmla_type thf_logic_formula ))

thf_unitary_type : thf_unitary_formula (( Fmla_type thf_unitary_formula ))

thf_binary_type : thf_mapping_type (( thf_mapping_type ))
                | thf_xprod_type   (( thf_xprod_type ))
                | thf_union_type   (( thf_union_type ))

thf_mapping_type : thf_unitary_type ARROW thf_unitary_type (( Fn_type(thf_unitary_type1, thf_unitary_type2) ))
                 | thf_unitary_type ARROW thf_mapping_type (( Fn_type(thf_unitary_type, thf_mapping_type) ))

thf_xprod_type : thf_unitary_type TIMES thf_unitary_type   (( Prod_type(thf_unitary_type1, thf_unitary_type2) ))
               | thf_xprod_type TIMES thf_unitary_type     (( Prod_type(thf_xprod_type, thf_unitary_type) ))

thf_union_type : thf_unitary_type PLUS thf_unitary_type    (( Sum_type(thf_unitary_type1, thf_unitary_type2) ))
               | thf_union_type PLUS thf_unitary_type      (( Sum_type(thf_union_type, thf_unitary_type) ))

thf_sequent : thf_tuple GENTZEN_ARROW thf_tuple  (( Sequent(thf_tuple1, thf_tuple2) ))
            | LPAREN thf_sequent RPAREN          (( thf_sequent ))

thf_tuple : LBRKT RBRKT                (( [] ))
          | LBRKT thf_tuple_list RBRKT (( thf_tuple_list ))

thf_tuple_list : thf_logic_formula                      (( [thf_logic_formula] ))
               | thf_logic_formula COMMA thf_tuple_list (( thf_logic_formula :: thf_tuple_list ))


(* TFF Formulas *)

tff_formula : tff_logic_formula  (( tff_logic_formula ))
            | tff_typed_atom     (( Atom (TFF_Typed_Atom tff_typed_atom) ))
            | tff_sequent        (( tff_sequent ))

tff_logic_formula : tff_binary_formula   (( tff_binary_formula ))
                  | tff_unitary_formula  (( tff_unitary_formula ))

tff_binary_formula : tff_binary_nonassoc (( tff_binary_nonassoc ))
                   | tff_binary_assoc    (( tff_binary_assoc ))

tff_binary_nonassoc : tff_unitary_formula binary_connective tff_unitary_formula (( Fmla (binary_connective, [tff_unitary_formula1, tff_unitary_formula2]) ))

tff_binary_assoc : tff_or_formula  (( tff_or_formula ))
                 | tff_and_formula (( tff_and_formula ))

tff_or_formula : tff_unitary_formula VLINE tff_unitary_formula      (( Fmla (Interpreted_Logic Or, [tff_unitary_formula1, tff_unitary_formula2]) ))
               | tff_or_formula VLINE tff_unitary_formula           (( Fmla (Interpreted_Logic Or, [tff_or_formula, tff_unitary_formula]) ))

tff_and_formula : tff_unitary_formula AMPERSAND tff_unitary_formula (( Fmla (Interpreted_Logic And, [tff_unitary_formula1, tff_unitary_formula2]) ))
                | tff_and_formula AMPERSAND tff_unitary_formula     (( Fmla (Interpreted_Logic And, [tff_and_formula, tff_unitary_formula]) ))

tff_unitary_formula : tff_quantified_formula           (( tff_quantified_formula ))
                    | tff_unary_formula                (( tff_unary_formula ))
                    | atomic_formula                   (( atomic_formula ))
                    | tff_conditional                  (( tff_conditional ))
                    | tff_let                          (( tff_let ))
                    | LPAREN tff_logic_formula RPAREN  (( tff_logic_formula ))

tff_quantified_formula : fol_quantifier LBRKT tff_variable_list RBRKT COLON tff_unitary_formula ((
  Quant (fol_quantifier, tff_variable_list, tff_unitary_formula)
))

tff_variable_list : tff_variable                         (( [tff_variable] ))
                  | tff_variable COMMA tff_variable_list (( tff_variable :: tff_variable_list ))

tff_variable : tff_typed_variable (( tff_typed_variable ))
             | variable_          (( (variable_, NONE) ))

tff_typed_variable : variable_ COLON tff_atomic_type (( (variable_, SOME tff_atomic_type) ))

tff_unary_formula : unary_connective tff_unitary_formula (( Fmla (unary_connective, [tff_unitary_formula]) ))
                  | fol_infix_unary                      (( fol_infix_unary ))

tff_conditional : ITE_F LPAREN tff_logic_formula COMMA tff_logic_formula COMMA tff_logic_formula RPAREN ((
  Conditional (tff_logic_formula1, tff_logic_formula2, tff_logic_formula3)
))

tff_let : LET_TF LPAREN tff_let_term_defn COMMA tff_formula RPAREN ((Let (tff_let_term_defn, tff_formula) ))
        | LET_FF LPAREN tff_let_formula_defn COMMA tff_formula RPAREN (( Let (tff_let_formula_defn, tff_formula) ))

(*FIXME here could check that fmla is of right form (TPTP BNF L210-214)*)
(*FIXME why "term" if using "Let_fmla"?*)
tff_let_term_defn : tff_quantified_formula ((
  let
    val (_, vars, fmla) = extract_quant_info tff_quantified_formula
  in [Let_fmla (hd vars, fmla)]
  end
))

(*FIXME here could check that fmla is of right form (TPTP BNF L215-217)*)
tff_let_formula_defn : tff_quantified_formula ((
  let
    val (_, vars, fmla) = extract_quant_info tff_quantified_formula
  in [Let_fmla (hd vars, fmla)]
  end
))

tff_sequent : tff_tuple GENTZEN_ARROW tff_tuple (( Sequent (tff_tuple1, tff_tuple2) ))
            | LPAREN tff_sequent RPAREN         (( tff_sequent ))

tff_tuple : LBRKT RBRKT    (( [] ))
          | LBRKT tff_tuple_list RBRKT (( tff_tuple_list ))

tff_tuple_list : tff_logic_formula COMMA tff_tuple_list (( tff_logic_formula :: tff_tuple_list ))
               | tff_logic_formula                      (( [tff_logic_formula] ))

tff_typed_atom : tff_untyped_atom COLON tff_top_level_type (( (fst tff_untyped_atom, SOME tff_top_level_type) ))
               | LPAREN tff_typed_atom RPAREN              (( tff_typed_atom ))

tff_untyped_atom : functor_       (( (functor_, NONE) ))
                 | system_functor (( (system_functor, NONE) ))

tff_top_level_type : tff_atomic_type     (( tff_atomic_type ))
                   | tff_mapping_type    (( tff_mapping_type ))
                   | tff_quantified_type (( tff_quantified_type ))

tff_quantified_type : DEP_PROD LBRKT tff_variable_list RBRKT COLON tff_monotype ((
       Fmla_type (Quant (Dep_Prod, tff_variable_list, THF_type tff_monotype))
))
                    | LPAREN tff_quantified_type RPAREN (( tff_quantified_type ))

tff_monotype : tff_atomic_type                (( tff_atomic_type ))
             | LPAREN tff_mapping_type RPAREN (( tff_mapping_type ))

tff_unitary_type : tff_atomic_type               (( tff_atomic_type ))
                 | LPAREN tff_xprod_type RPAREN  (( tff_xprod_type ))

tff_atomic_type : atomic_word   (( Atom_type atomic_word ))
                | defined_type  (( Defined_type defined_type ))
                | atomic_word LPAREN tff_type_arguments RPAREN (( Fmla_type (Fmla (Uninterpreted atomic_word, (map THF_type tff_type_arguments))) ))
                | variable_ (( Fmla_type (Pred (Interpreted_ExtraLogic Apply, [Term_Var variable_])) ))

tff_type_arguments : tff_atomic_type   (( [tff_atomic_type]  ))
                   | tff_atomic_type COMMA tff_type_arguments (( tff_atomic_type :: tff_type_arguments ))

tff_mapping_type : tff_unitary_type ARROW tff_atomic_type (( Fn_type(tff_unitary_type, tff_atomic_type) ))
                 | LPAREN tff_mapping_type RPAREN         (( tff_mapping_type ))

tff_xprod_type : tff_atomic_type TIMES tff_atomic_type (( Prod_type(tff_atomic_type1, tff_atomic_type2) ))
               | tff_xprod_type TIMES tff_atomic_type  (( Prod_type(tff_xprod_type, tff_atomic_type) ))
               | LPAREN tff_xprod_type RPAREN          (( tff_xprod_type ))


(* FOF Formulas *)

fof_formula : fof_logic_formula  (( fof_logic_formula ))
            | fof_sequent        (( fof_sequent ))

fof_logic_formula : fof_binary_formula   (( fof_binary_formula ))
                  | fof_unitary_formula  (( fof_unitary_formula ))

fof_binary_formula : fof_binary_nonassoc (( fof_binary_nonassoc ))
                   | fof_binary_assoc    (( fof_binary_assoc ))

fof_binary_nonassoc : fof_unitary_formula binary_connective fof_unitary_formula ((
  Fmla (binary_connective, [fof_unitary_formula1, fof_unitary_formula2] )
))

fof_binary_assoc : fof_or_formula  (( fof_or_formula ))
                 | fof_and_formula (( fof_and_formula ))

fof_or_formula : fof_unitary_formula VLINE fof_unitary_formula  (( Fmla (Interpreted_Logic Or, [fof_unitary_formula1, fof_unitary_formula2]) ))
               | fof_or_formula VLINE fof_unitary_formula       (( Fmla (Interpreted_Logic Or, [fof_or_formula, fof_unitary_formula]) ))

fof_and_formula : fof_unitary_formula AMPERSAND fof_unitary_formula (( Fmla (Interpreted_Logic And, [fof_unitary_formula1, fof_unitary_formula2]) ))
                | fof_and_formula AMPERSAND fof_unitary_formula     (( Fmla (Interpreted_Logic And, [fof_and_formula, fof_unitary_formula]) ))

fof_unitary_formula : fof_quantified_formula (( fof_quantified_formula ))
                    | fof_unary_formula      (( fof_unary_formula ))
                    | atomic_formula         (( atomic_formula ))
                    | LPAREN fof_logic_formula RPAREN (( fof_logic_formula ))

fof_quantified_formula : fol_quantifier LBRKT fof_variable_list RBRKT COLON fof_unitary_formula ((
  Quant (fol_quantifier, map (fn v => (v, NONE)) fof_variable_list, fof_unitary_formula)
))

fof_variable_list : variable_                          (( [variable_] ))
                  | variable_ COMMA fof_variable_list  (( variable_ :: fof_variable_list ))

fof_unary_formula : unary_connective fof_unitary_formula (( Fmla (unary_connective, [fof_unitary_formula]) ))
                  | fol_infix_unary                      (( fol_infix_unary ))

fof_sequent : fof_tuple GENTZEN_ARROW fof_tuple (( Sequent (fof_tuple1, fof_tuple2) ))
            | LPAREN fof_sequent RPAREN         (( fof_sequent ))

fof_tuple : LBRKT RBRKT                 (( [] ))
          | LBRKT fof_tuple_list RBRKT  (( fof_tuple_list ))

fof_tuple_list : fof_logic_formula                      (( [fof_logic_formula] ))
               | fof_logic_formula COMMA fof_tuple_list (( fof_logic_formula :: fof_tuple_list ))


(* CNF Formulas *)

cnf_formula : LPAREN disjunction RPAREN  (( disjunction ))
            | disjunction                (( disjunction ))

disjunction : literal                    (( literal ))
            | disjunction VLINE literal  (( Fmla (Interpreted_Logic Or, [disjunction, literal]) ))

literal : atomic_formula        (( atomic_formula ))
        | TILDE atomic_formula  (( Fmla (Interpreted_Logic Not, [atomic_formula]) ))
        | fol_infix_unary       (( fol_infix_unary ))


(* Special Formulas  *)

thf_conn_term : thf_pair_connective   (( thf_pair_connective ))
              | assoc_connective      (( assoc_connective ))
              | thf_unary_connective  (( thf_unary_connective ))

fol_infix_unary : term infix_inequality term (( Pred (infix_inequality, [term1, term2]) ))


(* Connectives - THF *)

thf_quantifier : fol_quantifier (( fol_quantifier ))
               | CARET          (( Lambda ))
               | DEP_PROD       (( Dep_Prod ))
               | DEP_SUM        (( Dep_Sum ))
               | INDEF_CHOICE   (( Epsilon ))
               | DEFIN_CHOICE   (( Iota ))

thf_pair_connective : infix_equality    (( infix_equality ))
                    | infix_inequality  (( infix_inequality ))
                    | binary_connective (( binary_connective ))

thf_unary_connective : unary_connective (( unary_connective ))
                     | OPERATOR_FORALL  (( Interpreted_Logic Op_Forall ))
                     | OPERATOR_EXISTS  (( Interpreted_Logic Op_Exists ))


(* Connectives - THF and TFF
instead of subtype_sign use token SUBTYPE
*)


(* Connectives - FOF *)

fol_quantifier : EXCLAMATION  (( Forall ))
               | QUESTION     (( Exists ))

binary_connective : IFF       (( Interpreted_Logic Iff ))
                  | IMPLIES   (( Interpreted_Logic If ))
                  | FI        (( Interpreted_Logic Fi ))
                  | XOR       (( Interpreted_Logic Xor ))
                  | NOR       (( Interpreted_Logic Nor ))
                  | NAND      (( Interpreted_Logic Nand ))

assoc_connective : VLINE      (( Interpreted_Logic Or ))
                 | AMPERSAND  (( Interpreted_Logic And ))

unary_connective : TILDE (( Interpreted_Logic Not ))


(* The sequent arrow
use token GENTZEN_ARROW
*)


(* Types for THF and TFF *)

defined_type : atomic_defined_word ((
  case atomic_defined_word of
    "$oType" => Type_Bool
  | "$o" => Type_Bool
  | "$iType" => Type_Ind
  | "$i" => Type_Ind
  | "$tType" => Type_Type
  | "$real" => Type_Real
  | "$rat" => Type_Rat
  | "$int" => Type_Int
  | thing => raise UNRECOGNISED_SYMBOL ("defined_type", thing)
))

system_type : atomic_system_word (( atomic_system_word ))


(* First-order atoms *)

atomic_formula : plain_atomic_formula   (( plain_atomic_formula ))
               | defined_atomic_formula (( defined_atomic_formula ))
               | system_atomic_formula  (( system_atomic_formula ))

plain_atomic_formula : plain_term (( Pred plain_term ))

defined_atomic_formula : defined_plain_formula (( defined_plain_formula ))
                       | defined_infix_formula (( defined_infix_formula ))

defined_plain_formula : defined_plain_term (( Pred defined_plain_term ))

(*FIXME not used*)
defined_prop : atomic_defined_word ((
  case atomic_defined_word of
    "$true"  => "$true"
  | "$false" => "$false"
  | thing => raise UNRECOGNISED_SYMBOL ("defined_prop", thing)
))

(*FIXME not used*)
defined_pred : atomic_defined_word ((
  case atomic_defined_word of
    "$distinct"  => "$distinct"
  | "$ite_f" => "$ite_f"
  | "$less" => "$less"
  | "$lesseq" => "$lesseq"
  | "$greater" => "$greater"
  | "$greatereq" => "$greatereq"
  | "$is_int" => "$is_int"
  | "$is_rat" => "$is_rat"
  | thing => raise UNRECOGNISED_SYMBOL ("defined_pred", thing)
))

defined_infix_formula : term defined_infix_pred term ((Pred (defined_infix_pred, [term1, term2])))

defined_infix_pred : infix_equality  (( infix_equality ))

infix_equality : EQUALS    (( Interpreted_Logic Equals ))

infix_inequality : NEQUALS (( Interpreted_Logic NEquals ))

system_atomic_formula : system_term  (( Pred system_term ))


(* First-order terms *)

term : function_term     (( function_term ))
     | variable_         (( Term_Var variable_ ))
     | conditional_term  (( conditional_term ))
     | let_term          (( let_term ))

function_term : plain_term    (( Term_Func plain_term ))
              | defined_term  (( defined_term ))
              | system_term   (( Term_Func system_term ))

plain_term : constant                          (( (constant, []) ))
           | functor_ LPAREN arguments RPAREN  (( (functor_, arguments) ))

constant : functor_ (( functor_ ))

functor_ : atomic_word (( Uninterpreted atomic_word ))

defined_term : defined_atom        (( defined_atom ))
             | defined_atomic_term (( defined_atomic_term ))

defined_atom : number          (( Term_Num number ))
             | DISTINCT_OBJECT (( Term_Distinct_Object DISTINCT_OBJECT ))

defined_atomic_term : defined_plain_term (( Term_Func defined_plain_term ))

defined_plain_term : defined_constant                        (( (defined_constant, []) ))
                   | defined_functor LPAREN arguments RPAREN (( (defined_functor, arguments) ))

defined_constant : defined_functor (( defined_functor ))

(*FIXME would be nicer to split these up*)
defined_functor : atomic_defined_word ((
  case atomic_defined_word of
    "$uminus" => Interpreted_ExtraLogic UMinus
  | "$sum" => Interpreted_ExtraLogic Sum
  | "$difference" => Interpreted_ExtraLogic Difference
  | "$product" => Interpreted_ExtraLogic Product
  | "$quotient" => Interpreted_ExtraLogic Quotient
  | "$quotient_e" => Interpreted_ExtraLogic Quotient_E
  | "$quotient_t" => Interpreted_ExtraLogic Quotient_T
  | "$quotient_f" => Interpreted_ExtraLogic Quotient_F
  | "$remainder_e" => Interpreted_ExtraLogic Remainder_E
  | "$remainder_t" => Interpreted_ExtraLogic Remainder_T
  | "$remainder_f" => Interpreted_ExtraLogic Remainder_F
  | "$floor" => Interpreted_ExtraLogic Floor
  | "$ceiling" => Interpreted_ExtraLogic Ceiling
  | "$truncate" => Interpreted_ExtraLogic Truncate
  | "$round" => Interpreted_ExtraLogic Round
  | "$to_int" => Interpreted_ExtraLogic To_Int
  | "$to_rat" => Interpreted_ExtraLogic To_Rat
  | "$to_real" => Interpreted_ExtraLogic To_Real

  | "$i" => TypeSymbol Type_Ind
  | "$o" => TypeSymbol Type_Bool
  | "$iType" => TypeSymbol Type_Ind
  | "$oType" => TypeSymbol Type_Bool
  | "$int" => TypeSymbol Type_Int
  | "$real" => TypeSymbol Type_Real
  | "$rat" => TypeSymbol Type_Rat
  | "$tType" => TypeSymbol Type_Type

  | "$true" => Interpreted_Logic True
  | "$false" => Interpreted_Logic False

  | "$less" => Interpreted_ExtraLogic Less
  | "$lesseq" => Interpreted_ExtraLogic LessEq
  | "$greatereq" => Interpreted_ExtraLogic GreaterEq
  | "$greater" => Interpreted_ExtraLogic Greater
  | "$evaleq" => Interpreted_ExtraLogic EvalEq

  | "$is_int" => Interpreted_ExtraLogic Is_Int
  | "$is_rat" => Interpreted_ExtraLogic Is_Rat

  | "$distinct" => Interpreted_ExtraLogic Distinct

  | thing => raise UNRECOGNISED_SYMBOL ("defined_functor", thing)
))

system_term : system_constant                         (( (system_constant, []) ))
            | system_functor LPAREN arguments RPAREN  (( (system_functor, arguments) ))

system_constant : system_functor (( system_functor ))

system_functor : atomic_system_word (( System atomic_system_word ))

variable_ : UPPER_WORD  (( UPPER_WORD ))

arguments : term                  (( [term] ))
          | term COMMA arguments  (( term :: arguments ))

conditional_term : ITE_T LPAREN tff_logic_formula COMMA term COMMA term RPAREN ((
  Term_Conditional (tff_logic_formula, term1, term2)
))


let_term : LET_FT LPAREN tff_let_formula_defn COMMA term RPAREN ((Term_Let (tff_let_formula_defn, term) ))
         | LET_TT LPAREN tff_let_term_defn COMMA term RPAREN ((Term_Let (tff_let_term_defn, term) ))


(* Formula sources
Don't currently use following non-terminals:
source, sources, dag_source, inference_record, inference_rule, parent_list,
parent_info, parent_details, internal_source, intro_type, external_source,
file_source, file_info, theory, theory_name, creator_source, creator_name.
*)


(* Useful info fields *)

optional_info : COMMA useful_info (( useful_info ))
              |                   (( [] ))

useful_info : general_list (( general_list ))

include_ : INCLUDE LPAREN file_name formula_selection RPAREN PERIOD ((
  Include (file_name, formula_selection)
))

formula_selection : COMMA LBRKT name_list RBRKT   (( name_list  ))
                  |                               (( [] ))

name_list : name COMMA name_list   (( name :: name_list ))
          | name                   (( [name] ))


(* Non-logical data *)

general_term : general_data                    (( General_Data general_data ))
             | general_data COLON general_term (( General_Term (general_data, general_term) ))
             | general_list                    (( General_List general_list ))

general_data : atomic_word       (( Atomic_Word atomic_word ))
             | general_function  (( general_function ))
             | variable_         (( V variable_ ))
             | number            (( Number number ))
             | DISTINCT_OBJECT   (( Distinct_Object DISTINCT_OBJECT ))
             | formula_data      (( formula_data ))

general_function: atomic_word LPAREN general_terms RPAREN (( Application (atomic_word, general_terms) ))

formula_data : DTHF LPAREN thf_formula RPAREN (( Formula_Data (THF, thf_formula) ))
             | DTFF LPAREN tff_formula RPAREN (( Formula_Data (TFF, tff_formula) ))
             | DFOF LPAREN fof_formula RPAREN (( Formula_Data (FOF, fof_formula) ))
             | DCNF LPAREN cnf_formula RPAREN (( Formula_Data (CNF, cnf_formula) ))
             | DFOT LPAREN term RPAREN (( Term_Data term ))

general_list : LBRKT general_terms RBRKT (( general_terms ))
             | LBRKT RBRKT               (( [] ))

general_terms : general_term COMMA general_terms (( general_term :: general_terms ))
              | general_term                     (( [general_term] ))


(* General purpose *)

name : atomic_word (( atomic_word ))
     | integer     (( integer ))

atomic_word : LOWER_WORD    (( LOWER_WORD ))
            | SINGLE_QUOTED (( SINGLE_QUOTED ))
            | THF           (( "thf" ))
            | TFF           (( "tff" ))
            | FOF           (( "fof" ))
            | CNF           (( "cnf" ))
            | INCLUDE       (( "include" ))

atomic_defined_word : DOLLAR_WORD (( DOLLAR_WORD ))

atomic_system_word : DOLLAR_DOLLAR_WORD (( DOLLAR_DOLLAR_WORD ))

integer: UNSIGNED_INTEGER (( UNSIGNED_INTEGER ))
       | SIGNED_INTEGER   (( SIGNED_INTEGER ))

number : integer          (( (Int_num, integer) ))
       | REAL             (( (Real_num, REAL) ))
       | RATIONAL         (( (Rat_num, RATIONAL) ))

file_name : SINGLE_QUOTED (( SINGLE_QUOTED ))
