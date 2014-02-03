(*  Title:      Tools/Code/code_symbol.ML
    Author:     Florian Haftmann, TU Muenchen

Data related to symbols in programs: constants, type constructors, classes,
class relations, class instances, modules.
*)

signature BASIC_CODE_SYMBOL =
sig
  datatype ('a, 'b, 'c, 'd, 'e, 'f) attr =
    Constant of 'a | Type_Constructor of 'b | Type_Class of 'c |
    Class_Relation of 'd  | Class_Instance of 'e | Module of 'f
end

signature CODE_SYMBOL =
sig
  include BASIC_CODE_SYMBOL
  type T = (string, string, class, class * class, string * class, string) attr
  structure Table: TABLE
  structure Graph: GRAPH
  val default_base: T -> string
  val default_prefix: Proof.context -> T -> string
  val quote: Proof.context -> T -> string
  val marker: T -> string
  val value: T
  val is_value: T -> bool
  val map_attr: ('a -> 'g) -> ('b -> 'h) -> ('c -> 'i) -> ('d -> 'j) -> ('e -> 'k) -> ('f -> 'l)
    -> ('a, 'b, 'c, 'd, 'e, 'f) attr -> ('g, 'h, 'i, 'j, 'k, 'l) attr
  val maps_attr: ('a -> 'g list) -> ('b -> 'h list)
    -> ('c -> 'i list) -> ('d -> 'j list) -> ('e -> 'k list) -> ('f -> 'l list)
    -> ('a, 'b, 'c, 'd, 'e, 'f) attr -> ('g, 'h, 'i, 'j, 'k, 'l) attr list
  val maps_attr': ('a -> ('m * 'g) list) -> ('b -> ('m * 'h) list)
    -> ('c -> ('m * 'i) list) -> ('d -> ('m * 'j) list) -> ('e -> ('m * 'k) list) -> ('f -> ('m * 'l) list)
    -> ('a, 'b, 'c, 'd, 'e, 'f) attr -> ('m * ('g, 'h, 'i, 'j, 'k, 'l) attr) list
  type ('a, 'b, 'c, 'd, 'e, 'f) data
  val empty_data: ('a, 'b, 'c, 'd, 'e, 'f) data
  val merge_data: ('a, 'b, 'c, 'd, 'e, 'f) data * ('a, 'b, 'c, 'd, 'e, 'f) data
    -> ('a, 'b, 'c, 'd, 'e, 'f) data
  val set_data: (string * 'a option, string * 'b option, string * 'c option,
      (class * class) * 'd option, (string * class) * 'e option, string * 'f option) attr
    -> ('a, 'b, 'c, 'd, 'e, 'f) data -> ('a, 'b, 'c, 'd, 'e, 'f) data
  val lookup_constant_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> string -> 'a option
  val lookup_type_constructor_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> string -> 'b option
  val lookup_type_class_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> class -> 'c option
  val lookup_class_relation_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> class * class -> 'd option
  val lookup_class_instance_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> string * class -> 'e option
  val lookup_module_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> string -> 'f option
  val lookup: ('a, 'a, 'a, 'a, 'a, 'a) data -> T -> 'a option
  val symbols_of: ('a, 'b, 'c, 'd, 'e, 'f) data -> T list
  val dest_module_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> (string * 'f) list
end;

structure Code_Symbol : CODE_SYMBOL =
struct

(* data for symbols *)

datatype ('a, 'b, 'c, 'd, 'e, 'f) attr =
  Constant of 'a | Type_Constructor of 'b | Type_Class of 'c | Class_Relation of 'd  | Class_Instance of 'e | Module of 'f;

type T = (string, string, class, string * class, class * class, string) attr;

fun symbol_ord (Constant c1, Constant c2) = fast_string_ord (c1, c2)
  | symbol_ord (Constant _, _) = GREATER
  | symbol_ord (_, Constant _) = LESS
  | symbol_ord (Type_Constructor tyco1, Type_Constructor tyco2) = fast_string_ord (tyco1, tyco2)
  | symbol_ord (Type_Constructor _, _) = GREATER
  | symbol_ord (_, Type_Constructor _) = LESS
  | symbol_ord (Type_Class class1, Type_Class class2) = fast_string_ord (class1, class2)
  | symbol_ord (Type_Class _, _) = GREATER
  | symbol_ord (_, Type_Class _) = LESS
  | symbol_ord (Class_Relation classrel1, Class_Relation classrel2) =
      prod_ord fast_string_ord fast_string_ord (classrel1, classrel2)
  | symbol_ord (Class_Relation _, _) = GREATER
  | symbol_ord (_, Class_Relation _) = LESS
  | symbol_ord (Class_Instance inst1, Class_Instance inst2) =
      prod_ord fast_string_ord fast_string_ord (inst1, inst2)
  | symbol_ord (Class_Instance _, _) = GREATER
  | symbol_ord (_, Class_Instance _) = LESS
  | symbol_ord (Module name1, Module name2) = fast_string_ord (name1, name2);

structure Table = Table(type key = T val ord = symbol_ord);
structure Graph = Graph(type key = T val ord = symbol_ord);

local
  val base = Name.desymbolize false o Long_Name.base_name;
  fun base_rel (x, y) = base y ^ "_" ^ base x;
in

fun default_base (Constant "") = "value"
  | default_base (Constant "==>") = "follows"
  | default_base (Constant "==") = "meta_eq"
  | default_base (Constant c) = base c
  | default_base (Type_Constructor tyco) = base tyco
  | default_base (Type_Class class) = base class
  | default_base (Class_Relation classrel) = base_rel classrel
  | default_base (Class_Instance inst) = base_rel inst;

end;

local
  fun thyname_of_type thy = #theory_name o Name_Space.the_entry (Sign.type_space thy);
  fun thyname_of_class thy = #theory_name o Name_Space.the_entry (Sign.class_space thy);
  fun thyname_of_instance thy inst = case Axclass.thynames_of_arity thy inst
   of [] => error ("No such instance: " ^ quote (fst inst ^ " :: " ^  snd inst))
    | thyname :: _ => thyname;
  fun thyname_of_const thy c = case Axclass.class_of_param thy c
   of SOME class => thyname_of_class thy class
    | NONE => (case Code.get_type_of_constr_or_abstr thy c
       of SOME (tyco, _) => thyname_of_type thy tyco
        | NONE => #theory_name (Name_Space.the_entry (Sign.const_space thy) c));
  fun prefix thy (Constant "") = "Code"
    | prefix thy (Constant c) = thyname_of_const thy c
    | prefix thy (Type_Constructor tyco) = thyname_of_type thy tyco
    | prefix thy (Type_Class class) = thyname_of_class thy class
    | prefix thy (Class_Relation (class, _)) = thyname_of_class thy class
    | prefix thy (Class_Instance inst) = thyname_of_instance thy inst;
in

fun default_prefix ctxt = prefix (Proof_Context.theory_of ctxt);

end;

val value = Constant "";
fun is_value (Constant "") = true
  | is_value _ = false;

fun quote ctxt (Constant c) =
      Library.quote (Code.string_of_const (Proof_Context.theory_of ctxt) c)
  | quote ctxt (Type_Constructor tyco) =
      "type " ^ Library.quote (Proof_Context.markup_type ctxt tyco)
  | quote ctxt (Type_Class class) =
      "class " ^ Library.quote (Proof_Context.markup_class ctxt class)
  | quote ctxt (Class_Relation (sub, super)) =
      Library.quote (Proof_Context.markup_class ctxt sub) ^ " < " ^
      Library.quote (Proof_Context.markup_class ctxt super)
  | quote ctxt (Class_Instance (tyco, class)) =
      Library.quote (Proof_Context.markup_type ctxt tyco) ^ " :: " ^
      Library.quote (Proof_Context.markup_class ctxt class);

fun marker (Constant c) = "CONST " ^ c
  | marker (Type_Constructor tyco) = "TYPE " ^ tyco
  | marker (Type_Class class) = "CLASS " ^ class
  | marker (Class_Relation (sub, super)) = "CLASSREL " ^ sub ^ " < " ^ super
  | marker (Class_Instance (tyco, class)) = "INSTANCE " ^ tyco ^ " :: " ^ class;

fun map_attr const tyco class classrel inst module (Constant x) = Constant (const x)
  | map_attr const tyco class classrel inst module (Type_Constructor x) = Type_Constructor (tyco x)
  | map_attr const tyco class classrel inst module (Type_Class x) = Type_Class (class x)
  | map_attr const tyco class classrel inst module (Class_Relation x) = Class_Relation (classrel x)
  | map_attr const tyco class classrel inst module (Class_Instance x) = Class_Instance (inst x)
  | map_attr const tyco class classrel inst module (Module x) = Module (module x);

fun maps_attr const tyco class classrel inst module (Constant x) = map Constant (const x)
  | maps_attr const tyco class classrel inst module (Type_Constructor x) = map Type_Constructor (tyco x)
  | maps_attr const tyco class classrel inst module (Type_Class x) = map Type_Class (class x)
  | maps_attr const tyco class classrel inst module (Class_Relation x) = map Class_Relation (classrel x)
  | maps_attr const tyco class classrel inst module (Class_Instance x) = map Class_Instance (inst x)
  | maps_attr const tyco class classrel inst module (Module x) = map Module (module x);

fun maps_attr' const tyco class classrel inst module (Constant x) = (map o apsnd) Constant (const x)
  | maps_attr' const tyco class classrel inst module (Type_Constructor x) = (map o apsnd) Type_Constructor (tyco x)
  | maps_attr' const tyco class classrel inst module (Type_Class x) = (map o apsnd) Type_Class (class x)
  | maps_attr' const tyco class classrel inst module (Class_Relation x) = (map o apsnd) Class_Relation (classrel x)
  | maps_attr' const tyco class classrel inst module (Class_Instance x) = (map o apsnd) Class_Instance (inst x)
  | maps_attr' const tyco class classrel inst module (Module x) = (map o apsnd) Module (module x);

datatype ('a, 'b, 'c, 'd, 'e, 'f) data =
  Data of { constant: 'a Symtab.table, type_constructor: 'b Symtab.table,
    type_class: 'c Symtab.table, class_relation: 'd Symreltab.table, class_instance: 'e Symreltab.table,
    module: 'f Symtab.table };

fun make_data constant type_constructor type_class class_relation class_instance module =
  Data { constant = constant, type_constructor = type_constructor,
    type_class = type_class, class_relation = class_relation, class_instance = class_instance, module = module };
fun dest_data (Data x) = x;
fun map_data map_constant map_type_constructor map_type_class map_class_relation map_class_instance map_module
  (Data { constant, type_constructor, type_class, class_relation, class_instance, module }) =
    Data { constant = map_constant constant, type_constructor = map_type_constructor type_constructor,
      type_class = map_type_class type_class, class_relation = map_class_relation class_relation,
        class_instance = map_class_instance class_instance, module = map_module module };

val empty_data = Data { constant = Symtab.empty, type_constructor = Symtab.empty,
  type_class = Symtab.empty, class_relation = Symreltab.empty, class_instance = Symreltab.empty, module = Symtab.empty };
fun merge_data (Data { constant = constant1, type_constructor = type_constructor1,
    type_class = type_class1, class_instance = class_instance1, class_relation = class_relation1, module = module1 },
  Data { constant = constant2, type_constructor = type_constructor2,
    type_class = type_class2, class_instance = class_instance2, class_relation = class_relation2, module = module2 }) =
  make_data (Symtab.join (K snd) (constant1, constant2))
    (Symtab.join (K snd) (type_constructor1, type_constructor2))
    (Symtab.join (K snd) (type_class1, type_class2))
    (Symreltab.join (K snd) (class_relation1, class_relation2))
    (Symreltab.join (K snd) (class_instance1, class_instance2))
    (Symtab.join (K snd) (module1, module2)); (*prefer later entries: K snd*)

fun set_sym (sym, NONE) = Symtab.delete_safe sym
  | set_sym (sym, SOME y) = Symtab.update (sym, y);
fun set_symrel (symrel, NONE) = Symreltab.delete_safe symrel
  | set_symrel (symrel, SOME y) = Symreltab.update (symrel, y);

fun set_data (Constant x) = map_data (set_sym x) I I I I I
  | set_data (Type_Constructor x) = map_data I (set_sym x) I I I I
  | set_data (Type_Class x) = map_data I I (set_sym x) I I I
  | set_data (Class_Relation x) = map_data I I I (set_symrel x) I I
  | set_data (Class_Instance x) = map_data I I I I (set_symrel x) I
  | set_data (Module x) = map_data I I I I I (set_sym x);

fun lookup_constant_data x = (Symtab.lookup o #constant o dest_data) x;
fun lookup_type_constructor_data x = (Symtab.lookup o #type_constructor o dest_data) x;
fun lookup_type_class_data x = (Symtab.lookup o #type_class o dest_data) x;
fun lookup_class_relation_data x = (Symreltab.lookup o #class_relation o dest_data) x;
fun lookup_class_instance_data x = (Symreltab.lookup o #class_instance o dest_data) x;
fun lookup_module_data x = (Symtab.lookup o #module o dest_data) x;

fun lookup data (Constant x) = lookup_constant_data data x
  | lookup data (Type_Constructor x) = lookup_type_constructor_data data x
  | lookup data (Type_Class x) = lookup_type_class_data data x
  | lookup data (Class_Relation x) = lookup_class_relation_data data x
  | lookup data (Class_Instance x) = lookup_class_instance_data data x
  | lookup data (Module x) = lookup_module_data data x;

fun symbols_of x = (map Constant o Symtab.keys o #constant o dest_data) x
  @ (map Type_Constructor o Symtab.keys o #type_constructor o dest_data) x
  @ (map Type_Class o Symtab.keys o #type_class o dest_data) x
  @ (map Class_Relation o Symreltab.keys o #class_relation o dest_data) x
  @ (map Class_Instance o Symreltab.keys o #class_instance o dest_data) x
  @ (map Module o Symtab.keys o #module o dest_data) x;

fun dest_module_data x = (Symtab.dest o #module o dest_data) x;

end;


structure Basic_Code_Symbol: BASIC_CODE_SYMBOL = Code_Symbol;
