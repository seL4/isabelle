(*  Title:      Tools/Code/ML
    Author:     Florian Haftmann, TU Muenchen

Data related to symbols in programs: constants, type constructors, classes,
class relations, class instances, modules.
*)

signature CODE_SYMBOL =
sig
  datatype ('a, 'b, 'c, 'd, 'e, 'f) attr =
    Constant of 'a | Type_Constructor of 'b | Type_Class of 'c |
    Class_Relation of 'd  | Class_Instance of 'e | Module of 'f
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
  val lookup_constant_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> string -> 'a option
  val lookup_type_constructor_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> string -> 'b option
  val lookup_type_class_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> class -> 'c option
  val lookup_class_relation_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> class * class -> 'd option
  val lookup_class_instance_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> string * class -> 'e option
  val lookup_module_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> string -> 'f option
  val dest_constant_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> (string * 'a) list
  val dest_type_constructor_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> (string * 'b) list
  val dest_type_class_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> (class * 'c) list
  val dest_class_relation_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> ((class * class) * 'd) list
  val dest_class_instance_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> ((string * class) * 'e) list
  val dest_module_data: ('a, 'b, 'c, 'd, 'e, 'f) data -> (string * 'f) list
  val set_data: (string * 'a option, string * 'b option, string * 'c option,
      (class * class) * 'd option, (string * class) * 'e option, string * 'f option) attr
    -> ('a, 'b, 'c, 'd, 'e, 'f) data -> ('a, 'b, 'c, 'd, 'e, 'f) data
  val quote_symbol: Proof.context -> (string, string, class, string * class, class * class, string) attr -> string
end;

structure Code_Symbol : CODE_SYMBOL =
struct

(* data for symbols *)

datatype ('a, 'b, 'c, 'd, 'e, 'f) attr =
  Constant of 'a | Type_Constructor of 'b | Type_Class of 'c | Class_Relation of 'd  | Class_Instance of 'e | Module of 'f;

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

fun lookup_constant_data x = (Symtab.lookup o #constant o dest_data) x;
fun lookup_type_constructor_data x = (Symtab.lookup o #type_constructor o dest_data) x;
fun lookup_type_class_data x = (Symtab.lookup o #type_class o dest_data) x;
fun lookup_class_relation_data x = (Symreltab.lookup o #class_relation o dest_data) x;
fun lookup_class_instance_data x = (Symreltab.lookup o #class_instance o dest_data) x;
fun lookup_module_data x = (Symtab.lookup o #module o dest_data) x;

fun dest_constant_data x = (Symtab.dest o #constant o dest_data) x;
fun dest_type_constructor_data x = (Symtab.dest o #type_constructor o dest_data) x;
fun dest_type_class_data x = (Symtab.dest o #type_class o dest_data) x;
fun dest_class_relation_data x = (Symreltab.dest o #class_relation o dest_data) x;
fun dest_class_instance_data x = (Symreltab.dest o #class_instance o dest_data) x;
fun dest_module_data x = (Symtab.dest o #module o dest_data) x;

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

fun quote_symbol ctxt (Constant c) = quote (Code.string_of_const (Proof_Context.theory_of ctxt) c)
  | quote_symbol ctxt (Type_Constructor tyco) = "type " ^ quote (Proof_Context.extern_type ctxt tyco)
  | quote_symbol ctxt (Type_Class class) = "class " ^ quote (Proof_Context.extern_class ctxt class)
  | quote_symbol ctxt (Class_Relation (sub, super)) =
      quote (Proof_Context.extern_class ctxt sub) ^ " < " ^ quote (Proof_Context.extern_class ctxt super)
  | quote_symbol ctxt (Class_Instance (tyco, class)) =
      quote (Proof_Context.extern_type ctxt tyco) ^ " :: " ^ quote (Proof_Context.extern_class ctxt class);

end;
