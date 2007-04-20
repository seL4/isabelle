(*  Title:      Pure/Tools/codegen_consts.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Identifying constants by name plus normalized type instantantiation schemes.
Convenient data structures for constants.  Auxiliary.
*)

signature CODEGEN_CONSTS =
sig
  type const = string * string option (* constant name, possibly instance *)
  val const_ord: const * const -> order
  val eq_const: const * const -> bool
  structure Consttab: TABLE
  val const_of_cexpr: theory -> string * typ -> const
  val string_of_typ: theory -> typ -> string
  val string_of_const: theory -> const -> string
  val read_const: theory -> string -> const
  val read_const_exprs: theory -> (const list -> const list)
    -> string list -> const list

  val co_of_const: theory -> const
    -> string * ((string * sort) list * (string * typ list))
  val co_of_const': theory -> const
    -> (string * ((string * sort) list * (string * typ list))) option
  val cos_of_consts: theory -> const list
    -> string * ((string * sort) list * (string * typ list) list)
  val const_of_co: theory -> string -> (string * sort) list
    -> string * typ list -> const
  val consts_of_cos: theory -> string -> (string * sort) list
    -> (string * typ list) list -> const list

  val typargs: theory -> string * typ -> typ list
  val typ_sort_inst: Sorts.algebra -> typ * sort
    -> sort Vartab.table -> sort Vartab.table
end;

structure CodegenConsts: CODEGEN_CONSTS =
struct


(* basic data structures *)

type const = string * string option;
val const_ord = prod_ord fast_string_ord (option_ord string_ord);
val eq_const = is_equal o const_ord;

structure Consttab =
  TableFun(
    type key = const;
    val ord = const_ord;
  );

fun string_of_typ thy = setmp show_sorts true (Sign.string_of_typ thy);


(* conversion between constant expressions and constants *)

fun const_of_cexpr thy (c_ty as (c, _)) =
  case AxClass.class_of_param thy c
   of SOME class => (case Sign.const_typargs thy c_ty
       of [Type (tyco, _)] => if can (Sorts.mg_domain (Sign.classes_of thy) tyco) [class]
              then (c, SOME tyco)
              else (c, NONE)
        | [_] => (c, NONE))
    | NONE => (c, NONE);

fun string_of_const thy (c, NONE) = Sign.extern_const thy c
  | string_of_const thy (c, SOME tyco) = Sign.extern_const thy c
      ^ " " ^ enclose "[" "]" (Sign.extern_type thy tyco);


(* reading constants as terms and wildcards pattern *)

fun read_const thy raw_t =
  let
    val t = Sign.read_term thy raw_t;
  in case try dest_Const t
   of SOME c_ty => const_of_cexpr thy c_ty
    | NONE => error ("Not a constant: " ^ Sign.string_of_term thy t)
  end;

local

fun consts_of thy some_thyname =
  let
    val this_thy = Option.map theory some_thyname |> the_default thy;
    val cs = Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
      ((snd o #constants o Consts.dest o #consts o Sign.rep_sg) this_thy) [];
    fun classop c = case AxClass.class_of_param thy c
     of NONE => [(c, NONE)]
      | SOME class => Symtab.fold
          (fn (tyco, classes) => if AList.defined (op =) classes class
            then cons (c, SOME tyco) else I)
          ((#arities o Sorts.rep_algebra o Sign.classes_of) this_thy)
          [(c, NONE)];
    val consts = maps classop cs;
    fun test_instance thy (class, tyco) =
      can (Sorts.mg_domain (Sign.classes_of thy) tyco) [class]
    fun belongs_here thyname (c, NONE) =
          not (exists (fn thy' => Sign.declared_const thy' c) (Theory.parents_of this_thy))
      | belongs_here thyname (c, SOME tyco) =
          let
            val SOME class = AxClass.class_of_param thy c
          in not (exists (fn thy' => test_instance thy' (class, tyco))
            (Theory.parents_of this_thy))
          end;
  in case some_thyname
   of NONE => consts
    | SOME thyname => filter (belongs_here thyname) consts
  end;

fun read_const_expr thy "*" = ([], consts_of thy NONE)
  | read_const_expr thy s = if String.isSuffix ".*" s
      then ([], consts_of thy (SOME (unsuffix ".*" s)))
      else ([read_const thy s], []);

in

fun read_const_exprs thy select =
  (op @) o apsnd select o pairself flat o split_list o map (read_const_expr thy);

end; (*local*)

(* conversion between constants, constant expressions and datatype constructors *)

fun const_of_co thy tyco vs (co, tys) =
  const_of_cexpr thy (co, tys ---> Type (tyco, map TFree vs));

fun consts_of_cos thy tyco vs cos =
  let
    val dty = Type (tyco, map TFree vs);
    fun mk_co (co, tys) = const_of_cexpr thy (co, tys ---> dty);
  in map mk_co cos end;

local

exception BAD of string;

fun mg_typ_of_const thy (c, NONE) = Sign.the_const_type thy c
  | mg_typ_of_const thy (c, SOME tyco) =
      let
        val SOME class = AxClass.class_of_param thy c;
        val ty = Sign.the_const_type thy c;
          (*an approximation*)
        val sorts = Sorts.mg_domain (Sign.classes_of thy) tyco [class]
          handle CLASS_ERROR => raise BAD ("No such instance: " ^ tyco ^ " :: " ^ class
            ^ ",\nrequired for overloaded constant " ^ c);
        val vs = Name.invents Name.context "'a" (length sorts);
      in map_atyps (K (Type (tyco, map (fn v => TVar ((v, 0), [])) vs))) ty end;

fun gen_co_of_const thy const =
  let
    val (c, _) = const;
    val ty = (Logic.unvarifyT o mg_typ_of_const thy) const;
    fun err () = raise BAD
     ("Illegal type for datatype constructor: " ^ string_of_typ thy ty);
    val (tys, ty') = strip_type ty;
    val (tyco, vs) = ((apsnd o map) dest_TFree o dest_Type) ty'
      handle TYPE _ => err ();
    val sorts = if has_duplicates (eq_fst op =) vs then err ()
      else map snd vs;
    val vs_names = Name.invent_list [] "'a" (length vs);
    val vs_map = map fst vs ~~ vs_names;
    val vs' = vs_names ~~ sorts;
    val tys' = (map o map_type_tfree) (fn (v, sort) =>
      (TFree ((the o AList.lookup (op =) vs_map) v, sort))) tys
      handle Option => err ();
  in (tyco, (vs', (c, tys'))) end;

in

fun co_of_const thy const = gen_co_of_const thy const handle BAD msg => error msg;
fun co_of_const' thy const = SOME (gen_co_of_const thy const) handle BAD msg => NONE;

end;

fun cos_of_consts thy consts =
  let
    val raw_cos  = map (co_of_const thy) consts;
    val (tyco, (vs_names, sorts_cos)) = if (length o distinct (eq_fst op =)) raw_cos = 1
      then ((fst o hd) raw_cos, ((map fst o fst o snd o hd) raw_cos,
        map ((apfst o map) snd o snd) raw_cos))
      else error ("Term constructors not referring to the same type: "
        ^ commas (map (string_of_const thy) consts));
    val sorts = foldr1 ((uncurry o map2 o curry o Sorts.inter_sort) (Sign.classes_of thy))
      (map fst sorts_cos);
    val cos = map snd sorts_cos;
    val vs = vs_names ~~ sorts;
  in (tyco, (vs, cos)) end;


(* dictionary values *)

fun typargs thy (c_ty as (c, ty)) =
  let
    val opt_class = AxClass.class_of_param thy c;
    val tys = Sign.const_typargs thy (c, ty);
  in case (opt_class, tys)
   of (SOME class, ty as [Type (tyco, tys')]) =>
        if can (Sorts.mg_domain (Sign.classes_of thy) tyco) [class]
        then tys' else ty
    | _ => tys
  end;

fun typ_sort_inst algebra =
  let
    val inters = Sorts.inter_sort algebra;
    fun match _ [] = I
      | match (TVar (v, S)) S' = Vartab.map_default (v, []) (fn S'' => inters (S, inters (S', S'')))
      | match (Type (a, Ts)) S =
          fold2 match Ts (Sorts.mg_domain algebra a S)
  in uncurry match end;

end;
