(*  Title:      HOL/record.ML
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen

Internal interface for records.
*)


signature RECORD =
sig
  val add_record: 
    (string list * bstring) -> string option -> 
      (bstring * string) list -> theory -> theory
  val add_record_i: 
    (string list * bstring) -> (typ list * string) option -> 
      (bstring * typ) list -> theory -> theory
end;

structure Record: RECORD =
struct

val base = Sign.base_name; 

(* FIXME move to Pure/library.ML *)
fun set_minus xs [] = xs
  | set_minus xs (y::ys) = set_minus (xs \ y) ys;
(* FIXME *)

(* FIXME move to Pure/sign.ML *)
fun of_sort sg = 
  Sorts.of_sort 
    (#classrel (Type.rep_tsig (#tsig (Sign.rep_sg sg))))
    (#arities (Type.rep_tsig (#tsig (Sign.rep_sg sg))));
(* FIXME *)



(** record info **)

fun get_record thy name = 
  let val table = ThyData.get_records thy
  in
    Symtab.lookup (table, name)
  end;

fun put_record thy name info = 
  let val table = ThyData.get_records thy 
  in
    ThyData.put_records (Symtab.update ((name, info), table))
  end;

local
  fun record_infos thy None = []
    | record_infos thy (Some info) =
        case #parent info of 
            None => [info]
          | Some (_, parent) => record_infos thy (get_record thy parent) @ [info];
  fun record_parass thy info = 
    (map (map (fn (str, _) => (str, 0)) o #args) (record_infos thy (Some info))) 
    : indexname list list; 
  fun record_argss thy info = 
    map (fst o the) (tl (map #parent (record_infos thy (Some info)))) @ 
    [map TFree (#args info)];
in  
  fun record_field_names thy info = 
    flat (map (map fst o #fields) (record_infos thy (Some info)));
  fun record_field_types thy info = 
    let 
      val paras_args = map (op ~~) (record_parass thy info ~~ record_argss thy info);
      val raw_substs = map typ_subst_TVars paras_args;
      fun make_substs [] = []
        | make_substs (x::xs) = (foldr1 (op o) (x::xs)) :: make_substs xs; 
      val free_TFree = map (map (map_type_tfree (fn (str, s) => TVar((str, 0), s))));
      val raw_record_field_types = map (map snd o #fields) (record_infos thy (Some info))
    in 
      flat (ListPair.map (fn (s, ts) => map s ts) 
                         (make_substs raw_substs, free_TFree raw_record_field_types))
    end;
end;



(** abstract syntax **)

(* tuples *)

val unitT = Type ("unit",[]);
val unit = Const ("()",unitT);
fun mk_prodT (T1, T2) = Type ("*", [T1,T2]);
fun mk_Pair (t1, t2) = 
  let val T1 = fastype_of t1
      and T2 = fastype_of t2
  in Const ("Pair", [T1, T2] ---> mk_prodT (T1,T2)) $ t1 $ t2  end;

fun dest_prodT (Type ("*", [T1, T2])) = (T1, T2)
  | dest_prodT T = raise TYPE ("dest_prodT: product type expected", [T], []);

fun mk_fst pT = Const ("fst", pT --> fst (dest_prodT pT));
fun mk_snd pT = Const ("snd", pT --> snd (dest_prodT pT));

fun ap_fst t = mk_fst (fastype_of t) $ t;
fun ap_snd t = mk_snd (fastype_of t) $ t;


(* records *)

fun selT T recT = recT --> T; 
fun updateT T recT = T --> recT --> recT;
val base_free = Free o apfst base;
val make_scheme_name = "make_scheme";
val make_name = "make";
val update_suffix = "_update";
fun make_schemeC full make_schemeT = Const (full make_scheme_name, make_schemeT);
fun makeC full makeT = Const (full make_name, makeT);
fun selC s T recT = Const (s, selT T recT);
fun updateC full s T recT = Const (full (base s ^ update_suffix), updateT T recT);
fun frees xs = foldr add_typ_tfree_names (xs, []);



(** constants, definitions, axioms **)

(* constant declarations for make, selectors and update *)

fun decls make_schemeT makeT selT updateT recT current_fields =
  let val make_scheme_decl = (make_scheme_name, make_schemeT, NoSyn);
      val make_decl = (make_name, makeT, NoSyn);
      val sel_decls = map (fn (c, T) => (c, selT T recT, NoSyn)) current_fields;
      val update_decls = 
        map (fn (c, T) => (c ^ update_suffix, updateT T recT, NoSyn)) current_fields
  in 
    make_scheme_decl :: make_decl :: sel_decls @ update_decls
  end;


(* definitions for make, selectors and update *)
 
(*make*)
fun make_defs make_schemeT makeT base_frees z thy =
  let
    val sign = sign_of thy;
    val full = Sign.full_name sign;
    val make_args_scheme = list_comb (make_schemeC full make_schemeT, base_frees) $ z;
    val make_args = list_comb (makeC full makeT, base_frees); 
    val make_scheme_def = 
      mk_defpair (make_args_scheme, foldr mk_Pair (base_frees, z));
    val make_def = 
      mk_defpair (make_args, foldr mk_Pair (base_frees, unit))
  in
    make_scheme_def :: [make_def]
  end;

(*selectors*)
fun sel_defs recT r all_fields current_fullfields = 
  let 
    val prefix_len = length all_fields  - length current_fullfields;
    val sel_terms = 
        map (fn k => ap_fst o funpow k ap_snd)
            (prefix_len upto length all_fields - 1)
  in
    ListPair.map 
      (fn ((s, T), t) => mk_defpair (selC s T recT $ r, t r)) 
      (current_fullfields, sel_terms)
  end;

(*update*)
fun update_defs recT r all_fields current_fullfields thy = 
  let
    val sign = sign_of thy;
    val full = Sign.full_name sign;
    val len_all_fields = length all_fields;
    fun sel_last r = funpow len_all_fields ap_snd r;
    fun update_def_s (s, T) = 
      let val updates = map (fn (s', T') => 
        if s = s' then base_free (s, T) else selC s' T' recT $ r)
        all_fields
      in
        mk_defpair (updateC full s T recT $ base_free (s, T) $ r,
                    foldr mk_Pair (updates, sel_last r)) 
      end;
  in 
    map update_def_s current_fullfields 
  end



(** errors **)

fun check_duplicate_fields all_field_names =
  let val has_dupl = findrep all_field_names
  in
    if null has_dupl then []
      else ["Duplicate field declaration: " ^ quote (hd has_dupl) ^
            " (Double might be in ancestor)"]
  end;

fun check_parent None name thy = []
  | check_parent (Some (args, parent)) name thy = 
     let 
       val opt_info = get_record thy parent;
       val sign = sign_of thy;
       fun check_sorts [] [] = []
         | check_sorts ((str, sort)::xs) (y::ys) = 
            if of_sort sign (y, sort)
              then check_sorts xs ys 
              else ["Sort of " ^ 
                    quote (Pretty.string_of (Sign.pretty_typ sign y)) ^ 
                    " does not match parent declaration"] 
     in 
       case opt_info of 
         None => ["Parent " ^ quote parent ^" not defined"]
       | Some {args = pargs, parent = pparent, 
               fields = pfields, sign_ref = psign_ref} =>
           if (length args = length pargs) 
             then check_sorts pargs args
             else ["Mismatching arities for parent " ^ quote (base parent)] 
     end;    

fun check_duplicate_records thy full_name =
  if is_none (get_record thy full_name) then [] 
    else ["Duplicate record declaration"];

fun check_duplicate_args raw_args =
  let val has_dupl = findrep raw_args
  in
    if null has_dupl then []
      else ["Duplicate parameter: " ^ quote (hd has_dupl)]
  end;

fun check_raw_args raw_args free_vars thy = 
  let
    val free_vars_names = map fst free_vars;
    val diff_set = set_minus free_vars_names raw_args;
    val default_sort =  Type.defaultS ((#tsig o Sign.rep_sg) (sign_of thy));
    val assign_sorts = 
      map (fn x => case assoc (free_vars, x) of
                     None => (x, default_sort)
                   | Some sort => (x, sort)) raw_args
  in
    if free_vars_names subset raw_args 
      then ([], assign_sorts)
      else (["Free type variable(s): " ^ 
               (foldr1 (fn (s, s') => s ^ ", " ^ s') (map quote diff_set))],
            []) 
  end;



(** ext_record **)

fun ext_record (args, name) opt_parent current_fields thy =
  let
    val full_name = Sign.full_name (sign_of thy) name;
    val thy = thy |> Theory.add_path name;
    val sign = sign_of thy;
    val full = Sign.full_name sign;

    val current_fullfields = map (apfst full) current_fields;
    val info = {args = args, fields = current_fullfields, 
                    parent = opt_parent, sign_ref = Sign.self_ref sign};
    val thy = thy |> put_record thy full_name info;
    val all_types = record_field_types thy info; 
    val all_fields = record_field_names thy info ~~ all_types;
    val base_frees = map base_free all_fields;

    val tfrees = frees all_types;
    val zeta = variant tfrees "'z";
    val zetaT = TFree (zeta, HOLogic.termS); 
    val z = base_free ("z", zetaT);
    val recT = foldr mk_prodT (all_types, zetaT);
    val recT_unitT = foldr mk_prodT (all_types, unitT);
    val make_schemeT = (all_types @ [zetaT]) ---> recT;
    val makeT = all_types ---> recT_unitT;
    val r = base_free ("r", recT);

    val errors = check_duplicate_fields (map base (record_field_names thy info))
  in
    if not (null errors) 
      then error (cat_lines errors) else 
        thy |> Theory.add_path ".."
            |> Theory.add_tyabbrs_i [(name, tfrees @ [zeta], recT, NoSyn)]  
            |> Theory.add_path name
            |> Theory.add_consts_i (decls make_schemeT makeT selT updateT recT current_fields)
            |> Theory.add_defs_i 
                  ((make_defs make_schemeT makeT base_frees z thy) @ 
                   (sel_defs recT r all_fields current_fullfields) @
                   (update_defs recT r all_fields current_fullfields thy))
            |> Theory.add_path ".." 
  end;



(** external interfaces **)

(* add_record *)

fun add_record_aux prep_typ prep_parent (raw_args, name) raw_parent raw_fields thy =
  let
    val _ = require_thy thy "Prod" "record definitions";
    val sign = sign_of thy;
    val full_name = Sign.full_name sign name;
    val make_assocs = map (fn (a, b) => ((a, ~1), b));

    val parent = apsome (prep_parent sign) raw_parent;
    val parent_args = if_none (apsome fst parent) [];
    val parent_assoc = make_assocs (foldr (op union) ((map typ_tfrees parent_args), []));
 
    fun prepare_fields ass [] = []
      | prepare_fields ass ((name, str)::xs) = 
         let val type_of_name = prep_typ sign ass str
         in (name, type_of_name)::
              (prepare_fields (ass union (make_assocs (typ_tfrees type_of_name))) xs)
         end;
    val fields = prepare_fields (parent_assoc) raw_fields;
    val fields_types = map snd fields;
    val free_vars = foldr (op union) ((map typ_tfrees fields_types), []);

    val check_args = check_raw_args raw_args free_vars thy;
    val args = snd check_args;

    val errors = (check_parent parent name thy) @ 
                 (check_duplicate_records thy full_name) @
                 (check_duplicate_args raw_args) @
                 (fst check_args)
  in 
    if not (null errors) 
      then error (cat_lines errors)
      else ext_record (args, name) parent fields thy 
  end
  handle ERROR =>
    error ("The error(s) above occurred in record declaration " ^ quote name);


(* internalization methods *)

fun read_parent sign name =
  (case Sign.read_raw_typ (sign, K None) name of
    Type (name, Ts) => (Ts, name)
  | _ => error ("Malformed parent specification: " ^ name));

fun read_typ sign ass name = 
  Sign.read_typ (sign, curry assoc ass) name handle TYPE (msg, _, _) => error msg;
 
fun cert_typ sign ass T =
  Sign.certify_typ sign T handle TYPE (msg, _, _) => error msg;


(* add_record(_i) *)

val add_record = add_record_aux read_typ read_parent;
val add_record_i = add_record_aux cert_typ (K I);


end; 
