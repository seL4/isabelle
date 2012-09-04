(*  Title:      HOL/Codatatype/Tools/bnf_fp_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugar for constructing LFPs and GFPs.
*)

signature BNF_FP_SUGAR =
sig
end;

structure BNF_FP_Sugar : BNF_FP_SUGAR =
struct

open BNF_Util
open BNF_Wrap
open BNF_FP_Util
open BNF_LFP
open BNF_GFP

fun cannot_merge_types () = error "Mutually recursive (co)datatypes must have same type parameters";

fun merge_type_arg_constrained ctxt (T, c) (T', c') =
  if T = T' then
    (case (c, c') of
      (_, NONE) => (T, c)
    | (NONE, _) => (T, c')
    | _ =>
      if c = c' then
        (T, c)
      else
        error ("Inconsistent sort constraints for type variable " ^
          quote (Syntax.string_of_typ ctxt T)))
  else
    cannot_merge_types ();

fun merge_type_args_constrained ctxt (cAs, cAs') =
  if length cAs = length cAs' then map2 (merge_type_arg_constrained ctxt) cAs cAs'
  else cannot_merge_types ();

fun type_args_constrained_of_spec (((cAs, _), _), _) = cAs;
fun type_name_of_spec (((_, b), _), _) = b;
fun mixfix_of_spec ((_, mx), _) = mx;
fun ctr_specs_of_spec (_, ctr_specs) = ctr_specs;

fun disc_of_ctr_spec (((disc, _), _), _) = disc;
fun ctr_of_ctr_spec (((_, ctr), _), _) = ctr;
fun args_of_ctr_spec ((_, args), _) = args;
fun mixfix_of_ctr_spec (_, mx) = mx;

val mk_prod_sum = mk_sumTN o map HOLogic.mk_tupleT;

val lfp_info = bnf_lfp;
val gfp_info = bnf_gfp;

fun prepare_data prepare_typ construct specs lthy =
  let
    val constrained_passiveAs =
      map (map (apfst (prepare_typ lthy)) o type_args_constrained_of_spec) specs
      |> Library.foldr1 (merge_type_args_constrained lthy);
    val passiveAs = map fst constrained_passiveAs;

    val _ = (case duplicates (op =) passiveAs of [] => ()
      | T :: _ => error ("Duplicate type parameter " ^ quote (Syntax.string_of_typ lthy T)));

    (* TODO: check that no type variables occur in the rhss that's not in the lhss *)
    (* TODO: use sort constraints on type args *)

    val N = length specs;

    val bs = map type_name_of_spec specs;
    val mixfixes = map mixfix_of_spec specs;

    val _ = (case duplicates Binding.eq_name bs of [] => ()
      | b :: _ => error ("Duplicate type name declaration " ^ quote (Binding.name_of b)));

    val ctr_specss = map ctr_specs_of_spec specs;

    val disc_namess = map (map disc_of_ctr_spec) ctr_specss;
    val raw_ctr_namess = map (map ctr_of_ctr_spec) ctr_specss;
    val ctr_argsss = map (map args_of_ctr_spec) ctr_specss;
    val ctr_mixfixess = map (map mixfix_of_ctr_spec) ctr_specss;

    val sel_namesss = map (map (map fst)) ctr_argsss;
    val ctr_Tsss = map (map (map (prepare_typ lthy o snd))) ctr_argsss;

    val (activeAs, _) = lthy |> mk_TFrees N;

    val eqs = map2 (fn TFree A => fn Tss => (A, mk_prod_sum Tss)) activeAs ctr_Tsss;

    val lthy' = fp_bnf construct bs eqs lthy;

    fun wrap_type ((b, disc_names), sel_namess) lthy =
      let
        val ctrs = [];
        val caseof = @{term True};
        val tacss = [];
      in
        wrap tacss ((ctrs, caseof), (disc_names, sel_namess)) lthy
      end;
  in
    lthy' |> fold wrap_type (bs ~~ disc_namess ~~ sel_namesss)
  end;

val data_cmd = prepare_data Syntax.read_typ;

val parse_opt_binding_colon = Scan.optional (Parse.binding --| Parse.$$$ ":") no_name

val parse_ctr_arg =
  Parse.$$$ "(" |-- parse_opt_binding_colon -- Parse.typ --| Parse.$$$ ")" ||
  (Parse.typ >> pair no_name);

val parse_single_spec =
  Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix --
  (@{keyword "="} |-- Parse.enum1 "|" (parse_opt_binding_colon -- Parse.binding --
    Scan.repeat parse_ctr_arg -- Parse.opt_mixfix));

val _ =
  Outer_Syntax.local_theory @{command_spec "data"} "define BNF-based inductive datatypes"
    (Parse.and_list1 parse_single_spec >> data_cmd lfp_info);

val _ =
  Outer_Syntax.local_theory @{command_spec "codata"} "define BNF-based coinductive datatypes"
    (Parse.and_list1 parse_single_spec >> data_cmd gfp_info);

end;
