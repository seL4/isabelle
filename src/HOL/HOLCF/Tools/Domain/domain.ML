(*  Title:      HOL/HOLCF/Tools/Domain/domain.ML
    Author:     David von Oheimb
    Author:     Brian Huffman

Theory extender for domain command, including theory syntax.
*)

signature DOMAIN =
sig
  val add_domain_cmd:
      ((string * string option) list * binding * mixfix *
       (binding * (bool * binding option * string) list * mixfix) list) list
      -> theory -> theory

  val add_domain:
      ((string * sort) list * binding * mixfix *
       (binding * (bool * binding option * typ) list * mixfix) list) list
      -> theory -> theory

  val add_new_domain_cmd:
      ((string * string option) list * binding * mixfix *
       (binding * (bool * binding option * string) list * mixfix) list) list
      -> theory -> theory

  val add_new_domain:
      ((string * sort) list * binding * mixfix *
       (binding * (bool * binding option * typ) list * mixfix) list) list
      -> theory -> theory
end

structure Domain : DOMAIN =
struct

open HOLCF_Library

fun first  (x,_,_) = x
fun second (_,x,_) = x

(* ----- calls for building new thy and thms -------------------------------- *)

type info =
     Domain_Take_Proofs.iso_info list * Domain_Take_Proofs.take_induct_info

fun add_arity ((b, sorts, mx), sort) thy : theory =
  thy
  |> Sign.add_types_global [(b, length sorts, mx)]
  |> AxClass.axiomatize_arity (Sign.full_name thy b, sorts, sort)

fun gen_add_domain
    (prep_sort : theory -> 'a -> sort)
    (prep_typ : theory -> (string * sort) list -> 'b -> typ)
    (add_isos : (binding * mixfix * (typ * typ)) list -> theory -> info * theory)
    (arg_sort : bool -> sort)
    (raw_specs : ((string * 'a) list * binding * mixfix *
               (binding * (bool * binding option * 'b) list * mixfix) list) list)
    (thy : theory) =
  let
    val dtnvs : (binding * typ list * mixfix) list =
      let
        fun prep_tvar (a, s) = TFree (a, prep_sort thy s)
      in
        map (fn (vs, dbind, mx, _) =>
                (dbind, map prep_tvar vs, mx)) raw_specs
      end

    fun thy_arity (dbind, tvars, mx) =
      ((dbind, map (snd o dest_TFree) tvars, mx), arg_sort false)

    (* this theory is used just for parsing and error checking *)
    val tmp_thy = thy
      |> Theory.copy
      |> fold (add_arity o thy_arity) dtnvs

    val dbinds : binding list =
        map (fn (_,dbind,_,_) => dbind) raw_specs
    val raw_rhss :
        (binding * (bool * binding option * 'b) list * mixfix) list list =
        map (fn (_,_,_,cons) => cons) raw_specs
    val dtnvs' : (string * typ list) list =
        map (fn (dbind, vs, _) => (Sign.full_name thy dbind, vs)) dtnvs

    val all_cons = map (Binding.name_of o first) (flat raw_rhss)
    val _ =
      case duplicates (op =) all_cons of 
        [] => false | dups => error ("Duplicate constructors: " 
                                      ^ commas_quote dups)
    val all_sels =
      (map Binding.name_of o map_filter second o maps second) (flat raw_rhss)
    val _ =
      case duplicates (op =) all_sels of
        [] => false | dups => error("Duplicate selectors: "^commas_quote dups)

    fun test_dupl_tvars s =
      case duplicates (op =) (map(fst o dest_TFree)s) of
        [] => false | dups => error("Duplicate type arguments: " 
                                    ^commas_quote dups)
    val _ = exists test_dupl_tvars (map snd dtnvs')

    val sorts : (string * sort) list =
      let val all_sorts = map (map dest_TFree o snd) dtnvs'
      in
        case distinct (eq_set (op =)) all_sorts of
          [sorts] => sorts
        | _ => error "Mutually recursive domains must have same type parameters"
      end

    (* a lazy argument may have an unpointed type *)
    (* unless the argument has a selector function *)
    fun check_pcpo (lazy, sel, T) =
      let val sort = arg_sort (lazy andalso is_none sel) in
        if Sign.of_sort tmp_thy (T, sort) then ()
        else error ("Constructor argument type is not of sort " ^
                    Syntax.string_of_sort_global tmp_thy sort ^ ": " ^
                    Syntax.string_of_typ_global tmp_thy T)
      end

    (* test for free type variables, illegal sort constraints on rhs,
       non-pcpo-types and invalid use of recursive type
       replace sorts in type variables on rhs *)
    val rec_tab = Domain_Take_Proofs.get_rec_tab thy
    fun check_rec _ (T as TFree (v,_))  =
        if AList.defined (op =) sorts v then T
        else error ("Free type variable " ^ quote v ^ " on rhs.")
      | check_rec no_rec (T as Type (s, Ts)) =
        (case AList.lookup (op =) dtnvs' s of
          NONE =>
            let val no_rec' =
                  if no_rec = NONE then
                    if Symtab.defined rec_tab s then NONE else SOME s
                  else no_rec
            in Type (s, map (check_rec no_rec') Ts) end
        | SOME typevars =>
          if typevars <> Ts
          then error ("Recursion of type " ^ 
                      quote (Syntax.string_of_typ_global tmp_thy T) ^ 
                      " with different arguments")
          else (case no_rec of
                  NONE => T
                | SOME c =>
                  error ("Illegal indirect recursion of type " ^ 
                         quote (Syntax.string_of_typ_global tmp_thy T) ^
                         " under type constructor " ^ quote c)))
      | check_rec _ (TVar _) = error "extender:check_rec"

    fun prep_arg (lazy, sel, raw_T) =
      let
        val T = prep_typ tmp_thy sorts raw_T
        val _ = check_rec NONE T
        val _ = check_pcpo (lazy, sel, T)
      in (lazy, sel, T) end
    fun prep_con (b, args, mx) = (b, map prep_arg args, mx)
    fun prep_rhs cons = map prep_con cons
    val rhss : (binding * (bool * binding option * typ) list * mixfix) list list =
        map prep_rhs raw_rhss

    fun mk_arg_typ (lazy, _, T) = if lazy then mk_upT T else T
    fun mk_con_typ (_, args, _) =
        if null args then oneT else foldr1 mk_sprodT (map mk_arg_typ args)
    fun mk_rhs_typ cons = foldr1 mk_ssumT (map mk_con_typ cons)

    val absTs : typ list = map Type dtnvs'
    val repTs : typ list = map mk_rhs_typ rhss

    val iso_spec : (binding * mixfix * (typ * typ)) list =
        map (fn ((dbind, _, mx), eq) => (dbind, mx, eq))
          (dtnvs ~~ (absTs ~~ repTs))

    val ((iso_infos, take_info), thy) = add_isos iso_spec thy

    val (constr_infos, thy) =
        thy
          |> fold_map (fn ((dbind, cons), info) =>
                Domain_Constructors.add_domain_constructors dbind cons info)
             (dbinds ~~ rhss ~~ iso_infos)

    val (_, thy) =
        Domain_Induction.comp_theorems
          dbinds take_info constr_infos thy
  in
    thy
  end

fun define_isos (spec : (binding * mixfix * (typ * typ)) list) =
  let
    fun prep (dbind, mx, (lhsT, rhsT)) =
      let val (_, vs) = dest_Type lhsT
      in (map (fst o dest_TFree) vs, dbind, mx, rhsT, NONE) end
  in
    Domain_Isomorphism.domain_isomorphism (map prep spec)
  end

fun pcpo_arg lazy = if lazy then @{sort cpo} else @{sort pcpo}
fun rep_arg lazy = if lazy then @{sort predomain} else @{sort "domain"}

fun read_sort thy (SOME s) = Syntax.read_sort_global thy s
  | read_sort thy NONE = Sign.defaultS thy

(* Adapted from src/HOL/Tools/Datatype/datatype_data.ML *)
fun read_typ thy sorts str =
  let
    val ctxt = Proof_Context.init_global thy
      |> fold (Variable.declare_typ o TFree) sorts
  in Syntax.read_typ ctxt str end

fun cert_typ sign sorts raw_T =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T)
      handle TYPE (msg, _, _) => error msg
    val sorts' = Term.add_tfreesT T sorts
    val _ =
      case duplicates (op =) (map fst sorts') of
        [] => ()
      | dups => error ("Inconsistent sort constraints for " ^ commas dups)
  in T end

val add_domain =
    gen_add_domain (K I) cert_typ Domain_Axioms.add_axioms pcpo_arg

val add_new_domain =
    gen_add_domain (K I) cert_typ define_isos rep_arg

val add_domain_cmd =
    gen_add_domain read_sort read_typ Domain_Axioms.add_axioms pcpo_arg

val add_new_domain_cmd =
    gen_add_domain read_sort read_typ define_isos rep_arg


(** outer syntax **)

val dest_decl : (bool * binding option * string) parser =
  Parse.$$$ "(" |-- Scan.optional (Parse.$$$ "lazy" >> K true) false --
    (Parse.binding >> SOME) -- (Parse.$$$ "::" |-- Parse.typ)  --| Parse.$$$ ")" >> Parse.triple1
    || Parse.$$$ "(" |-- Parse.$$$ "lazy" |-- Parse.typ --| Parse.$$$ ")"
    >> (fn t => (true,NONE,t))
    || Parse.typ >> (fn t => (false,NONE,t))

val cons_decl =
  Parse.binding -- Scan.repeat dest_decl -- Parse.opt_mixfix

val domain_decl =
  (Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix) --
    (Parse.$$$ "=" |-- Parse.enum1 "|" cons_decl)

val domains_decl =
  Scan.optional (Parse.$$$ "(" |-- (Parse.$$$ "unsafe" >> K true) --| Parse.$$$ ")") false --
    Parse.and_list1 domain_decl

fun mk_domain
    (unsafe : bool,
     doms : ((((string * string option) list * binding) * mixfix) *
             ((binding * (bool * binding option * string) list) * mixfix) list) list ) =
  let
    val specs : ((string * string option) list * binding * mixfix *
                 (binding * (bool * binding option * string) list * mixfix) list) list =
        map (fn (((vs, t), mx), cons) =>
                (vs, t, mx, map (fn ((c, ds), mx) => (c, ds, mx)) cons)) doms
  in
    if unsafe
    then add_domain_cmd specs
    else add_new_domain_cmd specs
  end

val _ =
  Outer_Syntax.command "domain" "define recursive domains (HOLCF)"
    Keyword.thy_decl (domains_decl >> (Toplevel.theory o mk_domain))

end
