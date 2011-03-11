(*  Title:      HOL/Tools/Quickcheck/quickcheck_common.ML
    Author:     Florian Haftmann, Lukas Bulwahn, TU Muenchen

Common functions for quickcheck's generators

*)

signature QUICKCHECK_COMMON =
sig
  val perhaps_constrain: theory -> (typ * sort) list -> (string * sort) list
    -> (string * sort -> string * sort) option
  val ensure_sort_datatype:
    sort * (Datatype.config -> Datatype.descr -> (string * sort) list -> string list -> string ->
      string list * string list -> typ list * typ list -> theory -> theory)
    -> Datatype.config -> string list -> theory -> theory
  val post_process_term : term -> term
end;

structure Quickcheck_Common : QUICKCHECK_COMMON =
struct

(** ensuring sort constraints **)

fun perhaps_constrain thy insts raw_vs =
  let
    fun meet (T, sort) = Sorts.meet_sort (Sign.classes_of thy) 
      (Logic.varifyT_global T, sort);
    val vtab = Vartab.empty
      |> fold (fn (v, sort) => Vartab.update ((v, 0), sort)) raw_vs
      |> fold meet insts;
  in SOME (fn (v, _) => (v, (the o Vartab.lookup vtab) (v, 0)))
  end handle Sorts.CLASS_ERROR _ => NONE;

fun ensure_sort_datatype (sort, instantiate_datatype) config raw_tycos thy =
  let
    val algebra = Sign.classes_of thy;
    val (descr, raw_vs, tycos, prfx, (names, auxnames), raw_TUs) =
      Datatype.the_descr thy raw_tycos;
    val typerep_vs = (map o apsnd)
      (curry (Sorts.inter_sort algebra) @{sort typerep}) raw_vs;
    val sort_insts = (map (rpair sort) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr typerep_vs
        { atyp = single, dtyp = (K o K o K) [] });
    val term_of_insts = (map (rpair @{sort term_of}) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr typerep_vs
        { atyp = K [], dtyp = K o K });
    val has_inst = exists (fn tyco =>
      can (Sorts.mg_domain algebra tyco) sort) tycos;
  in if has_inst then thy
    else case perhaps_constrain thy (sort_insts @ term_of_insts) typerep_vs
     of SOME constrain => instantiate_datatype config descr
          (map constrain typerep_vs) tycos prfx (names, auxnames)
            ((pairself o map o map_atyps) (fn TFree v => TFree (constrain v)) raw_TUs) thy
      | NONE => thy
  end;
  
(** post-processing of function terms **)

fun dest_fun_upd (Const (@{const_name fun_upd}, _) $ t0 $ t1 $ t2) = (t0, (t1, t2))
  | dest_fun_upd t = raise TERM ("dest_fun_upd", [t])

fun mk_fun_upd T1 T2 (t1, t2) t = 
  Const (@{const_name fun_upd}, (T1 --> T2) --> T1 --> T2 --> T1 --> T2) $ t $ t1 $ t2

fun dest_fun_upds t =
  case try dest_fun_upd t of
    NONE =>
      (case t of
        Abs (_, _, _) => ([], t) 
      | _ => raise TERM ("dest_fun_upds", [t]))
  | SOME (t0, (t1, t2)) => apfst (cons (t1, t2)) (dest_fun_upds t0)

fun make_fun_upds T1 T2 (tps, t) = fold_rev (mk_fun_upd T1 T2) tps t

fun make_set T1 [] = Const (@{const_abbrev Set.empty}, T1 --> @{typ bool})
  | make_set T1 ((_, @{const False}) :: tps) = make_set T1 tps
  | make_set T1 ((t1, @{const True}) :: tps) =
    Const (@{const_name insert}, T1 --> (T1 --> @{typ bool}) --> T1 --> @{typ bool})
      $ t1 $ (make_set T1 tps)
  | make_set T1 ((_, t) :: tps) = raise TERM ("make_set", [t])

fun make_coset T [] = Const (@{const_abbrev UNIV}, T --> @{typ bool})
  | make_coset T tps = 
    let
      val U = T --> @{typ bool}
      fun invert @{const False} = @{const True}
        | invert @{const True} = @{const False}
    in
      Const (@{const_name "Groups.minus_class.minus"}, U --> U --> U)
        $ Const (@{const_abbrev UNIV}, U) $ make_set T (map (apsnd invert) tps)
    end

fun make_map T1 T2 [] = Const (@{const_abbrev Map.empty}, T1 --> T2)
  | make_map T1 T2 ((_, Const (@{const_name None}, _)) :: tps) = make_map T1 T2 tps
  | make_map T1 T2 ((t1, t2) :: tps) = mk_fun_upd T1 T2 (t1, t2) (make_map T1 T2 tps)
  
fun post_process_term t =
  let
    fun map_Abs f t =
      case t of Abs (x, T, t') => Abs (x, T, f t') | _ => raise TERM ("map_Abs", [t]) 
    fun process_args t = case strip_comb t of
      (c as Const (_, _), ts) => list_comb (c, map post_process_term ts) 
  in
    case fastype_of t of
      Type (@{type_name fun}, [T1, T2]) =>
        (case try dest_fun_upds t of
          SOME (tps, t) =>
            (map (pairself post_process_term) tps, map_Abs post_process_term t)
            |> (case T2 of
              @{typ bool} => 
                (case t of
                   Abs(_, _, @{const True}) => fst #> rev #> make_set T1
                 | Abs(_, _, @{const False}) => fst #> rev #> make_coset T1
                 | Abs(_, _, Const (@{const_name undefined}, _)) => fst #> rev #> make_set T1
                 | _ => raise TERM ("post_process_term", [t]))
            | Type (@{type_name option}, _) =>
                (case t of
                  Abs(_, _, Const(@{const_name None}, _)) => fst #> make_map T1 T2
                | Abs(_, _, Const (@{const_name undefined}, _)) => fst #> make_map T1 T2
                | _ => make_fun_upds T1 T2) 
            | _ => make_fun_upds T1 T2)
        | NONE => process_args t)
    | _ => process_args t
  end
  

end;
