(*  Title:      HOL/Tools/recfun_codegen.ML
    Author:     Stefan Berghofer, TU Muenchen

Code generator for recursive functions.
*)

signature RECFUN_CODEGEN =
sig
  val setup: theory -> theory
end;

structure RecfunCodegen : RECFUN_CODEGEN =
struct

open Codegen;

val const_of = dest_Const o head_of o fst o Logic.dest_equals;

structure ModuleData = TheoryDataFun
(
  type T = string Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge (K true);
);

fun add_thm_target module_name thm thy =
  let
    val (thm', _) = Code.mk_eqn thy (thm, true)
  in
    thy
    |> ModuleData.map (Symtab.update (fst (Code.const_typ_eqn thy thm'), module_name))
  end;

fun avoid_value thy [thm] =
      let val (_, T) = Code.const_typ_eqn thy thm
      in if null (Term.add_tvarsT T []) orelse (null o fst o strip_type) T
        then [thm]
        else [Code_Thingol.expand_eta thy 1 thm]
      end
  | avoid_value thy thms = thms;

fun get_equations thy defs (raw_c, T) = if raw_c = @{const_name "op ="} then ([], "") else
  let
    val c = AxClass.unoverload_const thy (raw_c, T);
    val raw_thms = Code.these_eqns thy c
      |> map_filter (fn (thm, linear) => if linear then SOME thm else NONE)
      |> filter (is_instance T o snd o const_of o prop_of);
    val module_name = case Symtab.lookup (ModuleData.get thy) c
     of SOME module_name => module_name
      | NONE => case get_defn thy defs c T
         of SOME ((_, (thyname, _)), _) => thyname
          | NONE => Codegen.thyname_of_const thy c;
  in if null raw_thms then ([], "") else
    raw_thms
    |> preprocess thy
    |> avoid_value thy
    |> Code_Thingol.canonize_thms thy
    |> rpair module_name
  end;

fun mk_suffix thy defs (s, T) = (case get_defn thy defs s T of
  SOME (_, SOME i) => " def" ^ string_of_int i | _ => "");

exception EQN of string * typ * string;

fun cycle g (xs, x : string) =
  if member (op =) xs x then xs
  else Library.foldl (cycle g) (x :: xs, flat (Graph.all_paths (fst g) (x, x)));

fun add_rec_funs thy defs dep module eqs gr =
  let
    fun dest_eq t = (fst (const_of t) ^ mk_suffix thy defs (const_of t),
      Logic.dest_equals (rename_term t));
    val eqs' = map dest_eq eqs;
    val (dname, _) :: _ = eqs';
    val (s, T) = const_of (hd eqs);

    fun mk_fundef module fname first [] gr = ([], gr)
      | mk_fundef module fname first ((fname' : string, (lhs, rhs)) :: xs) gr =
      let
        val (pl, gr1) = invoke_codegen thy defs dname module false lhs gr;
        val (pr, gr2) = invoke_codegen thy defs dname module false rhs gr1;
        val (rest, gr3) = mk_fundef module fname' false xs gr2 ;
        val (ty, gr4) = invoke_tycodegen thy defs dname module false T gr3;
        val num_args = (length o snd o strip_comb) lhs;
        val prfx = if fname = fname' then "  |"
          else if not first then "and"
          else if num_args = 0 then "val"
          else "fun";
        val pl' = Pretty.breaks (str prfx
          :: (if num_args = 0 then [pl, str ":", ty] else [pl]));
      in
        (Pretty.blk (4, pl'
           @ [str " =", Pretty.brk 1, pr]) :: rest, gr4)
      end;

    fun put_code module fundef = map_node dname
      (K (SOME (EQN ("", dummyT, dname)), module, string_of (Pretty.blk (0,
      separate Pretty.fbrk fundef @ [str ";"])) ^ "\n\n"));

  in
    (case try (get_node gr) dname of
       NONE =>
         let
           val gr1 = add_edge (dname, dep)
             (new_node (dname, (SOME (EQN (s, T, "")), module, "")) gr);
           val (fundef, gr2) = mk_fundef module "" true eqs' gr1 ;
           val xs = cycle gr2 ([], dname);
           val cs = map (fn x => case get_node gr2 x of
               (SOME (EQN (s, T, _)), _, _) => (s, T)
             | _ => error ("RecfunCodegen: illegal cyclic dependencies:\n" ^
                implode (separate ", " xs))) xs
         in (case xs of
             [_] => (module, put_code module fundef gr2)
           | _ =>
             if not (dep mem xs) then
               let
                 val thmss as (_, thyname) :: _ = map (get_equations thy defs) cs;
                 val module' = if_library thyname module;
                 val eqs'' = map (dest_eq o prop_of) (List.concat (map fst thmss));
                 val (fundef', gr3) = mk_fundef module' "" true eqs''
                   (add_edge (dname, dep)
                     (List.foldr (uncurry new_node) (del_nodes xs gr2)
                       (map (fn k =>
                         (k, (SOME (EQN ("", dummyT, dname)), module', ""))) xs)))
               in (module', put_code module' fundef' gr3) end
             else (module, gr2))
         end
     | SOME (SOME (EQN (_, _, s)), module', _) =>
         (module', if s = "" then
            if dname = dep then gr else add_edge (dname, dep) gr
          else if s = dep then gr else add_edge (s, dep) gr))
  end;

fun recfun_codegen thy defs dep module brack t gr = (case strip_comb t of
    (Const (p as (s, T)), ts) => (case (get_equations thy defs p, get_assoc_code thy (s, T)) of
       (([], _), _) => NONE
     | (_, SOME _) => NONE
     | ((eqns, thyname), NONE) =>
        let
          val module' = if_library thyname module;
          val (ps, gr') = fold_map
            (invoke_codegen thy defs dep module true) ts gr;
          val suffix = mk_suffix thy defs p;
          val (module'', gr'') =
            add_rec_funs thy defs dep module' (map prop_of eqns) gr';
          val (fname, gr''') = mk_const_id module'' (s ^ suffix) gr''
        in
          SOME (mk_app brack (str (mk_qual_id module fname)) ps, gr''')
        end)
  | _ => NONE);

val setup = 
  add_codegen "recfun" recfun_codegen
  #> Code.set_code_target_attr add_thm_target;

end;
