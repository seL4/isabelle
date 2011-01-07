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

val const_of = dest_Const o head_of o fst o Logic.dest_equals;

structure ModuleData = Theory_Data
(
  type T = string Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
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
      in
        if null (Term.add_tvarsT T []) orelse null (binder_types T)
        then [thm]
        else [Code.expand_eta thy 1 thm]
      end
  | avoid_value thy thms = thms;

fun get_equations thy defs (raw_c, T) = if raw_c = @{const_name HOL.eq} then ([], "") else
  let
    val c = AxClass.unoverload_const thy (raw_c, T);
    val raw_thms = Code.get_cert thy (Code_Preproc.preprocess_functrans thy) c
      |> Code.bare_thms_of_cert thy
      |> map (AxClass.overload thy)
      |> filter (Codegen.is_instance T o snd o const_of o prop_of);
    val module_name = case Symtab.lookup (ModuleData.get thy) c
     of SOME module_name => module_name
      | NONE =>
        case Codegen.get_defn thy defs c T
         of SOME ((_, (thyname, _)), _) => thyname
          | NONE => Codegen.thyname_of_const thy c;
  in if null raw_thms then ([], "") else
    raw_thms
    |> Codegen.preprocess thy
    |> avoid_value thy
    |> rpair module_name
  end;

fun mk_suffix thy defs (s, T) =
  (case Codegen.get_defn thy defs s T of
    SOME (_, SOME i) => " def" ^ string_of_int i
  | _ => "");

exception EQN of string * typ * string;

fun cycle g x xs =
  if member (op =) xs x then xs
  else fold (cycle g) (flat (Graph.all_paths (fst g) (x, x))) (x :: xs);

fun add_rec_funs thy defs dep module eqs gr =
  let
    fun dest_eq t = (fst (const_of t) ^ mk_suffix thy defs (const_of t),
      Logic.dest_equals (Codegen.rename_term t));
    val eqs' = map dest_eq eqs;
    val (dname, _) :: _ = eqs';
    val (s, T) = const_of (hd eqs);

    fun mk_fundef module fname first [] gr = ([], gr)
      | mk_fundef module fname first ((fname' : string, (lhs, rhs)) :: xs) gr =
      let
        val (pl, gr1) = Codegen.invoke_codegen thy defs dname module false lhs gr;
        val (pr, gr2) = Codegen.invoke_codegen thy defs dname module false rhs gr1;
        val (rest, gr3) = mk_fundef module fname' false xs gr2 ;
        val (ty, gr4) = Codegen.invoke_tycodegen thy defs dname module false T gr3;
        val num_args = (length o snd o strip_comb) lhs;
        val prfx = if fname = fname' then "  |"
          else if not first then "and"
          else if num_args = 0 then "val"
          else "fun";
        val pl' = Pretty.breaks (Codegen.str prfx
          :: (if num_args = 0 then [pl, Codegen.str ":", ty] else [pl]));
      in
        (Pretty.blk (4, pl'
           @ [Codegen.str " =", Pretty.brk 1, pr]) :: rest, gr4)
      end;

    fun put_code module fundef = Codegen.map_node dname
      (K (SOME (EQN ("", dummyT, dname)), module, Codegen.string_of (Pretty.blk (0,
      separate Pretty.fbrk fundef @ [Codegen.str ";"])) ^ "\n\n"));

  in
    (case try (Codegen.get_node gr) dname of
       NONE =>
         let
           val gr1 = Codegen.add_edge (dname, dep)
             (Codegen.new_node (dname, (SOME (EQN (s, T, "")), module, "")) gr);
           val (fundef, gr2) = mk_fundef module "" true eqs' gr1 ;
           val xs = cycle gr2 dname [];
           val cs = map (fn x =>
             case Codegen.get_node gr2 x of
               (SOME (EQN (s, T, _)), _, _) => (s, T)
             | _ => error ("RecfunCodegen: illegal cyclic dependencies:\n" ^
                implode (separate ", " xs))) xs
         in
           (case xs of
             [_] => (module, put_code module fundef gr2)
           | _ =>
             if not (member (op =) xs dep) then
               let
                 val thmss as (_, thyname) :: _ = map (get_equations thy defs) cs;
                 val module' = Codegen.if_library thyname module;
                 val eqs'' = map (dest_eq o prop_of) (maps fst thmss);
                 val (fundef', gr3) = mk_fundef module' "" true eqs''
                   (Codegen.add_edge (dname, dep)
                     (List.foldr (uncurry Codegen.new_node) (Codegen.del_nodes xs gr2)
                       (map (fn k =>
                         (k, (SOME (EQN ("", dummyT, dname)), module', ""))) xs)))
               in (module', put_code module' fundef' gr3) end
             else (module, gr2))
         end
     | SOME (SOME (EQN (_, _, s)), module', _) =>
         (module', if s = "" then
            if dname = dep then gr else Codegen.add_edge (dname, dep) gr
          else if s = dep then gr else Codegen.add_edge (s, dep) gr))
  end;

fun recfun_codegen thy defs dep module brack t gr =
  (case strip_comb t of
    (Const (p as (s, T)), ts) =>
     (case (get_equations thy defs p, Codegen.get_assoc_code thy (s, T)) of
       (([], _), _) => NONE
     | (_, SOME _) => NONE
     | ((eqns, thyname), NONE) =>
        let
          val module' = Codegen.if_library thyname module;
          val (ps, gr') = fold_map
            (Codegen.invoke_codegen thy defs dep module true) ts gr;
          val suffix = mk_suffix thy defs p;
          val (module'', gr'') =
            add_rec_funs thy defs dep module' (map prop_of eqns) gr';
          val (fname, gr''') = Codegen.mk_const_id module'' (s ^ suffix) gr''
        in
          SOME (Codegen.mk_app brack (Codegen.str (Codegen.mk_qual_id module fname)) ps, gr''')
        end)
  | _ => NONE);

val setup = 
  Codegen.add_codegen "recfun" recfun_codegen
  #> Code.set_code_target_attr add_thm_target;

end;
