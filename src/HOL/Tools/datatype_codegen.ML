(*  Title:      HOL/datatype_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Code generator for inductive datatypes.
*)

signature DATATYPE_CODEGEN =
sig
  val setup: (theory -> theory) list
end;

structure DatatypeCodegen : DATATYPE_CODEGEN =
struct

open Codegen;

fun mk_tuple [p] = p
  | mk_tuple ps = Pretty.block (Pretty.str "(" ::
      flat (separate [Pretty.str ",", Pretty.brk 1] (map single ps)) @
        [Pretty.str ")"]);


(**** datatype definition ****)

fun add_dt_defs thy dep gr (descr: DatatypeAux.descr) =
  let
    val sg = sign_of thy;
    val tab = DatatypePackage.get_datatypes thy;

    val descr' = filter (can (map DatatypeAux.dest_DtTFree o #2 o snd)) descr;

    val (_, (_, _, (cname, _) :: _)) :: _ = descr';
    val dname = mk_const_id sg cname;

    fun mk_dtdef gr prfx [] = (gr, [])
      | mk_dtdef gr prfx ((_, (tname, dts, cs))::xs) =
          let
            val tvs = map DatatypeAux.dest_DtTFree dts;
            val sorts = map (rpair []) tvs;
            val cs' = map (apsnd (map (DatatypeAux.typ_of_dtyp descr sorts))) cs;
            val (gr', ps) = foldl_map (fn (gr, (cname, cargs)) =>
              apsnd (pair cname) (foldl_map
                (invoke_tycodegen thy dname false) (gr, cargs))) (gr, cs');
            val (gr'', rest) = mk_dtdef gr' "and " xs
          in
            (gr'',
             Pretty.block (Pretty.str prfx ::
               (if null tvs then [] else
                  [mk_tuple (map Pretty.str tvs), Pretty.str " "]) @
               [Pretty.str (mk_type_id sg tname ^ " ="), Pretty.brk 1] @
               flat (separate [Pretty.brk 1, Pretty.str "| "]
                 (map (fn (cname, ps') => [Pretty.block
                   (Pretty.str (mk_const_id sg cname) ::
                    (if null ps' then [] else
                     flat ([Pretty.str " of", Pretty.brk 1] ::
                       separate [Pretty.str " *", Pretty.brk 1]
                         (map single ps'))))]) ps))) :: rest)
          end
  in
    ((Graph.add_edge_acyclic (dname, dep) gr
        handle Graph.CYCLES _ => gr) handle Graph.UNDEF _ =>
         let
           val gr1 = Graph.add_edge (dname, dep)
             (Graph.new_node (dname, (None, "")) gr);
           val (gr2, dtdef) = mk_dtdef gr1 "datatype " descr';
         in
           Graph.map_node dname (K (None,
             Pretty.string_of (Pretty.blk (0, separate Pretty.fbrk dtdef @
               [Pretty.str ";"])) ^ "\n\n")) gr2
         end)
  end;


(**** case expressions ****)

fun pretty_case thy gr dep brack constrs (c as Const (_, T)) ts =
  let val i = length constrs
  in if length ts <= i then
       invoke_codegen thy dep brack (gr, eta_expand c ts (i+1))
    else
      let
        val ts1 = take (i, ts);
        val t :: ts2 = drop (i, ts);
        val names = foldr add_term_names (ts1,
          map (fst o fst o dest_Var) (foldr add_term_vars (ts1, [])));
        val (Ts, dT) = split_last (take (i+1, fst (strip_type T)));

        fun pcase gr [] [] [] = ([], gr)
          | pcase gr ((cname, cargs)::cs) (t::ts) (U::Us) =
              let
                val j = length cargs;
                val xs = variantlist (replicate j "x", names);
                val Us' = take (j, fst (strip_type U));
                val frees = map Free (xs ~~ Us');
                val (gr0, cp) = invoke_codegen thy dep false
                  (gr, list_comb (Const (cname, Us' ---> dT), frees));
                val t' = Envir.beta_norm (list_comb (t, frees));
                val (gr1, p) = invoke_codegen thy dep false (gr0, t');
                val (ps, gr2) = pcase gr1 cs ts Us;
              in
                ([Pretty.block [cp, Pretty.str " =>", Pretty.brk 1, p]] :: ps, gr2)
              end;

        val (ps1, gr1) = pcase gr constrs ts1 Ts;
        val ps = flat (separate [Pretty.brk 1, Pretty.str "| "] ps1);
        val (gr2, p) = invoke_codegen thy dep false (gr1, t);
        val (gr3, ps2) = foldl_map (invoke_codegen thy dep true) (gr2, ts2)
      in (gr3, (if not (null ts2) andalso brack then parens else I)
        (Pretty.block (separate (Pretty.brk 1)
          (Pretty.block ([Pretty.str "(case ", p, Pretty.str " of",
             Pretty.brk 1] @ ps @ [Pretty.str ")"]) :: ps2))))
      end
  end;


(**** constructors ****)

fun pretty_constr thy gr dep brack args (c as Const (s, _)) ts =
  let val i = length args
  in if i > 1 andalso length ts < i then
      invoke_codegen thy dep brack (gr, eta_expand c ts i)
     else
       let
         val id = mk_const_id (sign_of thy) s;
         val (gr', ps) = foldl_map (invoke_codegen thy dep (i = 1)) (gr, ts);
       in (case args of
          _ :: _ :: _ => (gr', (if brack then parens else I)
            (Pretty.block [Pretty.str id, Pretty.brk 1, mk_tuple ps]))
        | _ => (gr', mk_app brack (Pretty.str id) ps))
       end
  end;


(**** code generators for terms and types ****)

fun datatype_codegen thy gr dep brack t = (case strip_comb t of
   (c as Const (s, T), ts) =>
       (case find_first (fn (_, {index, descr, case_name, ...}) =>
         s = case_name orelse
           is_some (assoc (#3 (the (assoc (descr, index))), s)))
             (Symtab.dest (DatatypePackage.get_datatypes thy)) of
          None => None
        | Some (tname, {index, descr, ...}) =>
           if is_some (get_assoc_code thy s T) then None else
           let val Some (_, _, constrs) = assoc (descr, index)
           in (case (assoc (constrs, s), strip_type T) of
               (None, _) => Some (pretty_case thy gr dep brack
                 (#3 (the (assoc (descr, index)))) c ts)
             | (Some args, (_, Type _)) => Some (pretty_constr thy
                 (fst (invoke_tycodegen thy dep false (gr, snd (strip_type T))))
                 dep brack args c ts)
             | _ => None)
           end)
 |  _ => None);

fun datatype_tycodegen thy gr dep brack (Type (s, Ts)) =
      (case Symtab.lookup (DatatypePackage.get_datatypes thy, s) of
         None => None
       | Some {descr, ...} =>
           if is_some (get_assoc_type thy s) then None else
           let val (gr', ps) = foldl_map
             (invoke_tycodegen thy dep false) (gr, Ts)
           in Some (add_dt_defs thy dep gr' descr,
             Pretty.block ((if null Ts then [] else
               [mk_tuple ps, Pretty.str " "]) @
               [Pretty.str (mk_type_id (sign_of thy) s)]))
           end)
  | datatype_tycodegen _ _ _ _ _ = None;


val setup =
  [add_codegen "datatype" datatype_codegen,
   add_tycodegen "datatype" datatype_tycodegen];

end;
