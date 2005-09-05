(*  Title:      HOL/Tools/primrec_package.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen and Norbert Voelker, FernUni Hagen

Package for defining functions on datatypes by primitive recursion.
*)

signature PRIMREC_PACKAGE =
sig
  val quiet_mode: bool ref
  val add_primrec: string -> ((bstring * string) * Attrib.src list) list
    -> theory -> theory * thm list
  val add_primrec_i: string -> ((bstring * term) * theory attribute list) list
    -> theory -> theory * thm list
end;

structure PrimrecPackage : PRIMREC_PACKAGE =
struct

open DatatypeAux;

exception RecError of string;

fun primrec_err s = error ("Primrec definition error:\n" ^ s);
fun primrec_eq_err sign s eq =
  primrec_err (s ^ "\nin\n" ^ quote (Sign.string_of_term sign eq));


(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* preprocessing of equations *)

fun process_eqn sign (eq, rec_fns) = 
  let
    val (lhs, rhs) = 
	if null (term_vars eq) then
	    HOLogic.dest_eq (HOLogic.dest_Trueprop eq)
	      handle TERM _ => raise RecError "not a proper equation"
	else raise RecError "illegal schematic variable(s)";

    val (recfun, args) = strip_comb lhs;
    val fnameT = dest_Const recfun handle TERM _ => 
      raise RecError "function is not declared as constant in theory";

    val (ls', rest)  = take_prefix is_Free args;
    val (middle, rs') = take_suffix is_Free rest;
    val rpos = length ls';

    val (constr, cargs') = if null middle then raise RecError "constructor missing"
      else strip_comb (hd middle);
    val (cname, T) = dest_Const constr
      handle TERM _ => raise RecError "ill-formed constructor";
    val (tname, _) = dest_Type (body_type T) handle TYPE _ =>
      raise RecError "cannot determine datatype associated with function"

    val (ls, cargs, rs) = (map dest_Free ls', 
			   map dest_Free cargs', 
			   map dest_Free rs')
      handle TERM _ => raise RecError "illegal argument in pattern";
    val lfrees = ls @ rs @ cargs;

    fun check_vars _ [] = ()
      | check_vars s vars = raise RecError (s ^ commas_quote (map fst vars))
  in
    if length middle > 1 then 
      raise RecError "more than one non-variable in pattern"
    else
     (check_vars "repeated variable names in pattern: " (duplicates lfrees);
      check_vars "extra variables on rhs: "
        (map dest_Free (term_frees rhs) \\ lfrees);
      case AList.lookup (op =) rec_fns fnameT of
        NONE =>
          (fnameT, (tname, rpos, [(cname, (ls, cargs, rs, rhs, eq))]))::rec_fns
      | SOME (_, rpos', eqns) =>
          if AList.defined (op =) eqns cname then
            raise RecError "constructor already occurred as pattern"
          else if rpos <> rpos' then
            raise RecError "position of recursive argument inconsistent"
          else
            overwrite (rec_fns, 
		       (fnameT, 
			(tname, rpos,
			 (cname, (ls, cargs, rs, rhs, eq))::eqns))))
  end
  handle RecError s => primrec_eq_err sign s eq;

fun process_fun sign descr rec_eqns ((i, fnameT as (fname, _)), (fnameTs, fnss)) =
  let
    val (_, (tname, _, constrs)) = List.nth (descr, i);

    (* substitute "fname ls x rs" by "y ls rs" for (x, (_, y)) in subs *)

    fun subst [] x = x
      | subst subs (fs, Abs (a, T, t)) =
          let val (fs', t') = subst subs (fs, t)
          in (fs', Abs (a, T, t')) end
      | subst subs (fs, t as (_ $ _)) =
          let val (f, ts) = strip_comb t;
          in
            if is_Const f andalso dest_Const f mem map fst rec_eqns then
              let
                val fnameT' as (fname', _) = dest_Const f;
                val (_, rpos, _) = the (AList.lookup (op =) rec_eqns fnameT');
                val ls = Library.take (rpos, ts);
                val rest = Library.drop (rpos, ts);
                val (x', rs) = (hd rest, tl rest)
                  handle Empty => raise RecError ("not enough arguments\
                   \ in recursive application\nof function " ^ quote fname' ^ " on rhs");
                val (x, xs) = strip_comb x'
              in 
                (case AList.lookup (op =) subs x of
                    NONE =>
                      let
                        val (fs', ts') = foldl_map (subst subs) (fs, ts)
                      in (fs', list_comb (f, ts')) end
                  | SOME (i', y) =>
                      let
                        val (fs', ts') = foldl_map (subst subs) (fs, xs @ ls @ rs);
                        val fs'' = process_fun sign descr rec_eqns ((i', fnameT'), fs')
                      in (fs'', list_comb (y, ts'))
                      end)
              end
            else
              let
                val (fs', f'::ts') = foldl_map (subst subs) (fs, f::ts)
              in (fs', list_comb (f', ts')) end
          end
      | subst _ x = x;

    (* translate rec equations into function arguments suitable for rec comb *)

    fun trans eqns ((cname, cargs), (fnameTs', fnss', fns)) =
      (case AList.lookup (op =) eqns cname of
          NONE => (warning ("No equation for constructor " ^ quote cname ^
            "\nin definition of function " ^ quote fname);
              (fnameTs', fnss', (Const ("arbitrary", dummyT))::fns))
        | SOME (ls, cargs', rs, rhs, eq) =>
            let
              val recs = List.filter (is_rec_type o snd) (cargs' ~~ cargs);
              val rargs = map fst recs;
              val subs = map (rpair dummyT o fst) 
		             (rev (rename_wrt_term rhs rargs));
              val ((fnameTs'', fnss''), rhs') = 
		  (subst (map (fn ((x, y), z) =>
			       (Free x, (body_index y, Free z)))
			  (recs ~~ subs))
		   ((fnameTs', fnss'), rhs))
                  handle RecError s => primrec_eq_err sign s eq
            in (fnameTs'', fnss'', 
		(list_abs_free (cargs' @ subs @ ls @ rs, rhs'))::fns)
            end)

  in (case AList.lookup (op =) fnameTs i of
      NONE =>
        if exists (equal fnameT o snd) fnameTs then
          raise RecError ("inconsistent functions for datatype " ^ quote tname)
        else
          let
            val (_, _, eqns) = the (AList.lookup (op =) rec_eqns fnameT);
            val (fnameTs', fnss', fns) = foldr (trans eqns)
              ((i, fnameT)::fnameTs, fnss, []) constrs
          in
            (fnameTs', (i, (fname, #1 (snd (hd eqns)), fns))::fnss')
          end
    | SOME fnameT' =>
        if fnameT = fnameT' then (fnameTs, fnss)
        else raise RecError ("inconsistent functions for datatype " ^ quote tname))
  end;


(* prepare functions needed for definitions *)

fun get_fns fns (((i, (tname, _, constrs)), rec_name), (fs, defs)) =
  case AList.lookup (op =) fns i of
     NONE =>
       let
         val dummy_fns = map (fn (_, cargs) => Const ("arbitrary",
           replicate ((length cargs) + (length (List.filter is_rec_type cargs)))
             dummyT ---> HOLogic.unitT)) constrs;
         val _ = warning ("No function definition for datatype " ^ quote tname)
       in
         (dummy_fns @ fs, defs)
       end
   | SOME (fname, ls, fs') => (fs' @ fs, (fname, ls, rec_name, tname)::defs);


(* make definition *)

fun make_def sign fs (fname, ls, rec_name, tname) =
  let
    val rhs = foldr (fn (T, t) => Abs ("", T, t)) 
	            (list_comb (Const (rec_name, dummyT),
				fs @ map Bound (0 ::(length ls downto 1))))
		    ((map snd ls) @ [dummyT]);
    val defpair = (Sign.base_name fname ^ "_" ^ Sign.base_name tname ^ "_def",
		   Logic.mk_equals (Const (fname, dummyT), rhs))
  in Theory.inferT_axm sign defpair end;


(* find datatypes which contain all datatypes in tnames' *)

fun find_dts (dt_info : datatype_info Symtab.table) _ [] = []
  | find_dts dt_info tnames' (tname::tnames) =
      (case Symtab.curried_lookup dt_info tname of
          NONE => primrec_err (quote tname ^ " is not a datatype")
        | SOME dt =>
            if tnames' subset (map (#1 o snd) (#descr dt)) then
              (tname, dt)::(find_dts dt_info tnames' tnames)
            else find_dts dt_info tnames' tnames);

fun prepare_induct ({descr, induction, ...}: datatype_info) rec_eqns =
  let
    fun constrs_of (_, (_, _, cs)) =
      map (fn (cname:string, (_, cargs, _, _, _)) => (cname, map fst cargs)) cs;
    val params_of = these o AList.lookup (op =) (List.concat (map constrs_of rec_eqns));
  in
    induction
    |> RuleCases.rename_params (map params_of (List.concat (map (map #1 o #3 o #2) descr)))
    |> RuleCases.save induction
  end;

fun add_primrec_i alt_name eqns_atts thy =
  let
    val (eqns, atts) = split_list eqns_atts;
    val sg = Theory.sign_of thy;
    val dt_info = DatatypePackage.get_datatypes thy;
    val rec_eqns = foldr (process_eqn sg) [] (map snd eqns);
    val tnames = distinct (map (#1 o snd) rec_eqns);
    val dts = find_dts dt_info tnames tnames;
    val main_fns = 
	map (fn (tname, {index, ...}) =>
	     (index, 
	      fst (valOf (find_first (fn f => #1 (snd f) = tname) rec_eqns))))
	dts;
    val {descr, rec_names, rec_rewrites, ...} = 
	if null dts then
	    primrec_err ("datatypes " ^ commas_quote tnames ^ 
			 "\nare not mutually recursive")
	else snd (hd dts);
    val (fnameTs, fnss) = foldr (process_fun sg descr rec_eqns)
	                       ([], []) main_fns;
    val (fs, defs) = foldr (get_fns fnss) ([], []) (descr ~~ rec_names);
    val defs' = map (make_def sg fs) defs;
    val nameTs1 = map snd fnameTs;
    val nameTs2 = map fst rec_eqns;
    val primrec_name =
      if alt_name = "" then (space_implode "_" (map (Sign.base_name o #1) defs)) else alt_name;
    val (thy', defs_thms') = thy |> Theory.add_path primrec_name |>
      (if eq_set (nameTs1, nameTs2) then (PureThy.add_defs_i false o map Thm.no_attributes) defs'
       else primrec_err ("functions " ^ commas_quote (map fst nameTs2) ^
         "\nare not mutually recursive"));
    val rewrites = (map mk_meta_eq rec_rewrites) @ defs_thms';
    val _ = message ("Proving equations for primrec function(s) " ^
      commas_quote (map fst nameTs1) ^ " ...");
    val simps = map (fn (_, t) => prove_goalw_cterm rewrites (cterm_of (Theory.sign_of thy') t)
        (fn _ => [rtac refl 1])) eqns;
    val (thy'', simps') = PureThy.add_thms ((map fst eqns ~~ simps) ~~ atts) thy';
    val thy''' = thy''
      |> (#1 o PureThy.add_thmss [(("simps", simps'),
           [Simplifier.simp_add_global, RecfunCodegen.add NONE])])
      |> (#1 o PureThy.add_thms [(("induct", prepare_induct (#2 (hd dts)) rec_eqns), [])])
      |> Theory.parent_path
  in
    (thy''', simps')
  end;


fun add_primrec alt_name eqns thy =
  let
    val sign = Theory.sign_of thy;
    val ((names, strings), srcss) = apfst split_list (split_list eqns);
    val atts = map (map (Attrib.global_attribute thy)) srcss;
    val eqn_ts = map (fn s => term_of (Thm.read_cterm sign (s, propT))
      handle ERROR => error ("The error(s) above occurred for " ^ s)) strings;
    val rec_ts = map (fn eq => head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop eq)))
      handle TERM _ => primrec_eq_err sign "not a proper equation" eq) eqn_ts;
    val (_, eqn_ts') = InductivePackage.unify_consts (sign_of thy) rec_ts eqn_ts
  in
    add_primrec_i alt_name (names ~~ eqn_ts' ~~ atts) thy
  end;


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val primrec_decl =
  Scan.optional (P.$$$ "(" |-- P.name --| P.$$$ ")") "" --
    Scan.repeat1 (P.opt_thm_name ":" -- P.prop);

val primrecP =
  OuterSyntax.command "primrec" "define primitive recursive functions on datatypes" K.thy_decl
    (primrec_decl >> (fn (alt_name, eqns) =>
      Toplevel.theory (#1 o add_primrec alt_name (map P.triple_swap eqns))));

val _ = OuterSyntax.add_parsers [primrecP];

end;


end;

