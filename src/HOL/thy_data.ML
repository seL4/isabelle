(*  Title:      HOL/thy_data.ML
    ID:         $Id$
    Author:     Carsten Clasohm
    Copyright   1995 TU Muenchen

Definitions that have to be reread after init_thy_reader has been invoked
*)

fun simpset_of tname =
  case get_thydata tname "simpset" of
      None => empty_ss
    | Some (SS_DATA ss) => ss;

fun claset_of tname =
  case get_thydata tname "claset" of
      None => empty_cs
    | Some (CS_DATA cs) => cs;


(** Information about datatypes **)

(* Retrieve information for a specific datatype *)
fun datatype_info thy tname =
  case get_thydata (thyname_of_sign (sign_of thy)) "datatypes" of
      None => None
    | Some (DT_DATA ds) => assoc (ds, tname);

fun match_info thy tname =
  case datatype_info thy tname of
      Some {case_const, constructors, ...} =>
        {case_const=case_const, constructors=constructors}
    | None => error ("No datatype \"" ^ tname ^ "\" defined in this theory.");

fun induct_info thy tname =
  case datatype_info thy tname of
      Some {constructors, nchotomy, ...} =>
        {constructors=constructors, nchotomy=nchotomy}
    | None => error ("No datatype \"" ^ tname ^ "\" defined in this theory.");


(* Retrieve information for all datatypes defined in a theory and its
   ancestors *)
fun extract_info thy =
  let val (congs, rewrites) =
        case get_thydata (thyname_of_sign (sign_of thy)) "datatypes" of
            None => ([], [])
          | Some (DT_DATA ds) =>
              let val info = map snd ds
              in (map #case_cong info, flat (map #case_rewrites info)) end;
  in {case_congs = congs, case_rewrites = rewrites} end;

(* generic induction tactic for datatypes *)
fun induct_tac var i =
  let fun find_tname Bi =
        let val frees = map dest_Free (term_frees Bi)
            val params = Logic.strip_params Bi;
        in case assoc (frees@params, var) of
             None => error("No such variable in subgoal: " ^ quote var)
           | Some(Type(tn,_)) => tn
           | _ => error("Cannot induct on type of " ^ quote var)
        end;
      fun get_ind_tac sign tn =
        (case get_thydata (thyname_of_sign sign) "datatypes" of
           None => error ("No such datatype: " ^ quote tn)
         | Some (DT_DATA ds) =>
             (case assoc (ds, tn) of
                Some {induct_tac, ...} => induct_tac
              | None => error ("Not a datatype: " ^ quote tn)));
      fun induct state =
        let val (_, _, Bi, _) = dest_state (state, i) 
        in get_ind_tac (#sign(rep_thm state)) (find_tname Bi) var i end
  in STATE induct end;

(*Must be redefined in order to refer to the new instance of bind_thm
  created by init_thy_reader.*)

fun qed_spec_mp name =
  let val thm = normalize_thm [RSspec,RSmp] (result())
  in bind_thm(name, thm) end;

fun qed_goal_spec_mp name thy s p = 
	bind_thm (name, normalize_thm [RSspec,RSmp] (prove_goal thy s p));

fun qed_goalw_spec_mp name thy defs s p = 
	bind_thm (name, normalize_thm [RSspec,RSmp] (prove_goalw thy defs s p));
