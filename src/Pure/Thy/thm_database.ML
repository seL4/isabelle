(*  Title:      Pure/Thy/thm_database.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Tobias Nipkow
    Copyright   1995 TU Muenchen
*)

datatype thm_db =
  ThmDB of {count: int,
            thy_idx: (Sign.sg * (string list * int list)) list,
            const_idx: ((int * (string * thm)) list) Symtab.table};
    (*count: number of theorems in database (used as unique ID for next thm)
      thy_idx: constants and IDs of theorems
               indexed by the theory's signature they belong to
      const_idx: named theorems tagged by numbers and
                 indexed by the constants they contain*)

signature THM_DATABASE =
  sig
  val thm_db: thm_db ref
  val store_thm_db: string * thm -> thm
  val delete_thm_db: theory -> unit
  val thms_containing: string list -> (string * thm) list
  val findI:         int -> (string * thm)list
  val findEs:        int -> (string * thm)list
  val findE:  int -> int -> (string * thm)list

  val store_thm      : string * thm -> thm
  val bind_thm       : string * thm -> unit
  val qed            : string -> unit
  val qed_thm        : thm ref
  val qed_goal       : string -> theory -> string 
                       -> (thm list -> tactic list) -> unit
  val qed_goalw      : string -> theory -> thm list -> string 
                       -> (thm list -> tactic list) -> unit
  val get_thm        : theory -> string -> thm
  val thms_of        : theory -> (string * thm) list
  val delete_thms    : string -> unit

  val print_theory   : theory -> unit
  end;

structure ThmDatabase: THM_DATABASE =
struct

open ThyInfo BrowserInfo;

(*** ignore and top_const could be turned into functor-parameters, but are
currently identical for all object logics ***)

(* Constants not to be used for theorem indexing *)
val ignore = ["Trueprop", "all", "==>", "=="];

(* top_const: main constant, ignoring Trueprop *)
fun top_const (_ $ t) = (case head_of t of Const(c,_) => Some c
                                         | _          => None)
  | top_const _ = None;

(*Symtab which associates a constant with a list of theorems that contain the
  constant (theorems are tagged with numbers)*)
val thm_db = ref (ThmDB
 {count = 0, thy_idx = []:(Sign.sg * (string list * int list)) list,
  const_idx = Symtab.make ([]:(string * ((int * (string * thm)) list)) list)});

(*List all relevant constants a term contains*)
fun list_consts t =
  let fun consts (Const (c, _)) = if c mem ignore then [] else [c]
        | consts (Free _) = []
        | consts (Var _) = []
        | consts (Bound _) = []
        | consts (Abs (_, _, t)) = consts t
        | consts (t1$t2) = (consts t1) union (consts t2);
  in distinct (consts t) end;

(*Store a theorem in database*)
fun store_thm_db (named_thm as (name, thm)) =
  let val {prop, hyps, sign, ...} = rep_thm thm;

      val consts = distinct (flat (map list_consts (prop :: hyps)));

      val ThmDB {count, thy_idx, const_idx} = !thm_db;

      fun update_thys [] = [(sign, (consts, [count]))]
        | update_thys ((thy as (thy_sign, (thy_consts, thy_nums))) :: ts) =
            if Sign.eq_sg (sign, thy_sign) then
              (thy_sign, (thy_consts union consts, count :: thy_nums)) :: ts
            else thy :: update_thys ts;

      val tagged_thm = (count, named_thm);

      fun update_db _ [] result = Some result
        | update_db checked (c :: cs) result =
            let
              val old_thms = Symtab.lookup_multi (result, c);

              val duplicate =
                if checked then false
                else case find_first (fn (_, (n, _)) => n = name) old_thms of
                       Some (_, (_, t)) => eq_thm (t, thm)
                     | None => false
            in if duplicate then None
               else update_db true
                      cs (Symtab.update ((c, tagged_thm :: old_thms), result))
            end;

      val const_idx' = update_db false consts const_idx;
  in if consts = [] then warning ("Theorem " ^ name ^
                                  " cannot be stored in ThmDB\n\t because it \
                                  \contains no or only ignored constants.")
     else if is_some const_idx' then
       thm_db := ThmDB {count = count+1, thy_idx = update_thys thy_idx,
                        const_idx = the const_idx'}
     else ();
     thm
  end;

(*Remove all theorems with given signature from database*)
fun delete_thm_db thy =
  let
    val sign = sign_of thy;

    val ThmDB {count, thy_idx, const_idx} = !thm_db;

    (*Remove theory from thy_idx and get the data associated with it*)
    fun update_thys [] result = (result, [], [])
      | update_thys ((thy as (thy_sign, (thy_consts, thy_nums))) :: ts)
                    result =
          if Sign.eq_sg (sign, thy_sign) then
            (result @ ts, thy_consts, thy_nums)
          else update_thys ts (thy :: result);

    val (thy_idx', thy_consts, thy_nums) = update_thys thy_idx [];

    (*Remove all theorems belonging to a theory*)
    fun update_db [] result = result
      | update_db (c :: cs) result =
        let val thms' = filter_out (fn (num, _) => num mem thy_nums)
                                   (Symtab.lookup_multi (result, c));
        in update_db cs (Symtab.update ((c, thms'), result)) end;
  in thm_db := ThmDB {count = count, thy_idx = thy_idx',
                      const_idx = update_db thy_consts const_idx}
  end;

(*Intersection of two theorem lists with descending tags*)
infix desc_inter;
fun ([] : (int*'a) list) desc_inter (ys : (int*'a) list) = []
  | xs desc_inter [] = []
  | (xss as ((x as (xi,_)) :: xs)) desc_inter (yss as ((yi,_) :: ys)) =
      if xi = yi then x :: (xs desc_inter ys)
      else if xi > yi then xs desc_inter yss
      else xss desc_inter ys;

(*Get all theorems from database that contain a list of constants*)
fun thms_containing constants =
  let fun collect [] _ result = map snd result
        | collect (c :: cs) first result =
            let val ThmDB {const_idx, ...} = !thm_db;

                val new_thms = Symtab.lookup_multi (const_idx, c);
            in collect cs false (if first then new_thms
                                          else (result desc_inter new_thms))
            end;

      val look_for = constants \\ ignore;
  in if null look_for then
       error ("No or only ignored constants were specified for theorem \
              \database search:\n  " ^ commas (map quote ignore))
     else ();
     collect look_for true [] end;

val intro_const = top_const o concl_of;

fun elim_const thm = case prems_of thm of [] => None | p::_ => top_const(p);

(* In case faster access is necessary, the thm db should provide special
functions

index_intros, index_elims: string -> (string * thm) list

where thm [| A1 ; ...; An |] ==> B is returned by
- index_intros c if B  is of the form c t1 ... tn
- index_elims c  if A1 is of the form c t1 ... tn
*)

(* could be provided by thm db *)
fun index_intros c =
  let fun topc(_,thm) = intro_const thm = Some(c);
      val named_thms = thms_containing [c]
  in filter topc named_thms end;

(* could be provided by thm db *)
fun index_elims c =
  let fun topc(_,thm) = elim_const thm = Some(c);
      val named_thms = thms_containing [c]
  in filter topc named_thms end;

(*assume that parameters have unique names*)
fun goal_params i =
  let val gi = getgoal i
      val frees = map Free (Logic.strip_params gi)
  in (gi,frees) end;

fun concl_of_goal i =
  let val (gi,frees) = goal_params i
      val B = Logic.strip_assums_concl gi
  in subst_bounds(frees,B) end;

fun prems_of_goal i =
  let val (gi,frees) = goal_params i
      val As = Logic.strip_assums_hyp gi
  in map (fn A => subst_bounds(frees,A)) As end;

fun select_match(obj, signobj, named_thms, extract) =
  let fun matches(prop, tsig) =
            case extract prop of
              None => false
            | Some pat => Pattern.matches tsig (pat, obj);

      fun substsize(prop, tsig) =
            let val Some pat = extract prop
                val (_,subst) = Pattern.match tsig (pat,obj)
            in foldl op+
		(0, map (fn (_,t) => size_of_term t) subst)
            end

      fun thm_order ((p0:int,s0:int,_),(p1,s1,_)) =
            (((p0=0 andalso p1=0) orelse (p0<>0 andalso p1<>0)) andalso s0<=s1)
            orelse (p0=0 andalso p1<>0)

      fun select((p as (_,thm))::named_thms, sels) =
            let val {prop, sign, ...} = rep_thm thm
            in select(named_thms,
                      if Sign.subsig(sign, signobj) andalso
                         matches(prop,#tsig(Sign.rep_sg signobj))
                      then
			(nprems_of thm,substsize(prop,#tsig(Sign.rep_sg signobj)),p)::sels
                      else sels)
            end
        | select([],sels) = sels

  in map (fn (_,_,t) => t) (sort thm_order (select(named_thms, []))) end; 

fun find_matching(prop,sign,index,extract) =
  (case top_const prop of
     Some c => select_match(prop,sign,index c,extract)
   | _      => []);

fun find_intros(prop,sign) =
  find_matching(prop,sign,index_intros,Some o Logic.strip_imp_concl);

fun find_elims sign prop =
  let fun major prop = case Logic.strip_imp_prems prop of
                         [] => None | p::_ => Some p
  in find_matching(prop,sign,index_elims,major) end;

fun findI i = find_intros(concl_of_goal i,#sign(rep_thm(topthm())));

fun findEs i =
  let fun eq_nth((n1,th1),(n2,th2)) = n1=n2 andalso eq_thm(th1,th2);
      val sign = #sign(rep_thm(topthm()))
      val thmss = map (find_elims sign) (prems_of_goal i)
  in foldl (gen_union eq_nth) ([],thmss) end;

fun findE i j =
  let val sign = #sign(rep_thm(topthm()))
  in find_elims sign (nth_elem(j-1, prems_of_goal i)) end;


(*** Store and retrieve theorems ***)

(** Store theorems **)

(*Store a theorem in the thy_info of its theory,
  and in the theory's HTML file*)
fun store_thm (name, thm) =
  let
    val (thy_name, ThyInfo {path, children, parents, thy_time, ml_time,
                            theory, thms, methods, data}) =
      thyinfo_of_sign (#sign (rep_thm thm))

    val (thms', duplicate) = (Symtab.update_new ((name, thm), thms), false)
      handle Symtab.DUPLICATE s => 
        (if eq_thm (the (Symtab.lookup (thms, name)), thm) then 
           (warning ("Theory database already contains copy of\
                     \ theorem " ^ quote name);
            (thms, true))
         else error ("Duplicate theorem name " ^ quote s
                     ^ " used in theory database"));

    (*Label this theorem*)
    val thm' = Thm.name_thm (name, thm)
  in
    loaded_thys := Symtab.update
     ((thy_name, ThyInfo {path = path, children = children, parents = parents,
                          thy_time = thy_time, ml_time = ml_time,
                          theory = theory, thms = thms',
                          methods = methods, data = data}),
      !loaded_thys);
    thm_to_html thm name;
    if duplicate then thm' else store_thm_db (name, thm')
  end;


(*Store result of proof in loaded_thys and as ML value*)

val qed_thm = ref flexpair_def(*dummy*);


fun bind_thm (name, thm) =
 (qed_thm := store_thm (name, (standard thm));
  use_string ["val " ^ name ^ " = !qed_thm;"]);


fun qed name =
 (qed_thm := store_thm (name, result ());
  use_string ["val " ^ name ^ " = !qed_thm;"]);


fun qed_goal name thy agoal tacsf =
 (qed_thm := store_thm (name, prove_goal thy agoal tacsf);
  use_string ["val " ^ name ^ " = !qed_thm;"]);


fun qed_goalw name thy rths agoal tacsf =
 (qed_thm := store_thm (name, prove_goalw thy rths agoal tacsf);
  use_string ["val " ^ name ^ " = !qed_thm;"]);


(** Retrieve theorems **)

(*Get all theorems belonging to a given theory*)
fun thmtab_of_thy thy =
  let val (_, ThyInfo {thms, ...}) = thyinfo_of_sign (sign_of thy);
  in thms end;


fun thmtab_of_name name =
  let val ThyInfo {thms, ...} = the (get_thyinfo name);
  in thms end;


(*Get a stored theorem specified by theory and name. *)
fun get_thm thy name =
  let fun get [] [] searched =
           raise THEORY ("get_thm: no theorem " ^ quote name, [thy])
        | get [] ng searched =
            get (ng \\ searched) [] searched
        | get (t::ts) ng searched =
            (case Symtab.lookup (thmtab_of_name t, name) of
                 Some thm => thm
               | None => get ts (ng union (parents_of_name t)) (t::searched));

      val (tname, _) = thyinfo_of_sign (sign_of thy);
  in get [tname] [] [] end;


(*Get stored theorems of a theory (original derivations) *)
val thms_of = Symtab.dest o thmtab_of_thy;


(*Remove theorems associated with a theory from theory and theorem database*)
fun delete_thms tname =
  let
    val tinfo = case get_thyinfo tname of
        Some (ThyInfo {path, children, parents, thy_time, ml_time, theory,
                       methods, data, ...}) =>
          ThyInfo {path = path, children = children, parents = parents,
                   thy_time = thy_time, ml_time = ml_time,
                   theory = theory, thms = Symtab.null,
                   methods = methods, data = data}
      | None => error ("Theory " ^ tname ^ " not stored by loader");

    val ThyInfo {theory, ...} = tinfo;
  in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys);
     case theory of
         Some t => delete_thm_db t
       | None => ()
  end;


(*** Print theory ***)

fun print_thms thy =
  let
    val thms = thms_of thy;
    fun prt_thm (s, th) = Pretty.block [Pretty.str (s ^ ":"), Pretty.brk 1,
      Pretty.quote (pretty_thm th)];
  in
    Pretty.writeln (Pretty.big_list "stored theorems:" (map prt_thm thms))
  end;


fun print_theory thy = (Display.print_theory thy; print_thms thy);

end;
