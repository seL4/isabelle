(*  Author:     Makarius
    LICENSE:    Isabelle (BSD-3)

Statistics for theory content.
*)

type theory_statistics =
 {theory: string,
  locales: int,
  locale_thms: int,
  global_thms: int};

type session_statistics =
 {sizeof_thys_id: int,
  sizeof_thms_id: int,
  sizeof_terms: int,
  sizeof_types: int,
  sizeof_spaces: int};

structure Statistics:
sig
  val locale_names: theory -> string list
  val locale_thms: theory -> string -> thm list
  val global_thms: theory -> thm list
  val all_thms: theory -> thm list
  val statistics: string list -> theory_statistics list * session_statistics
  val main: unit -> unit
end =
struct

(* theory content *)

fun locale_names thy =
  let
    val parent_spaces = map Locale.locale_space (Theory.parents_of thy);
    fun add name =
      if exists (fn space => Name_Space.declared space name) parent_spaces then I
      else cons name;
  in fold add (Locale.get_locales thy) [] end;

fun proper_thm thm = not (Thm.eq_thm_prop (Drule.dummy_thm, thm));

fun locale_thms thy loc =
  (Locale.locale_notes thy loc, []) |->
    (fold (#2 #> fold (#2 #> (fold (#1 #> fold (fn thm => proper_thm thm ? cons thm ))))));

fun global_thms thy =
  Facts.dest_static true
    (map Global_Theory.facts_of (Theory.parents_of thy)) (Global_Theory.facts_of thy)
  |> maps #2;

fun all_thms thy =
  let val locales = locale_names thy
  in maps (locale_thms thy) locales @ global_thms thy end;


(* session content *)

fun theories_content thys =
  let
    val thms = maps all_thms thys;
    val thys_id = map Context.theory_id thys;
    val thms_id = map Thm.theory_id thms;
    val terms = (fold o Thm.fold_terms {hyps = true}) cons thms [];
    val types = (fold o fold_types) cons terms [];
    val spaces =
      maps (fn f => map f thys)
       [Sign.class_space,
        Sign.type_space,
        Sign.const_space,
        Theory.axiom_space,
        Thm.oracle_space,
        Global_Theory.fact_space,
        Locale.locale_space,
        Attrib.attribute_space o Context.Theory,
        Method.method_space o Context.Theory];
  in {thys_id = thys_id, thms_id = thms_id, terms = terms, types = types, spaces = spaces} end;

fun sizeof_diff (a, b) = ML_Heap.sizeof a - ML_Heap.sizeof b;


(* collect statistics *)

fun theory_statistics thy : theory_statistics =
  let
    val locales = locale_names thy;
  in
   {theory = Context.theory_long_name thy,
    locales = length locales,
    locale_thms = length (maps (locale_thms thy) locales),
    global_thms = length (global_thms thy)}
  end;

fun statistics theories =
  let
    val theories_member = Symtab.defined (Symtab.make_set theories) o Context.theory_long_name;

    val context_thys =
      #contexts (Context.finish_tracing ())
      |> map_filter (fn (Context.Theory thy, _) => SOME thy | _ => NONE);

    val loader_thys = map Thy_Info.get_theory (Thy_Info.get_names ());
    val loaded_thys = filter theories_member loader_thys;

    val all_thys = loader_thys @ context_thys;
    val base_thys = filter theories_member all_thys;

    val {thys_id = all_thys_id, thms_id = all_thms_id, terms = all_terms,
          types = all_types, spaces = all_spaces} = theories_content all_thys;
    val {thys_id = base_thys_id, thms_id = base_thms_id, terms = base_terms,
          types = base_types, spaces = base_spaces} = theories_content base_thys;
    val session_statistics =
      {sizeof_thys_id = sizeof_diff (all_thys_id, base_thys_id),
       sizeof_thms_id = sizeof_diff (all_thms_id, base_thms_id),
       sizeof_terms = sizeof_diff (all_terms, base_terms),
       sizeof_types = sizeof_diff (all_types, base_types),
       sizeof_spaces = sizeof_diff (all_spaces, base_spaces)};
  in (map theory_statistics loaded_thys, session_statistics) end;


(* main entry point for "isabelle process" *)

local

val decode_args : string list XML.Decode.T =
  let open XML.Decode in list string end;

val encode_theories_result : theory_statistics list XML.Encode.T =
  map (fn {theory = a, locales = b, locale_thms = c, global_thms = d} => (a, (b, (c, d))))
  #> let open XML.Encode in list (pair string (pair int (pair int int))) end;

val encode_session_result : session_statistics XML.Encode.T =
  (fn {sizeof_thys_id = a,
       sizeof_thms_id = b,
       sizeof_terms = c,
       sizeof_types = d,
       sizeof_spaces = e} => (a, (b, (c, (d, e)))))
  #> let open XML.Encode in pair int (pair int (pair int (pair int int))) end;

val encode_result = let open XML.Encode in pair encode_theories_result encode_session_result end;

in

fun main () =
  (case getenv "AUTOCORRES_STATISTICS" of
    "" => ()
  | dir_name =>
      let
        val dir = Path.explode dir_name;
        val args = decode_args (YXML.parse_body (File.read (dir + \<^path>\<open>args.yxml\<close>)));
        val result = statistics args;
      in File.write (dir + \<^path>\<open>result.yxml\<close>) (YXML.string_of_body (encode_result result)) end);

end;

end;
