(*  Title:      Pure/Thy/read
    ID:         $Id$
    Author:     Sonia Mahjoub / Tobias Nipkow / L C Paulson
    Copyright   1992  TU Muenchen

Reading and writing the theory definition files.

For theory XXX, the  input file is called XXX.thy
                the output file is called .XXX.thy.ML
                and it then tries to read XXX.ML
*)

signature READTHY =
sig
  type thy_info

  val use_thy        : string -> unit
  val update         : unit -> unit
  val time_use_thy   : string -> unit
  val base_on        : string list -> string -> Thm.theory
  val store_theory   : string -> Thm.theory -> unit
  val list_loaded    : unit -> thy_info list
  val set_loaded     : thy_info list -> unit
  val set_loadpath   : string list -> unit
  val relations      : string -> unit
end;


functor ReadthyFUN (structure ThySyn: THYSYN) : READTHY =
struct

datatype thy_info = ThyInfo of {name: string, childs: string list, 
                                thy_info: string, ml_info: string, 
                                theory: Thm.theory};

val loaded_thys = ref [ThyInfo {name = "pure", childs = [], thy_info = "",
                       ml_info = "", theory = Thm.pure_thy}];

val loadpath = ref ["."];


(*Make name of the output ML file for a theory *)
fun out_name thy = "." ^ thy ^ ".thy.ML";

(*Read a file specified by thy_file containing theory thy *)
fun read_thy thy thy_file =
    let val instream  = open_in thy_file;
        val outstream = open_out (out_name thy)
    in  output (outstream, ThySyn.read (explode(input(instream, 999999))));
        close_out outstream;
        close_in instream
    end;

fun file_exists file =
  let val instream = open_in file in close_in instream; true end
    handle Io _ => false;

exception FILE_NOT_FOUND; (*raised by find_file *)

(*Find a file using a list of paths if no absolute or relative path is
  specified.*)
fun find_file "" name =
      let fun find_it (curr :: paths) =
                if file_exists (tack_on curr name) then
                    tack_on curr name
                else 
                    find_it paths
           | find_it [] = raise FILE_NOT_FOUND
      in find_it (!loadpath) end
  | find_file path name =
      if file_exists (tack_on path name) then tack_on path name
                                         else raise FILE_NOT_FOUND;

(*Use the file if it exists *)
fun try_use file = 
      if file_exists file then use file else ();

(*Check if a theory was already loaded *)
fun already_loaded thy =
  let fun do_search ((ThyInfo {name, ...}) :: loaded) =
              if name = thy then true else do_search loaded
        | do_search [] = false
  in do_search (!loaded_thys) end;

(*Get thy_info for a loaded theory *)
fun get_thyinfo thy =
  let fun do_search (t :: loaded : thy_info list) =
            let val ThyInfo {name, ...} = t
            in if name = thy then t else do_search loaded end
        | do_search [] = error ("Internal error (get_thyinfo): theory " 
                                ^ thy ^ " not found.")
  in do_search (!loaded_thys) end;

(*Check if a theory file has changed since its last use.
  Return a pair of boolean values for .thy and for .ML. *)
fun thy_unchanged thy thy_file ml_file = 
      if already_loaded thy then 
        let val ThyInfo {thy_info, ml_info, ...} = get_thyinfo thy;
        in ((file_info (thy_file) = thy_info), (file_info (ml_file) = ml_info))
        end
      else (false, false);

(*Get theory object for a loaded theory *)
fun get_theory name =
  let val ThyInfo {theory, ...} = get_thyinfo name
  in theory end;

(*Read .thy and .ML files that haven't been read yet or have changed since 
  they were last read;
  loaded_thys is a thy_info list ref containing all theories that have 
  completly been read by this and preceeding use_thy calls.
  If a theory changed since its last use its childs are marked as changed *)
fun use_thy name =
    let val (path, thy_name) = split_filename name;
        val thy = to_lower thy_name;
        val thy_file = (find_file path (thy ^ ".thy")
                        handle FILE_NOT_FOUND => "");
        val (thy_path, _) = split_filename thy_file;
        val ml_file = if thy_file = ""
                      then (find_file path (thy ^ ".ML")
                            handle FILE_NOT_FOUND => 
                             error ("Could find no .thy or .ML file for theory "
                                    ^ thy_name))
                      else if file_exists (thy_path ^ thy ^ ".ML")
                      then thy_path ^ thy ^ ".ML"
                      else ""
        val (thy_uptodate, ml_uptodate) = thy_unchanged thy thy_file ml_file;

        (*Remove theory from all child lists in loaded_thys.
          Afterwards add_child should be called for the (new) base theories *)
        fun remove_child thy =
          let fun do_remove (ThyInfo {name, childs, thy_info, ml_info, theory}
                            :: loaded) result =
                    do_remove loaded 
                      (ThyInfo {name = name, childs = childs \ thy, 
                                thy_info = thy_info, ml_info = ml_info,
                                theory = theory} :: result)
                | do_remove [] result = result;
          in loaded_thys := do_remove (!loaded_thys) [] end;
          
         exception THY_NOT_FOUND;  (*Raised by set_info *)

         (*Change thy_info and ml_info for an existent item or create
           a new item with empty child list *)
         fun set_info thy_new ml_new thy =
               let fun make_change (t :: loaded) =
                         let val ThyInfo {name, childs, theory, ...} = t
                         in if name = thy then            
                              ThyInfo {name = name, childs = childs,
                                       thy_info = thy_new, ml_info = ml_new,
                                       theory = theory} :: loaded
                            else
                              t :: (make_change loaded)
                         end
                     | make_change [] = raise THY_NOT_FOUND
               in loaded_thys := make_change (!loaded_thys) end;

         (*Mark all direct and indirect descendants of a theory as changed *)
         fun mark_childs thy =
           let val ThyInfo {childs, ...} = get_thyinfo thy
           in writeln ("Marking childs of modified theory " ^ thy ^ " (" ^
                       (space_implode "," childs) ^ ")");
              seq (set_info "" "") childs
              handle THY_NOT_FOUND => ()
                        (*If this theory was automatically loaded by a child 
                          then the child cannot be found in loaded_thys *)
           end

    in if thy_uptodate andalso ml_uptodate then ()
       else
       (
         writeln ("Loading theory " ^ name);
         if thy_uptodate orelse (thy_file = "") then ()
         else
         (
             (*Allow dependency lists to be rebuild completely *)
             remove_child thy;
                
             read_thy thy thy_file
         );
         
         (*Actually read files!*)
         if thy_uptodate orelse (thy_file = "") then ()
                         else use (out_name thy);
         if (thy_file = "") then          (*theory object created in .ML file*)
             (
                 use ml_file;
                 let val outstream = open_out (".tmp.ML") 
                 in
                    output (outstream, "store_theory " ^ quote thy_name ^ " "
                                       ^ thy_name ^ ".thy;\n");
                    close_out outstream 
                 end;
                 use ".tmp.ML";
                 delete_file ".tmp.ML"
             )
         else try_use ml_file;

         (*Now set the correct info.*)
         (set_info (file_info thy_file) (file_info ml_file) thy
          handle THY_NOT_FOUND => error ("Could not find theory \"" ^ thy
                                         ^ "\" (wrong filename?)"));

         (*Mark theories that have to be reloaded.*)
         mark_childs thy;

         delete_file (out_name thy)
       )
    end;

fun time_use_thy tname = timeit(fn()=>
   (writeln("\n**** Starting Theory " ^ tname ^ " ****");  
    use_thy tname;
    writeln("\n**** Finished Theory " ^ tname ^ " ****"))
   );

(*Load all thy or ML files that have been changed and also
  all theories that depend on them *)
fun update () =
  let (*List theories in the order they have to be loaded *)
      fun load_order [] result = result
        | load_order thys result =
            let fun next_level (t :: ts) =
                      let val ThyInfo {childs, ...} = get_thyinfo t
                      in childs union (next_level ts)
                      end
                  | next_level [] = [];
                  
                val childs = next_level thys
            in load_order childs ((result \\ childs) @ childs) end;

      fun reload_changed (t :: ts) =
            let val curr = get_thyinfo t;
                val thy_file = (find_file "" (t ^ ".thy")
                                handle FILE_NOT_FOUND => "");
                val (thy_path, _) = split_filename thy_file;
                val ml_file = if thy_file = ""
                              then (find_file "" (t ^ ".ML")
                                    handle FILE_NOT_FOUND => 
                             error ("Could find no .thy or .ML file for theory "
                                    ^ t))
                              else if file_exists (thy_path ^ t ^ ".ML")
                              then thy_path ^ t ^ ".ML"
                              else ""
                val (thy_uptodate, ml_uptodate) =
                      thy_unchanged t thy_file ml_file;
 
            in if thy_uptodate andalso ml_uptodate then ()
                                                   else use_thy t;
               reload_changed ts
            end
        | reload_changed [] = ()
  in reload_changed (load_order ["pure"] []) end;

(*Merge theories to build a base for a new theory.
  Base members are only loaded if they are missing. *)
fun base_on (t :: ts) child =
      let val childl = to_lower child;

          fun load_base base =
              let val basel = to_lower base;

                  (*List all descendants of a theory list *)
                  fun list_descendants (t :: ts) =
                        if already_loaded t then
                          let val ThyInfo {childs, ...} = get_thyinfo t
                          in childs union (list_descendants (ts union childs))
                          end
                        else []
                    | list_descendants [] = [];
 
                  (*Show the cycle that would be created by add_child *)
                  fun show_cycle () =
                    let fun find_it result curr =
                          if basel = curr then 
                              error ("Cyclic dependency of theories: "
                                     ^ childl ^ "->" ^ basel ^ result)
                          else if already_loaded curr then
                            let val ThyInfo {childs, ...} = get_thyinfo curr
                            in seq (find_it ("->" ^ curr ^ result)) childs
                            end
                          else ()
                    in find_it "" childl end;

                  (*Check if a cycle will be created by add_child *)
                  fun find_cycle () =
                    if basel mem (list_descendants [childl]) then show_cycle ()
                    else ();
                   
                  (*Add child to child list of base *)
                  fun add_child (t :: loaded) =
                        let val ThyInfo {name, childs, thy_info, ml_info, 
                                         theory} = t
                        in if name = basel then
                             ThyInfo {name = name, childs = childl ins childs,
                                      thy_info = thy_info, ml_info = ml_info,
                                      theory = theory} :: loaded
                           else
                             t :: (add_child loaded)
                        end
                   | add_child [] =
                       [ThyInfo {name = basel, childs = [childl], 
                                 thy_info = "", ml_info = "",
                                 theory = Thm.pure_thy}];
                                         (*Thm.pure_thy is used as a dummy *)

                  val thy_there = already_loaded basel
                                            (*test this before child is added *)
              in
                if childl = basel then
                    error ("Cyclic dependency of theories: " ^ child
                           ^ "->" ^ child)
                else find_cycle ();
                loaded_thys := add_child (!loaded_thys);
                if thy_there then ()
                else (writeln ("Autoloading theory " ^ base
                               ^ " (used by " ^ child ^ ")");
                      use_thy base
                     )
              end;
              
          val (tl :: tls) = map to_lower (t :: ts)
     in seq load_base (t :: ts);
        foldl Thm.merge_theories (get_theory tl, map get_theory tls)
     end
  | base_on [] _ = raise Match;

(*Change theory object for an existent item of loaded_thys 
  or create a new item *)
fun store_theory thy_name thy =
  let fun make_change (t :: loaded) =
            let val ThyInfo {name, childs, thy_info, ml_info, ...} = t
            in if name = (to_lower thy_name) then            
                    ThyInfo {name = name, childs = childs,
                             thy_info = thy_info, ml_info = ml_info,
                             theory = thy} :: loaded
               else
                    t :: (make_change loaded)
            end
        | make_change [] =
            [ThyInfo {name = (to_lower thy_name), childs = [], thy_info = "", 
                      ml_info = "", theory = thy}]
  in loaded_thys := make_change (!loaded_thys) end;

(*Create a list of all theories loaded by this structure *)
fun list_loaded () = (!loaded_thys);

(*Change the list of loaded theories *)
fun set_loaded [] =
      loaded_thys := [ThyInfo {name = "pure", childs = [], thy_info = "",
                      ml_info = "", theory = Thm.pure_thy}]
  | set_loaded ts =
      loaded_thys := ts;

(*Change the path list that is to be searched for .thy and .ML files *)
fun set_loadpath new_path =
  loadpath := new_path;

(*This function is for debugging purposes only *)
fun relations thy =
  let val ThyInfo {childs, ...} = get_thyinfo thy
  in
     writeln (thy ^ ": " ^ (space_implode ", " childs));
     seq relations childs
  end

end;

