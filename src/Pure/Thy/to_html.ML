(*  ID:         $Id$
    Author:	Mateja Jamnik, University of Cambridge
    Copyright   1995  University of Cambridge

   Convert the Isabelle theory files to .html format for hypertext browsing
*)

val htmlpath = "/homes/lcp/html_isa/";

(* --------------------
   Exception declaration in case that there is a lexical
   error occurs.
   -------------------- *)

exception lex_err;

(* --------------------
   Get the list of all the theory files and the
   path to access them in their directories
   -------------------- *)

print_depth 1000;
val theory_list = !loaded_thys;
val files = Symtab.alist_of (theory_list);

(* --------------------
   The function move_eachf is going to move all the theory
   files in isabelle to their html format. It takes 
   for arguments the name of the theory (tname) and
   other theory information such as path (path), theorems (thms)
   proved, ... It is the main driver of the program, and basically
   contains all other functions. It contains the following
   subfunctions:
     - create_pure
     - gettext
     - move_onef
     - transform
   -------------------- *)

fun move_eachf (tname, ThyInfo{path,thms,...}) =
    let val intext = path^tname^".thy";
	val outtext = htmlpath^tname^".html";
	    
(* --------------------
   The function gettext takes an instrem from the auxilliary 
   file .thy whose name and path are specified in the existent
   Isabelle structure, treats the inputted string with all the
   necessary modifications for html format and puts it into the
   file with the same name but .html extension. The subfunctions
   it contains are:
      - after_first_c
      - filter
      - first_comment
      - format_link
      - getstring
      - get_word
      - he
      - html
      - html_escape
      - insert_link
      - leading_comment
      - lc_exists
      - modify_body
      - remove_lc
      - rest
      - thy_name
   -------------------- *)

	fun gettext is  =
	    let 
		val head = "<HTML>\n<HEAD>\n<TITLE>"^intext^
		    "</TITLE>\n</HEAD>\n\n"^"<BODY>\n";
		val title = "<H1>"^tname^".thy"^"</H1></P>\n\n"^
		    "<BR>\n<A HREF = \""^htmlpath^
		    "00-chart.html\">Dependency Chart</A>\n"^
		    ": display of dependencies between the theories.\n"^
		    "<BR>\n<HR>\n\n<PRE>\n";
		val tail = "</PRE>"^"</BODY>\n"^"</HTML>";
		

	     (* --------------------
		The function he (html escape) is going to take
		every single characterof the input stream and check
		for ">", "<" and "&" characters that have a special
		meaning in html and convert them into their corresponding
		escape sequences.   
		-------------------- *)
		fun he [] r = r
		  | he ("<"::sl) r = he sl (r@["&","l","t"])
		  | he (">"::sl) r = he sl (r@["&","g","t"])
		  | he ("&"::sl) r = he sl (r@["&","a","m","p"])
		  | he (c::sl) r = he sl (r@[c]);

		fun html_escape sl = he sl [];

	     (* --------------------
		The function first_comment is a pattern checking for
		nested comments. The argument d will keep track of how
		deep we are in the nested comment. The function will
		return the first comment extracted from the input stream,
		so that we can copy it into the output stream. Lexical
		error is raised if we open an empty file to read from.
		-------------------- *)
		fun first_comment ("*"::")"::cs) co 1 = co@["*",")"]
		  | first_comment ("*"::")"::cs) co d =
		    first_comment cs (co@["*",")"]) (d-1)
		  | first_comment ("("::"*"::cs) co d =
		    first_comment cs (co@["(","*"]) (d+1)
		  | first_comment (c::cs) co d =
		    if d>0 then first_comment cs (co@[c]) d
		    else first_comment cs co d
		  | first_comment [] _ _ = raise lex_err;
		    
	     (* --------------------
	        The function lc_exists leading comment exists?)
		checks whether in the input file at the very beginning
		there is a comment, which needs to be extracted and put
		into the output file. We also need to check whether there
		might be a space, a new line or a tab, which do not
		exclude the possibility that there is a leading comment.
		The function returns a boolean value. 
		-------------------- *)
		fun lc_exists ("("::"*"::_) = true
		  | lc_exists (" "::cs) = lc_exists cs
		  | lc_exists ("\n"::cs) = lc_exists cs
		  | lc_exists ("\t"::cs) = lc_exists cs
		  | lc_exists _ = false;
		    
	     (* --------------------
	        In the case that there is a leading comment, this
		function leading_comment extracts it> It also need
		to check for any html escape sequences in the comment.
		-------------------- *)
		fun leading_comment sl =
		    if (lc_exists sl) then
			(html_escape (first_comment sl [] 0))
		    else
			[""];
			
	     (* --------------------
	        The function thy_name checks for the parent theory
		names apearing after the leading comment. The function
		returns a boolean value indicating if the word is a
		theory name, so that a link can be inserted and can look
		for another potential theory name. If the word is not a
		theory name then continue to modify the rest of the body.
		-------------------- *)
		fun thy_name word = 
		    is_some (Symtab.lookup (theory_list, word));
		    
	     (* --------------------
	        Creates the right html format when inserting the link.
		-------------------- *)
		fun format_link s = 
		    let in
			output(std_out,"\n"^s);
			"<A HREF = \""^htmlpath^s^".html\">"^s^"</A>"
		    end;

	     (* --------------------
		-------------------- *)

		fun insert_link w = (explode (format_link (implode w)))
	     (* --------------------
		-------------------- *)

		fun html ( " "::l) r = html l (r@[ " "])
		  | html ( "+"::l) r = html l (r@[ "+"])
		  | html ("\n"::l) r = html l (r@["\n"])
		  | html ("\t"::l) r = html l (r@["\t"])
		  | html l r = r@(get_word l [])
	     (* --------------------
		-------------------- *)
		and get_word ( " "::l) w = 
		    if (thy_name (implode w)) 
			then (insert_link w)@[ " "]@(html l [])
		    else w@[" "]@(html_escape l)
		  | get_word ( "+"::l) w = 
		    if (thy_name (implode w))
			then (insert_link w)@[ "+"]@(html l [])
		    else w@["+"]@(html_escape l)
		  | get_word ("\n"::l) w = 
		    if (thy_name (implode w))
			then (insert_link w)@[ "\n"]@(html l [])
		    else w@["\n"]@(html_escape l)
		  | get_word ("\t"::l) w = 
		    if (thy_name (implode w))
			then (insert_link w)@[ "\t"]@(html l [])
		    else w@["\t"]@(html_escape l)
		  | get_word (c::l) w = (get_word l (w@[c]))
		  | get_word [] [] = []
		  | get_word [] w = 
		    if (thy_name (implode w))
			then (insert_link w)
		    else w;
			
	     (* --------------------
		-------------------- *)
		fun modify_body ("="::l) r = r@["="]@(html l [])
		  | modify_body (c::l) r = modify_body l (r@[c])
		  | modify_body [] r = r;
		    
	     (* --------------------
		-------------------- *)
		fun after_first_c ("*"::")"::cs) 1 = cs
		  | after_first_c ("*"::")"::cs) d = after_first_c cs (d-1)
		  | after_first_c ("("::"*"::cs) d = after_first_c cs (d+1)
		  | after_first_c (c::cs) d = after_first_c cs d
		  | after_first_c cs 0 = cs
		  | after_first_c [] _ = raise lex_err;
		    
	     (* --------------------
		-------------------- *)
		fun remove_lc sl =
		    if (lc_exists sl) then (after_first_c sl 0) else sl;
			
	     (* --------------------
		-------------------- *)
		fun rest sl = modify_body (remove_lc sl) [];
		    
	     (* --------------------
		-------------------- *)
		fun filter sl = (leading_comment sl) @ (rest sl);
		    
	     (* --------------------
		-------------------- *)
		fun getstring s =
		    case input (is, 1) of
			"" => head^title^(implode(filter(explode(s))))^tail
		      | "\n" => getstring (s^"\n")
		      | c  => getstring (s^c)
	    in
		getstring ""
	    end;

     (* --------------------
      	-------------------- *)
	fun transform t =
	    let
		val infile = open_in intext;
		val outfile = open_out outtext
	    in
		output(std_out,"\nTheory: "^t);
		output (outfile, gettext(infile));
		close_in (infile);
		close_out (outfile)
	    end;

     (* --------------------
      	-------------------- *)
	fun create_pure p =
	    let
		val outfile = open_out outtext
	    in
		output(std_out, "\nCreating Pure.html ...");
		output (outfile, "<HTML>\n<HEAD>\n<TITLE>"^intext^
			"</TITLE>\n</HEAD>\n\n"^"<BODY>\n"^
			"<H1>"^tname^".thy"^"</H1></P>\n\n"^"<PRE>\n"^
			"This is a theory file called Pure.\n"^
			"Its children are all other Isabelle theories."^
			"</PRE>"^"</BODY>\n"^"</HTML>");
		close_out (outfile)
	    end
	
    in
	if (tname <> "Pure") then (transform tname)
	else (create_pure tname)
    end;

(* --------------------
   -------------------- *)
map move_eachf (files);

