(*  Title:      HOL/Auth/DB-ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Root file for creating a **separate database** for protocol proofs.
             ** Use ROOT.ML to simply run the proofs. **
*)

HOL_build_completed;    (*Make examples fail if HOL did*)

val banner = "Security Protocols";
writeln banner;

init_thy_reader();

use_thy "Message";

