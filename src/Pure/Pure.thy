(*  Title:      Pure/Pure.thy
    ID:         $Id$
    Author:     Larry Paulson and Makarius

The Pure theory.
*)

theory Pure
imports ProtoPure
begin

setup "Context.setup ()"


text{*These meta-level elimination rules facilitate the use of assumptions
that contain !! and ==>, especially in linear scripts. *}

lemma meta_mp:
  assumes major: "PROP P ==> PROP Q" and minor: "PROP P"
  shows "PROP Q"
    by (rule major [OF minor])

lemma meta_spec:
  assumes major: "!!x. PROP P(x)"
  shows "PROP P(x)"
    by (rule major)

lemmas meta_allE = meta_spec [elim_format]

end
