(*  Title:      Pure/Pure.thy
    ID:         $Id$

The Pure theory.
*)

theory Pure
imports ProtoPure
begin

setup "Context.setup ()"


text{* These meta-level elimination rules facilitate the use of assumptions
  that contain !! and ==>, especially in linear scripts. *}

lemma meta_mp:
  assumes "PROP P ==> PROP Q" and "PROP P"
  shows "PROP Q"
    by (rule `PROP P ==> PROP Q` [OF `PROP P`])

lemma meta_spec:
  assumes "!!x. PROP P(x)"
  shows "PROP P(x)"
    by (rule `!!x. PROP P(x)`)

lemmas meta_allE = meta_spec [elim_format]

end
