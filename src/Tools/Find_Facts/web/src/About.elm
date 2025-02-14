{- Author: Fabian Huch, TU München

Find Facts about page.
-}
module About exposing (view)


import Html exposing (..)
import Html.Attributes exposing (href)
import Material.Typography as Typography


{- about -}

view_def name def = [dt [] [text name], dd [] [text def]]
defs =
  view_def "Terms" "are words and Isabelle symbols separated by space, with wildcards and phrases." ++
  view_def "Isabelle symbols" "can be entered as ascii, abbreviation (if unique) or UTF-8 symbol." ++
  view_def "Wildcards" "consist of ?/* inside a term and match a single/arbitrary many characters." ++
  view_def "Phrases" "are delimited by \" quotes and match a term sequence (no wildcards) exactly." ++
  view_def "Main search bar" "will look for any of your terms in source code and names." ++
  view_def "Filters" "allow you to exclude/include (click on the symbol) specific properties." ++
  view_def "Drill-down" "allows you to multi-select once your result set is small enough."

view: Html Never
view =
  div [] [
    h2 [Typography.headline4] [text "About"],
    p [Typography.body1] [
      text "This is a search engine for ",
      a [href "https://isabelle.in.tum.de"] [text "Isabelle"],
      text "."],
    p [Typography.body1] [
      text "Enter terms in the main search bar, add/remove filters, or drill down."],
    p [Typography.body1] [text "You can also click on results to find out more about them!"],
    p [Typography.body1] [dl [] defs]]
