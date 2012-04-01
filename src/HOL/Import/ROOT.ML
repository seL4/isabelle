use_thy "HOL_Light_Maps";

if getenv "HOL_LIGHT_BUNDLE" <> ""
then use_thy "HOL_Light_Import"
else ()
