(** Grammar declaration for [Hint EResolve]. *)

open Eresolve


VERNAC COMMAND EXTEND HintEResolve
  [ "Hint" "EResolve" ne_constr_list(lc) natural_opt(n)
    ":" preident_list(bl) ] ->
  [ add_hints_eresolve lc n bl ]
| [ "Hint" "EResolve" ne_constr_list(lc) natural_opt(n) ] ->
  [ add_hints_eresolve lc n ["core"] ]
END
