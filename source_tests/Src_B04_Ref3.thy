theory Src_B04_Ref3
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>EA Contract\<close>

contract EA
  for "STR ''log''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction hook
where
  "(assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 5)))" ,

cfunction f
where
  "(do {
      assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 1));
      (icall hook)
    })"

end
