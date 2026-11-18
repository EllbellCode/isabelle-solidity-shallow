theory Src_Fallback_Ref3
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Fr Contract\<close>

contract Fr
  for "STR ''hits''" : "SType.TValue TSint"
  and "STR ''last''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction receive external payable
where
  "(assign_storage_monad (STR ''last'') [] (sint_monad 1))" ,

cfunction fallback external
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''hits'') [] (plus_monad_safe (storeLookup (STR ''hits'') []) (sint_monad 1));
      assign_storage_monad (STR ''last'') [] (sint_monad 2)
    })
    })" ,

cfunction set external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''last'') [] (stackLookup (STR ''v'') []))
    })"

end
