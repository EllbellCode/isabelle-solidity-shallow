theory Src_Fallback_Ref2
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Fb Contract\<close>

contract Fb
  for "STR ''hits''" : "SType.TValue TSint"
  and "STR ''last''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction fallback external payable
where
  "(do {
      assign_storage_monad (STR ''hits'') [] (plus_monad_safe (storeLookup (STR ''hits'') []) (sint_monad 1));
      assign_storage_monad (STR ''last'') [] value_monad
    })" ,

cfunction set external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''last'') [] (stackLookup (STR ''v'') []))
    })"

end
