theory Src_Fallback_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>FbBase Contract\<close>

contract FbBase
  for "STR ''hits''" : "SType.TValue TSint"

constructor
where
  "skip_monad"

cfunction fallback external payable
where
  "(assign_storage_monad (STR ''hits'') [] (plus_monad_safe (storeLookup (STR ''hits'') []) (sint_monad 1)))"

section \<open>FbDerived Contract\<close>

contract FbDerived is FbBase
  for "STR ''extra''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction fallback external payable
where
  "(do {
      assign_storage_monad (STR ''hits'') [] (plus_monad_safe (storeLookup (STR ''hits'') []) (sint_monad 10));
      assign_storage_monad (STR ''extra'') [] (plus_monad_safe (storeLookup (STR ''extra'') []) (sint_monad 1))
    })" ,

cfunction bump external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''extra'') [] (plus_monad_safe (storeLookup (STR ''extra'') []) (sint_monad 5)))
    })"

end
