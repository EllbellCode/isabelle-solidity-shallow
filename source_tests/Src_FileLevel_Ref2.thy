theory Src_FileLevel_Ref2
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Other Contract\<close>

contract Other
  for "STR ''x''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction clamp
param "STR ''x''" : "SType.TValue TSint"
and "STR ''hi''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((cond_monad (less_monad (stackLookup (STR ''hi'') []) (stackLookup (STR ''x'') [])) ((stackLookup (STR ''hi'') [])) ((stackLookup (STR ''x'') []))))
    })" ,

cfunction f external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (stackLookup (STR ''v'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (sint_monad 100);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (clamp w0 w1))
    }))
    })"

end
