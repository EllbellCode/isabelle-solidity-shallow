theory Src_FileLevel_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>FileLevel Contract\<close>

contract FileLevel
  for "STR ''total''" : "SType.TValue TSint"
  and "STR ''narrow''" : "SType.TValue TSint"
  and "STR ''seen''" : "SType.TValue (TBytes 32)"

constructor
where
  "(value_guard)"

cfunction twice
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((mult_monad_safe (stackLookup (STR ''x'') []) (sint_monad 2)))
    })" ,

cfunction clamp
param "STR ''x''" : "SType.TValue TSint"
and "STR ''hi''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((cond_monad (less_monad (stackLookup (STR ''hi'') []) (stackLookup (STR ''x'') [])) ((stackLookup (STR ''hi'') [])) ((stackLookup (STR ''x'') []))))
    })" ,

cfunction plusSmall
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((plus_monad_safe (do {
      a0 <- (stackLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (twice w0))
    }) (sint_monad 7)))
    })" ,

cfunction add external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (not_monad (less_monad (sint_monad 100) (stackLookup (STR ''v'') []))));
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (plus_monad_safe (stackLookup (STR ''v'') []) (sint_monad 7)))
    })
    })" ,

cfunction dbl external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (do {
      a0 <- (stackLookup (STR ''v'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (twice w0))
    }))
    })" ,

cfunction cl external
param "STR ''v''" : "SType.TValue TSint"
and "STR ''hi''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (do {
      a0 <- (stackLookup (STR ''v'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''hi'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (clamp w0 w1))
    }))
    })" ,

cfunction ps external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (do {
      a0 <- (stackLookup (STR ''v'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (plusSmall w0))
    }))
    })" ,

cfunction nar external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 256));
      (assign_storage_monad (STR ''narrow'') [] (below_monad (plus_monad_safe (stackLookup (STR ''v'') []) (sint_monad 7)) (sint_monad 256)))
    })
    })" ,

cfunction tag external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''seen'') [] (keccak256_monad (bytes_monad2 [CHR 0x74, CHR 0x61, CHR 0x67])))
    })"

end
