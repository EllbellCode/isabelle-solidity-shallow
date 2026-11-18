theory Src_CtorCalls_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>CtorCalls Contract\<close>

contract CtorCalls
  for "STR ''owner''" : "SType.TValue TAddress"
  and "STR ''total''" : "SType.TValue TSint"
  and "STR ''base''" : "SType.TValue TSint"
  and "STR ''bal''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor
param "STR ''supply''" : "SType.TValue TSint"
and "STR ''first''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''base'') [] (do {
      a0 <- (sint_monad 3);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (scale w0))
    });
      (do {
      (do {
      a0 <- sender_monad;
      b0 <- readValue a0;
      w0 <- readAddress b0;
      (icall (setOwner w0))
    });
      (do {
      a0 <- sender_monad;
      b0 <- readValue a0;
      w0 <- readAddress b0;
      a1 <- (do {
      a0 <- (stackLookup (STR ''supply'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (scale w0))
    });
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (mint w0 w1))
    });
      (do {
      a0 <- (stackLookup (STR ''first'') []);
      b0 <- readValue a0;
      w0 <- readAddress b0;
      a1 <- (do {
      a0 <- (stackLookup (STR ''supply'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (checked w0))
    });
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (mint w0 w1))
    })
    })
    })
    })"

cfunction setOwner
param "STR ''o''" : "SType.TValue TAddress"
where
  "(assign_storage_monad (STR ''owner'') [] (stackLookup (STR ''o'') []))" ,

cfunction scale
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((mult_monad_safe (stackLookup (STR ''v'') []) (sint_monad 10)))
    })" ,

cfunction mint
param "STR ''to''" : "SType.TValue TAddress"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''v'') []));
      assign_storage_monad (STR ''bal'') [(stackLookup (STR ''to'') [])] (plus_monad_safe (storeLookup (STR ''bal'') [(stackLookup (STR ''to'') [])]) (stackLookup (STR ''v'') []))
    })" ,

cfunction checked
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      (do {
      (assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 1000)));
      (stackLookup (STR ''v'') [])
    })
    })" ,

cfunction again external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((do {
      a0 <- sender_monad;
      b0 <- readValue a0;
      w0 <- readAddress b0;
      a1 <- (stackLookup (STR ''v'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (mint w0 w1))
    }))
    })" ,

cfunction transferOwner external
param "STR ''o''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad sender_monad (storeLookup (STR ''owner'') [])));
      (do {
      a0 <- (stackLookup (STR ''o'') []);
      b0 <- readValue a0;
      w0 <- readAddress b0;
      (icall (setOwner w0))
    })
    })
    })"

end
