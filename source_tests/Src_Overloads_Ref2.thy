theory Src_Overloads_Ref2
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

(* overload put__uint256 3f81a2c0 *)
(* overload put__uint256_bool 0118cd8f *)
(* overload put__address_uint256 7f8d53c6 *)
section \<open>Base Contract\<close>

contract Base
  for "STR ''total''" : "SType.TValue TSint"
  and "STR ''last''" : "SType.TValue TSint"
  and "STR ''flag''" : "SType.TValue TBool"

constructor
where
  "skip_monad"

cfunction u_put__uint256
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''a'') []));
      assign_storage_monad (STR ''last'') [] (sint_monad 1)
    })" ,

cfunction u_put__uint256_bool
param "STR ''a''" : "SType.TValue TSint"
and "STR ''f''" : "SType.TValue TBool"
where
  "(do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''a'') []));
      assign_storage_monad (STR ''flag'') [] (stackLookup (STR ''f'') []);
      assign_storage_monad (STR ''last'') [] (sint_monad 2)
    })" ,

cfunction u_put__address_uint256
param "STR ''to''" : "SType.TValue TAddress"
and "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''a'') []));
      assign_storage_monad (STR ''last'') [] (sint_monad 3);
      (cond_monad (equals_monad (stackLookup (STR ''to'') []) sender_monad) (assign_storage_monad (STR ''flag'') [] true_monad) skip_monad)
    })" ,

cfunction put__uint256 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (u_put__uint256 w0))
    }))
    })" ,

cfunction put__uint256_bool external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''f''" : "SType.TValue TBool"
where
  "(do {
      value_guard;
      ((do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''f'') []);
      b1 <- readValue a1;
      w1 <- readBool b1;
      (icall (u_put__uint256_bool w0 w1))
    }))
    })" ,

cfunction put__address_uint256 external
param "STR ''to''" : "SType.TValue TAddress"
and "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((do {
      a0 <- (stackLookup (STR ''to'') []);
      b0 <- readValue a0;
      w0 <- readAddress b0;
      a1 <- (stackLookup (STR ''a'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (u_put__address_uint256 w0 w1))
    }))
    })" ,

cfunction noArgs external
where
  "(do {
      value_guard;
      ((do {
      a0 <- (sint_monad 1);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (u_put__uint256 w0))
    }))
    })"

section \<open>Over Contract\<close>

contract Over is Base

constructor
where
  "(value_guard)"

cfunction u_put__address_uint256
param "STR ''to''" : "SType.TValue TAddress"
and "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (mult_monad_safe (sint_monad 2) (stackLookup (STR ''a'') [])));
      assign_storage_monad (STR ''last'') [] (sint_monad 4);
      (cond_monad (equals_monad (stackLookup (STR ''to'') []) sender_monad) (assign_storage_monad (STR ''flag'') [] false_monad) skip_monad)
    })" ,

cfunction twice external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (u_put__uint256 w0))
    });
      (do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- true_monad;
      b1 <- readValue a1;
      w1 <- readBool b1;
      (icall (u_put__uint256_bool w0 w1))
    })
    })
    })"

end
