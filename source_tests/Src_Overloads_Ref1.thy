theory Src_Overloads_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

(* overload set__uint256 60fe47b1 *)
section \<open>OvA Contract\<close>

contract OvA
  for "STR ''x''" : "SType.TValue TSint"

constructor
where
  "skip_monad"

cfunction set__uint256 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (stackLookup (STR ''a'') []))
    })" ,

cfunction u_bump__uint256
param "STR ''a''" : "SType.TValue TSint"
where
  "(assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (stackLookup (STR ''a'') [])))" ,

cfunction set__uint256__int
param "STR ''a''" : "SType.TValue TSint"
where
  "(assign_storage_monad (STR ''x'') [] (stackLookup (STR ''a'') []))"

(* overload set__uint256_uint256 1ab06ee5 *)
section \<open>OvB Contract\<close>

contract OvB is OvA

constructor
where
  "(value_guard)"

cfunction u_bump__uint256_uint256
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (mult_monad_safe (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []))))" ,

cfunction set__uint256_uint256 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''x'') [] (plus_monad_safe (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []));
      (do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''b'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (u_bump__uint256_uint256 w0 w1))
    })
    })
    })" ,

cfunction set__uint256_uint256__int
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      assign_storage_monad (STR ''x'') [] (plus_monad_safe (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []));
      (do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''b'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (u_bump__uint256_uint256 w0 w1))
    })
    })" ,

cfunction again external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (u_bump__uint256 w0))
    });
      (do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (set__uint256__int w0))
    });
      (do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (sint_monad 1);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (set__uint256_uint256__int w0 w1))
    })
    })
    })"

end
