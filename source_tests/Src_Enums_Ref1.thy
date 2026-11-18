theory Src_Enums_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Enums Contract\<close>

contract Enums
  for "STR ''state''" : "SType.TValue TSint"
  and "STR ''level''" : "SType.TValue TSint"
  and "STR ''stateOf''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"
  and "STR ''counts''" : "SType.TMap (SType.TValue TSint) (SType.TValue TSint)"
  and "STR ''price''" : "SType.TValue TSint"
  and "STR ''tag''" : "SType.TValue (TBytes 32)"
  and "STR ''steps''" : "SType.TValue TSint"
  and "STR ''job''" : "SType.TEnum [SType.TValue TSint, SType.TValue TSint, SType.TValue TSint]"

constructor
where
  "(value_guard)"

cfunction start external
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad (storeLookup (STR ''state'') []) (sint_monad 0)));
      assign_storage_monad (STR ''state'') [] (sint_monad 1);
      assign_storage_monad (STR ''stateOf'') [sender_monad] (sint_monad 1);
      assign_storage_monad (STR ''counts'') [(sint_monad 1)] (plus_monad_safe (storeLookup (STR ''counts'') [(sint_monad 1)]) (sint_monad 1))
    })
    })" ,

cfunction finish external
param "STR ''ok''" : "SType.TValue TBool"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad (storeLookup (STR ''state'') []) (sint_monad 1)));
      assign_storage_monad (STR ''state'') [] (cond_monad (stackLookup (STR ''ok'') []) (sint_monad 2) (sint_monad 3));
      assign_storage_monad (STR ''counts'') [(storeLookup (STR ''state'') [])] (plus_monad_safe (storeLookup (STR ''counts'') [(storeLookup (STR ''state'') [])]) (sint_monad 1))
    })
    })" ,

cfunction setLevel external
param "STR ''l''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''l'') []) (sint_monad 3));
      (do {
      assign_storage_monad (STR ''level'') [] (stackLookup (STR ''l'') []);
      (cond_monad (equals_monad (stackLookup (STR ''l'') []) (sint_monad 2)) (assign_storage_monad (STR ''steps'') [] (plus_monad_safe (storeLookup (STR ''steps'') []) (sint_monad 10))) ((cond_monad (not_monad (less_monad (stackLookup (STR ''l'') []) (sint_monad 1))) (assign_storage_monad (STR ''steps'') [] (plus_monad_safe (storeLookup (STR ''steps'') []) (sint_monad 5))) skip_monad)))
    })
    })
    })" ,

cfunction setState external
param "STR ''s''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''s'') []) (sint_monad 4));
      (do {
      assign_storage_monad (STR ''state'') [] (stackLookup (STR ''s'') []);
      assign_storage_monad (STR ''stateOf'') [sender_monad] (stackLookup (STR ''s'') [])
    })
    })
    })" ,

cfunction fromNumber external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''state'') [] (below_monad (stackLookup (STR ''x'') []) (sint_monad 4)))
    })" ,

cfunction toNumber external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''steps'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''state'') []) (sint_monad 100)) (storeLookup (STR ''level'') [])))
    })" ,

cfunction levelFromNumber external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (do {
      assign_storage_monad (STR ''level'') [] (below_monad (stackLookup (STR ''x'') []) (sint_monad 3));
      assign_storage_monad (STR ''job'') [(sint_monad 1)] (storeLookup (STR ''level'') []);
      assign_storage_monad (STR ''job'') [(sint_monad 0)] (sint_monad 2);
      assign_storage_monad (STR ''job'') [(sint_monad 2)] (stackLookup (STR ''x'') [])
    })
    })
    })" ,

cfunction setPrice external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''price'') [] (stackLookup (STR ''p'') []))
    })" ,

cfunction bump external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''price'') [] (plus_monad_safe (storeLookup (STR ''price'') []) (sint_monad 1)))
    })" ,

cfunction setTag external
param "STR ''t''" : "SType.TValue (TBytes 32)"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''tag'') [] (stackLookup (STR ''t'') []))
    })" ,

cfunction tagIs external
param "STR ''t''" : "SType.TValue (TBytes 32)"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad (storeLookup (STR ''tag'') []) (stackLookup (STR ''t'') [])));
      assign_storage_monad (STR ''steps'') [] (plus_monad_safe (storeLookup (STR ''steps'') []) (sint_monad 1))
    })
    })" ,

cfunction reset external
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''state'') [] (sint_monad 0);
      assign_storage_monad (STR ''steps'') [] (sint_monad 0);
      assign_storage_monad (STR ''job'') [(sint_monad 0)] (sint_monad 0)
    })
    })"

end
