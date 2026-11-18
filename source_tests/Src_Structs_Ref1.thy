theory Src_Structs_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Structs Contract\<close>

contract Structs
  for "STR ''p''" : "SType.TEnum [SType.TValue TAddress, SType.TValue TSint, SType.TValue TBool]"
  and "STR ''book''" : "SType.TMap (SType.TValue TSint) (SType.TEnum [SType.TValue TAddress, SType.TValue TSint, SType.TValue TBool])"
  and "STR ''o''" : "SType.TEnum [SType.TValue TSint, SType.TEnum [SType.TValue TSint, SType.TValue TSint, SType.TValue TBool], SType.TMap (SType.TValue TAddress) (SType.TValue TSint), SType.TValue TSint]"
  and "STR ''users''" : "SType.TMap (SType.TValue TAddress) (SType.TEnum [SType.TValue TSint, SType.TEnum [SType.TValue TSint, SType.TValue TSint, SType.TValue TBool], SType.TMap (SType.TValue TAddress) (SType.TValue TSint), SType.TValue TSint])"
  and "STR ''byAmount''" : "SType.TMap (SType.TValue TSint) (SType.TValue TSint)"
  and "STR ''n''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction f1 external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 1)] (plus_monad_safe (storeLookup (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 1)]) (sint_monad 5));
      assign_storage_monad (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 2)] true_monad
    })
    })" ,

cfunction f2 external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      sdecl (SType.TEnum [SType.TValue TAddress, SType.TValue TSint, SType.TValue TBool]) (STR ''q'');
      assign_stack_monad (STR ''q'') [] (storeLookup (STR ''book'') [(stackLookup (STR ''k'') [])]);
      assign_stack_monad (STR ''q'') [(sint_monad 0)] sender_monad;
      assign_stack_monad (STR ''q'') [(sint_monad 1)] (plus_monad_safe (stackLookup (STR ''q'') [(sint_monad 1)]) (sint_monad 1))
    })
    })" ,

cfunction f3 external
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''o'') [(sint_monad 1), (sint_monad 0)] (sint_monad 7);
      assign_storage_monad (STR ''o'') [(sint_monad 1), (sint_monad 1)] (sint_monad 3);
      assign_storage_monad (STR ''o'') [(sint_monad 2), sender_monad] (sint_monad 9);
      assign_storage_monad (STR ''users'') [sender_monad, (sint_monad 1), (sint_monad 0)] (plus_monad_safe (storeLookup (STR ''users'') [sender_monad, (sint_monad 1), (sint_monad 0)]) (sint_monad 1))
    })
    })" ,

cfunction f4 external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''n'') [] (storeLookup (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 1)]))
    })" ,

cfunction f5 external
param "STR ''k''" : "SType.TValue TSint"
and "STR ''j''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''book'') [(stackLookup (STR ''k'') [])] (storeLookup (STR ''book'') [(stackLookup (STR ''j'') [])]))
    })" ,

cfunction f6 external
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''p'') [(sint_monad 0)] sender_monad;
      assign_storage_monad (STR ''p'') [(sint_monad 1)] (sint_monad 100);
      assign_storage_monad (STR ''p'') [(sint_monad 2)] (not_monad (storeLookup (STR ''p'') [(sint_monad 2)]))
    })
    })" ,

cfunction f7 external
where
  "(do {
      value_guard;
      (do {
      sdecl (SType.TEnum [SType.TValue TSint, SType.TValue TSint, SType.TValue TBool]) (STR ''i'');
      assign_stack_monad (STR ''i'') [] (storeLookup (STR ''o'') [(sint_monad 1)]);
      assign_stack_monad (STR ''i'') [(sint_monad 0)] (sint_monad 11);
      assign_stack_monad (STR ''i'') [(sint_monad 1)] (below_monad (plus_monad_safe (stackLookup (STR ''i'') [(sint_monad 1)]) (sint_monad 1)) (sint_monad 256));
      assign_stack_monad (STR ''i'') [(sint_monad 2)] true_monad
    })
    })" ,

cfunction f8 external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (do {
      sdecl (SType.TEnum [SType.TValue TSint, SType.TEnum [SType.TValue TSint, SType.TValue TSint, SType.TValue TBool], SType.TMap (SType.TValue TAddress) (SType.TValue TSint), SType.TValue TSint]) (STR ''u'');
      assign_stack_monad (STR ''u'') [] (storeLookup (STR ''users'') [(stackLookup (STR ''a'') [])]);
      assign_stack_monad (STR ''u'') [(sint_monad 0)] (sint_monad 5);
      assign_stack_monad (STR ''u'') [(sint_monad 2), sender_monad] (plus_monad_safe (stackLookup (STR ''u'') [(sint_monad 2), sender_monad]) (sint_monad 2));
      assign_stack_monad (STR ''u'') [(sint_monad 3)] (sint_monad 200)
    })
    })" ,

cfunction f9 external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''o'') [(sint_monad 3)] (below_monad (plus_monad_safe (storeLookup (STR ''o'') [(sint_monad 3)]) (sint_monad 100)) (sint_monad 256)))
    })" ,

cfunction f10 external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (storeLookup (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 2)]));
      assign_storage_monad (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 2)] false_monad
    })
    })" ,

cfunction f11 external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''byAmount'') [(storeLookup (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 1)])] (stackLookup (STR ''k'') []))
    })" ,

cfunction f12 external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''n'') [] (cond_monad (storeLookup (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 2)]) (storeLookup (STR ''book'') [(stackLookup (STR ''k'') []), (sint_monad 1)]) (sint_monad 1)))
    })" ,

cfunction f13 external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''users'') [(stackLookup (STR ''a'') []), (sint_monad 1)] (storeLookup (STR ''o'') [(sint_monad 1)]))
    })" ,

cfunction f14 external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      sdecl (SType.TEnum [SType.TValue TAddress, SType.TValue TSint, SType.TValue TBool]) (STR ''q'');
      assign_stack_monad (STR ''q'') [] (storeLookup (STR ''book'') [(stackLookup (STR ''k'') [])]);
      sdecl (SType.TEnum [SType.TValue TAddress, SType.TValue TSint, SType.TValue TBool]) (STR ''r'');
      assign_stack_monad (STR ''r'') [] (storeLookup (STR ''book'') [(plus_monad_safe (stackLookup (STR ''k'') []) (sint_monad 1))]);
      assign_stack_monad (STR ''r'') [(sint_monad 1)] (stackLookup (STR ''q'') [(sint_monad 1)]);
      assign_stack_monad (STR ''q'') [(sint_monad 1)] (sint_monad 0)
    })
    })"

end
