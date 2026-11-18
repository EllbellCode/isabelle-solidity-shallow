theory Src_ModsAbbrev_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Mods Contract\<close>

contract Mods
  for "STR ''owner''" : "SType.TValue TAddress"
  and "STR ''x''" : "SType.TValue TSint"
  and "STR ''y''" : "SType.TValue TSint"
  and "STR ''counter''" : "SType.TValue TSint"
  and "STR ''locked''" : "SType.TValue TBool"

constructor payable
where
  "(do {
      (do {
      assign_storage_monad (STR ''y'') [] (sint_monad 7);
      (do {
      assign_storage_monad (STR ''owner'') [] sender_monad;
      assign_storage_monad (STR ''x'') [] (storeLookup (STR ''y'') [])
    });
      assign_storage_monad (STR ''y'') [] (plus_monad_safe (storeLookup (STR ''y'') []) (sint_monad 1))
    })
    })"

cfunction setX external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (equals_monad sender_monad (storeLookup (STR ''owner'') [])));
      (assign_storage_monad (STR ''x'') [] (stackLookup (STR ''v'') []))
    })
    })
    })" ,

cfunction f external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''_m2_v'');
      assign_stack_monad (STR ''_m2_v'') [] (stackLookup (STR ''v'') []);
      (do {
      (assert_monad (not_monad (less_monad (storeLookup (STR ''x'') []) (stackLookup (STR ''_m2_v'') []))));
      (do {
      (do {
      assign_storage_monad (STR ''counter'') [] (plus_monad_safe (storeLookup (STR ''counter'') []) (sint_monad 1));
      (assign_storage_monad (STR ''y'') [] (stackLookup (STR ''v'') []));
      assign_storage_monad (STR ''counter'') [] (plus_monad_safe (storeLookup (STR ''counter'') []) (sint_monad 10))
    })
    })
    })
    })
    })" ,

cfunction g external
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (equals_monad sender_monad (storeLookup (STR ''owner'') [])));
      (do {
      (do {
      (assert_monad (not_monad (storeLookup (STR ''locked'') [])));
      assign_storage_monad (STR ''locked'') [] true_monad;
      (do {
      (do {
      assign_storage_monad (STR ''counter'') [] (plus_monad_safe (storeLookup (STR ''counter'') []) (sint_monad 1));
      (assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (sint_monad 1)));
      assign_storage_monad (STR ''counter'') [] (plus_monad_safe (storeLookup (STR ''counter'') []) (sint_monad 10))
    })
    });
      assign_storage_monad (STR ''locked'') [] false_monad
    })
    })
    })
    })
    })" ,

cfunction dbl external
where
  "(do {
      value_guard;
      (do {
      (do {
      (assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (sint_monad 1)));
      (assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (sint_monad 1)))
    })
    })
    })" ,

cfunction wl external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''_m1_a'');
      assign_stack_monad (STR ''_m1_a'') [] (stackLookup (STR ''v'') []);
      (do {
      decl TSint (STR ''_m1_t'');
      assign_stack_monad (STR ''_m1_t'') [] (plus_monad_safe (stackLookup (STR ''_m1_a'') []) (sint_monad 1));
      assign_storage_monad (STR ''x'') [] (stackLookup (STR ''_m1_t'') []);
      (assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (sint_monad 100)));
      assign_storage_monad (STR ''y'') [] (stackLookup (STR ''_m1_t'') [])
    })
    })
    })" ,

cfunction shadow external
param "STR ''t''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''_m1_a'');
      assign_stack_monad (STR ''_m1_a'') [] (stackLookup (STR ''t'') []);
      (do {
      decl TSint (STR ''_m1_t'');
      assign_stack_monad (STR ''_m1_t'') [] (plus_monad_safe (stackLookup (STR ''_m1_a'') []) (sint_monad 1));
      assign_storage_monad (STR ''x'') [] (stackLookup (STR ''_m1_t'') []);
      (assign_storage_monad (STR ''y'') [] (plus_monad_safe (storeLookup (STR ''y'') []) (stackLookup (STR ''t'') [])));
      assign_storage_monad (STR ''y'') [] (stackLookup (STR ''_m1_t'') [])
    })
    })
    })" ,

cfunction br external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TBool (STR ''_m1_b'');
      assign_stack_monad (STR ''_m1_b'') [] (less_monad (sint_monad 3) (stackLookup (STR ''v'') []));
      ((cond_monad (stackLookup (STR ''_m1_b'') []) ((assign_storage_monad (STR ''x'') [] (stackLookup (STR ''v'') []))) (assign_storage_monad (STR ''y'') [] (sint_monad 99))))
    })
    })" ,

cfunction loopLp external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''_m1_n'');
      assign_stack_monad (STR ''_m1_n'') [] (stackLookup (STR ''n'') []);
      (do {
      decl TSint (STR ''_m1_i'');
      assign_stack_monad (STR ''_m1_i'') [] (sint_monad 0);
      (while_monad (less_monad (stackLookup (STR ''_m1_i'') []) (stackLookup (STR ''_m1_n'') [])) (do {
      ((assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (sint_monad 1))));
      assign_stack_monad (STR ''_m1_i'') [] (plus_monad_safe (stackLookup (STR ''_m1_i'') []) (sint_monad 1))
    }))
    })
    })
    })" ,

cfunction ord external
where
  "(do {
      value_guard;
      (do {
      (do {
      assign_storage_monad (STR ''counter'') [] (sint_monad 5);
      (do {
      decl TSint (STR ''_m1_v'');
      assign_stack_monad (STR ''_m1_v'') [] (storeLookup (STR ''counter'') []);
      (do {
      assign_storage_monad (STR ''y'') [] (stackLookup (STR ''_m1_v'') []);
      skip_monad
    })
    })
    })
    })
    })" ,

cfunction ord2 external
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''_m2_v'');
      assign_stack_monad (STR ''_m2_v'') [] (storeLookup (STR ''counter'') []);
      (do {
      assign_storage_monad (STR ''y'') [] (stackLookup (STR ''_m2_v'') []);
      (do {
      (do {
      assign_storage_monad (STR ''counter'') [] (sint_monad 5);
      skip_monad
    })
    })
    })
    })
    })" ,

cfunction paid external payable
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      decl TSint (STR ''_m1_m'');
      assign_stack_monad (STR ''_m1_m'') [] (stackLookup (STR ''v'') []);
      (do {
      (assert_monad (not_monad (less_monad value_monad (stackLookup (STR ''_m1_m'') []))));
      (assign_storage_monad (STR ''x'') [] value_monad)
    })
    })" ,

cfunction nested external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (equals_monad sender_monad (storeLookup (STR ''owner'') [])));
      (do {
      decl TSint (STR ''_m3_v'');
      assign_stack_monad (STR ''_m3_v'') [] (stackLookup (STR ''v'') []);
      (do {
      (assert_monad (not_monad (less_monad (storeLookup (STR ''x'') []) (stackLookup (STR ''_m3_v'') []))));
      (do {
      decl TBool (STR ''_m2_b'');
      assign_stack_monad (STR ''_m2_b'') [] (less_monad (stackLookup (STR ''v'') []) (sint_monad 50));
      ((cond_monad (stackLookup (STR ''_m2_b'') []) ((do {
      (do {
      assign_storage_monad (STR ''counter'') [] (plus_monad_safe (storeLookup (STR ''counter'') []) (sint_monad 1));
      (assign_storage_monad (STR ''y'') [] (stackLookup (STR ''v'') []));
      assign_storage_monad (STR ''counter'') [] (plus_monad_safe (storeLookup (STR ''counter'') []) (sint_monad 10))
    })
    })) (assign_storage_monad (STR ''y'') [] (sint_monad 99))))
    })
    })
    })
    })
    })
    })"

end
