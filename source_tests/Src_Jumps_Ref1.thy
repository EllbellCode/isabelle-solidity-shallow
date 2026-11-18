theory Src_Jumps_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Jumps Contract\<close>

contract Jumps
  for "STR ''total''" : "SType.TValue TSint"
  and "STR ''count''" : "SType.TValue TSint"
  and "STR ''last''" : "SType.TValue TSint"
  and "STR ''seen''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor
where
  "(value_guard)"

cfunction sumUntil external
param "STR ''n''" : "SType.TValue TSint"
and "STR ''stop''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (less_monad (stackLookup (STR ''n'') []) (sint_monad 12)));
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      decl TBool (STR ''_brk1'');
      assign_stack_monad (STR ''_brk1'') [] false_monad;
      (while_monad (cond_monad (stackLookup (STR ''_brk1'') []) false_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') []))) (do {
      (do {
      (cond_monad (equals_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''stop'') [])) (assign_stack_monad (STR ''_brk1'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_brk1'') []) skip_monad (do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''i'') []));
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1))
    }))
    })
    }));
      assign_storage_monad (STR ''last'') [] (stackLookup (STR ''i'') [])
    })
    })" ,

cfunction skipEven external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (less_monad (stackLookup (STR ''n'') []) (sint_monad 12)));
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      (while_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') [])) (do {
      decl TBool (STR ''_cnt1'');
      assign_stack_monad (STR ''_cnt1'') [] false_monad;
      (do {
      (cond_monad (equals_monad (cond_monad (equals_monad (sint_monad 2) (sint_monad 0)) (assert_monad false_monad) (mod_monad (stackLookup (STR ''i'') []) (sint_monad 2))) (sint_monad 0)) (assign_stack_monad (STR ''_cnt1'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_cnt1'') []) skip_monad (do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''i'') []));
      assign_storage_monad (STR ''count'') [] (plus_monad_safe (storeLookup (STR ''count'') []) (sint_monad 1))
    }))
    });
      (do {
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1))
    })
    }))
    })
    })" ,

cfunction both external
param "STR ''n''" : "SType.TValue TSint"
and "STR ''skip''" : "SType.TValue TSint"
and "STR ''stop''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (less_monad (stackLookup (STR ''n'') []) (sint_monad 12)));
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      decl TBool (STR ''_brk1'');
      assign_stack_monad (STR ''_brk1'') [] false_monad;
      (while_monad (cond_monad (stackLookup (STR ''_brk1'') []) false_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') []))) (do {
      decl TBool (STR ''_cnt1'');
      assign_stack_monad (STR ''_cnt1'') [] false_monad;
      (do {
      (cond_monad (equals_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''skip'') [])) (assign_stack_monad (STR ''_cnt1'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_brk1'') []) skip_monad (cond_monad (stackLookup (STR ''_cnt1'') []) skip_monad (do {
      (cond_monad (equals_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''stop'') [])) (assign_stack_monad (STR ''_brk1'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_brk1'') []) skip_monad (cond_monad (stackLookup (STR ''_cnt1'') []) skip_monad (do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (sint_monad 3));
      assign_storage_monad (STR ''count'') [] (plus_monad_safe (storeLookup (STR ''count'') []) (stackLookup (STR ''i'') []))
    })))
    })))
    });
      (cond_monad (stackLookup (STR ''_brk1'') []) skip_monad (do {
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1))
    }))
    }))
    })
    })" ,

cfunction doOnce external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (less_monad (stackLookup (STR ''n'') []) (sint_monad 12)));
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (stackLookup (STR ''n'') []);
      decl TBool (STR ''_first1'');
      assign_stack_monad (STR ''_first1'') [] true_monad;
      (while_monad (cond_monad (stackLookup (STR ''_first1'') []) true_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') []))) (do {
      assign_stack_monad (STR ''_first1'') [] false_monad;
      (do {
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (sint_monad 1));
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1))
    })
    }));
      assign_storage_monad (STR ''last'') [] (stackLookup (STR ''i'') [])
    })
    })" ,

cfunction doCount external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (less_monad (stackLookup (STR ''n'') []) (sint_monad 12)));
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      decl TBool (STR ''_first1'');
      assign_stack_monad (STR ''_first1'') [] true_monad;
      (while_monad (cond_monad (stackLookup (STR ''_first1'') []) true_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') []))) (do {
      assign_stack_monad (STR ''_first1'') [] false_monad;
      (do {
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 2));
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''i'') []))
    })
    }));
      assign_storage_monad (STR ''last'') [] (stackLookup (STR ''i'') [])
    })
    })" ,

cfunction doJumps external
param "STR ''n''" : "SType.TValue TSint"
and "STR ''skip''" : "SType.TValue TSint"
and "STR ''stop''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (less_monad (stackLookup (STR ''n'') []) (sint_monad 12)));
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      decl TBool (STR ''_brk1'');
      assign_stack_monad (STR ''_brk1'') [] false_monad;
      decl TBool (STR ''_first1'');
      assign_stack_monad (STR ''_first1'') [] true_monad;
      (while_monad (cond_monad (stackLookup (STR ''_first1'') []) true_monad (cond_monad (stackLookup (STR ''_brk1'') []) false_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') [])))) (do {
      assign_stack_monad (STR ''_first1'') [] false_monad;
      decl TBool (STR ''_cnt1'');
      assign_stack_monad (STR ''_cnt1'') [] false_monad;
      (do {
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1));
      (cond_monad (equals_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''skip'') [])) (assign_stack_monad (STR ''_cnt1'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_brk1'') []) skip_monad (cond_monad (stackLookup (STR ''_cnt1'') []) skip_monad (do {
      (cond_monad (equals_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''stop'') [])) (assign_stack_monad (STR ''_brk1'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_brk1'') []) skip_monad (cond_monad (stackLookup (STR ''_cnt1'') []) skip_monad (assign_storage_monad (STR ''count'') [] (plus_monad_safe (storeLookup (STR ''count'') []) (stackLookup (STR ''i'') [])))))
    })))
    })
    }));
      assign_storage_monad (STR ''last'') [] (stackLookup (STR ''i'') [])
    })
    })" ,

cfunction nested external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
and "STR ''stop''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (cond_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 6)) (less_monad (stackLookup (STR ''b'') []) (sint_monad 6)) false_monad));
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      (while_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''a'') [])) (do {
      decl TBool (STR ''_cnt1'');
      assign_stack_monad (STR ''_cnt1'') [] false_monad;
      (do {
      decl TSint (STR ''j'');
      assign_stack_monad (STR ''j'') [] (sint_monad 0);
      decl TBool (STR ''_brk2'');
      assign_stack_monad (STR ''_brk2'') [] false_monad;
      (while_monad (cond_monad (stackLookup (STR ''_brk2'') []) false_monad (less_monad (stackLookup (STR ''j'') []) (stackLookup (STR ''b'') []))) (do {
      (do {
      (cond_monad (equals_monad (stackLookup (STR ''j'') []) (stackLookup (STR ''stop'') [])) (assign_stack_monad (STR ''_brk2'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_brk2'') []) skip_monad (assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (sint_monad 1))))
    });
      (cond_monad (stackLookup (STR ''_brk2'') []) skip_monad (do {
      assign_stack_monad (STR ''j'') [] (plus_monad_safe (stackLookup (STR ''j'') []) (sint_monad 1))
    }))
    }));
      (cond_monad (equals_monad (stackLookup (STR ''i'') []) (sint_monad 2)) (assign_stack_monad (STR ''_cnt1'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_cnt1'') []) skip_monad (assign_storage_monad (STR ''count'') [] (plus_monad_safe (storeLookup (STR ''count'') []) (sint_monad 10))))
    });
      (do {
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1))
    })
    }))
    })
    })" ,

cfunction revertInLoop external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (less_monad (stackLookup (STR ''n'') []) (sint_monad 12)));
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      decl TBool (STR ''_brk1'');
      assign_stack_monad (STR ''_brk1'') [] false_monad;
      (while_monad (cond_monad (stackLookup (STR ''_brk1'') []) false_monad true_monad) (do {
      (do {
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1));
      (cond_monad (less_monad (stackLookup (STR ''n'') []) (stackLookup (STR ''i'') [])) (assign_stack_monad (STR ''_brk1'') [] true_monad) skip_monad);
      (cond_monad (stackLookup (STR ''_brk1'') []) skip_monad (do {
      (assert_monad (not_monad (equals_monad (stackLookup (STR ''i'') []) (sint_monad 7))));
      assign_storage_monad (STR ''seen'') [sender_monad] (plus_monad_safe (storeLookup (STR ''seen'') [sender_monad]) (stackLookup (STR ''i'') []))
    }))
    })
    }))
    })
    })" ,

cfunction afterBreak external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      decl TBool (STR ''_brk1'');
      assign_stack_monad (STR ''_brk1'') [] false_monad;
      (while_monad (cond_monad (stackLookup (STR ''_brk1'') []) false_monad (less_monad (stackLookup (STR ''i'') []) (sint_monad 10))) (do {
      (do {
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1));
      ((cond_monad (not_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') []))) (assign_stack_monad (STR ''_brk1'') [] true_monad) skip_monad));
      (cond_monad (stackLookup (STR ''_brk1'') []) skip_monad (do {
      (assign_storage_monad (STR ''total'') [] (plus_monad (storeLookup (STR ''total'') []) (stackLookup (STR ''i'') [])));
      assign_storage_monad (STR ''count'') [] (plus_monad_safe (storeLookup (STR ''count'') []) (sint_monad 1))
    }))
    })
    }))
    })
    })"

end
