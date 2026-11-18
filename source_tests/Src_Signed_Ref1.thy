theory Src_Signed_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Signed Contract\<close>

contract Signed
  for "STR ''r''" : "SType.TValue TSint"
  and "STR ''r2''" : "SType.TValue TSint"
  and "STR ''u''" : "SType.TValue TSint"
  and "STR ''b''" : "SType.TValue TBool"
  and "STR ''m''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor
where
  "(value_guard)"

cfunction add external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (splus_safe_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })" ,

cfunction sub external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (sminus_safe_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })" ,

cfunction mul external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (smult_safe_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })" ,

cfunction dv external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (sdiv_safe_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })" ,

cfunction md external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (smod_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })" ,

cfunction neg external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (sminus_safe_monad (sint_monad 0) (stackLookup (STR ''x'') [])))
    })" ,

cfunction uadd external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''r'') [] (plus_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })" ,

cfunction usub external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''r'') [] (minus_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })" ,

cfunction umul external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''r'') [] (mult_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })" ,

cfunction udv external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (sdiv_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))))
    })" ,

cfunction umd external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (smod_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))))
    })" ,

cfunction uneg external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''r'') [] (minus_monad (sint_monad 0) (stackLookup (STR ''x'') []))))
    })" ,

cfunction lt external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''b'') [] (sless_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })" ,

cfunction gt external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''b'') [] (sless_monad (stackLookup (STR ''y'') []) (stackLookup (STR ''x'') [])))
    })" ,

cfunction le external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''b'') [] (not_monad (sless_monad (stackLookup (STR ''y'') []) (stackLookup (STR ''x'') []))))
    })" ,

cfunction ge external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''b'') [] (not_monad (sless_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })" ,

cfunction eq external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''b'') [] (equals_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })" ,

cfunction ne external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''b'') [] (not_monad (equals_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })" ,

cfunction ltZero external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''b'') [] (sless_monad (stackLookup (STR ''x'') []) (sint_monad 0)))
    })" ,

cfunction geMinusOne external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''b'') [] (not_monad (sless_monad (stackLookup (STR ''x'') []) (sint_monad (- 1)))))
    })" ,

cfunction addLit external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (splus_safe_monad (stackLookup (STR ''x'') []) (sint_monad 1)))
    })" ,

cfunction subLit external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (sminus_safe_monad (stackLookup (STR ''x'') []) (sint_monad 5)))
    })" ,

cfunction mulNeg external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (smult_safe_monad (stackLookup (STR ''x'') []) (sint_monad (- 1))))
    })" ,

cfunction divNeg external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (sint_monad (- 1)) (sint_monad 0)) (assert_monad false_monad) (sdiv_safe_monad (stackLookup (STR ''x'') []) (sint_monad (- 1)))))
    })" ,

cfunction divLit external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (sint_monad 3) (sint_monad 0)) (assert_monad false_monad) (sdiv_safe_monad (stackLookup (STR ''x'') []) (sint_monad 3))))
    })" ,

cfunction mdLit external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (sint_monad (- 3)) (sint_monad 0)) (assert_monad false_monad) (smod_monad (stackLookup (STR ''x'') []) (sint_monad (- 3)))))
    })" ,

cfunction folded external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (splus_safe_monad (stackLookup (STR ''x'') []) (sint_monad (- 3))))
    })" ,

cfunction foldedDiff external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (sint_monad 7))
    })" ,

cfunction minLit external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (sint_monad (- 57896044618658097711785492504343953926634992332820282019728792003956564819968)))
    })" ,

cfunction bigLit external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (sint_monad 57896044618658097711785492504343953926634992332820282019728792003956564819967))
    })" ,

cfunction addEq external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []);
      assign_storage_monad (STR ''r'') [] (splus_safe_monad (storeLookup (STR ''r'') []) (stackLookup (STR ''y'') []))
    })
    })" ,

cfunction subEq external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []);
      assign_storage_monad (STR ''r'') [] (sminus_safe_monad (storeLookup (STR ''r'') []) (stackLookup (STR ''y'') []))
    })
    })" ,

cfunction mulEq external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []);
      assign_storage_monad (STR ''r'') [] (smult_safe_monad (storeLookup (STR ''r'') []) (stackLookup (STR ''y'') []))
    })
    })" ,

cfunction dvEq external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []);
      assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (sdiv_safe_monad (storeLookup (STR ''r'') []) (stackLookup (STR ''y'') [])))
    })
    })" ,

cfunction mdEq external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []);
      assign_storage_monad (STR ''r'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (smod_monad (storeLookup (STR ''r'') []) (stackLookup (STR ''y'') [])))
    })
    })" ,

cfunction incFrom external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []);
      assign_storage_monad (STR ''r'') [] (splus_safe_monad (storeLookup (STR ''r'') []) (sint_monad 1))
    })
    })" ,

cfunction decFrom external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []);
      assign_storage_monad (STR ''r'') [] (sminus_safe_monad (storeLookup (STR ''r'') []) (sint_monad 1))
    })
    })" ,

cfunction setR external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []))
    })" ,

cfunction toU external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''u'') [] (stackLookup (STR ''x'') []))
    })" ,

cfunction fromU external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []))
    })" ,

cfunction roundTrip external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []))
    })" ,

cfunction absLike external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((cond_monad (sless_monad (stackLookup (STR ''x'') []) (sint_monad 0)) (assign_storage_monad (STR ''r'') [] (sminus_safe_monad (sint_monad 0) (stackLookup (STR ''x'') []))) (assign_storage_monad (STR ''r'') [] (stackLookup (STR ''x'') []))))
    })" ,

cfunction setM external
param "STR ''who''" : "SType.TValue TAddress"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''m'') [(stackLookup (STR ''who'') [])] (stackLookup (STR ''v'') []))
    })" ,

cfunction addM external
param "STR ''who''" : "SType.TValue TAddress"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''m'') [(stackLookup (STR ''who'') [])] (splus_safe_monad (storeLookup (STR ''m'') [(stackLookup (STR ''who'') [])]) (stackLookup (STR ''v'') [])))
    })" ,

cfunction local external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''t'');
      assign_stack_monad (STR ''t'') [] (stackLookup (STR ''x'') []);
      assign_stack_monad (STR ''t'') [] (sminus_safe_monad (stackLookup (STR ''t'') []) (stackLookup (STR ''y'') []));
      assign_storage_monad (STR ''r2'') [] (smult_safe_monad (stackLookup (STR ''t'') []) (sint_monad 2))
    })
    })" ,

cfunction loopS external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''n'') []) (sint_monad 256));
      (do {
      decl TSint (STR ''s'');
      assign_stack_monad (STR ''s'') [] (sint_monad 0);
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad (- 3));
      (while_monad (sless_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') [])) (do {
      (assign_stack_monad (STR ''s'') [] (splus_safe_monad (stackLookup (STR ''s'') []) (stackLookup (STR ''i'') [])));
      assign_stack_monad (STR ''i'') [] (splus_safe_monad (stackLookup (STR ''i'') []) (sint_monad 1))
    }));
      assign_storage_monad (STR ''r'') [] (stackLookup (STR ''s'') [])
    })
    })
    })"

end
