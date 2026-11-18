theory Src_Bits_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Bits Contract\<close>

contract Bits
  for "STR ''x''" : "SType.TValue TSint"
  and "STR ''small''" : "SType.TValue TSint"
  and "STR ''mid''" : "SType.TValue TSint"
  and "STR ''s''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction b1 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitand_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])))
    })" ,

cfunction b2 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitor_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])))
    })" ,

cfunction b3 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitxor_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])))
    })" ,

cfunction b4 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitnot_monad (stackLookup (STR ''a'') [])))
    })" ,

cfunction b5 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (shl_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''n'') [])))
    })" ,

cfunction b6 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (shr_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''n'') [])))
    })" ,

cfunction b7 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''s'') [] (sar_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''n'') [])))
    })" ,

cfunction b8 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''s'') [] (bitand_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])))
    })" ,

cfunction b9 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''s'') [] (bitnot_monad (stackLookup (STR ''a'') [])))
    })" ,

cfunction b10 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''s'') [] (shl_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''n'') [])))
    })" ,

cfunction n1 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 256));
      (assign_storage_monad (STR ''small'') [] (mod_monad (bitnot_monad (stackLookup (STR ''a'') [])) (sint_monad 256)))
    })
    })" ,

cfunction n2 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 256));
      (assign_storage_monad (STR ''small'') [] (mod_monad (shl_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''n'') [])) (sint_monad 256)))
    })
    })" ,

cfunction n3 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''b'') []) (sint_monad 256));
      (assign_storage_monad (STR ''small'') [] (bitxor_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])))
    })
    })" ,

cfunction n4 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 340282366920938463463374607431768211456));
      (assign_storage_monad (STR ''mid'') [] (mod_monad (shl_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''n'') [])) (sint_monad 340282366920938463463374607431768211456)))
    })
    })" ,

cfunction n5 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 256));
      (assign_storage_monad (STR ''small'') [] (shr_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''n'') [])))
    })
    })" ,

cfunction e1 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (exp_safe_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])))
    })" ,

cfunction e2 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''b'') []) (sint_monad 256));
      (assign_storage_monad (STR ''small'') [] (below_monad (exp_safe_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])) (sint_monad 256)))
    })
    })" ,

cfunction e3 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''x'') [] (exp_wrap_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []))))
    })" ,

cfunction e4 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''b'') []) (sint_monad 256));
      ((assign_storage_monad (STR ''small'') [] (mod_monad (exp_wrap_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])) (sint_monad 256))))
    })
    })" ,

cfunction e5 external
param "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (exp_safe_monad (sint_monad 10) (stackLookup (STR ''b'') [])))
    })" ,

cfunction e6 external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (sint_monad 57896044618658097711785492504343953926634992332820282019728792003956564819968))
    })" ,

cfunction c1 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitand_monad (storeLookup (STR ''x'') []) (stackLookup (STR ''a'') [])))
    })" ,

cfunction c2 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitor_monad (storeLookup (STR ''x'') []) (stackLookup (STR ''a'') [])))
    })" ,

cfunction c3 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitxor_monad (storeLookup (STR ''x'') []) (stackLookup (STR ''a'') [])))
    })" ,

cfunction c4 external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (shl_monad (storeLookup (STR ''x'') []) (stackLookup (STR ''n'') [])))
    })" ,

cfunction c5 external
param "STR ''n''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (shr_monad (storeLookup (STR ''x'') []) (stackLookup (STR ''n'') [])))
    })" ,

cfunction c7 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 256));
      (do {
      assign_storage_monad (STR ''small'') [] (bitxor_monad (storeLookup (STR ''small'') []) (stackLookup (STR ''a'') []));
      assign_storage_monad (STR ''small'') [] (mod_monad (shl_monad (storeLookup (STR ''small'') []) (sint_monad 1)) (sint_monad 256))
    })
    })
    })" ,

cfunction k1 external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitxor_monad (sint_monad 115792089237316195423570985008687907853269984665640564039457584007913129639935) (shl_monad (sint_monad 1) (sint_monad 255))))
    })" ,

cfunction k2 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (bitor_monad (shl_monad (bitand_monad (stackLookup (STR ''a'') []) (sint_monad 255)) (sint_monad 8)) (bitand_monad (shr_monad (stackLookup (STR ''a'') []) (sint_monad 8)) (sint_monad 255))))
    })"

end
