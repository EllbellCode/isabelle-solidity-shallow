theory Src_Hash_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Hash Contract\<close>

contract Hash
  for "STR ''h1''" : "SType.TValue (TBytes 32)"
  and "STR ''h2''" : "SType.TValue (TBytes 32)"
  and "STR ''h3''" : "SType.TValue (TBytes 32)"
  and "STR ''hs''" : "SType.TValue (TBytes 32)"
  and "STR ''hs2''" : "SType.TValue (TBytes 32)"
  and "STR ''hs3''" : "SType.TValue (TBytes 32)"
  and "STR ''hl''" : "SType.TValue (TBytes 32)"
  and "STR ''hl2''" : "SType.TValue (TBytes 32)"
  and "STR ''commitment''" : "SType.TMap (SType.TValue TAddress) (SType.TValue (TBytes 32))"
  and "STR ''seen''" : "SType.TMap (SType.TValue (TBytes 32)) (SType.TValue TBool)"
  and "STR ''count''" : "SType.TMap (SType.TValue (TBytes 32)) (SType.TValue TSint)"
  and "STR ''n''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction enc2 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''h1'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''a'') []), (stackLookup (STR ''b'') [])]));
      assign_storage_monad (STR ''h2'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''b'') []), (stackLookup (STR ''a'') [])]))
    })
    })" ,

cfunction enc1 external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''h3'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77]), (stackLookup (STR ''a'') [])])))
    })" ,

cfunction enc3 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
and "STR ''c''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''h1'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''a'') []), (stackLookup (STR ''b'') []), (stackLookup (STR ''c'') [])]));
      assign_storage_monad (STR ''h2'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''a'') []), (stackLookup (STR ''b'') [])]))
    })
    })" ,

cfunction packed external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''h1'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''a'') []), (stackLookup (STR ''b'') [])]));
      assign_storage_monad (STR ''h2'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''a'') []), (stackLookup (STR ''b'') [])]))
    })
    })" ,

cfunction mixed external
param "STR ''who''" : "SType.TValue TAddress"
and "STR ''flag''" : "SType.TValue TBool"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''h1'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x61, CHR 0x2C, CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''who'') []), (stackLookup (STR ''flag'') []), (stackLookup (STR ''v'') [])]));
      assign_storage_monad (STR ''h2'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x61, CHR 0x2C, CHR 0x77, CHR 0x2C, CHR 0x77]), sender_monad, (stackLookup (STR ''flag'') []), (stackLookup (STR ''v'') [])]))
    })
    })" ,

cfunction narrow external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''a'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''b'') []) (sint_monad 256));
      (do {
      assign_storage_monad (STR ''h1'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x50, CHR 0x3A, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x38, CHR 0x2C, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x38]), (stackLookup (STR ''a'') []), (stackLookup (STR ''b'') [])]));
      assign_storage_monad (STR ''h2'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''a'') []), (stackLookup (STR ''b'') [])]));
      assign_storage_monad (STR ''h3'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x50, CHR 0x3A, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x38, CHR 0x2C, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x38]), (stackLookup (STR ''b'') []), (stackLookup (STR ''a'') [])]))
    })
    })
    })" ,

cfunction viaSender external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''h3'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x50, CHR 0x3A, CHR 0x61, CHR 0x64, CHR 0x64, CHR 0x72, CHR 0x65, CHR 0x73, CHR 0x73, CHR 0x2C, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x32, CHR 0x35, CHR 0x36]), sender_monad, (stackLookup (STR ''v'') [])])))
    })" ,

cfunction str external
param "STR ''s''" : "SType.TValue (TBytes 0)"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''hs'') [] (keccak256_monad (stackLookup (STR ''s'') []));
      assign_storage_monad (STR ''hs2'') [] (keccak256_monad (stackLookup (STR ''s'') []));
      assign_storage_monad (STR ''hs3'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x64]), (stackLookup (STR ''s'') [])]))
    })
    })" ,

cfunction bytesArg external
param "STR ''b''" : "SType.TValue (TBytes 0)"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''hs'') [] (keccak256_monad (stackLookup (STR ''b'') []));
      assign_storage_monad (STR ''hs3'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x64, CHR 0x2C, CHR 0x64]), (stackLookup (STR ''b'') []), (stackLookup (STR ''b'') [])]))
    })
    })" ,

cfunction strPlus external
param "STR ''s''" : "SType.TValue (TBytes 0)"
and "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''hs2'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x50, CHR 0x3A, CHR 0x73, CHR 0x74, CHR 0x72, CHR 0x69, CHR 0x6E, CHR 0x67, CHR 0x20, CHR 0x6D, CHR 0x65, CHR 0x6D, CHR 0x6F, CHR 0x72, CHR 0x79, CHR 0x2C, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x32, CHR 0x35, CHR 0x36]), (stackLookup (STR ''s'') []), (stackLookup (STR ''k'') [])]));
      assign_storage_monad (STR ''hs3'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x64, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''s'') []), (stackLookup (STR ''k'') [])]))
    })
    })" ,

cfunction two external
param "STR ''a''" : "SType.TValue (TBytes 0)"
and "STR ''b''" : "SType.TValue (TBytes 0)"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''hs'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x64, CHR 0x2C, CHR 0x64]), (stackLookup (STR ''a'') []), (stackLookup (STR ''b'') [])]));
      assign_storage_monad (STR ''hs2'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x64, CHR 0x2C, CHR 0x64]), (stackLookup (STR ''b'') []), (stackLookup (STR ''a'') [])]))
    })
    })" ,

cfunction lit external
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''hl'') [] (keccak256_monad (bytes_monad2 [CHR 0x61, CHR 0x62, CHR 0x63]));
      assign_storage_monad (STR ''hl2'') [] (keccak256_monad (bytes_monad2 [CHR 0x61, CHR 0x62, CHR 0x63]))
    })
    })" ,

cfunction litOther external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''hl2'') [] (keccak256_monad (bytes_monad2 [CHR 0x61, CHR 0x62, CHR 0x64])))
    })" ,

cfunction litEq external
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad (storeLookup (STR ''hl'') []) (keccak256_monad (bytes_monad2 [CHR 0x61, CHR 0x62, CHR 0x63]))));
      assign_storage_monad (STR ''n'') [] (plus_monad_safe (storeLookup (STR ''n'') []) (sint_monad 1))
    })
    })" ,

cfunction same external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77]), (stackLookup (STR ''a'') [])])) (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77]), (stackLookup (STR ''b'') [])]))));
      assign_storage_monad (STR ''n'') [] (plus_monad_safe (storeLookup (STR ''n'') []) (sint_monad 1))
    })
    })" ,

cfunction differ external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (not_monad (equals_monad (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''a'') []), (sint_monad 1)])) (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (stackLookup (STR ''b'') []), (sint_monad 1)])))));
      assign_storage_monad (STR ''n'') [] (plus_monad_safe (storeLookup (STR ''n'') []) (sint_monad 1))
    })
    })" ,

cfunction sameStr external
param "STR ''a''" : "SType.TValue (TBytes 0)"
and "STR ''b''" : "SType.TValue (TBytes 0)"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad (keccak256_monad (stackLookup (STR ''a'') [])) (keccak256_monad (stackLookup (STR ''b'') []))));
      assign_storage_monad (STR ''n'') [] (plus_monad_safe (storeLookup (STR ''n'') []) (sint_monad 1))
    })
    })" ,

cfunction typed external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''h3'') [] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (bytes_monad2 [CHR 0x7C, CHR 0x7C, CHR 0x6C, CHR 0xDB, CHR 0x67, CHR 0xA1, CHR 0x87, CHR 0x43, CHR 0xF4, CHR 0x9E, CHR 0xC6, CHR 0xFA, CHR 0x9B, CHR 0x35, CHR 0xF5, CHR 0x0D, CHR 0x52, CHR 0xED, CHR 0x05, CHR 0xCB, CHR 0xED, CHR 0x4C, CHR 0xC5, CHR 0x92, CHR 0xE1, CHR 0x3B, CHR 0x44, CHR 0x50, CHR 0x1C, CHR 0x1A, CHR 0x22, CHR 0x67]), (stackLookup (STR ''a'') [])]));
      assign_storage_monad (STR ''h2'') [] (bytes_monad2 [CHR 0x7C, CHR 0x7C, CHR 0x6C, CHR 0xDB, CHR 0x67, CHR 0xA1, CHR 0x87, CHR 0x43, CHR 0xF4, CHR 0x9E, CHR 0xC6, CHR 0xFA, CHR 0x9B, CHR 0x35, CHR 0xF5, CHR 0x0D, CHR 0x52, CHR 0xED, CHR 0x05, CHR 0xCB, CHR 0xED, CHR 0x4C, CHR 0xC5, CHR 0x92, CHR 0xE1, CHR 0x3B, CHR 0x44, CHR 0x50, CHR 0x1C, CHR 0x1A, CHR 0x22, CHR 0x67])
    })
    })" ,

cfunction typedEq external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad (storeLookup (STR ''h3'') []) (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77]), (bytes_monad2 [CHR 0x7C, CHR 0x7C, CHR 0x6C, CHR 0xDB, CHR 0x67, CHR 0xA1, CHR 0x87, CHR 0x43, CHR 0xF4, CHR 0x9E, CHR 0xC6, CHR 0xFA, CHR 0x9B, CHR 0x35, CHR 0xF5, CHR 0x0D, CHR 0x52, CHR 0xED, CHR 0x05, CHR 0xCB, CHR 0xED, CHR 0x4C, CHR 0xC5, CHR 0x92, CHR 0xE1, CHR 0x3B, CHR 0x44, CHR 0x50, CHR 0x1C, CHR 0x1A, CHR 0x22, CHR 0x67]), (stackLookup (STR ''a'') [])]))));
      assign_storage_monad (STR ''n'') [] (plus_monad_safe (storeLookup (STR ''n'') []) (sint_monad 1))
    })
    })" ,

cfunction commit external
param "STR ''secret''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''commitment'') [sender_monad] (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x50, CHR 0x3A, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x32, CHR 0x35, CHR 0x36, CHR 0x2C, CHR 0x61, CHR 0x64, CHR 0x64, CHR 0x72, CHR 0x65, CHR 0x73, CHR 0x73]), (stackLookup (STR ''secret'') []), sender_monad])))
    })" ,

cfunction reveal external
param "STR ''secret''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (equals_monad (storeLookup (STR ''commitment'') [sender_monad]) (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x50, CHR 0x3A, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x32, CHR 0x35, CHR 0x36, CHR 0x2C, CHR 0x61, CHR 0x64, CHR 0x64, CHR 0x72, CHR 0x65, CHR 0x73, CHR 0x73]), (stackLookup (STR ''secret'') []), sender_monad]))));
      assign_storage_monad (STR ''n'') [] (plus_monad_safe (storeLookup (STR ''n'') []) (sint_monad 1));
      assign_storage_monad (STR ''commitment'') [sender_monad] (bytes_monad2 [CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00, CHR 0x00])
    })
    })" ,

cfunction mark external
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''seen'') [(keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77]), (stackLookup (STR ''a'') [])]))] true_monad)
    })" ,

cfunction check external
param "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (storeLookup (STR ''seen'') [(keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77]), (stackLookup (STR ''b'') [])]))]));
      assign_storage_monad (STR ''n'') [] (plus_monad_safe (storeLookup (STR ''n'') []) (sint_monad 1))
    })
    })" ,

cfunction bump external
param "STR ''k''" : "SType.TValue (TBytes 0)"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''count'') [(keccak256_monad (stackLookup (STR ''k'') []))] (plus_monad_safe (storeLookup (STR ''count'') [(keccak256_monad (stackLookup (STR ''k'') []))]) (sint_monad 1)))
    })" ,

cfunction need external
param "STR ''k''" : "SType.TValue (TBytes 0)"
and "STR ''atLeast''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (not_monad (less_monad (storeLookup (STR ''count'') [(keccak256_monad (stackLookup (STR ''k'') []))]) (stackLookup (STR ''atLeast'') []))));
      assign_storage_monad (STR ''n'') [] (plus_monad_safe (storeLookup (STR ''n'') []) (sint_monad 1))
    })
    })"

end
