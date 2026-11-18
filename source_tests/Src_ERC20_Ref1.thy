theory Src_ERC20_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

(* Omitted: view/pure functions with return values that nothing calls (no effect on state): contractOwner, totalSupply, balanceOf, allowance, nonces *)

section \<open>ERC20 Contract\<close>

contract ERC20
  for "STR ''name''" : "SType.TValue (TBytes 0)"
  and "STR ''symbol''" : "SType.TValue (TBytes 0)"
  and "STR ''decimals''" : "SType.TValue TSint"
  and "STR ''_owner''" : "SType.TValue TAddress"
  and "STR ''_balances''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"
  and "STR ''_allowances''" : "SType.TMap (SType.TValue TAddress) (SType.TMap (SType.TValue TAddress) (SType.TValue TSint))"
  and "STR ''_totalSupply''" : "SType.TValue TSint"
  and "STR ''INITIAL_CHAIN_ID''" : "SType.TValue TSint"
  and "STR ''INITIAL_DOMAIN_SEPARATOR''" : "SType.TValue (TBytes 32)"
  and "STR ''_nonces''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor
param "STR ''_name''" : "SType.TValue (TBytes 0)"
and "STR ''_symbol''" : "SType.TValue (TBytes 0)"
and "STR ''_decimals''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''_decimals'') []) (sint_monad 256));
      (do {
      assign_storage_monad (STR ''_owner'') [] sender_monad;
      assign_storage_monad (STR ''name'') [] (stackLookup (STR ''_name'') []);
      assign_storage_monad (STR ''symbol'') [] (stackLookup (STR ''_symbol'') []);
      assign_storage_monad (STR ''decimals'') [] (stackLookup (STR ''_decimals'') []);
      assign_storage_monad (STR ''INITIAL_CHAIN_ID'') [] chain_id_monad;
      assign_storage_monad (STR ''INITIAL_DOMAIN_SEPARATOR'') [] (icall computeDomainSeparator)
    })
    })
    })"

cfunction approve external
param "STR ''spender''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''_allowances'') [sender_monad, (stackLookup (STR ''spender'') [])] (stackLookup (STR ''amount'') []);
      skip_monad;
      skip_monad
    })
    })" ,

cfunction transfer external
param "STR ''to''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''_balances'') [sender_monad] (minus_monad_safe (storeLookup (STR ''_balances'') [sender_monad]) (stackLookup (STR ''amount'') []));
      (assign_storage_monad (STR ''_balances'') [(stackLookup (STR ''to'') [])] (plus_monad (storeLookup (STR ''_balances'') [(stackLookup (STR ''to'') [])]) (stackLookup (STR ''amount'') [])));
      skip_monad;
      skip_monad
    })
    })" ,

cfunction transferFrom external
param "STR ''from''" : "SType.TValue TAddress"
and "STR ''to''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''allowed'');
      assign_stack_monad (STR ''allowed'') [] (storeLookup (STR ''_allowances'') [(stackLookup (STR ''from'') []), sender_monad]);
      (cond_monad (not_monad (equals_monad (stackLookup (STR ''allowed'') []) (sint_monad 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (assign_storage_monad (STR ''_allowances'') [(stackLookup (STR ''from'') []), sender_monad] (minus_monad_safe (stackLookup (STR ''allowed'') []) (stackLookup (STR ''amount'') []))) skip_monad);
      assign_storage_monad (STR ''_balances'') [(stackLookup (STR ''from'') [])] (minus_monad_safe (storeLookup (STR ''_balances'') [(stackLookup (STR ''from'') [])]) (stackLookup (STR ''amount'') []));
      (assign_storage_monad (STR ''_balances'') [(stackLookup (STR ''to'') [])] (plus_monad (storeLookup (STR ''_balances'') [(stackLookup (STR ''to'') [])]) (stackLookup (STR ''amount'') [])));
      skip_monad;
      skip_monad
    })
    })" ,

cfunction computeDomainSeparator
where
  "(do {
      skip_monad;
      ((keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x77, CHR 0x2C, CHR 0x77, CHR 0x2C, CHR 0x77, CHR 0x2C, CHR 0x61]), (keccak256_monad (bytes_monad2 [CHR 0x45, CHR 0x49, CHR 0x50, CHR 0x37, CHR 0x31, CHR 0x32, CHR 0x44, CHR 0x6F, CHR 0x6D, CHR 0x61, CHR 0x69, CHR 0x6E, CHR 0x28, CHR 0x73, CHR 0x74, CHR 0x72, CHR 0x69, CHR 0x6E, CHR 0x67, CHR 0x20, CHR 0x6E, CHR 0x61, CHR 0x6D, CHR 0x65, CHR 0x2C, CHR 0x73, CHR 0x74, CHR 0x72, CHR 0x69, CHR 0x6E, CHR 0x67, CHR 0x20, CHR 0x76, CHR 0x65, CHR 0x72, CHR 0x73, CHR 0x69, CHR 0x6F, CHR 0x6E, CHR 0x2C, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x32, CHR 0x35, CHR 0x36, CHR 0x20, CHR 0x63, CHR 0x68, CHR 0x61, CHR 0x69, CHR 0x6E, CHR 0x49, CHR 0x64, CHR 0x2C, CHR 0x61, CHR 0x64, CHR 0x64, CHR 0x72, CHR 0x65, CHR 0x73, CHR 0x73, CHR 0x20, CHR 0x76, CHR 0x65, CHR 0x72, CHR 0x69, CHR 0x66, CHR 0x79, CHR 0x69, CHR 0x6E, CHR 0x67, CHR 0x43, CHR 0x6F, CHR 0x6E, CHR 0x74, CHR 0x72, CHR 0x61, CHR 0x63, CHR 0x74, CHR 0x29])), (keccak256_monad (storeLookup (STR ''name'') [])), (keccak256_monad (bytes_monad2 [CHR 0x31])), chain_id_monad, this_monad])))
    })" ,

cfunction DOMAIN_SEPARATOR__int
where
  "(do {
      skip_monad;
      ((cond_monad (equals_monad chain_id_monad (storeLookup (STR ''INITIAL_CHAIN_ID'') [])) (storeLookup (STR ''INITIAL_DOMAIN_SEPARATOR'') []) (icall computeDomainSeparator)))
    })" ,

cfunction permit external
param "STR ''owner''" : "SType.TValue TAddress"
and "STR ''spender''" : "SType.TValue TAddress"
and "STR ''value''" : "SType.TValue TSint"
and "STR ''deadline''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
and "STR ''r''" : "SType.TValue (TBytes 32)"
and "STR ''s''" : "SType.TValue (TBytes 32)"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 256));
      (do {
      (assert_monad (not_monad (less_monad (stackLookup (STR ''deadline'') []) block_timestamp_monad)));
      (do {
      decl TAddress (STR ''recoveredAddress'');
      assign_stack_monad (STR ''recoveredAddress'') [] (ecrecover_monad (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x50, CHR 0x3A, CHR 0x6C, CHR 0x69, CHR 0x74, CHR 0x65, CHR 0x72, CHR 0x61, CHR 0x6C, CHR 0x5F, CHR 0x73, CHR 0x74, CHR 0x72, CHR 0x69, CHR 0x6E, CHR 0x67, CHR 0x20, CHR 0x68, CHR 0x65, CHR 0x78, CHR 0x22, CHR 0x31, CHR 0x39, CHR 0x30, CHR 0x31, CHR 0x22, CHR 0x2C, CHR 0x62, CHR 0x79, CHR 0x74, CHR 0x65, CHR 0x73, CHR 0x33, CHR 0x32, CHR 0x2C, CHR 0x62, CHR 0x79, CHR 0x74, CHR 0x65, CHR 0x73, CHR 0x33, CHR 0x32]), (bytes_monad2 [CHR 0x19, CHR 0x01]), (icall DOMAIN_SEPARATOR__int), (keccak256_monad (encodeABI_monad [(bytes_monad2 [CHR 0x77, CHR 0x2C, CHR 0x61, CHR 0x2C, CHR 0x61, CHR 0x2C, CHR 0x77, CHR 0x2C, CHR 0x77, CHR 0x2C, CHR 0x77]), (keccak256_monad (bytes_monad2 [CHR 0x50, CHR 0x65, CHR 0x72, CHR 0x6D, CHR 0x69, CHR 0x74, CHR 0x28, CHR 0x61, CHR 0x64, CHR 0x64, CHR 0x72, CHR 0x65, CHR 0x73, CHR 0x73, CHR 0x20, CHR 0x6F, CHR 0x77, CHR 0x6E, CHR 0x65, CHR 0x72, CHR 0x2C, CHR 0x61, CHR 0x64, CHR 0x64, CHR 0x72, CHR 0x65, CHR 0x73, CHR 0x73, CHR 0x20, CHR 0x73, CHR 0x70, CHR 0x65, CHR 0x6E, CHR 0x64, CHR 0x65, CHR 0x72, CHR 0x2C, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x32, CHR 0x35, CHR 0x36, CHR 0x20, CHR 0x76, CHR 0x61, CHR 0x6C, CHR 0x75, CHR 0x65, CHR 0x2C, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x32, CHR 0x35, CHR 0x36, CHR 0x20, CHR 0x6E, CHR 0x6F, CHR 0x6E, CHR 0x63, CHR 0x65, CHR 0x2C, CHR 0x75, CHR 0x69, CHR 0x6E, CHR 0x74, CHR 0x32, CHR 0x35, CHR 0x36, CHR 0x20, CHR 0x64, CHR 0x65, CHR 0x61, CHR 0x64, CHR 0x6C, CHR 0x69, CHR 0x6E, CHR 0x65, CHR 0x29])), (stackLookup (STR ''owner'') []), (stackLookup (STR ''spender'') []), (stackLookup (STR ''value'') []), (do {
      old <- (storeLookup (STR ''_nonces'') [(stackLookup (STR ''owner'') [])]);
      assign_storage_monad (STR ''_nonces'') [(stackLookup (STR ''owner'') [])] (plus_monad (storeLookup (STR ''_nonces'') [(stackLookup (STR ''owner'') [])]) (sint_monad 1));
      (return old)
    }), (stackLookup (STR ''deadline'') [])]))])) (stackLookup (STR ''v'') []) (stackLookup (STR ''r'') []) (stackLookup (STR ''s'') []));
      (assert_monad (cond_monad (not_monad (equals_monad (stackLookup (STR ''recoveredAddress'') []) null_monad)) (equals_monad (stackLookup (STR ''recoveredAddress'') []) (stackLookup (STR ''owner'') [])) false_monad));
      assign_storage_monad (STR ''_allowances'') [(stackLookup (STR ''recoveredAddress'') []), (stackLookup (STR ''spender'') [])] (stackLookup (STR ''value'') [])
    });
      skip_monad
    })
    })
    })" ,

cfunction DOMAIN_SEPARATOR external
where
  "(do {
      value_guard;
      (do {
      skip_monad;
      ((cond_monad (equals_monad chain_id_monad (storeLookup (STR ''INITIAL_CHAIN_ID'') [])) (storeLookup (STR ''INITIAL_DOMAIN_SEPARATOR'') []) (icall computeDomainSeparator)))
    })
    })" ,

cfunction mint external
param "STR ''to''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (equals_monad (storeLookup (STR ''_owner'') []) sender_monad));
      (do {
      assign_storage_monad (STR ''_totalSupply'') [] (plus_monad_safe (storeLookup (STR ''_totalSupply'') []) (stackLookup (STR ''amount'') []));
      (assign_storage_monad (STR ''_balances'') [(stackLookup (STR ''to'') [])] (plus_monad (storeLookup (STR ''_balances'') [(stackLookup (STR ''to'') [])]) (stackLookup (STR ''amount'') [])));
      skip_monad
    })
    })
    })
    })" ,

cfunction burn external
param "STR ''from''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (equals_monad (storeLookup (STR ''_owner'') []) sender_monad));
      (do {
      assign_storage_monad (STR ''_balances'') [(stackLookup (STR ''from'') [])] (minus_monad_safe (storeLookup (STR ''_balances'') [(stackLookup (STR ''from'') [])]) (stackLookup (STR ''amount'') []));
      (assign_storage_monad (STR ''_totalSupply'') [] (minus_monad (storeLookup (STR ''_totalSupply'') []) (stackLookup (STR ''amount'') [])));
      skip_monad
    })
    })
    })
    })"

end
