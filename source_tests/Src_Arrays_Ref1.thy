theory Src_Arrays_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Arrays Contract\<close>

contract Arrays
  for "STR ''xs''" : "SType.DArray (SType.TValue TSint)"
  and "STR ''fixedXs''" : "SType.TArray 3 (SType.TValue TSint)"
  and "STR ''owners''" : "SType.DArray (SType.TValue TAddress)"
  and "STR ''flags''" : "SType.DArray (SType.TValue TBool)"
  and "STR ''hashes''" : "SType.DArray (SType.TValue (TBytes 32))"
  and "STR ''small''" : "SType.DArray (SType.TValue TSint)"
  and "STR ''grid''" : "SType.DArray (SType.DArray (SType.TValue TSint))"
  and "STR ''pairs''" : "SType.DArray (SType.TArray 2 (SType.TValue TSint))"
  and "STR ''byUser''" : "SType.TMap (SType.TValue TAddress) (SType.DArray (SType.TValue TSint))"
  and "STR ''items''" : "SType.DArray (SType.TEnum [SType.TValue TSint, SType.DArray (SType.TValue TSint)])"
  and "STR ''total''" : "SType.TValue TSint"

constructor
where
  "(value_guard)"

cfunction push external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((do {
      v <- (stackLookup (STR ''v'') []);
      (allocate (STR ''xs'') [] (sdefault (SType.TValue TSint)));
      n <- (storeArrayLength (STR ''xs'') []);
      assign_storage_monad (STR ''xs'') [(minus_monad (return n) (sint_monad 1))] (return v)
    }))
    })" ,

cfunction pushEmpty external
where
  "(do {
      value_guard;
      ((allocate (STR ''xs'') [] (sdefault (SType.TValue TSint))))
    })" ,

cfunction pop external
where
  "(do {
      value_guard;
      ((pop_monad (STR ''xs'') []))
    })" ,

cfunction len external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (storeArrayLength (STR ''xs'') []))
    })" ,

cfunction set external
param "STR ''i''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''xs'') [(stackLookup (STR ''i'') [])] (stackLookup (STR ''v'') []))
    })" ,

cfunction add external
param "STR ''i''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''xs'') [(stackLookup (STR ''i'') [])] (plus_monad_safe (storeLookup (STR ''xs'') [(stackLookup (STR ''i'') [])]) (stackLookup (STR ''v'') [])))
    })" ,

cfunction get external
param "STR ''i''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (storeLookup (STR ''xs'') [(stackLookup (STR ''i'') [])]))
    })" ,

cfunction sum external
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''s'');
      assign_stack_monad (STR ''s'') [] (sint_monad 0);
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      (while_monad (less_monad (stackLookup (STR ''i'') []) (storeArrayLength (STR ''xs'') [])) (do {
      (assign_stack_monad (STR ''s'') [] (plus_monad_safe (stackLookup (STR ''s'') []) (storeLookup (STR ''xs'') [(stackLookup (STR ''i'') [])])));
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1))
    }));
      assign_storage_monad (STR ''total'') [] (stackLookup (STR ''s'') [])
    })
    })" ,

cfunction clear external
where
  "(do {
      value_guard;
      (delete_monad (STR ''xs'') [] (sdefault (SType.DArray (SType.TValue TSint))))
    })" ,

cfunction clearAt external
param "STR ''i''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''xs'') [(stackLookup (STR ''i'') [])] (sint_monad 0))
    })" ,

cfunction setFixed external
param "STR ''i''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''fixedXs'') [(stackLookup (STR ''i'') [])] (stackLookup (STR ''v'') []))
    })" ,

cfunction fixedLen external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (storeArrayLength (STR ''fixedXs'') []))
    })" ,

cfunction clearFixed external
where
  "(do {
      value_guard;
      (delete_monad (STR ''fixedXs'') [] (sdefault (SType.TArray 3 (SType.TValue TSint))))
    })" ,

cfunction addOwner external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      ((do {
      v <- (stackLookup (STR ''a'') []);
      (allocate (STR ''owners'') [] (sdefault (SType.TValue TAddress)));
      n <- (storeArrayLength (STR ''owners'') []);
      assign_storage_monad (STR ''owners'') [(minus_monad (return n) (sint_monad 1))] (return v)
    }))
    })" ,

cfunction isOwner external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (do {
      decl TBool (STR ''found'');
      assign_stack_monad (STR ''found'') [] false_monad;
      decl TSint (STR ''i'');
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      (while_monad (less_monad (stackLookup (STR ''i'') []) (storeArrayLength (STR ''owners'') [])) (do {
      ((cond_monad (equals_monad (storeLookup (STR ''owners'') [(stackLookup (STR ''i'') [])]) (stackLookup (STR ''a'') [])) (assign_stack_monad (STR ''found'') [] true_monad) skip_monad));
      assign_stack_monad (STR ''i'') [] (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1))
    }));
      (assert_monad (stackLookup (STR ''found'') []));
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (sint_monad 1))
    })
    })" ,

cfunction pushFlag external
param "STR ''b''" : "SType.TValue TBool"
where
  "(do {
      value_guard;
      ((do {
      v <- (stackLookup (STR ''b'') []);
      (allocate (STR ''flags'') [] (sdefault (SType.TValue TBool)));
      n <- (storeArrayLength (STR ''flags'') []);
      assign_storage_monad (STR ''flags'') [(minus_monad (return n) (sint_monad 1))] (return v)
    }))
    })" ,

cfunction toggle external
param "STR ''i''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''flags'') [(stackLookup (STR ''i'') [])] (not_monad (storeLookup (STR ''flags'') [(stackLookup (STR ''i'') [])])))
    })" ,

cfunction pushHash external
param "STR ''h''" : "SType.TValue (TBytes 32)"
where
  "(do {
      value_guard;
      ((do {
      v <- (stackLookup (STR ''h'') []);
      (allocate (STR ''hashes'') [] (sdefault (SType.TValue (TBytes 32))));
      n <- (storeArrayLength (STR ''hashes'') []);
      assign_storage_monad (STR ''hashes'') [(minus_monad (return n) (sint_monad 1))] (return v)
    }))
    })" ,

cfunction pushSmall external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 256));
      ((do {
      v <- (stackLookup (STR ''v'') []);
      (allocate (STR ''small'') [] (sdefault (SType.TValue TSint)));
      n <- (storeArrayLength (STR ''small'') []);
      assign_storage_monad (STR ''small'') [(minus_monad (return n) (sint_monad 1))] (return v)
    }))
    })
    })" ,

cfunction addSmall external
param "STR ''i''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 256));
      (assign_storage_monad (STR ''small'') [(stackLookup (STR ''i'') [])] (below_monad (plus_monad_safe (storeLookup (STR ''small'') [(stackLookup (STR ''i'') [])]) (stackLookup (STR ''v'') [])) (sint_monad 256)))
    })
    })" ,

cfunction pushRow external
where
  "(do {
      value_guard;
      ((allocate (STR ''grid'') [] (sdefault (SType.DArray (SType.TValue TSint)))))
    })" ,

cfunction pushCell external
param "STR ''r''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((do {
      v <- (stackLookup (STR ''v'') []);
      (allocate (STR ''grid'') [(stackLookup (STR ''r'') [])] (sdefault (SType.TValue TSint)));
      n <- (storeArrayLength (STR ''grid'') [(stackLookup (STR ''r'') [])]);
      assign_storage_monad (STR ''grid'') [(stackLookup (STR ''r'') []), (minus_monad (return n) (sint_monad 1))] (return v)
    }))
    })" ,

cfunction setCell external
param "STR ''r''" : "SType.TValue TSint"
and "STR ''c''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''grid'') [(stackLookup (STR ''r'') []), (stackLookup (STR ''c'') [])] (stackLookup (STR ''v'') []))
    })" ,

cfunction rowLen external
param "STR ''r''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (storeArrayLength (STR ''grid'') [(stackLookup (STR ''r'') [])]))
    })" ,

cfunction popCell external
param "STR ''r''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((pop_monad (STR ''grid'') [(stackLookup (STR ''r'') [])]))
    })" ,

cfunction pushPair external
where
  "(do {
      value_guard;
      ((allocate (STR ''pairs'') [] (sdefault (SType.TArray 2 (SType.TValue TSint)))))
    })" ,

cfunction setPair external
param "STR ''i''" : "SType.TValue TSint"
and "STR ''j''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''pairs'') [(stackLookup (STR ''i'') []), (stackLookup (STR ''j'') [])] (stackLookup (STR ''v'') []))
    })" ,

cfunction userPush external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((do {
      v <- (stackLookup (STR ''v'') []);
      (allocate (STR ''byUser'') [sender_monad] (sdefault (SType.TValue TSint)));
      n <- (storeArrayLength (STR ''byUser'') [sender_monad]);
      assign_storage_monad (STR ''byUser'') [sender_monad, (minus_monad (return n) (sint_monad 1))] (return v)
    }))
    })" ,

cfunction userGet external
param "STR ''a''" : "SType.TValue TAddress"
and "STR ''i''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (storeLookup (STR ''byUser'') [(stackLookup (STR ''a'') []), (stackLookup (STR ''i'') [])]))
    })" ,

cfunction userLen external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (storeArrayLength (STR ''byUser'') [(stackLookup (STR ''a'') [])]))
    })" ,

cfunction userPop external
where
  "(do {
      value_guard;
      ((pop_monad (STR ''byUser'') [sender_monad]))
    })" ,

cfunction newItem external
param "STR ''id''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (allocate (STR ''items'') [] (sdefault (SType.TEnum [SType.TValue TSint, SType.DArray (SType.TValue TSint)])));
      assign_storage_monad (STR ''items'') [(minus_monad_safe (storeArrayLength (STR ''items'') []) (sint_monad 1)), (sint_monad 0)] (stackLookup (STR ''id'') [])
    })
    })" ,

cfunction tag external
param "STR ''i''" : "SType.TValue TSint"
and "STR ''t''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((do {
      v <- (stackLookup (STR ''t'') []);
      (allocate (STR ''items'') [(stackLookup (STR ''i'') []), (sint_monad 1)] (sdefault (SType.TValue TSint)));
      n <- (storeArrayLength (STR ''items'') [(stackLookup (STR ''i'') []), (sint_monad 1)]);
      assign_storage_monad (STR ''items'') [(stackLookup (STR ''i'') []), (sint_monad 1), (minus_monad (return n) (sint_monad 1))] (return v)
    }))
    })" ,

cfunction tagLen external
param "STR ''i''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''total'') [] (storeArrayLength (STR ''items'') [(stackLookup (STR ''i'') []), (sint_monad 1)]))
    })" ,

cfunction dropItem external
param "STR ''i''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (delete_monad (STR ''items'') [(stackLookup (STR ''i'') [])] (sdefault (SType.TEnum [SType.TValue TSint, SType.DArray (SType.TValue TSint)])))
    })" ,

cfunction viaPointer external
param "STR ''r''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      sdecl (SType.DArray (SType.TValue TSint)) (STR ''row'');
      assign_stack_monad (STR ''row'') [] (storeLookup (STR ''grid'') [(stackLookup (STR ''r'') [])]);
      assign_stack_monad (STR ''row'') [(sint_monad 0)] (stackLookup (STR ''v'') []);
      assign_storage_monad (STR ''total'') [] (arrayLength (STR ''row'') [])
    })
    })"

end
