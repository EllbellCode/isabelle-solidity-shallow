theory Src_Libs_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Libs Contract\<close>

contract Libs
  for "STR ''x''" : "SType.TValue TSint"
  and "STR ''small''" : "SType.TValue TSint"
  and "STR ''flag''" : "SType.TValue TBool"
  and "STR ''bal''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor
where
  "(value_guard)"

cfunction guard
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((cond_monad (less_monad (sint_monad 10) (stackLookup (STR ''p'') [])) ((sint_monad 1)) (do {
      assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (sint_monad 1));
      (cond_monad (equals_monad (stackLookup (STR ''p'') []) (sint_monad 3)) ((sint_monad 2)) ((sint_monad 3)))
    })))
    })" ,

cfunction early
param "STR ''p''" : "SType.TValue TSint"
where
  "((cond_monad (equals_monad (stackLookup (STR ''p'') []) (sint_monad 0)) skip_monad (assign_storage_monad (STR ''x'') [] (plus_monad_safe (storeLookup (STR ''x'') []) (stackLookup (STR ''p'') [])))))" ,

cfunction SafeMath__add
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      (do {
      decl TSint (STR ''c'');
      assign_stack_monad (STR ''c'') [] (plus_monad_safe (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []));
      (assert_monad (not_monad (less_monad (stackLookup (STR ''c'') []) (stackLookup (STR ''a'') []))));
      (stackLookup (STR ''c'') [])
    })
    })" ,

cfunction t1 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (storeLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''p'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__add w0 w1))
    }))
    })" ,

cfunction SafeMath__sub_65
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
and "STR ''message''" : "SType.TValue (TBytes 0)"
where
  "(do {
      skip_monad;
      (do {
      (assert_monad (not_monad (less_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []))));
      (minus_monad_safe (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []))
    })
    })" ,

cfunction SafeMath__sub
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''b'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      a2 <- (bytes_monad2 [CHR 0x53, CHR 0x61, CHR 0x66, CHR 0x65, CHR 0x4D, CHR 0x61, CHR 0x74, CHR 0x68, CHR 0x3A, CHR 0x20, CHR 0x73, CHR 0x75, CHR 0x62, CHR 0x74, CHR 0x72, CHR 0x61, CHR 0x63, CHR 0x74, CHR 0x69, CHR 0x6F, CHR 0x6E, CHR 0x20, CHR 0x6F, CHR 0x76, CHR 0x65, CHR 0x72, CHR 0x66, CHR 0x6C, CHR 0x6F, CHR 0x77]);
      b2 <- readValue a2;
      w2 <- readBytes b2;
      (icall (SafeMath__sub_65 w0 w1 w2))
    }))
    })" ,

cfunction t2 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (storeLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''p'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__sub w0 w1))
    }))
    })" ,

cfunction t3 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (storeLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''p'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      a2 <- (bytes_monad2 [CHR 0x63, CHR 0x75, CHR 0x73, CHR 0x74, CHR 0x6F, CHR 0x6D]);
      b2 <- readValue a2;
      w2 <- readBytes b2;
      (icall (SafeMath__sub_65 w0 w1 w2))
    }))
    })" ,

cfunction SafeMath__mul
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((cond_monad (equals_monad (stackLookup (STR ''a'') []) (sint_monad 0)) ((sint_monad 0)) (do {
      decl TSint (STR ''c'');
      assign_stack_monad (STR ''c'') [] (mult_monad_safe (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []));
      (assert_monad (equals_monad (cond_monad (equals_monad (stackLookup (STR ''a'') []) (sint_monad 0)) (assert_monad false_monad) (div_monad (stackLookup (STR ''c'') []) (stackLookup (STR ''a'') []))) (stackLookup (STR ''b'') [])));
      (stackLookup (STR ''c'') [])
    })))
    })" ,

cfunction t4 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (storeLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''p'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__mul w0 w1))
    }))
    })" ,

cfunction SafeMath__div
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      (do {
      (assert_monad (less_monad (sint_monad 0) (stackLookup (STR ''b'') [])));
      (cond_monad (equals_monad (stackLookup (STR ''b'') []) (sint_monad 0)) (assert_monad false_monad) (div_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])))
    })
    })" ,

cfunction t5 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (storeLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''p'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__div w0 w1))
    }))
    })" ,

cfunction SafeMath__min
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((cond_monad (less_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') [])) ((stackLookup (STR ''a'') [])) ((stackLookup (STR ''b'') []))))
    })" ,

cfunction t6 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (storeLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''p'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__min w0 w1))
    }))
    })" ,

cfunction SafeMath__wrappingAdd
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      (((plus_monad (stackLookup (STR ''a'') []) (stackLookup (STR ''b'') []))))
    })" ,

cfunction t7 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (storeLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''p'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__wrappingAdd w0 w1))
    }))
    })" ,

cfunction SafeMath__mulDiv
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
and "STR ''c''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((do {
      a0 <- (do {
      a0 <- (stackLookup (STR ''a'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''b'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__mul w0 w1))
    });
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''c'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__div w0 w1))
    }))
    })" ,

cfunction t8 external
param "STR ''a''" : "SType.TValue TSint"
and "STR ''b''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (storeLookup (STR ''x'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''a'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      a2 <- (stackLookup (STR ''b'') []);
      b2 <- readValue a2;
      w2 <- readSint b2;
      (icall (SafeMath__mulDiv w0 w1 w2))
    }))
    })" ,

cfunction Small__inc
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((below_monad (plus_monad_safe (stackLookup (STR ''a'') []) (sint_monad 1)) (sint_monad 256)))
    })" ,

cfunction t9 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''p'') []) (sint_monad 256));
      (assign_storage_monad (STR ''small'') [] (do {
      a0 <- (stackLookup (STR ''p'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (Small__inc w0))
    }))
    })
    })" ,

cfunction Small__isZero
param "STR ''a''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((equals_monad (stackLookup (STR ''a'') []) (sint_monad 0)))
    })" ,

cfunction t10 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''flag'') [] (do {
      a0 <- (stackLookup (STR ''p'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (Small__isZero w0))
    }))
    })" ,

cfunction t11 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''bal'') [sender_monad] (do {
      a0 <- (do {
      a0 <- (storeLookup (STR ''bal'') [sender_monad]);
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (stackLookup (STR ''p'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__add w0 w1))
    });
      b0 <- readValue a0;
      w0 <- readSint b0;
      a1 <- (sint_monad 2);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (SafeMath__mul w0 w1))
    }))
    })" ,

cfunction t12 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''x'') [] (do {
      a0 <- (stackLookup (STR ''p'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (guard w0))
    }))
    })" ,

cfunction t13 external
param "STR ''p''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      ((do {
      a0 <- (stackLookup (STR ''p'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (early w0))
    }))
    })"

end
