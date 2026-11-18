theory Src_Inh1_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>A Contract\<close>

contract A
  for "STR ''a''" : "SType.TValue TSint"
  and "STR ''owner''" : "SType.TValue TAddress"
  and "STR ''log''" : "SType.TValue TSint"

constructor
param "STR ''_i0_x''" : "SType.TValue TSint"
initialiser
  "assign_storage_monad (STR ''a'') [] (sint_monad 5)"
where
  "(do {
      assign_storage_monad (STR ''a'') [] (plus_monad_safe (storeLookup (STR ''a'') []) (stackLookup (STR ''_i0_x'') []));
      assign_storage_monad (STR ''owner'') [] sender_monad;
      assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 1))
    })"

cfunction f external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 4)))
    })" ,

cfunction g
where
  "(assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 5)))" ,

cfunction callG external
where
  "(do {
      value_guard;
      ((icall g))
    })" ,

cfunction setA external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (equals_monad sender_monad (storeLookup (STR ''owner'') [])));
      (assign_storage_monad (STR ''a'') [] (stackLookup (STR ''v'') []))
    })
    })
    })" ,

cfunction f__int
where
  "(assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 4)))"

section \<open>B Contract\<close>

contract B is A ("(plus_monad_safe (stackLookup (STR ''_i1_y'') []) (sint_monad 1))")
  for "STR ''b''" : "SType.TValue TSint"

constructor
param "STR ''_i1_y''" : "SType.TValue TSint"
initialiser
  "assign_storage_monad (STR ''b'') [] (plus_monad_safe (storeLookup (STR ''a'') []) (sint_monad 10))"
where
  "(do {
      assign_storage_monad (STR ''b'') [] (plus_monad_safe (storeLookup (STR ''b'') []) (stackLookup (STR ''_i1_y'') []));
      assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 2))
    })"

cfunction f external
where
  "(do {
      value_guard;
      (do {
      (icall super_f__int);
      assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 6))
    })
    })" ,

cfunction g
where
  "(assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 7)))" ,

cfunction f__int
where
  "(do {
      (icall super_f__int);
      assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 6))
    })"

section \<open>C Contract\<close>

contract C is B ("(sint_monad 5)")
  for "STR ''c''" : "SType.TValue TSint"

constructor payable
where
  "(do {
      assign_storage_monad (STR ''c'') [] (plus_monad_safe (storeLookup (STR ''a'') []) (storeLookup (STR ''b'') []));
      assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 3))
    })"

cfunction f external
where
  "(do {
      value_guard;
      (do {
      (icall super_f__int);
      assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 8))
    })
    })" ,

cfunction h external
param "STR ''d''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (equals_monad sender_monad (storeLookup (STR ''owner'') [])));
      (do {
      assign_storage_monad (STR ''c'') [] (plus_monad_safe (storeLookup (STR ''c'') []) (stackLookup (STR ''d'') []));
      assign_storage_monad (STR ''a'') [] (plus_monad_safe (storeLookup (STR ''a'') []) (sint_monad 1))
    })
    })
    })
    })" ,

cfunction f__int
where
  "(do {
      (icall super_f__int);
      assign_storage_monad (STR ''log'') [] (plus_monad_safe (mult_monad_safe (storeLookup (STR ''log'') []) (sint_monad 10)) (sint_monad 8))
    })"

end
