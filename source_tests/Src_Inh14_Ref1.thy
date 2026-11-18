theory Src_Inh14_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Ra Contract\<close>

contract Ra
  for "STR ''a''" : "SType.TValue TSint"
  and "STR ''marker''" : "SType.TValue TSint"
  and "STR ''ini''" : "SType.TValue TSint"

constructor
param "STR ''_i0_x''" : "SType.TValue TSint"
initialiser
  "assign_storage_monad (STR ''ini'') [] (sint_monad 4)"
where
  "(do {
      decl TSint (STR ''_m1_v'');
      assign_stack_monad (STR ''_m1_v'') [] (stackLookup (STR ''_i0_x'') []);
      (do {
      decl TSint (STR ''_m1_t'');
      assign_stack_monad (STR ''_m1_t'') [] (plus_monad_safe (stackLookup (STR ''_m1_v'') []) (sint_monad 1));
      assign_storage_monad (STR ''marker'') [] (stackLookup (STR ''_m1_t'') []);
      (assign_storage_monad (STR ''a'') [] (plus_monad_safe (stackLookup (STR ''_i0_x'') []) (storeLookup (STR ''ini'') [])))
    })
    })"

cfunction bump external
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''_m1_v'');
      assign_stack_monad (STR ''_m1_v'') [] (sint_monad 1);
      (do {
      decl TSint (STR ''_m1_t'');
      assign_stack_monad (STR ''_m1_t'') [] (plus_monad_safe (stackLookup (STR ''_m1_v'') []) (sint_monad 1));
      assign_storage_monad (STR ''marker'') [] (stackLookup (STR ''_m1_t'') []);
      (assign_storage_monad (STR ''a'') [] (plus_monad_safe (storeLookup (STR ''a'') []) (sint_monad 1)))
    })
    })
    })"

section \<open>Rb Contract\<close>

contract Rb is Ra

constructor
replacing Ra
  "(do {
      decl TSint (STR ''_m1_v'');
      assign_stack_monad (STR ''_m1_v'') [] (stackLookup (STR ''_i0_x'') []);
      (do {
      decl TSint (STR ''_m1_t'');
      assign_stack_monad (STR ''_m1_t'') [] (plus_monad_safe (stackLookup (STR ''_m1_v'') []) (sint_monad 20));
      assign_storage_monad (STR ''marker'') [] (stackLookup (STR ''_m1_t'') []);
      (assign_storage_monad (STR ''a'') [] (plus_monad_safe (stackLookup (STR ''_i0_x'') []) (storeLookup (STR ''ini'') [])))
    })
    })"
where
  "skip_monad"

cfunction bump external
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''_m1_v'');
      assign_stack_monad (STR ''_m1_v'') [] (sint_monad 1);
      (do {
      decl TSint (STR ''_m1_t'');
      assign_stack_monad (STR ''_m1_t'') [] (plus_monad_safe (stackLookup (STR ''_m1_v'') []) (sint_monad 20));
      assign_storage_monad (STR ''marker'') [] (stackLookup (STR ''_m1_t'') []);
      (assign_storage_monad (STR ''a'') [] (plus_monad_safe (storeLookup (STR ''a'') []) (sint_monad 1)))
    })
    })
    })"

section \<open>Rc Contract\<close>

contract Rc is Ra ("(sint_monad 3)"), Rb
  for "STR ''c''" : "SType.TValue TSint"

constructor
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''c'') [] (storeLookup (STR ''marker'') []))
    })"

cfunction more external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''c'') [] (plus_monad_safe (storeLookup (STR ''c'') []) (storeLookup (STR ''marker'') [])))
    })"

end
