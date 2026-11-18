theory Src_Widths_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

section \<open>Widths Contract\<close>

contract Widths
  for "STR ''a8''" : "SType.TValue TSint"
  and "STR ''a64''" : "SType.TValue TSint"
  and "STR ''a128''" : "SType.TValue TSint"
  and "STR ''a192''" : "SType.TValue TSint"
  and "STR ''a248''" : "SType.TValue TSint"
  and "STR ''a256''" : "SType.TValue TSint"
  and "STR ''b''" : "SType.TValue TBool"
  and "STR ''m8''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"
  and "STR ''k8''" : "SType.TMap (SType.TValue TSint) (SType.TValue TSint)"

constructor
param "STR ''init''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''init'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (stackLookup (STR ''init'') []))
    })
    })"

cfunction add8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (below_monad (plus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 256)))
    })
    })" ,

cfunction sub8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (minus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })
    })" ,

cfunction mul8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (below_monad (mult_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 256)))
    })
    })" ,

cfunction add64 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 18446744073709551616));
      (assign_storage_monad (STR ''a64'') [] (below_monad (plus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 18446744073709551616)))
    })
    })" ,

cfunction sub64 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 18446744073709551616));
      (assign_storage_monad (STR ''a64'') [] (minus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })
    })" ,

cfunction mul64 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 18446744073709551616));
      (assign_storage_monad (STR ''a64'') [] (below_monad (mult_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 18446744073709551616)))
    })
    })" ,

cfunction add128 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 340282366920938463463374607431768211456));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 340282366920938463463374607431768211456));
      (assign_storage_monad (STR ''a128'') [] (below_monad (plus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 340282366920938463463374607431768211456)))
    })
    })" ,

cfunction mul128 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 340282366920938463463374607431768211456));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 340282366920938463463374607431768211456));
      (assign_storage_monad (STR ''a128'') [] (below_monad (mult_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 340282366920938463463374607431768211456)))
    })
    })" ,

cfunction mul192 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 6277101735386680763835789423207666416102355444464034512896));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 6277101735386680763835789423207666416102355444464034512896));
      (assign_storage_monad (STR ''a192'') [] (below_monad (mult_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 6277101735386680763835789423207666416102355444464034512896)))
    })
    })" ,

cfunction add248 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656));
      (assign_storage_monad (STR ''a248'') [] (below_monad (plus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656)))
    })
    })" ,

cfunction mul248 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656));
      (assign_storage_monad (STR ''a248'') [] (below_monad (mult_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656)))
    })
    })" ,

cfunction uadd8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      ((assign_storage_monad (STR ''a8'') [] (mod_monad (plus_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 256))))
    })
    })" ,

cfunction usub8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      ((assign_storage_monad (STR ''a8'') [] (mod_monad (minus_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 256))))
    })
    })" ,

cfunction umul8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      ((assign_storage_monad (STR ''a8'') [] (mod_monad (mult_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 256))))
    })
    })" ,

cfunction uadd64 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 18446744073709551616));
      ((assign_storage_monad (STR ''a64'') [] (mod_monad (plus_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 18446744073709551616))))
    })
    })" ,

cfunction usub64 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 18446744073709551616));
      ((assign_storage_monad (STR ''a64'') [] (mod_monad (minus_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 18446744073709551616))))
    })
    })" ,

cfunction umul64 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 18446744073709551616));
      ((assign_storage_monad (STR ''a64'') [] (mod_monad (mult_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 18446744073709551616))))
    })
    })" ,

cfunction umul128 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 340282366920938463463374607431768211456));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 340282366920938463463374607431768211456));
      ((assign_storage_monad (STR ''a128'') [] (mod_monad (mult_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 340282366920938463463374607431768211456))))
    })
    })" ,

cfunction umul192 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 6277101735386680763835789423207666416102355444464034512896));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 6277101735386680763835789423207666416102355444464034512896));
      ((assign_storage_monad (STR ''a192'') [] (mod_monad (mult_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 6277101735386680763835789423207666416102355444464034512896))))
    })
    })" ,

cfunction usub248 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656));
      ((assign_storage_monad (STR ''a248'') [] (mod_monad (minus_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656))))
    })
    })" ,

cfunction uadd248 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656));
      ((assign_storage_monad (STR ''a248'') [] (mod_monad (plus_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 452312848583266388373324160190187140051835877600158453279131187530910662656))))
    })
    })" ,

cfunction wide external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a256'') [] (below_monad (plus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 256)))
    })
    })" ,

cfunction wideConv external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a256'') [] (plus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })
    })" ,

cfunction mixed external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 18446744073709551616));
      (assign_storage_monad (STR ''a64'') [] (below_monad (plus_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 18446744073709551616)))
    })
    })" ,

cfunction mixed2 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 340282366920938463463374607431768211456));
      (assign_storage_monad (STR ''a128'') [] (below_monad (mult_monad_safe (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])) (sint_monad 340282366920938463463374607431768211456)))
    })
    })" ,

cfunction mixedSub external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 340282366920938463463374607431768211456));
      (assign_storage_monad (STR ''a128'') [] (minus_monad_safe (stackLookup (STR ''y'') []) (stackLookup (STR ''x'') [])))
    })
    })" ,

cfunction lit8 external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (below_monad (plus_monad_safe (stackLookup (STR ''x'') []) (sint_monad 200)) (sint_monad 256)))
    })
    })" ,

cfunction lit8m external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (below_monad (mult_monad_safe (stackLookup (STR ''x'') []) (sint_monad 3)) (sint_monad 256)))
    })
    })" ,

cfunction dv8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (div_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })
    })" ,

cfunction md8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (mod_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })
    })" ,

cfunction dv128 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 340282366920938463463374607431768211456));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 340282366920938463463374607431768211456));
      (assign_storage_monad (STR ''a128'') [] (cond_monad (equals_monad (stackLookup (STR ''y'') []) (sint_monad 0)) (assert_monad false_monad) (div_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })
    })" ,

cfunction inc8 external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''a8'') [] (below_monad (plus_monad_safe (storeLookup (STR ''a8'') []) (sint_monad 1)) (sint_monad 256)))
    })" ,

cfunction dec8 external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''a8'') [] (minus_monad_safe (storeLookup (STR ''a8'') []) (sint_monad 1)))
    })" ,

cfunction addEq8 external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (below_monad (plus_monad_safe (storeLookup (STR ''a8'') []) (stackLookup (STR ''x'') [])) (sint_monad 256)))
    })
    })" ,

cfunction subEq8 external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a8'') [] (minus_monad_safe (storeLookup (STR ''a8'') []) (stackLookup (STR ''x'') [])))
    })
    })" ,

cfunction mulEq64 external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616));
      (assign_storage_monad (STR ''a64'') [] (below_monad (mult_monad_safe (storeLookup (STR ''a64'') []) (stackLookup (STR ''x'') [])) (sint_monad 18446744073709551616)))
    })
    })" ,

cfunction uinc8 external
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''a8'') [] (mod_monad (plus_monad (storeLookup (STR ''a8'') []) (sint_monad 1)) (sint_monad 256))))
    })" ,

cfunction udec8 external
where
  "(do {
      value_guard;
      ((assign_storage_monad (STR ''a8'') [] (mod_monad (minus_monad (storeLookup (STR ''a8'') []) (sint_monad 1)) (sint_monad 256))))
    })" ,

cfunction local8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (do {
      decl TSint (STR ''t'');
      assign_stack_monad (STR ''t'') [] (stackLookup (STR ''x'') []);
      assign_stack_monad (STR ''t'') [] (below_monad (plus_monad_safe (stackLookup (STR ''t'') []) (stackLookup (STR ''y'') [])) (sint_monad 256));
      assign_storage_monad (STR ''a8'') [] (stackLookup (STR ''t'') [])
    })
    })
    })" ,

cfunction down8 external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''a8'') [] (mod_monad (stackLookup (STR ''x'') []) (sint_monad 256)))
    })" ,

cfunction down64 external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 340282366920938463463374607431768211456));
      (assign_storage_monad (STR ''a64'') [] (mod_monad (stackLookup (STR ''x'') []) (sint_monad 18446744073709551616)))
    })
    })" ,

cfunction down192 external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''a192'') [] (mod_monad (stackLookup (STR ''x'') []) (sint_monad 6277101735386680763835789423207666416102355444464034512896)))
    })" ,

cfunction up external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a256'') [] (stackLookup (STR ''x'') []))
    })
    })" ,

cfunction upd external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a64'') [] (below_monad (mult_monad_safe (stackLookup (STR ''x'') []) (sint_monad 1000000000000)) (sint_monad 18446744073709551616)))
    })
    })" ,

cfunction chain external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''a128'') [] (below_monad (plus_monad_safe (mod_monad (stackLookup (STR ''x'') []) (sint_monad 256)) (sint_monad 1)) (sint_monad 340282366920938463463374607431768211456)))
    })" ,

cfunction lt8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''b'') [] (less_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })
    })" ,

cfunction ge8 external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 256));
      (assign_storage_monad (STR ''b'') [] (not_monad (less_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') []))))
    })
    })" ,

cfunction eqMixed external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''y'') []) (sint_monad 18446744073709551616));
      (assign_storage_monad (STR ''b'') [] (equals_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })
    })" ,

cfunction ltMixed external
param "STR ''x''" : "SType.TValue TSint"
and "STR ''y''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''b'') [] (less_monad (stackLookup (STR ''x'') []) (stackLookup (STR ''y'') [])))
    })
    })" ,

cfunction setM external
param "STR ''who''" : "SType.TValue TAddress"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 256));
      (assign_storage_monad (STR ''m8'') [(stackLookup (STR ''who'') [])] (stackLookup (STR ''v'') []))
    })
    })" ,

cfunction addM external
param "STR ''who''" : "SType.TValue TAddress"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 256));
      (assign_storage_monad (STR ''m8'') [(stackLookup (STR ''who'') [])] (below_monad (plus_monad_safe (storeLookup (STR ''m8'') [(stackLookup (STR ''who'') [])]) (stackLookup (STR ''v'') [])) (sint_monad 256)))
    })
    })" ,

cfunction setK external
param "STR ''k''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''k'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 18446744073709551616));
      (assign_storage_monad (STR ''k8'') [(stackLookup (STR ''k'') [])] (stackLookup (STR ''v'') []))
    })
    })" ,

cfunction addK external
param "STR ''k''" : "SType.TValue TSint"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''k'') []) (sint_monad 256));
      assert_monad (less_monad (stackLookup (STR ''v'') []) (sint_monad 18446744073709551616));
      (assign_storage_monad (STR ''k8'') [(stackLookup (STR ''k'') [])] (below_monad (plus_monad_safe (storeLookup (STR ''k8'') [(stackLookup (STR ''k'') [])]) (stackLookup (STR ''v'') [])) (sint_monad 18446744073709551616)))
    })
    })" ,

cfunction loop8 external
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
      assign_stack_monad (STR ''i'') [] (sint_monad 0);
      (while_monad (less_monad (stackLookup (STR ''i'') []) (stackLookup (STR ''n'') [])) (do {
      (assign_stack_monad (STR ''s'') [] (below_monad (plus_monad_safe (stackLookup (STR ''s'') []) (stackLookup (STR ''i'') [])) (sint_monad 256)));
      assign_stack_monad (STR ''i'') [] (below_monad (plus_monad_safe (stackLookup (STR ''i'') []) (sint_monad 1)) (sint_monad 256))
    }));
      assign_storage_monad (STR ''a8'') [] (stackLookup (STR ''s'') [])
    })
    })
    })" ,

cfunction unused external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a256'') [] (sint_monad 1))
    })
    })" ,

cfunction unusedPay external payable
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      assert_monad (less_monad (stackLookup (STR ''x'') []) (sint_monad 256));
      (assign_storage_monad (STR ''a256'') [] (sint_monad 2))
    })"

end
