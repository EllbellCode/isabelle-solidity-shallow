theory Src_Pool_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

(* ext-fn {"assume": [["norevert"]], "params": ["address", "address", "uint256"], "ret": "bool", "sig": "transferFrom(address,address,uint256)", "view": false} *)
(* ext-fn {"assume": [["norevert"]], "params": ["address"], "ret": "uint256", "sig": "balanceOf(address)", "view": true} *)
(* ext-fn {"assume": [["norevert"]], "params": ["uint256", "uint256", "address"], "ret": "bool", "sig": "executeOperation(uint256,uint256,address)", "view": false} *)

(* Assumptions on the callees, from the @custom:assume natspec of the called functions: transferFrom(address,address,uint256): norevert; balanceOf(address): norevert; executeOperation(uint256,uint256,address): norevert *)
definition Pool_callee_assm :: "('a::address \<Rightarrow> bool) \<Rightarrow> (256 word \<Rightarrow> ('a, 'a valtype) storage \<Rightarrow> 'a balances \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> 'a valtype list \<Rightarrow> 'a valtype option) \<Rightarrow> bool" where
  "Pool_callee_assm isc r \<equiv>
    (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>b. r ep st bal a ''transferFrom(address,address,uint256)'' vs = Some (Bool b)))
    \<and> (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>w. r ep st bal a ''balanceOf(address)'' vs = Some (Uint w)))
    \<and> (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>b. r ep st bal a ''executeOperation(uint256,uint256,address)'' vs = Some (Bool b)))"

definition Pool_callee_wit :: "256 word \<Rightarrow> ('a::address, 'a valtype) storage \<Rightarrow> 'a balances \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> 'a valtype list \<Rightarrow> 'a valtype option" where
  "Pool_callee_wit ep st bal a f vs = (if f = ''transferFrom(address,address,uint256)'' then Some (Bool False) else (if f = ''balanceOf(address)'' then Some (Uint 0) else (if f = ''executeOperation(uint256,uint256,address)'' then Some (Bool False) else None)))"

locale Pool_Callee = Keccak256 +
  assumes callee_assumptions: "Pool_callee_assm ext_isc ext_result"

lemma (in Pool_Callee) callee_transferFrom_norevert: "ext_isc a \<Longrightarrow> \<exists>b. ext_result ep st bal a ''transferFrom(address,address,uint256)'' vs = Some (Bool b)"
  using callee_assumptions unfolding Pool_callee_assm_def by fastforce

lemma (in Pool_Callee) callee_balanceOf_norevert: "ext_isc a \<Longrightarrow> \<exists>w. ext_result ep st bal a ''balanceOf(address)'' vs = Some (Uint w)"
  using callee_assumptions unfolding Pool_callee_assm_def by fastforce

lemma (in Pool_Callee) callee_executeOperation_norevert: "ext_isc a \<Longrightarrow> \<exists>b. ext_result ep st bal a ''executeOperation(uint256,uint256,address)'' vs = Some (Bool b)"
  using callee_assumptions unfolding Pool_callee_assm_def by fastforce

lemma Pool_callee_assm_sat: "Pool_callee_assm (\<lambda>_. True) Pool_callee_wit"
  unfolding Pool_callee_assm_def Pool_callee_wit_def by auto

lemma Pool_Callee_sat: "Pool_Callee id (\<lambda>_. True) Pool_callee_wit"
  unfolding Pool_Callee_def Pool_Callee_axioms_def Keccak256_def using Pool_callee_assm_sat by simp

(* Omitted: view/pure functions with return values that nothing calls (no effect on state): balanceOf, allowance *)

section \<open>ERC20 Contract\<close>

contract ERC20 assuming Pool_Callee
  for "STR ''_totalSupply''" : "SType.TValue TSint"
  and "STR ''_balanceOf''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"
  and "STR ''_allowance''" : "SType.TMap (SType.TValue TAddress) (SType.TMap (SType.TValue TAddress) (SType.TValue TSint))"

constructor
where
  "skip_monad"

cfunction totalSupply external
where
  "(do {
      value_guard;
      (do {
      skip_monad;
      ((storeLookup (STR ''_totalSupply'') []))
    })
    })" ,

cfunction approve external
param "STR ''spender''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''_allowance'') [sender_monad, (stackLookup (STR ''spender'') [])] (stackLookup (STR ''amount'') []);
      skip_monad
    })
    })" ,

cfunction transfer external
param "STR ''recipient''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      assign_storage_monad (STR ''_balanceOf'') [sender_monad] (minus_monad_safe (storeLookup (STR ''_balanceOf'') [sender_monad]) (stackLookup (STR ''amount'') []));
      assign_storage_monad (STR ''_balanceOf'') [(stackLookup (STR ''recipient'') [])] (plus_monad_safe (storeLookup (STR ''_balanceOf'') [(stackLookup (STR ''recipient'') [])]) (stackLookup (STR ''amount'') []));
      skip_monad
    })
    })" ,

cfunction transferFrom external
param "STR ''from''" : "SType.TValue TAddress"
and "STR ''recipient''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (cond_monad (not_monad (equals_monad (storeLookup (STR ''_allowance'') [(stackLookup (STR ''from'') []), sender_monad]) (sint_monad 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (assign_storage_monad (STR ''_allowance'') [(stackLookup (STR ''from'') []), sender_monad] (minus_monad_safe (storeLookup (STR ''_allowance'') [(stackLookup (STR ''from'') []), sender_monad]) (stackLookup (STR ''amount'') []))) skip_monad);
      assign_storage_monad (STR ''_balanceOf'') [(stackLookup (STR ''from'') [])] (minus_monad_safe (storeLookup (STR ''_balanceOf'') [(stackLookup (STR ''from'') [])]) (stackLookup (STR ''amount'') []));
      assign_storage_monad (STR ''_balanceOf'') [(stackLookup (STR ''recipient'') [])] (plus_monad_safe (storeLookup (STR ''_balanceOf'') [(stackLookup (STR ''recipient'') [])]) (stackLookup (STR ''amount'') []));
      skip_monad
    })
    })" ,

cfunction u_mint
param "STR ''recipient''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      assign_storage_monad (STR ''_totalSupply'') [] (plus_monad_safe (storeLookup (STR ''_totalSupply'') []) (stackLookup (STR ''amount'') []));
      assign_storage_monad (STR ''_balanceOf'') [(stackLookup (STR ''recipient'') [])] (plus_monad_safe (storeLookup (STR ''_balanceOf'') [(stackLookup (STR ''recipient'') [])]) (stackLookup (STR ''amount'') []))
    })" ,

cfunction u_burn
param "STR ''user''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      assign_storage_monad (STR ''_totalSupply'') [] (minus_monad_safe (storeLookup (STR ''_totalSupply'') []) (stackLookup (STR ''amount'') []));
      assign_storage_monad (STR ''_balanceOf'') [(stackLookup (STR ''user'') [])] (minus_monad_safe (storeLookup (STR ''_balanceOf'') [(stackLookup (STR ''user'') [])]) (stackLookup (STR ''amount'') []))
    })" ,

cfunction totalSupply__int
where
  "(do {
      skip_monad;
      ((storeLookup (STR ''_totalSupply'') []))
    })"

(* Omitted: view/pure functions with return values that nothing calls (no effect on state): assetBalance *)

section \<open>Pool Contract\<close>

contract Pool is ERC20 assuming Pool_Callee
  for "STR ''_status''" : "SType.TValue TSint"
  and "STR ''asset''" : "SType.TValue TAddress"
  and "STR ''feeRate''" : "SType.TValue TSint"
  and "STR ''depositedAmount''" : "SType.TValue TSint"
  and "STR ''ghost_ext_epoch''" : "SType.TValue TSint"

constructor
initialiser
  "assign_storage_monad (STR ''depositedAmount'') [] (sint_monad 0)"
where
  "(value_guard)"

cfunction sharesToAmount external
param "STR ''shares''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      skip_monad;
      ((do {
      lv <- (mult_monad_safe (stackLookup (STR ''shares'') []) (storeLookup (STR ''depositedAmount'') []));
      rv <- (icall totalSupply__int);
      (cond_monad (equals_monad (return rv) (sint_monad 0)) (assert_monad false_monad) (div_monad (return lv) (return rv)))
    }))
    })
    })" ,

cfunction amountToShares external
param "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      skip_monad;
      ((cond_monad (equals_monad (storeLookup (STR ''depositedAmount'') []) (sint_monad 0)) (assert_monad false_monad) (div_monad (mult_monad_safe (stackLookup (STR ''amount'') []) (icall totalSupply__int)) (storeLookup (STR ''depositedAmount'') []))))
    })
    })" ,

cfunction amountToShares__int
param "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((cond_monad (equals_monad (storeLookup (STR ''depositedAmount'') []) (sint_monad 0)) (assert_monad false_monad) (div_monad (mult_monad_safe (stackLookup (STR ''amount'') []) (icall totalSupply__int)) (storeLookup (STR ''depositedAmount'') []))))
    })" ,

cfunction deposit external
param "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (not_monad (equals_monad (storeLookup (STR ''_status'') []) (sint_monad 2))));
      assign_storage_monad (STR ''_status'') [] (sint_monad 2);
      (do {
      decl TSint (STR ''shares'');
      (do {
      (cond_monad (cond_monad (equals_monad (icall totalSupply__int) (sint_monad 0)) true_monad (equals_monad (storeLookup (STR ''depositedAmount'') []) (sint_monad 0))) (assign_stack_monad (STR ''shares'') [] (stackLookup (STR ''amount'') [])) (do {
      assign_stack_monad (STR ''shares'') [] (do {
      a0 <- (stackLookup (STR ''amount'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (amountToShares__int w0))
    });
      (assert_monad (not_monad (equals_monad (stackLookup (STR ''shares'') []) (sint_monad 0))))
    }));
      (do {
      t <- (storeLookup (STR ''asset'') []);
      a0 <- sender_monad;
      a1 <- this_monad;
      a2 <- (stackLookup (STR ''amount'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''transferFrom(address,address,uint256)'' ep t [a0, a1, a2]
    });
      assign_storage_monad (STR ''depositedAmount'') [] (plus_monad_safe (storeLookup (STR ''depositedAmount'') []) (stackLookup (STR ''amount'') []));
      (do {
      a0 <- sender_monad;
      b0 <- readValue a0;
      w0 <- readAddress b0;
      a1 <- (stackLookup (STR ''shares'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (u_mint w0 w1))
    })
    })
    });
      assign_storage_monad (STR ''_status'') [] (sint_monad 1)
    })
    })
    })" ,

cfunction sharesToAmount__int
param "STR ''shares''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((do {
      lv <- (mult_monad_safe (stackLookup (STR ''shares'') []) (storeLookup (STR ''depositedAmount'') []));
      rv <- (icall totalSupply__int);
      (cond_monad (equals_monad (return rv) (sint_monad 0)) (assert_monad false_monad) (div_monad (return lv) (return rv)))
    }))
    })" ,

cfunction withdraw external
param "STR ''shares''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (not_monad (equals_monad (storeLookup (STR ''_status'') []) (sint_monad 2))));
      assign_storage_monad (STR ''_status'') [] (sint_monad 2);
      (do {
      decl TSint (STR ''amountOut'');
      (do {
      decl TSint (STR ''poolBalance'');
      assign_stack_monad (STR ''poolBalance'') [] (do {
      t <- (storeLookup (STR ''asset'') []);
      a0 <- this_monad;
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    });
      (assert_monad (not_monad (equals_monad (stackLookup (STR ''poolBalance'') []) (sint_monad 0))));
      assign_stack_monad (STR ''amountOut'') [] (do {
      a0 <- (stackLookup (STR ''shares'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (sharesToAmount__int w0))
    });
      (assert_monad (not_monad (equals_monad (stackLookup (STR ''amountOut'') []) (sint_monad 0))));
      (do {
      a0 <- sender_monad;
      b0 <- readValue a0;
      w0 <- readAddress b0;
      a1 <- (stackLookup (STR ''shares'') []);
      b1 <- readValue a1;
      w1 <- readSint b1;
      (icall (u_burn w0 w1))
    });
      (do {
      t <- (storeLookup (STR ''asset'') []);
      a0 <- this_monad;
      a1 <- sender_monad;
      a2 <- (stackLookup (STR ''amountOut'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''transferFrom(address,address,uint256)'' ep t [a0, a1, a2]
    });
      assign_storage_monad (STR ''depositedAmount'') [] (minus_monad_safe (storeLookup (STR ''depositedAmount'') []) (stackLookup (STR ''amountOut'') []))
    })
    });
      assign_storage_monad (STR ''_status'') [] (sint_monad 1)
    })
    })
    })" ,

cfunction calcPremium__int
param "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      skip_monad;
      ((cond_monad (equals_monad (sint_monad 10000) (sint_monad 0)) (assert_monad false_monad) (div_monad (mult_monad_safe (stackLookup (STR ''amount'') []) (storeLookup (STR ''feeRate'') [])) (sint_monad 10000))))
    })" ,

cfunction flashLoan external
param "STR ''receiverAddress''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (do {
      (assert_monad (not_monad (equals_monad (storeLookup (STR ''_status'') []) (sint_monad 2))));
      assign_storage_monad (STR ''_status'') [] (sint_monad 2);
      (do {
      decl TSint (STR ''totalPremium'');
      assign_stack_monad (STR ''totalPremium'') [] (do {
      a0 <- (stackLookup (STR ''amount'') []);
      b0 <- readValue a0;
      w0 <- readSint b0;
      (icall (calcPremium__int w0))
    });
      (assert_monad (not_monad (equals_monad (stackLookup (STR ''totalPremium'') []) (sint_monad 0))));
      decl TSint (STR ''amountPlusPremium'');
      assign_stack_monad (STR ''amountPlusPremium'') [] (plus_monad_safe (stackLookup (STR ''amount'') []) (stackLookup (STR ''totalPremium'') []));
      (do {
      t <- (storeLookup (STR ''asset'') []);
      a0 <- this_monad;
      a1 <- sender_monad;
      a2 <- (stackLookup (STR ''amount'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''transferFrom(address,address,uint256)'' ep t [a0, a1, a2]
    });
      assign_storage_monad (STR ''depositedAmount'') [] (minus_monad_safe (storeLookup (STR ''depositedAmount'') []) (stackLookup (STR ''amount'') []));
      (assert_monad (do {
      t <- (stackLookup (STR ''receiverAddress'') []);
      a0 <- (stackLookup (STR ''amount'') []);
      a1 <- (stackLookup (STR ''totalPremium'') []);
      a2 <- sender_monad;
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''executeOperation(uint256,uint256,address)'' ep t [a0, a1, a2]
    }));
      (do {
      t <- (storeLookup (STR ''asset'') []);
      a0 <- sender_monad;
      a1 <- this_monad;
      a2 <- (stackLookup (STR ''amountPlusPremium'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''transferFrom(address,address,uint256)'' ep t [a0, a1, a2]
    });
      assign_storage_monad (STR ''depositedAmount'') [] (plus_monad_safe (storeLookup (STR ''depositedAmount'') []) (stackLookup (STR ''amountPlusPremium'') []))
    });
      assign_storage_monad (STR ''_status'') [] (sint_monad 1)
    })
    })
    })" ,

cfunction calcPremium external
param "STR ''amount''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      skip_monad;
      ((cond_monad (equals_monad (sint_monad 10000) (sint_monad 0)) (assert_monad false_monad) (div_monad (mult_monad_safe (stackLookup (STR ''amount'') []) (storeLookup (STR ''feeRate'') [])) (sint_monad 10000))))
    })
    })"

end
