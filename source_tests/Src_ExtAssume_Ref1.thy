theory Src_ExtAssume_Ref1
  imports Solidity_Main Solidity_Ext
begin

(* Reference specification: the output of transpile.py --inherit for the sample of the same name. *)

(* ext-fn {"assume": [["norevert"], ["max", "1000000"]], "params": ["address"], "ret": "uint256", "sig": "balanceOf(address)", "view": true} *)
(* ext-fn {"params": ["address", "uint256"], "ret": "bool", "sig": "transfer(address,uint256)", "view": false} *)
(* ext-fn {"params": ["address", "address", "uint256"], "ret": "bool", "sig": "transferFrom(address,address,uint256)", "view": false} *)
(* ext-fn {"assume": [["constant"], ["norevert"]], "params": [], "ret": "uint8", "sig": "decimals()", "view": true} *)
(* ext-fn {"params": [], "ret": null, "sig": "ping()", "view": false} *)
(* ext-fn {"assume": [["norevert"], ["min", "3"], ["max", "9"]], "params": ["uint256"], "ret": "uint256", "sig": "grow(uint256)", "view": false} *)
(* ext-fn {"assume": [["norevert"]], "params": ["address", "uint256"], "ret": "bool", "sig": "approve(address,uint256)", "view": false} *)
(* ext-fn {"assume": [["min", "10"], ["max", "20"]], "params": ["uint256"], "ret": "uint256", "sig": "quota(uint256)", "view": true} *)
(* ext-fn {"assume": [["norevert"]], "params": [], "ret": "address", "sig": "owner()", "view": true} *)
(* ext-fn {"assume": [["norevert"]], "params": ["uint256"], "ret": "bool", "sig": "flag(uint256)", "view": true} *)

(* Assumptions on the callees, from the @custom:assume natspec of the called functions: balanceOf(address): norevert, max 1000000; decimals(): constant, norevert; grow(uint256): norevert, min 3, max 9; approve(address,uint256): norevert; quota(uint256): min 10, max 20; owner(): norevert; flag(uint256): norevert *)
definition ExtAssume_callee_assm :: "('a::address \<Rightarrow> bool) \<Rightarrow> (256 word \<Rightarrow> ('a, 'a valtype) storage \<Rightarrow> 'a balances \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> 'a valtype list \<Rightarrow> 'a valtype option) \<Rightarrow> bool" where
  "ExtAssume_callee_assm isc r \<equiv>
    (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>w. r ep st bal a ''balanceOf(address)'' vs = Some (Uint w)))
    \<and> (\<forall>ep st bal a vs w. isc a \<longrightarrow> r ep st bal a ''balanceOf(address)'' vs = Some (Uint w) \<longrightarrow> unat w \<le> 1000000)
    \<and> (\<forall>ep ep' st st' bal bal' a vs. isc a \<longrightarrow> r ep st bal a ''decimals()'' vs = r ep' st' bal' a ''decimals()'' vs)
    \<and> (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>w. r ep st bal a ''decimals()'' vs = Some (Uint w) \<and> unat w < 256))
    \<and> (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>w. r ep st bal a ''grow(uint256)'' vs = Some (Uint w)))
    \<and> (\<forall>ep st bal a vs w. isc a \<longrightarrow> r ep st bal a ''grow(uint256)'' vs = Some (Uint w) \<longrightarrow> 3 \<le> unat w)
    \<and> (\<forall>ep st bal a vs w. isc a \<longrightarrow> r ep st bal a ''grow(uint256)'' vs = Some (Uint w) \<longrightarrow> unat w \<le> 9)
    \<and> (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>b. r ep st bal a ''approve(address,uint256)'' vs = Some (Bool b)))
    \<and> (\<forall>ep st bal a vs w. isc a \<longrightarrow> r ep st bal a ''quota(uint256)'' vs = Some (Uint w) \<longrightarrow> 10 \<le> unat w)
    \<and> (\<forall>ep st bal a vs w. isc a \<longrightarrow> r ep st bal a ''quota(uint256)'' vs = Some (Uint w) \<longrightarrow> unat w \<le> 20)
    \<and> (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>x. r ep st bal a ''owner()'' vs = Some (Address x)))
    \<and> (\<forall>ep st bal a vs. isc a \<longrightarrow> (\<exists>b. r ep st bal a ''flag(uint256)'' vs = Some (Bool b)))"

definition ExtAssume_callee_wit :: "256 word \<Rightarrow> ('a::address, 'a valtype) storage \<Rightarrow> 'a balances \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> 'a valtype list \<Rightarrow> 'a valtype option" where
  "ExtAssume_callee_wit ep st bal a f vs = (if f = ''balanceOf(address)'' then Some (Uint 0) else (if f = ''decimals()'' then Some (Uint 0) else (if f = ''grow(uint256)'' then Some (Uint 3) else (if f = ''approve(address,uint256)'' then Some (Bool False) else (if f = ''quota(uint256)'' then Some (Uint 10) else (if f = ''owner()'' then Some (Address null) else (if f = ''flag(uint256)'' then Some (Bool False) else None)))))))"

locale ExtAssume_Callee = Keccak256 +
  assumes callee_assumptions: "ExtAssume_callee_assm ext_isc ext_result"

lemma (in ExtAssume_Callee) callee_balanceOf_norevert: "ext_isc a \<Longrightarrow> \<exists>w. ext_result ep st bal a ''balanceOf(address)'' vs = Some (Uint w)"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_balanceOf_max_1000000: "ext_result ep st bal a ''balanceOf(address)'' vs = Some (Uint w) \<Longrightarrow> ext_isc a \<Longrightarrow> unat w \<le> 1000000"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_decimals_constant: "ext_isc a \<Longrightarrow> ext_result ep st bal a ''decimals()'' vs = ext_result ep' st' bal' a ''decimals()'' vs"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_decimals_norevert: "ext_isc a \<Longrightarrow> \<exists>w. ext_result ep st bal a ''decimals()'' vs = Some (Uint w) \<and> unat w < 256"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_grow_norevert: "ext_isc a \<Longrightarrow> \<exists>w. ext_result ep st bal a ''grow(uint256)'' vs = Some (Uint w)"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_grow_min_3: "ext_result ep st bal a ''grow(uint256)'' vs = Some (Uint w) \<Longrightarrow> ext_isc a \<Longrightarrow> 3 \<le> unat w"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_grow_max_9: "ext_result ep st bal a ''grow(uint256)'' vs = Some (Uint w) \<Longrightarrow> ext_isc a \<Longrightarrow> unat w \<le> 9"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_approve_norevert: "ext_isc a \<Longrightarrow> \<exists>b. ext_result ep st bal a ''approve(address,uint256)'' vs = Some (Bool b)"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_quota_min_10: "ext_result ep st bal a ''quota(uint256)'' vs = Some (Uint w) \<Longrightarrow> ext_isc a \<Longrightarrow> 10 \<le> unat w"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_quota_max_20: "ext_result ep st bal a ''quota(uint256)'' vs = Some (Uint w) \<Longrightarrow> ext_isc a \<Longrightarrow> unat w \<le> 20"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_owner_norevert: "ext_isc a \<Longrightarrow> \<exists>x. ext_result ep st bal a ''owner()'' vs = Some (Address x)"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma (in ExtAssume_Callee) callee_flag_norevert: "ext_isc a \<Longrightarrow> \<exists>b. ext_result ep st bal a ''flag(uint256)'' vs = Some (Bool b)"
  using callee_assumptions unfolding ExtAssume_callee_assm_def by fastforce

lemma ExtAssume_callee_assm_sat: "ExtAssume_callee_assm (\<lambda>_. True) ExtAssume_callee_wit"
  unfolding ExtAssume_callee_assm_def ExtAssume_callee_wit_def by auto

lemma ExtAssume_Callee_sat: "ExtAssume_Callee id (\<lambda>_. True) ExtAssume_callee_wit"
  unfolding ExtAssume_Callee_def ExtAssume_Callee_axioms_def Keccak256_def using ExtAssume_callee_assm_sat by simp

section \<open>ExtAssume Contract\<close>

contract ExtAssume assuming ExtAssume_Callee
  for "STR ''token''" : "SType.TValue TAddress"
  and "STR ''last''" : "SType.TValue TSint"
  and "STR ''total''" : "SType.TValue TSint"
  and "STR ''okFlag''" : "SType.TValue TBool"
  and "STR ''who''" : "SType.TValue TAddress"
  and "STR ''seen''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"
  and "STR ''ghost_ext_epoch''" : "SType.TValue TSint"

constructor
param "STR ''t''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''token'') [] (stackLookup (STR ''t'') []))
    })"

cfunction setToken external
param "STR ''t''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''token'') [] (stackLookup (STR ''t'') []))
    })" ,

cfunction bal external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''last'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''a'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    }))
    })" ,

cfunction bal2 external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''last'') [] (plus_monad_safe (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''a'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    }) (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- this_monad;
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    })))
    })" ,

cfunction send external
param "STR ''to''" : "SType.TValue TAddress"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''to'') []);
      a1 <- (stackLookup (STR ''v'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''transfer(address,uint256)'' ep t [a0, a1]
    }));
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''v'') []))
    })
    })" ,

cfunction pull external
param "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      decl TBool (STR ''ok'');
      assign_stack_monad (STR ''ok'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- sender_monad;
      a1 <- this_monad;
      a2 <- (stackLookup (STR ''v'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''transferFrom(address,address,uint256)'' ep t [a0, a1, a2]
    });
      assign_storage_monad (STR ''okFlag'') [] (stackLookup (STR ''ok'') []);
      (cond_monad (stackLookup (STR ''ok'') []) (assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (stackLookup (STR ''v'') []))) skip_monad)
    })
    })" ,

cfunction dec external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''last'') [] (below_monad (do {
      t <- (storeLookup (STR ''token'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''decimals()'' ep t []
    }) (sint_monad 256)))
    })" ,

cfunction pg external
where
  "(do {
      value_guard;
      ((do {
      t <- (storeLookup (STR ''token'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_unit_monad ''ping()'' ep t []
    }))
    })" ,

cfunction gr external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''last'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''k'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''grow(uint256)'' ep t [a0]
    }))
    })" ,

cfunction ap external
param "STR ''s''" : "SType.TValue TAddress"
and "STR ''v''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''okFlag'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''s'') []);
      a1 <- (stackLookup (STR ''v'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''approve(address,uint256)'' ep t [a0, a1]
    }))
    })" ,

cfunction qt external
param "STR ''k''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''last'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''k'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''quota(uint256)'' ep t [a0]
    }))
    })" ,

cfunction own external
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''who'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_addr_monad ''owner()'' ep t []
    }))
    })" ,

cfunction fl external
param "STR ''x''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''okFlag'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''x'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_flag_monad ''flag(uint256)'' ep t [a0]
    }))
    })" ,

cfunction twice external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (do {
      decl TSint (STR ''b1'');
      assign_stack_monad (STR ''b1'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''a'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    });
      (do {
      t <- (storeLookup (STR ''token'') []);
      ext_code_monad t;
      assign_storage_monad (STR ''ghost_ext_epoch'') [] (plus_monad (storeLookup (STR ''ghost_ext_epoch'') []) (sint_monad 1));
      transfer_monad (return t) (sint_monad 0);
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_unit_monad ''ping()'' ep t []
    });
      decl TSint (STR ''b2'');
      assign_stack_monad (STR ''b2'') [] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''a'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    });
      assign_storage_monad (STR ''last'') [] (cond_monad (equals_monad (stackLookup (STR ''b1'') []) (stackLookup (STR ''b2'') [])) (sint_monad 1) (sint_monad 2))
    })
    })" ,

cfunction viaConv external
param "STR ''t''" : "SType.TValue TAddress"
and "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''last'') [] (do {
      t <- (stackLookup (STR ''t'') []);
      a0 <- (stackLookup (STR ''a'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    }))
    })" ,

cfunction remember external
param "STR ''a''" : "SType.TValue TAddress"
where
  "(do {
      value_guard;
      (assign_storage_monad (STR ''seen'') [(stackLookup (STR ''a'') [])] (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''a'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    }))
    })" ,

cfunction guarded external
param "STR ''a''" : "SType.TValue TAddress"
and "STR ''min''" : "SType.TValue TSint"
where
  "(do {
      value_guard;
      (do {
      (assert_monad (do {
      lv <- (do {
      t <- (storeLookup (STR ''token'') []);
      a0 <- (stackLookup (STR ''a'') []);
      ext_code_monad t;
      ep <- storeLookup (STR ''ghost_ext_epoch'') [];
      ext_word_monad ''balanceOf(address)'' ep t [a0]
    });
      rv <- (stackLookup (STR ''min'') []);
      (not_monad (less_monad (return lv) (return rv)))
    }));
      assign_storage_monad (STR ''total'') [] (plus_monad_safe (storeLookup (STR ''total'') []) (sint_monad 1))
    })
    })"

end
