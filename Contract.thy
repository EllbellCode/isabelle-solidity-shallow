theory Contract
  imports Solidity WP
  keywords "contract" :: thy_decl
       and "constructor"
       and "cfunction"
       and "external"
       and "memory"
       and "param"
       and "calldata"
       and "payable"
       and "assuming"
       and "is"
       and "abstract"
       and "verification" :: thy_goal
       and "invariant"::thy_decl

begin

named_theorems alias_defs "definitions of the base methods behind inherited (alias) methods"

text \<open>Facts for inheritance: a contract's locale holds for a constant external function, so the definitions of its methods can be used
  unconditionally when an inherited method passes a constant function as the base's external function.\<close>

lemma meth_const: "Method ts"
  unfolding Method_def using unsigned_less[of ts, where ?'a=nat] by simp

lemma sol_const: "Solidity id ts (\<lambda>_. X)"
  unfolding Solidity_def Keccak256_def External_def
  by (auto intro!: monotoneI sm_ordI meth_const)

lemma External_const: "External (\<lambda>_. X)"
  unfolding External_def by (auto intro!: monotoneI sm_ordI)

lemmas transfer_const [alias_defs] = External.transfer_monad_def[OF External_const]

ML_file Utils.ML
ML_file Data.ML
ML_file Inheritance.ML
ML_file Specification.ML
ML_file Invariant.ML
ML_file Verification.ML

end
