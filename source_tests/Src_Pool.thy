theory Src_Pool
imports Solidity_Source_Diff Src_Pool_Ref1
begin

text \<open>The sample Pool: the contracts of Src_Pool.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Pool.sol" [("Src_Pool_Ref1", [("ERC20", ["constructor", "totalSupply", "approve", "transfer", "transferFrom", "u_mint", "u_burn", "totalSupply__int"]), ("Pool", ["constructor", "sharesToAmount", "amountToShares", "amountToShares__int", "deposit", "sharesToAmount__int", "withdraw", "calcPremium__int", "flashLoan", "calcPremium"])])]
\<close>

end
