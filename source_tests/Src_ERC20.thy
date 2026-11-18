theory Src_ERC20
imports Solidity_Source_Diff Src_ERC20_Ref1
begin

text \<open>The sample ERC20: the contracts of Src_ERC20.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_ERC20.sol" [("Src_ERC20_Ref1", [("ERC20", ["constructor", "approve", "transfer", "transferFrom", "computeDomainSeparator", "DOMAIN_SEPARATOR__int", "permit", "DOMAIN_SEPARATOR", "mint", "burn"])])]
\<close>

end
