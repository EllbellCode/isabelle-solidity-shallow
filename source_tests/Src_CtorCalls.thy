theory Src_CtorCalls
imports Solidity_Source_Diff Src_CtorCalls_Ref1
begin

text \<open>The sample CtorCalls: the contracts of Src_CtorCalls.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_CtorCalls.sol" [("Src_CtorCalls_Ref1", [("CtorCalls", ["constructor", "setOwner", "scale", "mint", "checked", "again", "transferOwner"])])]
\<close>

end
