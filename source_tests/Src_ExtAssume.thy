theory Src_ExtAssume
imports Solidity_Source_Diff Src_ExtAssume_Ref1
begin

text \<open>The sample ExtAssume: the contracts of Src_ExtAssume.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_ExtAssume.sol" [("Src_ExtAssume_Ref1", [("ExtAssume", ["constructor", "setToken", "bal", "bal2", "send", "pull", "dec", "pg", "gr", "ap", "qt", "own", "fl", "twice", "viaConv", "remember", "guarded"])])]
\<close>

end
