theory Src_Fallback
imports Solidity_Source_Diff Src_Fallback_Ref1 Src_Fallback_Ref2 Src_Fallback_Ref3
begin

text \<open>The sample Fallback: the contracts of Src_Fallback.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Fallback.sol" [("Src_Fallback_Ref1", [("FbBase", ["constructor", "fallback"]), ("FbDerived", ["constructor", "fallback", "bump"])]), ("Src_Fallback_Ref2", [("Fb", ["constructor", "fallback", "set"])]), ("Src_Fallback_Ref3", [("Fr", ["constructor", "receive", "fallback", "set"])])]
\<close>

end
