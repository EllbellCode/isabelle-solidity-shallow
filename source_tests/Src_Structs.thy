theory Src_Structs
imports Solidity_Source_Diff Src_Structs_Ref1
begin

text \<open>The sample Structs: the contracts of Src_Structs.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Structs.sol" [("Src_Structs_Ref1", [("Structs", ["constructor", "f1", "f2", "f3", "f4", "f5", "f6", "f7", "f8", "f9", "f10", "f11", "f12", "f13", "f14"])])]
\<close>

end
