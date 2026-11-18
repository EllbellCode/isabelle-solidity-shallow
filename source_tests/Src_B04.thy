theory Src_B04
imports Solidity_Source_Diff Src_B04_Ref1 Src_B04_Ref2 Src_B04_Ref3
begin

text \<open>The sample B04: the contracts of Src_B04.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_B04.sol" [("Src_B04_Ref1", [("EA", ["constructor", "hook", "f"])]), ("Src_B04_Ref2", [("EA", ["constructor", "hook", "f"]), ("EB", ["constructor", "f"]), ("EC", ["constructor", "hook", "viaA", "viaB"])]), ("Src_B04_Ref3", [])]
\<close>

end
