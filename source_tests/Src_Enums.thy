theory Src_Enums
imports Solidity_Source_Diff Src_Enums_Ref1
begin

text \<open>The sample Enums: the contracts of Src_Enums.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Enums.sol" [("Src_Enums_Ref1", [("Enums", ["constructor", "start", "finish", "setLevel", "setState", "fromNumber", "toNumber", "levelFromNumber", "setPrice", "bump", "setTag", "tagIs", "reset"])])]
\<close>

end
