theory Src_FileLevel
imports Solidity_Source_Diff Src_FileLevel_Ref1 Src_FileLevel_Ref2
begin

text \<open>The sample FileLevel: the contracts of Src_FileLevel.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_FileLevel.sol" [("Src_FileLevel_Ref1", [("FileLevel", ["constructor", "twice", "clamp", "plusSmall", "add", "dbl", "cl", "ps", "nar", "tag"])]), ("Src_FileLevel_Ref2", [("Other", ["constructor", "clamp", "f"])])]
\<close>

end
