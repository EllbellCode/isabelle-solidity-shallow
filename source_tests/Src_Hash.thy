theory Src_Hash
imports Solidity_Source_Diff Src_Hash_Ref1
begin

text \<open>The sample Hash: the contracts of Src_Hash.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Hash.sol" [("Src_Hash_Ref1", [("Hash", ["constructor", "enc2", "enc1", "enc3", "packed", "mixed", "narrow", "viaSender", "str", "bytesArg", "strPlus", "two", "lit", "litOther", "litEq", "same", "differ", "sameStr", "typed", "typedEq", "commit", "reveal", "mark", "check", "bump", "need"])])]
\<close>

end
