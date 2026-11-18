theory Src_Bits
imports Solidity_Source_Diff Src_Bits_Ref1
begin

text \<open>The sample Bits: the contracts of Src_Bits.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Bits.sol" [("Src_Bits_Ref1", [("Bits", ["constructor", "b1", "b2", "b3", "b4", "b5", "b6", "b7", "b8", "b9", "b10", "n1", "n2", "n3", "n4", "n5", "e1", "e2", "e3", "e4", "e5", "e6", "c1", "c2", "c3", "c4", "c5", "c7", "k1", "k2"])])]
\<close>

end
