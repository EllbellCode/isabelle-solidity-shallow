theory Src_Inh1
imports Solidity_Source_Diff Src_Inh1_Ref1
begin

text \<open>The sample Inh1: the contracts of Src_Inh1.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Inh1.sol" [("Src_Inh1_Ref1", [("A", ["constructor", "f", "g", "callG", "setA", "f__int"]), ("B", ["constructor", "f", "g", "f__int"]), ("C", ["constructor", "f", "h", "f__int"])])]
\<close>

end
