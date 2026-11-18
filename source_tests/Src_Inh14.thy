theory Src_Inh14
imports Solidity_Source_Diff Src_Inh14_Ref1 Src_Inh14_Ref2
begin

text \<open>The sample Inh14: the contracts of Src_Inh14.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Inh14.sol" [("Src_Inh14_Ref1", [("Ra", ["constructor", "bump"]), ("Rb", ["constructor", "bump"]), ("Rc", ["constructor", "more"])]), ("Src_Inh14_Ref2", [("Ra", ["constructor", "bump"]), ("Rb", ["constructor", "bump"]), ("Rq", ["constructor", "bump"])])]
\<close>

end
