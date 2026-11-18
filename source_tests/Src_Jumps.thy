theory Src_Jumps
imports Solidity_Source_Diff Src_Jumps_Ref1
begin

text \<open>The sample Jumps: the contracts of Src_Jumps.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Jumps.sol" [("Src_Jumps_Ref1", [("Jumps", ["constructor", "sumUntil", "skipEven", "both", "doOnce", "doCount", "doJumps", "nested", "revertInLoop", "afterBreak"])])]
\<close>

end
