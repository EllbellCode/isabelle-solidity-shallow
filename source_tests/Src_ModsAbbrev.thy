theory Src_ModsAbbrev
imports Solidity_Source_Diff Src_ModsAbbrev_Ref1
begin

text \<open>The sample ModsAbbrev: the contracts of Src_ModsAbbrev.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> ["solidity_modifier_abbreviations = true"] "Src_ModsAbbrev.sol" [("Src_ModsAbbrev_Ref1", [("Mods", ["constructor", "setX", "f", "g", "dbl", "wl", "shadow", "br", "loopLp", "ord", "ord2", "paid", "nested"])])]
\<close>

end
