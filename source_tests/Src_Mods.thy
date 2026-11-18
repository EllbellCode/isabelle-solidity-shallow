theory Src_Mods
imports Solidity_Source_Diff Src_Mods_Ref1
begin

text \<open>The sample Mods: the contracts of Src_Mods.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Mods.sol" [("Src_Mods_Ref1", [("Mods", ["constructor", "setX", "f", "g", "dbl", "wl", "shadow", "br", "loopLp", "ord", "ord2", "paid", "nested"])])]
\<close>

end
