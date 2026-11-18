theory Src_Arrays
imports Solidity_Source_Diff Src_Arrays_Ref1
begin

text \<open>The sample Arrays: the contracts of Src_Arrays.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Arrays.sol" [("Src_Arrays_Ref1", [("Arrays", ["constructor", "push", "pushEmpty", "pop", "len", "set", "add", "get", "sum", "clear", "clearAt", "setFixed", "fixedLen", "clearFixed", "addOwner", "isOwner", "pushFlag", "toggle", "pushHash", "pushSmall", "addSmall", "pushRow", "pushCell", "setCell", "rowLen", "popCell", "pushPair", "setPair", "userPush", "userGet", "userLen", "userPop", "newItem", "tag", "tagLen", "dropItem", "viaPointer"])])]
\<close>

end
