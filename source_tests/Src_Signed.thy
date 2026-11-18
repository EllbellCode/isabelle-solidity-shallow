theory Src_Signed
imports Solidity_Source_Diff Src_Signed_Ref1
begin

text \<open>The sample Signed: the contracts of Src_Signed.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Signed.sol" [("Src_Signed_Ref1", [("Signed", ["constructor", "add", "sub", "mul", "dv", "md", "neg", "uadd", "usub", "umul", "udv", "umd", "uneg", "lt", "gt", "le", "ge", "eq", "ne", "ltZero", "geMinusOne", "addLit", "subLit", "mulNeg", "divNeg", "divLit", "mdLit", "folded", "foldedDiff", "minLit", "bigLit", "addEq", "subEq", "mulEq", "dvEq", "mdEq", "incFrom", "decFrom", "setR", "toU", "fromU", "roundTrip", "absLike", "setM", "addM", "local", "loopS"])])]
\<close>

end
