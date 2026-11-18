theory Src_Widths
imports Solidity_Source_Diff Src_Widths_Ref1
begin

text \<open>The sample Widths: the contracts of Src_Widths.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Widths.sol" [("Src_Widths_Ref1", [("Widths", ["constructor", "add8", "sub8", "mul8", "add64", "sub64", "mul64", "add128", "mul128", "mul192", "add248", "mul248", "uadd8", "usub8", "umul8", "uadd64", "usub64", "umul64", "umul128", "umul192", "usub248", "uadd248", "wide", "wideConv", "mixed", "mixed2", "mixedSub", "lit8", "lit8m", "dv8", "md8", "dv128", "inc8", "dec8", "addEq8", "subEq8", "mulEq64", "uinc8", "udec8", "local8", "down8", "down64", "down192", "up", "upd", "chain", "lt8", "ge8", "eqMixed", "ltMixed", "setM", "addM", "setK", "addK", "loop8", "unused", "unusedPay"])])]
\<close>

end
