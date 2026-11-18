theory Src_Libs
imports Solidity_Source_Diff Src_Libs_Ref1
begin

text \<open>The sample Libs: the contracts of Src_Libs.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Libs.sol" [("Src_Libs_Ref1", [("Libs", ["constructor", "guard", "early", "SafeMath__add", "t1", "SafeMath__sub_65", "SafeMath__sub", "t2", "t3", "SafeMath__mul", "t4", "SafeMath__div", "t5", "SafeMath__min", "t6", "SafeMath__wrappingAdd", "t7", "SafeMath__mulDiv", "t8", "Small__inc", "t9", "Small__isZero", "t10", "t11", "t12", "t13"])])]
\<close>

end
