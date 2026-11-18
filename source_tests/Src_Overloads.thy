theory Src_Overloads
imports Solidity_Source_Diff Src_Overloads_Ref1 Src_Overloads_Ref2
begin

text \<open>The sample Overloads: the contracts of Src_Overloads.sol, created by the command, compared with the reference specifications.\<close>

ML \<open>
  Source_Diff.check \<^theory> [] "Src_Overloads.sol" [("Src_Overloads_Ref1", [("OvA", ["constructor", "set__uint256", "u_bump__uint256", "set__uint256__int"]), ("OvB", ["constructor", "u_bump__uint256_uint256", "set__uint256_uint256", "set__uint256_uint256__int", "again"])]), ("Src_Overloads_Ref2", [("Base", ["constructor", "u_put__uint256", "u_put__uint256_bool", "u_put__address_uint256", "put__uint256", "put__uint256_bool", "put__address_uint256", "noArgs"]), ("Over", ["constructor", "u_put__address_uint256", "twice"])])]
\<close>

end
