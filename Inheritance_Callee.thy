theory Inheritance_Callee
  imports Solidity_Main
begin

section \<open>Inheritance: bases that depend on the unspecified functions of the framework\<close>

text \<open>
  The methods of a contract that hashes take the abstract hash function as a parameter, and a contract can be declared to run in an
  environment that satisfies a locale (\<open>assuming\<close>). The proofs about the bases are still reused: the locale of a base holds in the
  locale of the derived contract (as a constant external function), because the derived contract has the same parameters and
  assumes what the base assumes.
\<close>

subsection \<open>A base that hashes\<close>

abbreviation "hh \<equiv> STR ''hh''"
abbreviation(in Solidity) hp where "hp (_::'a state) \<equiv> True"
abbreviation(in Solidity) hq where "hq (_::'a state) (_::'a rvalue) (_::'a state) \<equiv> True"

contract HB
  for hh: "SType.TValue (TBytes 32)"

constructor
where
  "\<langle>skip\<rangle>"

cfunction rehash external
where
  "\<langle>assert\<rangle> (\<langle>keccak256\<rangle> (hh ~\<^sub>s []) \<langle>=\<rangle> \<langle>keccak256\<rangle> (hh ~\<^sub>s []))"

text \<open>
  \<open>HD\<close> inherits \<open>rehash\<close>, which uses the hash function: the definition of the base method is unfolded in the locale of \<open>HD\<close>,
  where the hash function is a parameter and injective by assumption (the instance of \<open>HB\<close>'s locale is the fact \<open>hB_const\<close>).
\<close>

contract HD is HB

constructor
where
  "\<langle>skip\<rangle>"

cfunction other external
where
  "\<langle>skip\<rangle>"

context hD
begin
lemma "hB keccak256 timestamp (\<lambda>_. X)"
  by (rule hB_const)
end

subsection \<open>A base with an assuming clause\<close>

locale Callee = Keccak256 +
  assumes callee_ok: "ext_isc a \<Longrightarrow> \<exists>b. ext_result ep st bal a ''f()'' vs = Some (Bool b)"

contract CB assuming Callee
  for "STR ''x''": "SType.TValue TSint"

constructor
where
  "\<langle>skip\<rangle>"

cfunction f external
where
  "\<langle>skip\<rangle>"

text \<open>A derived contract has to assume what the base assumes.\<close>

contract CD is CB assuming Callee

constructor
where
  "\<langle>skip\<rangle>"

cfunction g external
where
  "\<langle>skip\<rangle>"

context cD
begin
lemma "cB keccak256 ext_isc ext_result timestamp (\<lambda>_. X)"
  by (rule cB_const)
end

end
