import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4900 = true := by
  decide +kernel

theorem tot4900 : totK PA10K2 A10K2.t4900 = [260403760671, 1373703419651, 2211813857570, 1112516769672, 134165175000, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4901 = true := by
  decide +kernel

theorem tot4901 : totK PA10K2 A10K2.t4901 = [0, 497168117592, 1808661039901, 1983823176204, 659512536069, 49660736315, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4902 = true := by
  decide +kernel

theorem tot4902 : totK PA10K2 A10K2.t4902 = [0, 463670369812, 1892263675308, 1936207510312, 465477359208, 26479096260, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4903 = true := by
  decide +kernel

theorem tot4903 : totK PA10K2 A10K2.t4903 = [0, 263466900334, 1330043636162, 2168350358097, 976402584122, 74666917410, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
