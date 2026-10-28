import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8180 = true := by
  decide +kernel

theorem tot8180 : totK PA10K2 A10K2.t8180 = [0, 0, 0, 499253963694, 1705838081399, 1891389172260, 736194950129, 72046966972, 0, 0] := by
  decide +kernel

theorem rows8181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8181 = true := by
  decide +kernel

theorem tot8181 : totK PA10K2 A10K2.t8181 = [0, 0, 0, 391633904751, 1739736031733, 2200817636155, 711917226275, 30302906995, 0, 0] := by
  decide +kernel

theorem rows8182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8182 = true := by
  decide +kernel

theorem tot8182 : totK PA10K2 A10K2.t8182 = [0, 0, 0, 0, 557633361000, 1954451171153, 1939556104390, 414690114655, 13653259670, 0] := by
  decide +kernel

theorem rows8183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8183 = true := by
  decide +kernel

theorem tot8183 : totK PA10K2 A10K2.t8183 = [0, 0, 0, 0, 534890508459, 1835589985233, 1912768052080, 605132526873, 49180423016, 0] := by
  decide +kernel

end QECKChecks.A10K2
