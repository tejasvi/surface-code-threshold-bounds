import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2192 = true := by
  decide +kernel

theorem tot2192 : totK PA10K2 A10K2.t2192 = [0, 0, 636946397967, 1985113915596, 1677136925567, 398031249958, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows2193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2193 = true := by
  decide +kernel

theorem tot2193 : totK PA10K2 A10K2.t2193 = [0, 292336804476, 1262526431676, 1906832088614, 1148337380781, 194056191006, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows2194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2194 = true := by
  decide +kernel

theorem tot2194 : totK PA10K2 A10K2.t2194 = [0, 263576605871, 1462892775493, 2169783895174, 797933032780, 46129175324, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2195 = true := by
  decide +kernel

theorem tot2195 : totK PA10K2 A10K2.t2195 = [0, 382813825965, 1384723532860, 1834977956742, 1012327088943, 174546124065, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
