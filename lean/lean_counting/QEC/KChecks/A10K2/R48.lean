import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t192 = true := by
  decide +kernel

theorem tot192 : totK PA10K2 A10K2.t192 = [0, 0, 172764753457, 1100702093090, 2105896373078, 1306028383021, 233099905188, 7007974415, 0, 0] := by
  decide +kernel

theorem rows193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t193 = true := by
  decide +kernel

theorem tot193 : totK PA10K2 A10K2.t193 = [0, 0, 289635076060, 1483303156205, 2111720937050, 807037132842, 64090622956, 0, 0, 0] := by
  decide +kernel

theorem rows194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t194 = true := by
  decide +kernel

theorem tot194 : totK PA10K2 A10K2.t194 = [0, 0, 554642504047, 1955502137660, 1826945012653, 399594118416, 23500939800, 0, 0, 0] := by
  decide +kernel

theorem rows195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t195 = true := by
  decide +kernel

theorem tot195 : totK PA10K2 A10K2.t195 = [0, 0, 519676275052, 1928399948729, 2106895149104, 540147328164, 19145700860, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
