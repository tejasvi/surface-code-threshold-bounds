import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2748 = true := by
  decide +kernel

theorem tot2748 : totK PA10K2 A10K2.t2748 = [0, 0, 198522554467, 832994213701, 1681007458004, 1402938606767, 383057631108, 30074883546, 0, 0] := by
  decide +kernel

theorem rows2749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2749 = true := by
  decide +kernel

theorem tot2749 : totK PA10K2 A10K2.t2749 = [0, 0, 430629444871, 1761758103418, 1941335141568, 548354326384, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows2750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2750 = true := by
  decide +kernel

theorem tot2750 : totK PA10K2 A10K2.t2750 = [0, 0, 100631327429, 903018935490, 1971438146741, 1296173461578, 308234442938, 24969229125, 0, 0] := by
  decide +kernel

theorem rows2751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2751 = true := by
  decide +kernel

theorem tot2751 : totK PA10K2 A10K2.t2751 = [0, 0, 263649460354, 1206493372013, 1895511645669, 1079558633054, 183043125638, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
