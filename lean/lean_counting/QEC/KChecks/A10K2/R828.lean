import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3312 = true := by
  decide +kernel

theorem tot3312 : totK PA10K2 A10K2.t3312 = [0, 0, 0, 540364873135, 1912034873653, 1769943725323, 400023476909, 26178842160, 0, 0] := by
  decide +kernel

theorem rows3313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3313 = true := by
  decide +kernel

theorem tot3313 : totK PA10K2 A10K2.t3313 = [0, 0, 0, 664921430873, 2024015856895, 1680017760799, 332473616831, 11866545492, 0, 0] := by
  decide +kernel

theorem rows3314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3314 = true := by
  decide +kernel

theorem tot3314 : totK PA10K2 A10K2.t3314 = [0, 0, 0, 496779440502, 1793876636795, 1738628146168, 429949136839, 30874154442, 0, 0] := by
  decide +kernel

theorem rows3315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3315 = true := by
  decide +kernel

theorem tot3315 : totK PA10K2 A10K2.t3315 = [0, 0, 0, 111788177375, 1317250059868, 2262482406468, 793949733647, 49848848256, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
