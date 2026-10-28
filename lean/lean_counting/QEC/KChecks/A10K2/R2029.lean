import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8116 = true := by
  decide +kernel

theorem tot8116 : totK PA10K2 A10K2.t8116 = [0, 0, 0, 297007965898, 1575420560052, 2166185911477, 762608634079, 47862013103, 0, 0] := by
  decide +kernel

theorem rows8117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8117 = true := by
  decide +kernel

theorem tot8117 : totK PA10K2 A10K2.t8117 = [0, 0, 0, 110665848719, 761647664491, 1936762359961, 1551479233723, 308554969352, 12477124820, 0] := by
  decide +kernel

theorem rows8118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8118 = true := by
  decide +kernel

theorem tot8118 : totK PA10K2 A10K2.t8118 = [0, 0, 0, 328573825494, 1607516260361, 2108017638464, 683799638605, 33611290320, 0, 0] := by
  decide +kernel

theorem rows8119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8119 = true := by
  decide +kernel

theorem tot8119 : totK PA10K2 A10K2.t8119 = [0, 0, 0, 509889124420, 1906489468012, 2035275490213, 509368287172, 17492233754, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
