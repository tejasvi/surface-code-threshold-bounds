import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3272 = true := by
  decide +kernel

theorem tot3272 : totK PA10K2 A10K2.t3272 = [0, 0, 525699093747, 1833172661596, 1876095467161, 510857562389, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows3273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3273 = true := by
  decide +kernel

theorem tot3273 : totK PA10K2 A10K2.t3273 = [0, 0, 0, 700118220179, 2076151416264, 1612199449087, 376816154847, 25565504801, 0, 0] := by
  decide +kernel

theorem rows3274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3274 = true := by
  decide +kernel

theorem tot3274 : totK PA10K2 A10K2.t3274 = [0, 0, 176945644412, 1068074190265, 2002424153987, 1220440249085, 195030227056, 5517381808, 0, 0] := by
  decide +kernel

theorem rows3275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3275 = true := by
  decide +kernel

theorem tot3275 : totK PA10K2 A10K2.t3275 = [0, 0, 583274707886, 1901705038170, 1766895264929, 495903543673, 31936107789, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
