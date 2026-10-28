import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9208 = true := by
  decide +kernel

theorem tot9208 : totK PD2M8K2 D2M8K2.t9208 = [0, 90128064229, 267840472237, 353916255295, 162461987459, 7877424857, 0, 0] := by
  decide +kernel

theorem rows9209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9209 = true := by
  decide +kernel

theorem tot9209 : totK PD2M8K2 D2M8K2.t9209 = [0, 166832184106, 432468978122, 271274873174, 30347703461, 0, 0, 0] := by
  decide +kernel

theorem rows9210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9210 = true := by
  decide +kernel

theorem tot9210 : totK PD2M8K2 D2M8K2.t9210 = [0, 122126538995, 443562068565, 313918078911, 28385394358, 0, 0, 0] := by
  decide +kernel

theorem rows9211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9211 = true := by
  decide +kernel

theorem tot9211 : totK PD2M8K2 D2M8K2.t9211 = [0, 0, 226066627085, 509591559440, 140262305916, 4009909289, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
