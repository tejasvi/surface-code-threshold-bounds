import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10516 = true := by
  decide +kernel

theorem tot10516 : totK PD2M8K2 D2M8K2.t10516 = [0, 124442828397, 449382715880, 314674146428, 24935089690, 0, 0, 0] := by
  decide +kernel

theorem rows10517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10517 = true := by
  decide +kernel

theorem tot10517 : totK PD2M8K2 D2M8K2.t10517 = [0, 0, 213099406339, 495443788634, 171025446292, 5011483316, 0, 0] := by
  decide +kernel

theorem rows10518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10518 = true := by
  decide +kernel

theorem tot10518 : totK PD2M8K2 D2M8K2.t10518 = [0, 0, 200586093862, 486477373112, 195960999305, 10374152040, 0, 0] := by
  decide +kernel

theorem rows10519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10519 = true := by
  decide +kernel

theorem tot10519 : totK PD2M8K2 D2M8K2.t10519 = [0, 0, 182664818885, 446537076082, 215524666326, 16632994142, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
