import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6376 = true := by
  decide +kernel

theorem tot6376 : totK PD2M8K2 D2M8K2.t6376 = [0, 0, 181129898269, 468739381280, 244646247228, 22762079039, 0, 0] := by
  decide +kernel

theorem rows6377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6377 = true := by
  decide +kernel

theorem tot6377 : totK PD2M8K2 D2M8K2.t6377 = [0, 0, 238650724827, 477797035588, 165603078840, 6698972513, 0, 0] := by
  decide +kernel

theorem rows6378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6378 = true := by
  decide +kernel

theorem tot6378 : totK PD2M8K2 D2M8K2.t6378 = [0, 0, 173326401152, 472800164509, 231028866261, 19426508831, 0, 0] := by
  decide +kernel

theorem rows6379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6379 = true := by
  decide +kernel

theorem tot6379 : totK PD2M8K2 D2M8K2.t6379 = [0, 0, 179010905355, 464100554230, 235833850771, 13761953177, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
