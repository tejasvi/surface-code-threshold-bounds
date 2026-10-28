import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t844 = true := by
  decide +kernel

theorem tot844 : totK PD2M8K2 D2M8K2.t844 = [0, 8002455866, 305766599417, 477314617356, 91607090949, 1310517177, 0, 0] := by
  decide +kernel

theorem rows845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t845 = true := by
  decide +kernel

theorem tot845 : totK PD2M8K2 D2M8K2.t845 = [0, 90915334787, 371930803487, 392379507933, 51839087149, 0, 0, 0] := by
  decide +kernel

theorem rows846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t846 = true := by
  decide +kernel

theorem tot846 : totK PD2M8K2 D2M8K2.t846 = [0, 156110406171, 436530502402, 281819453214, 24402111723, 0, 0, 0] := by
  decide +kernel

theorem rows847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t847 = true := by
  decide +kernel

theorem tot847 : totK PD2M8K2 D2M8K2.t847 = [0, 139173077885, 439189872144, 302161341577, 34543532744, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
