import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3316 = true := by
  decide +kernel

theorem tot3316 : totK PD2M8K2 D2M8K2.t3316 = [0, 0, 245018905330, 507761413645, 146076879287, 2328621201, 0, 0] := by
  decide +kernel

theorem rows3317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3317 = true := by
  decide +kernel

theorem tot3317 : totK PD2M8K2 D2M8K2.t3317 = [0, 89126311553, 277731802972, 335830390479, 166729322473, 14266142696, 0, 0] := by
  decide +kernel

theorem rows3318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3318 = true := by
  decide +kernel

theorem tot3318 : totK PD2M8K2 D2M8K2.t3318 = [0, 185112433766, 465658371738, 217534247821, 12186818197, 0, 0, 0] := by
  decide +kernel

theorem rows3319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3319 = true := by
  decide +kernel

theorem tot3319 : totK PD2M8K2 D2M8K2.t3319 = [0, 122351253747, 428817422866, 304853849744, 24183551369, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
