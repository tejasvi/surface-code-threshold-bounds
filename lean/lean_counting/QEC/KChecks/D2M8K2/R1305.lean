import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5220 = true := by
  decide +kernel

theorem tot5220 : totK PD2M8K2 D2M8K2.t5220 = [0, 192521516780, 467012111171, 234671867204, 20819825286, 0, 0, 0] := by
  decide +kernel

theorem rows5221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5221 = true := by
  decide +kernel

theorem tot5221 : totK PD2M8K2 D2M8K2.t5221 = [0, 179331535276, 469194779753, 242115246561, 13438430209, 0, 0, 0] := by
  decide +kernel

theorem rows5222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5222 = true := by
  decide +kernel

theorem tot5222 : totK PD2M8K2 D2M8K2.t5222 = [0, 0, 282590063707, 498655834316, 113523096586, 1268739303, 0, 0] := by
  decide +kernel

theorem rows5223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5223 = true := by
  decide +kernel

theorem tot5223 : totK PD2M8K2 D2M8K2.t5223 = [0, 0, 209398343625, 483957954039, 176092825690, 7442000727, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
