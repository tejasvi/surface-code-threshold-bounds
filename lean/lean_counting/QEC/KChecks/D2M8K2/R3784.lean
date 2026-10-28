import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15136 = true := by
  decide +kernel

theorem tot15136 : totK PD2M8K2 D2M8K2.t15136 = [0, 159574573203, 424148164114, 318281733139, 39070426784, 0, 0, 0] := by
  decide +kernel

theorem rows15137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15137 = true := by
  decide +kernel

theorem tot15137 : totK PD2M8K2 D2M8K2.t15137 = [0, 168712267179, 476148733753, 251047831232, 14570397433, 0, 0, 0] := by
  decide +kernel

theorem rows15138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15138 = true := by
  decide +kernel

theorem tot15138 : totK PD2M8K2 D2M8K2.t15138 = [0, 0, 214542920157, 470723991466, 217323678508, 19877599667, 0, 0] := by
  decide +kernel

theorem rows15139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15139 = true := by
  decide +kernel

theorem tot15139 : totK PD2M8K2 D2M8K2.t15139 = [0, 32194035719, 198241465534, 426690066625, 223952203332, 12218958159, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
