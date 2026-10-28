import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10648 = true := by
  decide +kernel

theorem tot10648 : totK PD2M8K2 D2M8K2.t10648 = [0, 0, 297878785974, 517195441463, 99196719883, 1069412848, 0, 0] := by
  decide +kernel

theorem rows10649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10649 = true := by
  decide +kernel

theorem tot10649 : totK PD2M8K2 D2M8K2.t10649 = [0, 0, 173081314783, 465995485457, 213326784382, 12554737991, 0, 0] := by
  decide +kernel

theorem rows10650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10650 = true := by
  decide +kernel

theorem tot10650 : totK PD2M8K2 D2M8K2.t10650 = [0, 0, 196769915548, 466950285361, 207239723182, 12421902774, 0, 0] := by
  decide +kernel

theorem rows10651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10651 = true := by
  decide +kernel

theorem tot10651 : totK PD2M8K2 D2M8K2.t10651 = [0, 0, 40814012050, 342107601230, 383378430744, 65020973887, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
