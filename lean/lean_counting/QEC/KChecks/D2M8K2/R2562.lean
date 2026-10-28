import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10248 = true := by
  decide +kernel

theorem tot10248 : totK PD2M8K2 D2M8K2.t10248 = [0, 0, 89612700785, 268833151732, 367727323440, 168543345428, 6505774710, 0] := by
  decide +kernel

theorem rows10249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10249 = true := by
  decide +kernel

theorem tot10249 : totK PD2M8K2 D2M8K2.t10249 = [0, 0, 167975355248, 458217694755, 262487593227, 18711436946, 0, 0] := by
  decide +kernel

theorem rows10250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10250 = true := by
  decide +kernel

theorem tot10250 : totK PD2M8K2 D2M8K2.t10250 = [0, 0, 70017419708, 408423168671, 399360807463, 43549701120, 0, 0] := by
  decide +kernel

theorem rows10251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10251 = true := by
  decide +kernel

theorem tot10251 : totK PD2M8K2 D2M8K2.t10251 = [0, 0, 127072888829, 379163503562, 329121230065, 55593488378, 1149959346, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
