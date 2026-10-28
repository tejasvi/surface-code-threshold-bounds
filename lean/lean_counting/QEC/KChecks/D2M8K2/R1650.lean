import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6600 = true := by
  decide +kernel

theorem tot6600 : totK PD2M8K2 D2M8K2.t6600 = [0, 173698713130, 476794556448, 229798991933, 14542588619, 0, 0, 0] := by
  decide +kernel

theorem rows6601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6601 = true := by
  decide +kernel

theorem tot6601 : totK PD2M8K2 D2M8K2.t6601 = [0, 207719790938, 474701658746, 199137485383, 8111614932, 0, 0, 0] := by
  decide +kernel

theorem rows6602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6602 = true := by
  decide +kernel

theorem tot6602 : totK PD2M8K2 D2M8K2.t6602 = [0, 181558428851, 461835110358, 246942752105, 18246066036, 0, 0, 0] := by
  decide +kernel

theorem rows6603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6603 = true := by
  decide +kernel

theorem tot6603 : totK PD2M8K2 D2M8K2.t6603 = [0, 177016198386, 472273174703, 219500939277, 8932258738, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
