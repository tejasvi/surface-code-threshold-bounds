import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3948 = true := by
  decide +kernel

theorem tot3948 : totK PD2M8K2 D2M8K2.t3948 = [0, 92992240269, 384922381531, 392195650881, 53341704086, 0, 0, 0] := by
  decide +kernel

theorem rows3949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3949 = true := by
  decide +kernel

theorem tot3949 : totK PD2M8K2 D2M8K2.t3949 = [0, 159395983999, 446683665058, 288308324077, 24133921439, 0, 0, 0] := by
  decide +kernel

theorem rows3950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3950 = true := by
  decide +kernel

theorem tot3950 : totK PD2M8K2 D2M8K2.t3950 = [0, 168335624325, 470708852870, 256655324349, 21283362589, 0, 0, 0] := by
  decide +kernel

theorem rows3951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3951 = true := by
  decide +kernel

theorem tot3951 : totK PD2M8K2 D2M8K2.t3951 = [0, 0, 191754253764, 453422827688, 239712341555, 20729740161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
