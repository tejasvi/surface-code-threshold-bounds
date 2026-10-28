import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6072 = true := by
  decide +kernel

theorem tot6072 : totK PD2M8K2 D2M8K2.t6072 = [0, 71280161657, 233434508350, 384497877427, 177960662108, 12052611869, 0, 0] := by
  decide +kernel

theorem rows6073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6073 = true := by
  decide +kernel

theorem tot6073 : totK PD2M8K2 D2M8K2.t6073 = [0, 183513536143, 463238844163, 248717214985, 23193760017, 0, 0, 0] := by
  decide +kernel

theorem rows6074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6074 = true := by
  decide +kernel

theorem tot6074 : totK PD2M8K2 D2M8K2.t6074 = [0, 178274373545, 464390557532, 234978212975, 17036558032, 0, 0, 0] := by
  decide +kernel

theorem rows6075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6075 = true := by
  decide +kernel

theorem tot6075 : totK PD2M8K2 D2M8K2.t6075 = [0, 0, 314119800222, 482717177245, 91415992561, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
