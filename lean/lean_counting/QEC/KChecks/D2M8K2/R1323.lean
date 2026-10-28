import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5292 = true := by
  decide +kernel

theorem tot5292 : totK PD2M8K2 D2M8K2.t5292 = [0, 0, 274351340222, 498110928173, 120952135735, 1268739303, 0, 0] := by
  decide +kernel

theorem rows5293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5293 = true := by
  decide +kernel

theorem tot5293 : totK PD2M8K2 D2M8K2.t5293 = [0, 0, 186369218360, 478281120784, 209426862523, 8667377803, 0, 0] := by
  decide +kernel

theorem rows5294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5294 = true := by
  decide +kernel

theorem tot5294 : totK PD2M8K2 D2M8K2.t5294 = [0, 0, 174746027262, 468366138957, 222906431424, 14629206711, 0, 0] := by
  decide +kernel

theorem rows5295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5295 = true := by
  decide +kernel

theorem tot5295 : totK PD2M8K2 D2M8K2.t5295 = [0, 0, 203260277620, 475287337553, 189174475469, 12297600962, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
