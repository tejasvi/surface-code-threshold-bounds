import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6140 = true := by
  decide +kernel

theorem tot6140 : totK PD2M8K2 D2M8K2.t6140 = [88521112267, 342647069302, 385141907123, 88001688583, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows6141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6141 = true := by
  decide +kernel

theorem tot6141 : totK PD2M8K2 D2M8K2.t6141 = [0, 213633380282, 471511215781, 179152437866, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows6142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6142 = true := by
  decide +kernel

theorem tot6142 : totK PD2M8K2 D2M8K2.t6142 = [0, 183426765983, 474499802439, 221804581354, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows6143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6143 = true := by
  decide +kernel

theorem tot6143 : totK PD2M8K2 D2M8K2.t6143 = [0, 186584360954, 449209108690, 218742188138, 16632994142, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
