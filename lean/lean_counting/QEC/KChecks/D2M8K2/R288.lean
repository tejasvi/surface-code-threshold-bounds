import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1152 = true := by
  decide +kernel

theorem tot1152 : totK PD2M8K2 D2M8K2.t1152 = [0, 14622541859, 203217119161, 492205388447, 185055518871, 5393550755, 0, 0] := by
  decide +kernel

theorem rows1153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1153 = true := by
  decide +kernel

theorem tot1153 : totK PD2M8K2 D2M8K2.t1153 = [0, 172450629097, 452738624474, 240987213370, 22405250615, 0, 0, 0] := by
  decide +kernel

theorem rows1154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1154 = true := by
  decide +kernel

theorem tot1154 : totK PD2M8K2 D2M8K2.t1154 = [0, 191366376405, 475932639091, 223646054736, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows1155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1155 = true := by
  decide +kernel

theorem tot1155 : totK PD2M8K2 D2M8K2.t1155 = [0, 33077440972, 310325879681, 440740166676, 83443981786, 1128973710, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
