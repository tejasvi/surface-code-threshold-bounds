import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15948 = true := by
  decide +kernel

theorem tot15948 : totK PD2M8K2 D2M8K2.t15948 = [0, 0, 184917117711, 466320170540, 240198372208, 20104377587, 0, 0] := by
  decide +kernel

theorem rows15949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15949 = true := by
  decide +kernel

theorem tot15949 : totK PD2M8K2 D2M8K2.t15949 = [0, 0, 192416108428, 478092870186, 230548763206, 12524207686, 0, 0] := by
  decide +kernel

theorem rows15950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15950 = true := by
  decide +kernel

theorem tot15950 : totK PD2M8K2 D2M8K2.t15950 = [0, 0, 56604951192, 321431210009, 422418920862, 90914053036, 1242138600, 0] := by
  decide +kernel

theorem rows15951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15951 = true := by
  decide +kernel

theorem tot15951 : totK PD2M8K2 D2M8K2.t15951 = [0, 0, 0, 222663219810, 469608295793, 162675178351, 7182288656, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
