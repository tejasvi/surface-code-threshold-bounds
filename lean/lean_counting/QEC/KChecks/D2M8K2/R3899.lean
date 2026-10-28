import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15596 = true := by
  decide +kernel

theorem tot15596 : totK PD2M8K2 D2M8K2.t15596 = [0, 0, 0, 284921327107, 478796892480, 86950121003, 1206465782, 0] := by
  decide +kernel

theorem rows15597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15597 = true := by
  decide +kernel

theorem tot15597 : totK PD2M8K2 D2M8K2.t15597 = [0, 0, 138455550409, 413826610999, 327058224215, 34711425744, 0, 0] := by
  decide +kernel

theorem rows15598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15598 = true := by
  decide +kernel

theorem tot15598 : totK PD2M8K2 D2M8K2.t15598 = [0, 0, 195860961293, 487824733573, 205525458316, 10026904872, 0, 0] := by
  decide +kernel

theorem rows15599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15599 = true := by
  decide +kernel

theorem tot15599 : totK PD2M8K2 D2M8K2.t15599 = [0, 0, 173878539320, 463774321152, 241032007446, 15606374376, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
