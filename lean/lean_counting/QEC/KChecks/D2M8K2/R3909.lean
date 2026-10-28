import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15636 = true := by
  decide +kernel

theorem tot15636 : totK PD2M8K2 D2M8K2.t15636 = [0, 71310072568, 99007747382, 237249528524, 367208181642, 93082756375, 3882006667, 0] := by
  decide +kernel

theorem rows15637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15637 = true := by
  decide +kernel

theorem tot15637 : totK PD2M8K2 D2M8K2.t15637 = [0, 183399290500, 488094693516, 217618532261, 9845055932, 0, 0, 0] := by
  decide +kernel

theorem rows15638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15638 = true := by
  decide +kernel

theorem tot15638 : totK PD2M8K2 D2M8K2.t15638 = [0, 153505176087, 443053234365, 268711228596, 17246506947, 0, 0, 0] := by
  decide +kernel

theorem rows15639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15639 = true := by
  decide +kernel

theorem tot15639 : totK PD2M8K2 D2M8K2.t15639 = [0, 0, 273925167933, 505491038956, 111583134110, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
