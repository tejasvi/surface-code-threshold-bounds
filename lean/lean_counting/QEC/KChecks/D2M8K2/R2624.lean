import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10496 = true := by
  decide +kernel

theorem tot10496 : totK PD2M8K2 D2M8K2.t10496 = [0, 0, 171818403563, 440475850140, 269914352761, 27516575778, 0, 0] := by
  decide +kernel

theorem rows10497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10497 = true := by
  decide +kernel

theorem tot10497 : totK PD2M8K2 D2M8K2.t10497 = [0, 0, 93763583743, 395883115743, 365525639870, 54669970080, 1268739303, 0] := by
  decide +kernel

theorem rows10498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10498 = true := by
  decide +kernel

theorem tot10498 : totK PD2M8K2 D2M8K2.t10498 = [0, 0, 0, 258066667378, 495110807463, 137362175742, 3742744013, 0] := by
  decide +kernel

theorem rows10499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10499 = true := by
  decide +kernel

theorem tot10499 : totK PD2M8K2 D2M8K2.t10499 = [0, 110047735289, 240876973602, 177654544751, 247837006752, 122157033314, 9327184179, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
