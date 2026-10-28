import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1304 = true := by
  decide +kernel

theorem tot1304 : totK PD2M8K2 D2M8K2.t1304 = [0, 184818827740, 478866667885, 224528001346, 12900833004, 0, 0, 0] := by
  decide +kernel

theorem rows1305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1305 = true := by
  decide +kernel

theorem tot1305 : totK PD2M8K2 D2M8K2.t1305 = [0, 175181894332, 435031116391, 268337020640, 27075565644, 0, 0, 0] := by
  decide +kernel

theorem rows1306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1306 = true := by
  decide +kernel

theorem tot1306 : totK PD2M8K2 D2M8K2.t1306 = [0, 88698579362, 391606500379, 341755061692, 50759997346, 1171084559, 0, 0] := by
  decide +kernel

theorem rows1307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1307 = true := by
  decide +kernel

theorem tot1307 : totK PD2M8K2 D2M8K2.t1307 = [0, 0, 236578292274, 470718004079, 157953852453, 8462178015, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
