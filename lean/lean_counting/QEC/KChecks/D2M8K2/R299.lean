import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1196 = true := by
  decide +kernel

theorem tot1196 : totK PD2M8K2 D2M8K2.t1196 = [0, 276711298526, 503256467963, 122700001387, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows1197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1197 = true := by
  decide +kernel

theorem tot1197 : totK PD2M8K2 D2M8K2.t1197 = [0, 207781607494, 482726910285, 184131068666, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows1198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1198 = true := by
  decide +kernel

theorem tot1198 : totK PD2M8K2 D2M8K2.t1198 = [0, 178586387761, 475225784094, 224670691334, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows1199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1199 = true := by
  decide +kernel

theorem tot1199 : totK PD2M8K2 D2M8K2.t1199 = [0, 169147309026, 448526552566, 231009795402, 17714277454, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
