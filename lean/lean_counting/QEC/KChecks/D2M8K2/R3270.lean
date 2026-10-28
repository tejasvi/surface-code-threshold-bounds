import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13080 = true := by
  decide +kernel

theorem tot13080 : totK PD2M8K2 D2M8K2.t13080 = [0, 0, 186735504401, 499564779520, 208023348398, 3783938788, 0, 0] := by
  decide +kernel

theorem rows13081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13081 = true := by
  decide +kernel

theorem tot13081 : totK PD2M8K2 D2M8K2.t13081 = [0, 49430535357, 208793066250, 416598120946, 215627913365, 13042442396, 0, 0] := by
  decide +kernel

theorem rows13082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13082 = true := by
  decide +kernel

theorem tot13082 : totK PD2M8K2 D2M8K2.t13082 = [0, 169872804273, 447819897997, 277629477027, 28786245148, 0, 0, 0] := by
  decide +kernel

theorem rows13083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13083 = true := by
  decide +kernel

theorem tot13083 : totK PD2M8K2 D2M8K2.t13083 = [0, 192737570968, 480115864036, 222031615949, 12148140469, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
