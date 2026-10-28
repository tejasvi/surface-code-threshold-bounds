import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7260 = true := by
  decide +kernel

theorem tot7260 : totK PD2M8K2 D2M8K2.t7260 = [0, 0, 189956624985, 469323147653, 217578807667, 12534051746, 0, 0] := by
  decide +kernel

theorem rows7261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7261 = true := by
  decide +kernel

theorem tot7261 : totK PD2M8K2 D2M8K2.t7261 = [0, 0, 66612772842, 323352427039, 404266283574, 83712255941, 1369150432, 0] := by
  decide +kernel

theorem rows7262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7262 = true := by
  decide +kernel

theorem tot7262 : totK PD2M8K2 D2M8K2.t7262 = [0, 0, 68563118959, 367514025347, 412807398378, 41234444691, 0, 0] := by
  decide +kernel

theorem rows7263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7263 = true := by
  decide +kernel

theorem tot7263 : totK PD2M8K2 D2M8K2.t7263 = [0, 0, 184597239299, 478791920110, 240094287790, 13013126192, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
