import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11284 = true := by
  decide +kernel

theorem tot11284 : totK PD2M8K2 D2M8K2.t11284 = [0, 204770895869, 485835100867, 216376050458, 11056080877, 0, 0, 0] := by
  decide +kernel

theorem rows11285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11285 = true := by
  decide +kernel

theorem tot11285 : totK PD2M8K2 D2M8K2.t11285 = [0, 158937770451, 472915163284, 241324333199, 13126448176, 0, 0, 0] := by
  decide +kernel

theorem rows11286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11286 = true := by
  decide +kernel

theorem tot11286 : totK PD2M8K2 D2M8K2.t11286 = [0, 0, 318684957602, 465218052891, 76387210362, 1021600638, 0, 0] := by
  decide +kernel

theorem rows11287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11287 = true := by
  decide +kernel

theorem tot11287 : totK PD2M8K2 D2M8K2.t11287 = [0, 123016409097, 350593459171, 308303108382, 76179041852, 3552795014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
