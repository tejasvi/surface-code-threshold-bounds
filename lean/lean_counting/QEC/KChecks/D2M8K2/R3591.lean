import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14364 = true := by
  decide +kernel

theorem tot14364 : totK PD2M8K2 D2M8K2.t14364 = [0, 0, 144129484749, 459337327543, 215759129580, 11696355327, 0, 0] := by
  decide +kernel

theorem rows14365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14365 = true := by
  decide +kernel

theorem tot14365 : totK PD2M8K2 D2M8K2.t14365 = [0, 0, 84796181830, 341482373532, 357863962387, 71447013693, 1206465782, 0] := by
  decide +kernel

theorem rows14366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14366 = true := by
  decide +kernel

theorem tot14366 : totK PD2M8K2 D2M8K2.t14366 = [0, 0, 80481154917, 385841585997, 352888967382, 35215089353, 0, 0] := by
  decide +kernel

theorem rows14367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14367 = true := by
  decide +kernel

theorem tot14367 : totK PD2M8K2 D2M8K2.t14367 = [0, 0, 191755823587, 456998738757, 237022489548, 20001318118, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
