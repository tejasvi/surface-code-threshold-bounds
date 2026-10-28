import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7240 = true := by
  decide +kernel

theorem tot7240 : totK PD2M8K2 D2M8K2.t7240 = [0, 0, 150635045005, 373029042170, 278661389702, 98319912265, 8932028497, 0] := by
  decide +kernel

theorem rows7241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7241 = true := by
  decide +kernel

theorem tot7241 : totK PD2M8K2 D2M8K2.t7241 = [0, 0, 177038733533, 455116228063, 218855257908, 13382189823, 0, 0] := by
  decide +kernel

theorem rows7242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7242 = true := by
  decide +kernel

theorem tot7242 : totK PD2M8K2 D2M8K2.t7242 = [0, 0, 84346306670, 372821221074, 359304891290, 59682539514, 1369150432, 0] := by
  decide +kernel

theorem rows7243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7243 = true := by
  decide +kernel

theorem tot7243 : totK PD2M8K2 D2M8K2.t7243 = [0, 0, 0, 302447314944, 509374039376, 71632854876, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
