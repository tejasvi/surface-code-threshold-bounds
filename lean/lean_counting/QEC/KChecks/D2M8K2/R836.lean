import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3344 = true := by
  decide +kernel

theorem tot3344 : totK PD2M8K2 D2M8K2.t3344 = [0, 0, 185213346727, 481594780647, 232085621401, 16277061306, 0, 0] := by
  decide +kernel

theorem rows3345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3345 = true := by
  decide +kernel

theorem tot3345 : totK PD2M8K2 D2M8K2.t3345 = [0, 0, 173521486396, 465748842523, 240313584148, 13655399297, 0, 0] := by
  decide +kernel

theorem rows3346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3346 = true := by
  decide +kernel

theorem tot3346 : totK PD2M8K2 D2M8K2.t3346 = [0, 0, 0, 295607960758, 480698313584, 98604301335, 1171084559, 0] := by
  decide +kernel

theorem rows3347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3347 = true := by
  decide +kernel

theorem tot3347 : totK PD2M8K2 D2M8K2.t3347 = [0, 0, 18351256589, 214318395211, 424230000479, 181204176367, 11934365838, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
