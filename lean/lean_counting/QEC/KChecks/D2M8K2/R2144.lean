import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8576 = true := by
  decide +kernel

theorem tot8576 : totK PD2M8K2 D2M8K2.t8576 = [126667677847, 356943198984, 316554884527, 91316638714, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows8577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8577 = true := by
  decide +kernel

theorem tot8577 : totK PD2M8K2 D2M8K2.t8577 = [183317399248, 451602601298, 255904096051, 27068950774, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8578 = true := by
  decide +kernel

theorem tot8578 : totK PD2M8K2 D2M8K2.t8578 = [103714856752, 428447904055, 346269348319, 30225045063, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8579 = true := by
  decide +kernel

theorem tot8579 : totK PD2M8K2 D2M8K2.t8579 = [0, 214366734757, 491908757978, 176989427632, 4813189065, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
