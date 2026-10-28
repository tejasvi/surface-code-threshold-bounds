import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9460 = true := by
  decide +kernel

theorem tot9460 : totK PD2M8K2 D2M8K2.t9460 = [0, 167406134303, 452490618589, 223379514971, 16561712910, 0, 0, 0] := by
  decide +kernel

theorem rows9461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9461 = true := by
  decide +kernel

theorem tot9461 : totK PD2M8K2 D2M8K2.t9461 = [0, 88265605660, 337650658852, 361307270313, 84763374797, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9462 = true := by
  decide +kernel

theorem tot9462 : totK PD2M8K2 D2M8K2.t9462 = [0, 18616785608, 339148834589, 438316911713, 60638061104, 0, 0, 0] := by
  decide +kernel

theorem rows9463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9463 = true := by
  decide +kernel

theorem tot9463 : totK PD2M8K2 D2M8K2.t9463 = [0, 211409411851, 502695126962, 181224485651, 4149795279, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
