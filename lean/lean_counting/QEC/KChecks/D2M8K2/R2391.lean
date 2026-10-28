import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9564 = true := by
  decide +kernel

theorem tot9564 : totK PD2M8K2 D2M8K2.t9564 = [0, 202504605666, 488473561812, 217912261950, 12454366108, 0, 0, 0] := by
  decide +kernel

theorem rows9565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9565 = true := by
  decide +kernel

theorem tot9565 : totK PD2M8K2 D2M8K2.t9565 = [0, 193259467352, 470672319309, 221421128875, 12900833004, 0, 0, 0] := by
  decide +kernel

theorem rows9566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9566 = true := by
  decide +kernel

theorem tot9566 : totK PD2M8K2 D2M8K2.t9566 = [0, 164548332593, 450158864852, 278144492981, 27190566548, 0, 0, 0] := by
  decide +kernel

theorem rows9567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9567 = true := by
  decide +kernel

theorem tot9567 : totK PD2M8K2 D2M8K2.t9567 = [0, 136668606607, 441923653569, 290392746598, 22360307755, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
