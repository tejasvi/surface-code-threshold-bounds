import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11928 = true := by
  decide +kernel

theorem tot11928 : totK PD2M8K2 D2M8K2.t11928 = [0, 90952881055, 416208127753, 361606262585, 33744274957, 0, 0, 0] := by
  decide +kernel

theorem rows11929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11929 = true := by
  decide +kernel

theorem tot11929 : totK PD2M8K2 D2M8K2.t11929 = [0, 6555814167, 271355447712, 510402039286, 114184011445, 1415142070, 0, 0] := by
  decide +kernel

theorem rows11930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11930 = true := by
  decide +kernel

theorem tot11930 : totK PD2M8K2 D2M8K2.t11930 = [0, 199048956297, 467797441461, 237184370379, 23151734398, 0, 0, 0] := by
  decide +kernel

theorem rows11931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11931 = true := by
  decide +kernel

theorem tot11931 : totK PD2M8K2 D2M8K2.t11931 = [0, 176825815311, 469699695991, 245019829345, 13359007839, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
