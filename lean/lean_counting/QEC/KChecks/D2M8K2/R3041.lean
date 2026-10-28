import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12164 = true := by
  decide +kernel

theorem tot12164 : totK PD2M8K2 D2M8K2.t12164 = [0, 172926634261, 445328444407, 245674898387, 41718083721, 2524036228, 0, 0] := by
  decide +kernel

theorem rows12165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12165 = true := by
  decide +kernel

theorem tot12165 : totK PD2M8K2 D2M8K2.t12165 = [0, 161376899561, 443368804039, 281538222399, 27869107020, 0, 0, 0] := by
  decide +kernel

theorem rows12166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12166 = true := by
  decide +kernel

theorem tot12166 : totK PD2M8K2 D2M8K2.t12166 = [0, 93373242333, 382634714864, 363303820676, 63034793825, 1268739303, 0, 0] := by
  decide +kernel

theorem rows12167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12167 = true := by
  decide +kernel

theorem tot12167 : totK PD2M8K2 D2M8K2.t12167 = [0, 0, 248394104616, 488572567860, 151085117214, 3633193399, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
