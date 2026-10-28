import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4676 = true := by
  decide +kernel

theorem tot4676 : totK PD2M8K2 D2M8K2.t4676 = [0, 0, 178806709573, 475371928163, 242243152571, 10340525452, 0, 0] := by
  decide +kernel

theorem rows4677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4677 = true := by
  decide +kernel

theorem tot4677 : totK PD2M8K2 D2M8K2.t4677 = [0, 179528440046, 444390617566, 264713356621, 41540635808, 5782147159, 0, 0] := by
  decide +kernel

theorem rows4678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4678 = true := by
  decide +kernel

theorem tot4678 : totK PD2M8K2 D2M8K2.t4678 = [0, 186520465478, 475570909582, 234151067886, 13616186441, 0, 0, 0] := by
  decide +kernel

theorem rows4679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4679 = true := by
  decide +kernel

theorem tot4679 : totK PD2M8K2 D2M8K2.t4679 = [0, 75068494160, 317973557131, 363098383338, 151024668695, 17186218589, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
