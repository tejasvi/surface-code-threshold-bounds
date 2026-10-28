import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1440 = true := by
  decide +kernel

theorem tot1440 : totK PD2M8K2 D2M8K2.t1440 = [0, 0, 175335954122, 494161999660, 217520178859, 6459579517, 0, 0] := by
  decide +kernel

theorem rows1441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1441 = true := by
  decide +kernel

theorem tot1441 : totK PD2M8K2 D2M8K2.t1441 = [0, 173283618171, 428569070876, 232285252880, 60623602626, 5616265657, 0, 0] := by
  decide +kernel

theorem rows1442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1442 = true := by
  decide +kernel

theorem tot1442 : totK PD2M8K2 D2M8K2.t1442 = [0, 179296120326, 463754743171, 242523333354, 16849144356, 0, 0, 0] := by
  decide +kernel

theorem rows1443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1443 = true := by
  decide +kernel

theorem tot1443 : totK PD2M8K2 D2M8K2.t1443 = [0, 82003542383, 346307032925, 385530032598, 86774377405, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
