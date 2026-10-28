import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t544 = true := by
  decide +kernel

theorem tot544 : totK PD2M8K2 D2M8K2.t544 = [0, 153651326887, 368477681337, 294700920137, 81701349544, 1409560813, 0, 0] := by
  decide +kernel

theorem rows545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t545 = true := by
  decide +kernel

theorem tot545 : totK PD2M8K2 D2M8K2.t545 = [0, 163591849007, 436889323802, 276468869400, 29513921743, 0, 0, 0] := by
  decide +kernel

theorem rows546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t546 = true := by
  decide +kernel

theorem tot546 : totK PD2M8K2 D2M8K2.t546 = [0, 105261807112, 408083332601, 333081250867, 39983420743, 0, 0, 0] := by
  decide +kernel

theorem rows547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t547 = true := by
  decide +kernel

theorem tot547 : totK PD2M8K2 D2M8K2.t547 = [0, 0, 227221864192, 486847336127, 170185418784, 8423393484, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
