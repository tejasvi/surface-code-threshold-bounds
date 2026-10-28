import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3652 = true := by
  decide +kernel

theorem tot3652 : totK PD2M8K2 D2M8K2.t3652 = [0, 180619357860, 470479489950, 240998702951, 16953985325, 0, 0, 0] := by
  decide +kernel

theorem rows3653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3653 = true := by
  decide +kernel

theorem tot3653 : totK PD2M8K2 D2M8K2.t3653 = [0, 0, 281323447672, 503865923108, 97391541114, 1096505104, 0, 0] := by
  decide +kernel

theorem rows3654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3654 = true := by
  decide +kernel

theorem tot3654 : totK PD2M8K2 D2M8K2.t3654 = [0, 82495334887, 321232342186, 382244521351, 105227115936, 3884009855, 0, 0] := by
  decide +kernel

theorem rows3655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3655 = true := by
  decide +kernel

theorem tot3655 : totK PD2M8K2 D2M8K2.t3655 = [0, 171578316301, 446648021044, 278210582359, 28405850615, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
