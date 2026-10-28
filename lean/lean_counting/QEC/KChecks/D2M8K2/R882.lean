import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3528 = true := by
  decide +kernel

theorem tot3528 : totK PD2M8K2 D2M8K2.t3528 = [0, 92785537557, 383863018684, 377170620921, 47973862392, 0, 0, 0] := by
  decide +kernel

theorem rows3529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3529 = true := by
  decide +kernel

theorem tot3529 : totK PD2M8K2 D2M8K2.t3529 = [0, 172023613202, 460603239073, 264947555114, 18390522882, 0, 0, 0] := by
  decide +kernel

theorem rows3530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3530 = true := by
  decide +kernel

theorem tot3530 : totK PD2M8K2 D2M8K2.t3530 = [0, 202810112590, 473908355100, 217506085557, 14150402197, 0, 0, 0] := by
  decide +kernel

theorem rows3531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3531 = true := by
  decide +kernel

theorem tot3531 : totK PD2M8K2 D2M8K2.t3531 = [0, 179858212716, 462396323946, 247188369493, 19905493017, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
