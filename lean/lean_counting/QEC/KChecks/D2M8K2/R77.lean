import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t308 = true := by
  decide +kernel

theorem tot308 : totK PD2M8K2 D2M8K2.t308 = [0, 191800808428, 469032811537, 213633588869, 12593797338, 0, 0, 0] := by
  decide +kernel

theorem rows309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t309 = true := by
  decide +kernel

theorem tot309 : totK PD2M8K2 D2M8K2.t309 = [0, 188281081381, 486626770980, 214338852539, 9902972185, 0, 0, 0] := by
  decide +kernel

theorem rows310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t310 = true := by
  decide +kernel

theorem tot310 : totK PD2M8K2 D2M8K2.t310 = [0, 170695049247, 465069253362, 239841425163, 13964593734, 0, 0, 0] := by
  decide +kernel

theorem rows311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t311 = true := by
  decide +kernel

theorem tot311 : totK PD2M8K2 D2M8K2.t311 = [0, 183777629266, 474409995490, 210997209230, 9757737807, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
