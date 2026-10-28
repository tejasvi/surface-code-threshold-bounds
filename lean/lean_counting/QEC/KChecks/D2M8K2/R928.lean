import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3712 = true := by
  decide +kernel

theorem tot3712 : totK PD2M8K2 D2M8K2.t3712 = [0, 204333743677, 465937787881, 206206081634, 12243442891, 0, 0, 0] := by
  decide +kernel

theorem rows3713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3713 = true := by
  decide +kernel

theorem tot3713 : totK PD2M8K2 D2M8K2.t3713 = [0, 188504298473, 488061271586, 211726340624, 10177609099, 0, 0, 0] := by
  decide +kernel

theorem rows3714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3714 = true := by
  decide +kernel

theorem tot3714 : totK PD2M8K2 D2M8K2.t3714 = [0, 158515300953, 468652542032, 250522992590, 13737756793, 0, 0, 0] := by
  decide +kernel

theorem rows3715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3715 = true := by
  decide +kernel

theorem tot3715 : totK PD2M8K2 D2M8K2.t3715 = [0, 193834752871, 472283620011, 224555711717, 12886997561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
