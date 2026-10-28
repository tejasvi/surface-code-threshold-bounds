import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10672 = true := by
  decide +kernel

theorem tot10672 : totK PD2M8K2 D2M8K2.t10672 = [0, 0, 37322106084, 319021931183, 447441537530, 86901708827, 1198073392, 0] := by
  decide +kernel

theorem rows10673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10673 = true := by
  decide +kernel

theorem tot10673 : totK PD2M8K2 D2M8K2.t10673 = [0, 0, 0, 203177739546, 466047226429, 178983016692, 11986244008, 0] := by
  decide +kernel

theorem rows10674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10674 = true := by
  decide +kernel

theorem tot10674 : totK PD2M8K2 D2M8K2.t10674 = [0, 0, 174722983593, 447826529625, 253462374371, 20749000501, 0, 0] := by
  decide +kernel

theorem rows10675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10675 = true := by
  decide +kernel

theorem tot10675 : totK PD2M8K2 D2M8K2.t10675 = [0, 0, 185998463940, 442621683682, 222733540768, 17104814242, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
