import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16180 = true := by
  decide +kernel

theorem tot16180 : totK PD2M8K2 D2M8K2.t16180 = [0, 182261201038, 478939305449, 252306768082, 15091507579, 0, 0, 0] := by
  decide +kernel

theorem rows16181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16181 = true := by
  decide +kernel

theorem tot16181 : totK PD2M8K2 D2M8K2.t16181 = [0, 0, 249468898386, 503369962392, 136293473811, 2303467656, 0, 0] := by
  decide +kernel

theorem rows16182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16182 = true := by
  decide +kernel

theorem tot16182 : totK PD2M8K2 D2M8K2.t16182 = [0, 0, 181019388762, 480064395398, 218502133307, 10130891972, 0, 0] := by
  decide +kernel

theorem rows16183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16183 = true := by
  decide +kernel

theorem tot16183 : totK PD2M8K2 D2M8K2.t16183 = [0, 0, 200876479352, 474899907270, 194897637198, 12126792705, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
