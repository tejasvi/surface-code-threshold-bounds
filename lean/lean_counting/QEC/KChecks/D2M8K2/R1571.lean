import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6284 = true := by
  decide +kernel

theorem tot6284 : totK PD2M8K2 D2M8K2.t6284 = [0, 208224811657, 482838389741, 186555670140, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows6285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6285 = true := by
  decide +kernel

theorem tot6285 : totK PD2M8K2 D2M8K2.t6285 = [0, 188118703051, 474090657608, 216938382091, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows6286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6286 = true := by
  decide +kernel

theorem tot6286 : totK PD2M8K2 D2M8K2.t6286 = [0, 149606191502, 465613146850, 236448279767, 9064506700, 0, 0, 0] := by
  decide +kernel

theorem rows6287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6287 = true := by
  decide +kernel

theorem tot6287 : totK PD2M8K2 D2M8K2.t6287 = [0, 85129052935, 343026579440, 382143318112, 77080161773, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
