import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3376 = true := by
  decide +kernel

theorem tot3376 : totK PD2M8K2 D2M8K2.t3376 = [0, 0, 253726328735, 492335883570, 160867463668, 5070837572, 0, 0] := by
  decide +kernel

theorem rows3377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3377 = true := by
  decide +kernel

theorem tot3377 : totK PD2M8K2 D2M8K2.t3377 = [0, 0, 273303897324, 474910959948, 138981142449, 2895580614, 0, 0] := by
  decide +kernel

theorem rows3378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3378 = true := by
  decide +kernel

theorem tot3378 : totK PD2M8K2 D2M8K2.t3378 = [0, 0, 200215763248, 482417345117, 167789183946, 7351427945, 0, 0] := by
  decide +kernel

theorem rows3379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3379 = true := by
  decide +kernel

theorem tot3379 : totK PD2M8K2 D2M8K2.t3379 = [0, 0, 177739499712, 475598075555, 226455548374, 12078908513, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
