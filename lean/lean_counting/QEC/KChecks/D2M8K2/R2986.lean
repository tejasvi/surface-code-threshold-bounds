import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11944 = true := by
  decide +kernel

theorem tot11944 : totK PD2M8K2 D2M8K2.t11944 = [88301595136, 350322261593, 381891381122, 74415836743, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows11945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11945 = true := by
  decide +kernel

theorem tot11945 : totK PD2M8K2 D2M8K2.t11945 = [0, 260763674799, 489523430732, 155110848056, 8470662040, 0, 0, 0] := by
  decide +kernel

theorem rows11946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11946 = true := by
  decide +kernel

theorem tot11946 : totK PD2M8K2 D2M8K2.t11946 = [113741617645, 344631508436, 331709572424, 89773381682, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows11947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11947 = true := by
  decide +kernel

theorem tot11947 : totK PD2M8K2 D2M8K2.t11947 = [177793395069, 433864373439, 262568066508, 30215549995, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
