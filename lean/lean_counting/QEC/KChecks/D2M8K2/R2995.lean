import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11980 = true := by
  decide +kernel

theorem tot11980 : totK PD2M8K2 D2M8K2.t11980 = [140648108908, 456577780076, 288822232726, 19901820999, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11981 = true := by
  decide +kernel

theorem tot11981 : totK PD2M8K2 D2M8K2.t11981 = [0, 205981551967, 483121276326, 183630230854, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows11982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11982 = true := by
  decide +kernel

theorem tot11982 : totK PD2M8K2 D2M8K2.t11982 = [140435179648, 371336865090, 300808106704, 75002679607, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows11983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11983 = true := by
  decide +kernel

theorem tot11983 : totK PD2M8K2 D2M8K2.t11983 = [168512285745, 440656668959, 280188965600, 30374593025, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
