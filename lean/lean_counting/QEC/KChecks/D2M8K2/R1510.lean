import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6040 = true := by
  decide +kernel

theorem tot6040 : totK PD2M8K2 D2M8K2.t6040 = [0, 0, 293630327394, 509212783967, 102477330827, 1096505104, 0, 0] := by
  decide +kernel

theorem rows6041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6041 = true := by
  decide +kernel

theorem tot6041 : totK PD2M8K2 D2M8K2.t6041 = [0, 157098051438, 374801798985, 272519120604, 91380907027, 3884009855, 0, 0] := by
  decide +kernel

theorem rows6042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6042 = true := by
  decide +kernel

theorem tot6042 : totK PD2M8K2 D2M8K2.t6042 = [0, 156845446919, 443099592326, 285837692999, 22960484676, 0, 0, 0] := by
  decide +kernel

theorem rows6043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6043 = true := by
  decide +kernel

theorem tot6043 : totK PD2M8K2 D2M8K2.t6043 = [0, 91891950289, 347954452527, 369839823731, 86144530326, 1232609433, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
