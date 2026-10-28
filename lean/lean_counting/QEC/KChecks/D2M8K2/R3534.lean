import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14136 = true := by
  decide +kernel

theorem tot14136 : totK PD2M8K2 D2M8K2.t14136 = [167821546688, 449587818432, 271301262752, 27553669283, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14137 = true := by
  decide +kernel

theorem tot14137 : totK PD2M8K2 D2M8K2.t14137 = [158017993640, 452526004554, 274272851458, 23449779354, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14138 = true := by
  decide +kernel

theorem tot14138 : totK PD2M8K2 D2M8K2.t14138 = [0, 225052492565, 492917432151, 167124510576, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows14139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14139 = true := by
  decide +kernel

theorem tot14139 : totK PD2M8K2 D2M8K2.t14139 = [0, 170249451224, 456869622979, 233911905872, 17080783126, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
