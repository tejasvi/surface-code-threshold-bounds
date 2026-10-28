import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4760 = true := by
  decide +kernel

theorem tot4760 : totK PD2M8K2 D2M8K2.t4760 = [0, 0, 167384086992, 460770491400, 258889239722, 18341618344, 0, 0] := by
  decide +kernel

theorem rows4761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4761 = true := by
  decide +kernel

theorem tot4761 : totK PD2M8K2 D2M8K2.t4761 = [0, 28553961470, 189850466885, 439688939563, 233971543976, 12208704324, 0, 0] := by
  decide +kernel

theorem rows4762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4762 = true := by
  decide +kernel

theorem tot4762 : totK PD2M8K2 D2M8K2.t4762 = [0, 196220854180, 457129485663, 238816383582, 23245831472, 0, 0, 0] := by
  decide +kernel

theorem rows4763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4763 = true := by
  decide +kernel

theorem tot4763 : totK PD2M8K2 D2M8K2.t4763 = [0, 102323418709, 429571626980, 328697485135, 33354258303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
