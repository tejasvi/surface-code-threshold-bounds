import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3848 = true := by
  decide +kernel

theorem tot3848 : totK PD2M8K2 D2M8K2.t3848 = [0, 193614679638, 469026202584, 221224681268, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows3849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3849 = true := by
  decide +kernel

theorem tot3849 : totK PD2M8K2 D2M8K2.t3849 = [0, 198697835786, 487993784716, 195734034746, 5336070015, 0, 0, 0] := by
  decide +kernel

theorem rows3850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3850 = true := by
  decide +kernel

theorem tot3850 : totK PD2M8K2 D2M8K2.t3850 = [0, 168081169584, 467863810276, 227804351469, 8917007962, 0, 0, 0] := by
  decide +kernel

theorem rows3851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3851 = true := by
  decide +kernel

theorem tot3851 : totK PD2M8K2 D2M8K2.t3851 = [0, 0, 272263940552, 499549136073, 91346717881, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
