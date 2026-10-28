import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2652 = true := by
  decide +kernel

theorem tot2652 : totK PD2M8K2 D2M8K2.t2652 = [0, 0, 0, 320758888707, 476776747082, 91221839978, 1782779017, 0] := by
  decide +kernel

theorem rows2653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2653 = true := by
  decide +kernel

theorem tot2653 : totK PD2M8K2 D2M8K2.t2653 = [0, 0, 64198478510, 286245863747, 388041499778, 103856775201, 2246260049, 0] := by
  decide +kernel

theorem rows2654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2654 = true := by
  decide +kernel

theorem tot2654 : totK PD2M8K2 D2M8K2.t2654 = [0, 0, 174820651465, 452172367807, 262160893526, 26340315286, 0, 0] := by
  decide +kernel

theorem rows2655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2655 = true := by
  decide +kernel

theorem tot2655 : totK PD2M8K2 D2M8K2.t2655 = [0, 0, 175830485202, 465953544520, 232809750000, 9587304030, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
