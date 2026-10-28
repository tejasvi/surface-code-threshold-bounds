import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2332 = true := by
  decide +kernel

theorem tot2332 : totK PD2M8K2 D2M8K2.t2332 = [0, 145168034505, 442894005638, 267047498501, 19260128653, 0, 0, 0] := by
  decide +kernel

theorem rows2333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2333 = true := by
  decide +kernel

theorem tot2333 : totK PD2M8K2 D2M8K2.t2333 = [0, 87089311879, 331585454125, 381286185017, 91503961707, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2334 = true := by
  decide +kernel

theorem tot2334 : totK PD2M8K2 D2M8K2.t2334 = [0, 34667807051, 339839569840, 476638320783, 63655787323, 0, 0, 0] := by
  decide +kernel

theorem rows2335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2335 = true := by
  decide +kernel

theorem tot2335 : totK PD2M8K2 D2M8K2.t2335 = [0, 163921356476, 439918653514, 276705702197, 30349548734, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
