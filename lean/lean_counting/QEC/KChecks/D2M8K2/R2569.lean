import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10276 = true := by
  decide +kernel

theorem tot10276 : totK PD2M8K2 D2M8K2.t10276 = [0, 158225601644, 437900233494, 276560269734, 28015997015, 0, 0, 0] := by
  decide +kernel

theorem rows10277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10277 = true := by
  decide +kernel

theorem tot10277 : totK PD2M8K2 D2M8K2.t10277 = [0, 174186749660, 477022656608, 250672105053, 13916467904, 0, 0, 0] := by
  decide +kernel

theorem rows10278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10278 = true := by
  decide +kernel

theorem tot10278 : totK PD2M8K2 D2M8K2.t10278 = [0, 0, 279873476894, 509152723035, 101525116043, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10279 = true := by
  decide +kernel

theorem tot10279 : totK PD2M8K2 D2M8K2.t10279 = [0, 104752565381, 335346801916, 349687416821, 96106884847, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
