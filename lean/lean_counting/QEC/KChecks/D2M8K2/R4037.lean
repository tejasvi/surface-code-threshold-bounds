import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16148 = true := by
  decide +kernel

theorem tot16148 : totK PD2M8K2 D2M8K2.t16148 = [0, 0, 186628058017, 477048587791, 217083714450, 14704558535, 0, 0] := by
  decide +kernel

theorem rows16149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16149 = true := by
  decide +kernel

theorem tot16149 : totK PD2M8K2 D2M8K2.t16149 = [0, 0, 170047662761, 467814429848, 211682515585, 8964298071, 0, 0] := by
  decide +kernel

theorem rows16150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16150 = true := by
  decide +kernel

theorem tot16150 : totK PD2M8K2 D2M8K2.t16150 = [0, 0, 86953184342, 351820535925, 359329972087, 63990617147, 1206465782, 0] := by
  decide +kernel

theorem rows16151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16151 = true := by
  decide +kernel

theorem tot16151 : totK PD2M8K2 D2M8K2.t16151 = [0, 0, 74110042871, 393143790947, 384674870730, 31401872293, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
