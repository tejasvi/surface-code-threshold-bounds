import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14100 = true := by
  decide +kernel

theorem tot14100 : totK PD2M8K2 D2M8K2.t14100 = [0, 0, 257238563980, 509701163365, 129243095966, 1162515529, 0, 0] := by
  decide +kernel

theorem rows14101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14101 = true := by
  decide +kernel

theorem tot14101 : totK PD2M8K2 D2M8K2.t14101 = [0, 79434949537, 260404785683, 386966871315, 153957842052, 6900030410, 0, 0] := by
  decide +kernel

theorem rows14102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14102 = true := by
  decide +kernel

theorem tot14102 : totK PD2M8K2 D2M8K2.t14102 = [0, 182253299535, 472312385821, 252213298716, 23107452121, 0, 0, 0] := by
  decide +kernel

theorem rows14103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14103 = true := by
  decide +kernel

theorem tot14103 : totK PD2M8K2 D2M8K2.t14103 = [0, 181745577975, 472542626773, 241662311564, 15925649356, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
