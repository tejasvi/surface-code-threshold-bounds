import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9116 = true := by
  decide +kernel

theorem tot9116 : totK PD2M8K2 D2M8K2.t9116 = [0, 187855369111, 458871797285, 245372220452, 22718183475, 0, 0, 0] := by
  decide +kernel

theorem rows9117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9117 = true := by
  decide +kernel

theorem tot9117 : totK PD2M8K2 D2M8K2.t9117 = [0, 182658897506, 461638493853, 238016248902, 16999175936, 0, 0, 0] := by
  decide +kernel

theorem rows9118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9118 = true := by
  decide +kernel

theorem tot9118 : totK PD2M8K2 D2M8K2.t9118 = [0, 44373624882, 344654890059, 426086870561, 79163488229, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9119 = true := by
  decide +kernel

theorem tot9119 : totK PD2M8K2 D2M8K2.t9119 = [0, 0, 274094516427, 496191925477, 124345619687, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
