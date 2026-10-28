import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11132 = true := by
  decide +kernel

theorem tot11132 : totK PD2M8K2 D2M8K2.t11132 = [0, 0, 86403723232, 390695638379, 346344914090, 42416723119, 0, 0] := by
  decide +kernel

theorem rows11133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11133 = true := by
  decide +kernel

theorem tot11133 : totK PD2M8K2 D2M8K2.t11133 = [0, 0, 211310612111, 483410388230, 173638703081, 8337422257, 0, 0] := by
  decide +kernel

theorem rows11134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11134 = true := by
  decide +kernel

theorem tot11134 : totK PD2M8K2 D2M8K2.t11134 = [0, 0, 195695845621, 471420755647, 188442123245, 12434957066, 0, 0] := by
  decide +kernel

theorem rows11135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11135 = true := by
  decide +kernel

theorem tot11135 : totK PD2M8K2 D2M8K2.t11135 = [0, 0, 202777595525, 477198433334, 186631495228, 9782461661, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
