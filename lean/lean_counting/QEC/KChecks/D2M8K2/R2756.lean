import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11024 = true := by
  decide +kernel

theorem tot11024 : totK PD2M8K2 D2M8K2.t11024 = [125877197901, 357494810165, 312926112799, 91445513468, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows11025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11025 = true := by
  decide +kernel

theorem tot11025 : totK PD2M8K2 D2M8K2.t11025 = [163573741969, 443451223942, 270902882619, 30773707025, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11026 = true := by
  decide +kernel

theorem tot11026 : totK PD2M8K2 D2M8K2.t11026 = [90019449239, 345934377112, 367322323000, 75959058759, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows11027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11027 = true := by
  decide +kernel

theorem tot11027 : totK PD2M8K2 D2M8K2.t11027 = [0, 218452927689, 475617973560, 185434350626, 7439274334, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
