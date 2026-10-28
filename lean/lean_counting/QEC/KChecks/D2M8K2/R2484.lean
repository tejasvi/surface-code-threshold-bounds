import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9936 = true := by
  decide +kernel

theorem tot9936 : totK PD2M8K2 D2M8K2.t9936 = [0, 0, 177690170285, 434395838074, 229188686754, 14054534522, 0, 0] := by
  decide +kernel

theorem rows9937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9937 = true := by
  decide +kernel

theorem tot9937 : totK PD2M8K2 D2M8K2.t9937 = [0, 0, 142278760943, 454996604497, 274324413776, 18721956145, 0, 0] := by
  decide +kernel

theorem rows9938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9938 = true := by
  decide +kernel

theorem tot9938 : totK PD2M8K2 D2M8K2.t9938 = [0, 0, 0, 283621377985, 506160741823, 80827678796, 1096505104, 0] := by
  decide +kernel

theorem rows9939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9939 = true := by
  decide +kernel

theorem tot9939 : totK PD2M8K2 D2M8K2.t9939 = [0, 0, 155397482314, 361586812590, 294241061378, 76489952687, 3838026431, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
