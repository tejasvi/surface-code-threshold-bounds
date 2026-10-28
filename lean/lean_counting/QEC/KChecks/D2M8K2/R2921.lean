import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11684 = true := by
  decide +kernel

theorem tot11684 : totK PD2M8K2 D2M8K2.t11684 = [92722701599, 385319901899, 358243338499, 57093393945, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11685 = true := by
  decide +kernel

theorem tot11685 : totK PD2M8K2 D2M8K2.t11685 = [0, 324100882869, 519920111481, 82584657858, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11686 = true := by
  decide +kernel

theorem tot11686 : totK PD2M8K2 D2M8K2.t11686 = [0, 201140345365, 497762835186, 181992559219, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows11687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11687 = true := by
  decide +kernel

theorem tot11687 : totK PD2M8K2 D2M8K2.t11687 = [0, 164766972975, 443785734553, 239796184693, 17973025655, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
