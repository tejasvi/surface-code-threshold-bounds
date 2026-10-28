import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2692 = true := by
  decide +kernel

theorem tot2692 : totK PD2M8K2 D2M8K2.t2692 = [0, 0, 156965737626, 365072790062, 284068395004, 57182391559, 1225787871, 0] := by
  decide +kernel

theorem rows2693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2693 = true := by
  decide +kernel

theorem tot2693 : totK PD2M8K2 D2M8K2.t2693 = [0, 0, 160544049336, 449551633163, 272961319368, 24996295453, 0, 0] := by
  decide +kernel

theorem rows2694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2694 = true := by
  decide +kernel

theorem tot2694 : totK PD2M8K2 D2M8K2.t2694 = [0, 81043402320, 277838128105, 339540372885, 179326649726, 13065910070, 0, 0] := by
  decide +kernel

theorem rows2695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2695 = true := by
  decide +kernel

theorem tot2695 : totK PD2M8K2 D2M8K2.t2695 = [0, 186920922980, 474017218535, 217135481706, 12411567665, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
