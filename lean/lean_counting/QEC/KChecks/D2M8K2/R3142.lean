import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12568 = true := by
  decide +kernel

theorem tot12568 : totK PD2M8K2 D2M8K2.t12568 = [0, 176663725160, 426130839365, 223639614706, 67991255112, 7923020108, 0, 0] := by
  decide +kernel

theorem rows12569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12569 = true := by
  decide +kernel

theorem tot12569 : totK PD2M8K2 D2M8K2.t12569 = [0, 173903408887, 463665750923, 243521822954, 13271230369, 0, 0, 0] := by
  decide +kernel

theorem rows12570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12570 = true := by
  decide +kernel

theorem tot12570 : totK PD2M8K2 D2M8K2.t12570 = [0, 70694836363, 320662913558, 398907365763, 92754801752, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12571 = true := by
  decide +kernel

theorem tot12571 : totK PD2M8K2 D2M8K2.t12571 = [0, 48866670332, 344683311738, 457895922663, 59371603831, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
