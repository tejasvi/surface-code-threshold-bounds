import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2812 = true := by
  decide +kernel

theorem tot2812 : totK PD2M8K2 D2M8K2.t2812 = [0, 74855184586, 332222914845, 371144542074, 89322477605, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2813 = true := by
  decide +kernel

theorem tot2813 : totK PD2M8K2 D2M8K2.t2813 = [0, 50835957208, 358093357689, 398906380548, 53345994976, 0, 0, 0] := by
  decide +kernel

theorem rows2814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2814 = true := by
  decide +kernel

theorem tot2814 : totK PD2M8K2 D2M8K2.t2814 = [0, 201006598944, 497427097405, 200931319482, 5463989431, 0, 0, 0] := by
  decide +kernel

theorem rows2815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2815 = true := by
  decide +kernel

theorem tot2815 : totK PD2M8K2 D2M8K2.t2815 = [0, 171716756874, 458376973104, 233708475820, 13452000861, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
