import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7732 = true := by
  decide +kernel

theorem tot7732 : totK PD2M8K2 D2M8K2.t7732 = [0, 0, 175422674038, 387240779446, 226502737295, 98722700215, 8935385149, 0] := by
  decide +kernel

theorem rows7733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7733 = true := by
  decide +kernel

theorem tot7733 : totK PD2M8K2 D2M8K2.t7733 = [0, 0, 162799861301, 456100627589, 234865621713, 13298971041, 0, 0] := by
  decide +kernel

theorem rows7734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7734 = true := by
  decide +kernel

theorem tot7734 : totK PD2M8K2 D2M8K2.t7734 = [0, 0, 66339875482, 323339113153, 396750806636, 79300122087, 1310166938, 0] := by
  decide +kernel

theorem rows7735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7735 = true := by
  decide +kernel

theorem tot7735 : totK PD2M8K2 D2M8K2.t7735 = [0, 0, 67155910414, 355629342996, 418620811950, 44169470019, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
