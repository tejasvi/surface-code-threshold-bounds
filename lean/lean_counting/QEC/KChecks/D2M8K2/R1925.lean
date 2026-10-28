import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7700 = true := by
  decide +kernel

theorem tot7700 : totK PD2M8K2 D2M8K2.t7700 = [0, 0, 115747572338, 386977181307, 371932304221, 45661073272, 0, 0] := by
  decide +kernel

theorem rows7701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7701 = true := by
  decide +kernel

theorem tot7701 : totK PD2M8K2 D2M8K2.t7701 = [0, 0, 217601454437, 478275003811, 202335571822, 9710008315, 0, 0] := by
  decide +kernel

theorem rows7702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7702 = true := by
  decide +kernel

theorem tot7702 : totK PD2M8K2 D2M8K2.t7702 = [0, 0, 86707775517, 410780127605, 361442768474, 45038351153, 0, 0] := by
  decide +kernel

theorem rows7703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7703 = true := by
  decide +kernel

theorem tot7703 : totK PD2M8K2 D2M8K2.t7703 = [0, 0, 0, 208155553838, 452373403792, 223553013755, 18567029682, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
