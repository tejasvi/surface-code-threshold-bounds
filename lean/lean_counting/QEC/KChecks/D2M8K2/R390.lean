import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1560 = true := by
  decide +kernel

theorem tot1560 : totK PD2M8K2 D2M8K2.t1560 = [0, 0, 211059124772, 474185366909, 216261974007, 11621717850, 0, 0] := by
  decide +kernel

theorem rows1561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1561 = true := by
  decide +kernel

theorem tot1561 : totK PD2M8K2 D2M8K2.t1561 = [0, 0, 201821726827, 491788099258, 191049617296, 9499038804, 0, 0] := by
  decide +kernel

theorem rows1562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1562 = true := by
  decide +kernel

theorem tot1562 : totK PD2M8K2 D2M8K2.t1562 = [0, 0, 176873715828, 481685692917, 231923311680, 9578394677, 0, 0] := by
  decide +kernel

theorem rows1563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1563 = true := by
  decide +kernel

theorem tot1563 : totK PD2M8K2 D2M8K2.t1563 = [0, 0, 174201577589, 460207423017, 236398976476, 14874568699, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
