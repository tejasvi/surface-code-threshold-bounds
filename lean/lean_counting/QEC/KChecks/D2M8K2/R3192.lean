import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12768 = true := by
  decide +kernel

theorem tot12768 : totK PD2M8K2 D2M8K2.t12768 = [0, 191077404294, 454218067171, 240732244290, 26056332664, 0, 0, 0] := by
  decide +kernel

theorem rows12769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12769 = true := by
  decide +kernel

theorem tot12769 : totK PD2M8K2 D2M8K2.t12769 = [0, 197416775609, 459393200467, 232737084084, 17051174684, 0, 0, 0] := by
  decide +kernel

theorem rows12770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12770 = true := by
  decide +kernel

theorem tot12770 : totK PD2M8K2 D2M8K2.t12770 = [0, 25236971407, 330358619009, 444660248391, 84776341395, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12771 = true := by
  decide +kernel

theorem tot12771 : totK PD2M8K2 D2M8K2.t12771 = [0, 49699473797, 283363897213, 441338414492, 120765257366, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
