import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7712 = true := by
  decide +kernel

theorem tot7712 : totK PD2M8K2 D2M8K2.t7712 = [0, 0, 48317887137, 286424600974, 441653569942, 107437225489, 3783381897, 0] := by
  decide +kernel

theorem rows7713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7713 = true := by
  decide +kernel

theorem tot7713 : totK PD2M8K2 D2M8K2.t7713 = [0, 0, 178700346307, 456958330894, 248201419506, 21384711590, 0, 0] := by
  decide +kernel

theorem rows7714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7714 = true := by
  decide +kernel

theorem tot7714 : totK PD2M8K2 D2M8K2.t7714 = [0, 0, 193564049060, 479054954335, 225322498533, 10884111244, 0, 0] := by
  decide +kernel

theorem rows7715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7715 = true := by
  decide +kernel

theorem tot7715 : totK PD2M8K2 D2M8K2.t7715 = [0, 0, 0, 279975032399, 496491918596, 106886048492, 1240621948, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
