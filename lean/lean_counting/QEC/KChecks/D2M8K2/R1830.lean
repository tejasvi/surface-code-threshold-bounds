import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7320 = true := by
  decide +kernel

theorem tot7320 : totK PD2M8K2 D2M8K2.t7320 = [0, 157662576518, 384441312728, 276110954609, 87460359719, 3867150671, 0, 0] := by
  decide +kernel

theorem rows7321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7321 = true := by
  decide +kernel

theorem tot7321 : totK PD2M8K2 D2M8K2.t7321 = [0, 172461866204, 436632139571, 265995004717, 20519276429, 0, 0, 0] := by
  decide +kernel

theorem rows7322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7322 = true := by
  decide +kernel

theorem tot7322 : totK PD2M8K2 D2M8K2.t7322 = [0, 92759131966, 363020137279, 365592721609, 70773266519, 1260002070, 0, 0] := by
  decide +kernel

theorem rows7323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7323 = true := by
  decide +kernel

theorem tot7323 : totK PD2M8K2 D2M8K2.t7323 = [0, 0, 261996404175, 492623609756, 141143823173, 3669675759, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
