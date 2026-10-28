import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8692 = true := by
  decide +kernel

theorem tot8692 : totK PD2M8K2 D2M8K2.t8692 = [0, 0, 140267586186, 360760329774, 290929101503, 105140491660, 6524090962, 0] := by
  decide +kernel

theorem rows8693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8693 = true := by
  decide +kernel

theorem tot8693 : totK PD2M8K2 D2M8K2.t8693 = [0, 0, 174350606226, 460491139247, 235411777090, 11762366706, 0, 0] := by
  decide +kernel

theorem rows8694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8694 = true := by
  decide +kernel

theorem tot8694 : totK PD2M8K2 D2M8K2.t8694 = [0, 0, 85151295732, 387423427132, 377644749805, 43660858666, 0, 0] := by
  decide +kernel

theorem rows8695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8695 = true := by
  decide +kernel

theorem tot8695 : totK PD2M8K2 D2M8K2.t8695 = [0, 0, 3657503759, 214447233899, 492460811388, 146160239512, 5067863418, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
