import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8632 = true := by
  decide +kernel

theorem tot8632 : totK PD2M8K2 D2M8K2.t8632 = [179462074237, 427035085288, 284677035930, 35872930825, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8633 = true := by
  decide +kernel

theorem tot8633 : totK PD2M8K2 D2M8K2.t8633 = [159622170936, 475731250619, 248926621624, 14997513199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8634 = true := by
  decide +kernel

theorem tot8634 : totK PD2M8K2 D2M8K2.t8634 = [90286224711, 333612255992, 363457098346, 124456936434, 15857395774, 0, 0, 0] := by
  decide +kernel

theorem rows8635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8635 = true := by
  decide +kernel

theorem tot8635 : totK PD2M8K2 D2M8K2.t8635 = [0, 172771994630, 460157959310, 236384843823, 13518339727, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
