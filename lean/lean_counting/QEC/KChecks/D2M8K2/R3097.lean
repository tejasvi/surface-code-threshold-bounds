import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12388 = true := by
  decide +kernel

theorem tot12388 : totK PD2M8K2 D2M8K2.t12388 = [0, 164098953872, 446803990450, 281064874207, 30464007850, 0, 0, 0] := by
  decide +kernel

theorem rows12389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12389 = true := by
  decide +kernel

theorem tot12389 : totK PD2M8K2 D2M8K2.t12389 = [0, 177697891872, 471522197416, 237048437630, 13810701828, 0, 0, 0] := by
  decide +kernel

theorem rows12390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12390 = true := by
  decide +kernel

theorem tot12390 : totK PD2M8K2 D2M8K2.t12390 = [0, 0, 328594404653, 517679042250, 70377215768, 0, 0, 0] := by
  decide +kernel

theorem rows12391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12391 = true := by
  decide +kernel

theorem tot12391 : totK PD2M8K2 D2M8K2.t12391 = [0, 111463607843, 328173517043, 365591272165, 109618775066, 3880716147, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
