import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13304 = true := by
  decide +kernel

theorem tot13304 : totK PD2M8K2 D2M8K2.t13304 = [0, 0, 210381546025, 481789328257, 183134596168, 7428547934, 0, 0] := by
  decide +kernel

theorem rows13305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13305 = true := by
  decide +kernel

theorem tot13305 : totK PD2M8K2 D2M8K2.t13305 = [0, 0, 182888343051, 482200962047, 206499469035, 9840992866, 0, 0] := by
  decide +kernel

theorem rows13306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13306 = true := by
  decide +kernel

theorem tot13306 : totK PD2M8K2 D2M8K2.t13306 = [0, 0, 160975441361, 468792104306, 214929326389, 7693443986, 0, 0] := by
  decide +kernel

theorem rows13307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13307 = true := by
  decide +kernel

theorem tot13307 : totK PD2M8K2 D2M8K2.t13307 = [0, 0, 0, 284765637692, 470803802280, 76790009822, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
