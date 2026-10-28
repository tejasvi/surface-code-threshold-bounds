import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3336 = true := by
  decide +kernel

theorem tot3336 : totK PD2M8K2 D2M8K2.t3336 = [0, 30722815107, 309846258361, 447662628589, 96151699710, 1268739303, 0, 0] := by
  decide +kernel

theorem rows3337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3337 = true := by
  decide +kernel

theorem tot3337 : totK PD2M8K2 D2M8K2.t3337 = [0, 0, 217046391387, 493690534842, 162068155804, 4683989726, 0, 0] := by
  decide +kernel

theorem rows3338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3338 = true := by
  decide +kernel

theorem tot3338 : totK PD2M8K2 D2M8K2.t3338 = [0, 0, 172083126798, 461759247075, 209385997751, 13665114095, 0, 0] := by
  decide +kernel

theorem rows3339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3339 = true := by
  decide +kernel

theorem tot3339 : totK PD2M8K2 D2M8K2.t3339 = [0, 0, 170233854908, 461733250662, 218111202871, 12293492090, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
