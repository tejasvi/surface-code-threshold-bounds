import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16360 = true := by
  decide +kernel

theorem tot16360 : totK PD2M8K2 D2M8K2.t16360 = [0, 0, 23509793184, 313530081571, 465355963530, 91657434970, 1198073392, 0] := by
  decide +kernel

theorem rows16361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16361 = true := by
  decide +kernel

theorem tot16361 : totK PD2M8K2 D2M8K2.t16361 = [0, 0, 0, 226801246594, 471050878755, 162384606722, 7458616031, 0] := by
  decide +kernel

theorem rows16362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16362 = true := by
  decide +kernel

theorem tot16362 : totK PD2M8K2 D2M8K2.t16362 = [0, 0, 176675633041, 453546944704, 266600796876, 29369303708, 0, 0] := by
  decide +kernel

theorem rows16363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16363 = true := by
  decide +kernel

theorem tot16363 : totK PD2M8K2 D2M8K2.t16363 = [0, 0, 177080075921, 457244467883, 252422019656, 20193855604, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
