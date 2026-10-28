import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16212 = true := by
  decide +kernel

theorem tot16212 : totK PD2M8K2 D2M8K2.t16212 = [0, 157088974604, 461810532630, 279835292068, 18321600741, 0, 0, 0] := by
  decide +kernel

theorem rows16213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16213 = true := by
  decide +kernel

theorem tot16213 : totK PD2M8K2 D2M8K2.t16213 = [0, 0, 216866654219, 494898531754, 170742374611, 7232373827, 0, 0] := by
  decide +kernel

theorem rows16214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16214 = true := by
  decide +kernel

theorem tot16214 : totK PD2M8K2 D2M8K2.t16214 = [0, 87123270202, 309030199248, 376447875881, 115889827586, 4112248878, 0, 0] := by
  decide +kernel

theorem rows16215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16215 = true := by
  decide +kernel

theorem tot16215 : totK PD2M8K2 D2M8K2.t16215 = [0, 178588180851, 469481391114, 257874401571, 22839296428, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
