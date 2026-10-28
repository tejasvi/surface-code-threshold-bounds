import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11260 = true := by
  decide +kernel

theorem tot11260 : totK PD2M8K2 D2M8K2.t11260 = [0, 182548835618, 451558590926, 253958836804, 25368447013, 0, 0, 0] := by
  decide +kernel

theorem rows11261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11261 = true := by
  decide +kernel

theorem tot11261 : totK PD2M8K2 D2M8K2.t11261 = [0, 209158855637, 487612204036, 196492881163, 5428298985, 0, 0, 0] := by
  decide +kernel

theorem rows11262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11262 = true := by
  decide +kernel

theorem tot11262 : totK PD2M8K2 D2M8K2.t11262 = [171648477473, 375260099905, 244274945737, 98943228367, 6800370819, 0, 0, 0] := by
  decide +kernel

theorem rows11263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11263 = true := by
  decide +kernel

theorem tot11263 : totK PD2M8K2 D2M8K2.t11263 = [161330055897, 440994354032, 287530249088, 30310421197, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
