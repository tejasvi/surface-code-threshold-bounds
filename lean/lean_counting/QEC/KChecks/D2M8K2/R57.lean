import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t228 = true := by
  decide +kernel

theorem tot228 : totK PD2M8K2 D2M8K2.t228 = [0, 0, 281171528767, 496567884316, 110276685432, 1369150432, 0, 0] := by
  decide +kernel

theorem rows229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t229 = true := by
  decide +kernel

theorem tot229 : totK PD2M8K2 D2M8K2.t229 = [0, 73545479377, 364202176072, 421579027570, 54683585126, 0, 0, 0] := by
  decide +kernel

theorem rows230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t230 = true := by
  decide +kernel

theorem tot230 : totK PD2M8K2 D2M8K2.t230 = [0, 183978966912, 457478088982, 240593581627, 16736637023, 0, 0, 0] := by
  decide +kernel

theorem rows231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t231 = true := by
  decide +kernel

theorem tot231 : totK PD2M8K2 D2M8K2.t231 = [0, 69451585063, 365022615180, 412878981823, 68785947818, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
