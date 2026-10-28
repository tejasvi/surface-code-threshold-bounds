import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3156 = true := by
  decide +kernel

theorem tot3156 : totK PD2M8K2 D2M8K2.t3156 = [0, 0, 279983588571, 483857229884, 128208342659, 4031931762, 0, 0] := by
  decide +kernel

theorem rows3157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3157 = true := by
  decide +kernel

theorem tot3157 : totK PD2M8K2 D2M8K2.t3157 = [0, 102243800671, 343697922566, 352096119997, 76617592673, 1186940923, 0, 0] := by
  decide +kernel

theorem rows3158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3158 = true := by
  decide +kernel

theorem tot3158 : totK PD2M8K2 D2M8K2.t3158 = [0, 177394267237, 440087021389, 271598487729, 30141023496, 0, 0, 0] := by
  decide +kernel

theorem rows3159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3159 = true := by
  decide +kernel

theorem tot3159 : totK PD2M8K2 D2M8K2.t3159 = [0, 131255284521, 452462756661, 284150230652, 15904190786, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
