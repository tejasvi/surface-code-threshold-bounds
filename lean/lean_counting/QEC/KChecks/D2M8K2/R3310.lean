import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13240 = true := by
  decide +kernel

theorem tot13240 : totK PD2M8K2 D2M8K2.t13240 = [0, 0, 181638507913, 468092527352, 212344844162, 12243442891, 0, 0] := by
  decide +kernel

theorem rows13241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13241 = true := by
  decide +kernel

theorem tot13241 : totK PD2M8K2 D2M8K2.t13241 = [0, 0, 172996937440, 484396963822, 216236655947, 8080707082, 0, 0] := by
  decide +kernel

theorem rows13242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13242 = true := by
  decide +kernel

theorem tot13242 : totK PD2M8K2 D2M8K2.t13242 = [0, 0, 177393392379, 467475718654, 225798360604, 11970538636, 0, 0] := by
  decide +kernel

theorem rows13243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13243 = true := by
  decide +kernel

theorem tot13243 : totK PD2M8K2 D2M8K2.t13243 = [0, 0, 207373309013, 478145512763, 188990443630, 6851625295, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
