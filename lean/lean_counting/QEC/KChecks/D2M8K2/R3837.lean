import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15348 = true := by
  decide +kernel

theorem tot15348 : totK PD2M8K2 D2M8K2.t15348 = [0, 0, 229912351500, 501205743042, 160306649332, 4929677829, 0, 0] := by
  decide +kernel

theorem rows15349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15349 = true := by
  decide +kernel

theorem tot15349 : totK PD2M8K2 D2M8K2.t15349 = [0, 0, 178779249288, 469329533132, 221733160788, 11253488567, 0, 0] := by
  decide +kernel

theorem rows15350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15350 = true := by
  decide +kernel

theorem tot15350 : totK PD2M8K2 D2M8K2.t15350 = [0, 0, 182735830479, 451325663774, 268631887409, 32229084478, 0, 0] := by
  decide +kernel

theorem rows15351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15351 = true := by
  decide +kernel

theorem tot15351 : totK PD2M8K2 D2M8K2.t15351 = [0, 0, 185992283914, 472841730951, 237880035918, 11019007305, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
