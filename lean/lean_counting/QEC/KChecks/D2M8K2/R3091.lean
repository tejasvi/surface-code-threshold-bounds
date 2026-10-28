import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12364 = true := by
  decide +kernel

theorem tot12364 : totK PD2M8K2 D2M8K2.t12364 = [0, 0, 292336611123, 503261722913, 104490134796, 1369820453, 0, 0] := by
  decide +kernel

theorem rows12365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12365 = true := by
  decide +kernel

theorem tot12365 : totK PD2M8K2 D2M8K2.t12365 = [0, 0, 168613168811, 460399147109, 211212545642, 16516604865, 0, 0] := by
  decide +kernel

theorem rows12366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12366 = true := by
  decide +kernel

theorem tot12366 : totK PD2M8K2 D2M8K2.t12366 = [0, 0, 163613328602, 456824421823, 226477957745, 14433246171, 0, 0] := by
  decide +kernel

theorem rows12367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12367 = true := by
  decide +kernel

theorem tot12367 : totK PD2M8K2 D2M8K2.t12367 = [0, 0, 0, 322287823223, 429242402225, 75749134871, 1209030869, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
