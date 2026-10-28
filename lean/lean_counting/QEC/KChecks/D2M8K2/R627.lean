import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2508 = true := by
  decide +kernel

theorem tot2508 : totK PD2M8K2 D2M8K2.t2508 = [0, 186772526655, 480293169007, 230963001718, 12206498855, 0, 0, 0] := by
  decide +kernel

theorem rows2509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2509 = true := by
  decide +kernel

theorem tot2509 : totK PD2M8K2 D2M8K2.t2509 = [0, 158146766690, 471681797849, 242452895258, 12974349761, 0, 0, 0] := by
  decide +kernel

theorem rows2510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2510 = true := by
  decide +kernel

theorem tot2510 : totK PD2M8K2 D2M8K2.t2510 = [0, 0, 312738036874, 460116675644, 76695627722, 1021600638, 0, 0] := by
  decide +kernel

theorem rows2511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2511 = true := by
  decide +kernel

theorem tot2511 : totK PD2M8K2 D2M8K2.t2511 = [0, 131972496502, 355461171301, 292100161598, 73515744304, 3552795014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
