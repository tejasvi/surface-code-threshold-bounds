import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2272 = true := by
  decide +kernel

theorem tot2272 : totK PD2M8K2 D2M8K2.t2272 = [0, 37194636605, 343834125470, 472740193667, 63865058547, 0, 0, 0] := by
  decide +kernel

theorem rows2273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2273 = true := by
  decide +kernel

theorem tot2273 : totK PD2M8K2 D2M8K2.t2273 = [0, 202302322018, 457667750961, 222160338583, 19645426257, 0, 0, 0] := by
  decide +kernel

theorem rows2274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2274 = true := by
  decide +kernel

theorem tot2274 : totK PD2M8K2 D2M8K2.t2274 = [0, 173198750947, 465910701777, 232341255219, 13632511348, 0, 0, 0] := by
  decide +kernel

theorem rows2275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2275 = true := by
  decide +kernel

theorem tot2275 : totK PD2M8K2 D2M8K2.t2275 = [0, 0, 284750436087, 501812656103, 109090064032, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
