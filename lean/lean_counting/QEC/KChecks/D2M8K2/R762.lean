import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3048 = true := by
  decide +kernel

theorem tot3048 : totK PD2M8K2 D2M8K2.t3048 = [0, 146060098176, 358650709099, 274122127541, 106959807371, 8935385149, 0, 0] := by
  decide +kernel

theorem rows3049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3049 = true := by
  decide +kernel

theorem tot3049 : totK PD2M8K2 D2M8K2.t3049 = [0, 177590076730, 446996132148, 232507027987, 18130804188, 0, 0, 0] := by
  decide +kernel

theorem rows3050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3050 = true := by
  decide +kernel

theorem tot3050 : totK PD2M8K2 D2M8K2.t3050 = [0, 52708991598, 327642280343, 405341971190, 82993726855, 1310166938, 0, 0] := by
  decide +kernel

theorem rows3051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3051 = true := by
  decide +kernel

theorem tot3051 : totK PD2M8K2 D2M8K2.t3051 = [0, 85034397123, 366088505937, 407257995891, 47535736078, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
