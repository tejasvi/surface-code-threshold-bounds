import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16336 = true := by
  decide +kernel

theorem tot16336 : totK PD2M8K2 D2M8K2.t16336 = [0, 0, 0, 0, 313950620594, 450858706328, 69159545605, 1200365979] := by
  decide +kernel

theorem rows16337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16337 = true := by
  decide +kernel

theorem tot16337 : totK PD2M8K2 D2M8K2.t16337 = [0, 0, 0, 162905041139, 453833075749, 270206567490, 21942340307, 0] := by
  decide +kernel

theorem rows16338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16338 = true := by
  decide +kernel

theorem tot16338 : totK PD2M8K2 D2M8K2.t16338 = [0, 0, 0, 242422800547, 496783183019, 172026538384, 3380884156, 0] := by
  decide +kernel

theorem rows16339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16339 = true := by
  decide +kernel

theorem tot16339 : totK PD2M8K2 D2M8K2.t16339 = [0, 0, 0, 202223730384, 466925295096, 203609999166, 15229159918, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
