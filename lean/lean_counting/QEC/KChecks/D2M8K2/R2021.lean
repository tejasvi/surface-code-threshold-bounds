import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8084 = true := by
  decide +kernel

theorem tot8084 : totK PD2M8K2 D2M8K2.t8084 = [0, 49223707097, 330273572756, 438875283589, 94136598964, 1163840124, 0, 0] := by
  decide +kernel

theorem rows8085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8085 = true := by
  decide +kernel

theorem tot8085 : totK PD2M8K2 D2M8K2.t8085 = [0, 0, 211714795389, 482379888348, 176958648515, 10868955253, 0, 0] := by
  decide +kernel

theorem rows8086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8086 = true := by
  decide +kernel

theorem tot8086 : totK PD2M8K2 D2M8K2.t8086 = [0, 158299425549, 429893096825, 298251998449, 36546908136, 0, 0, 0] := by
  decide +kernel

theorem rows8087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8087 = true := by
  decide +kernel

theorem tot8087 : totK PD2M8K2 D2M8K2.t8087 = [0, 207421989131, 484980572848, 211715859337, 10213534575, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
