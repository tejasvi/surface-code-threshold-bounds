import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8020 = true := by
  decide +kernel

theorem tot8020 : totK PD2M8K2 D2M8K2.t8020 = [0, 0, 170323481364, 484071546059, 248403417607, 13743597331, 0, 0] := by
  decide +kernel

theorem rows8021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8021 = true := by
  decide +kernel

theorem tot8021 : totK PD2M8K2 D2M8K2.t8021 = [0, 0, 0, 195696703627, 474981095593, 200671984947, 13625832554, 0] := by
  decide +kernel

theorem rows8022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8022 = true := by
  decide +kernel

theorem tot8022 : totK PD2M8K2 D2M8K2.t8022 = [0, 0, 83758629463, 344336586592, 379975504928, 96295730012, 1409560813, 0] := by
  decide +kernel

theorem rows8023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8023 = true := by
  decide +kernel

theorem tot8023 : totK PD2M8K2 D2M8K2.t8023 = [0, 0, 177556925637, 452467643791, 253075160679, 18558482919, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
