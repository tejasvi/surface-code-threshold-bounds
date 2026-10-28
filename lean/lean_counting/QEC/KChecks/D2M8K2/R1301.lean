import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5204 = true := by
  decide +kernel

theorem tot5204 : totK PD2M8K2 D2M8K2.t5204 = [0, 0, 0, 205652697565, 472226413938, 197723528777, 12337737162, 0] := by
  decide +kernel

theorem rows5205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5205 = true := by
  decide +kernel

theorem tot5205 : totK PD2M8K2 D2M8K2.t5205 = [0, 0, 0, 190515751535, 470813853625, 217181817554, 15817296786, 0] := by
  decide +kernel

theorem rows5206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5206 = true := by
  decide +kernel

theorem tot5206 : totK PD2M8K2 D2M8K2.t5206 = [0, 0, 0, 189093621931, 464132660509, 216569117426, 16702988424, 0] := by
  decide +kernel

theorem rows5207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5207 = true := by
  decide +kernel

theorem tot5207 : totK PD2M8K2 D2M8K2.t5207 = [0, 0, 0, 0, 374083575183, 439653398247, 50246966307, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
