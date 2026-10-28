import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16288 = true := by
  decide +kernel

theorem tot16288 : totK PD2M8K2 D2M8K2.t16288 = [0, 0, 126538963394, 396730483701, 356316224712, 42734440473, 0, 0] := by
  decide +kernel

theorem rows16289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16289 = true := by
  decide +kernel

theorem tot16289 : totK PD2M8K2 D2M8K2.t16289 = [0, 0, 202716730843, 498031276750, 214153244353, 8533180437, 0, 0] := by
  decide +kernel

theorem rows16290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16290 = true := by
  decide +kernel

theorem tot16290 : totK PD2M8K2 D2M8K2.t16290 = [0, 0, 88156931025, 359553959799, 359223826772, 102531043349, 7646483521, 0] := by
  decide +kernel

theorem rows16291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16291 = true := by
  decide +kernel

theorem tot16291 : totK PD2M8K2 D2M8K2.t16291 = [0, 0, 0, 284888867482, 489422110468, 143783462443, 4418210786, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
