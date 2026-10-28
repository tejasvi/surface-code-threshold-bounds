import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t448 = true := by
  decide +kernel

theorem tot448 : totK PD2M8K2 D2M8K2.t448 = [0, 176294763562, 459701187085, 261935752866, 19530720407, 0, 0, 0] := by
  decide +kernel

theorem rows449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t449 = true := by
  decide +kernel

theorem tot449 : totK PD2M8K2 D2M8K2.t449 = [0, 0, 261079927867, 497126039511, 114667524315, 2160984415, 0, 0] := by
  decide +kernel

theorem rows450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t450 = true := by
  decide +kernel

theorem tot450 : totK PD2M8K2 D2M8K2.t450 = [0, 154651197687, 400988942710, 276996570554, 59045095970, 2770420231, 0, 0] := by
  decide +kernel

theorem rows451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t451 = true := by
  decide +kernel

theorem tot451 : totK PD2M8K2 D2M8K2.t451 = [0, 171459659894, 442786088629, 268490341479, 24872968063, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
