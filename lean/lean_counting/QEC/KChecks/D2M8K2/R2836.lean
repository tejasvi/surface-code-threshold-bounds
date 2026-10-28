import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11344 = true := by
  decide +kernel

theorem tot11344 : totK PD2M8K2 D2M8K2.t11344 = [0, 228919644107, 502804316023, 164886512055, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows11345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11345 = true := by
  decide +kernel

theorem tot11345 : totK PD2M8K2 D2M8K2.t11345 = [0, 169325865030, 456099948808, 230373093571, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows11346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11346 = true := by
  decide +kernel

theorem tot11346 : totK PD2M8K2 D2M8K2.t11346 = [0, 80021421004, 365710747918, 357473969667, 63578924231, 1138244013, 0, 0] := by
  decide +kernel

theorem rows11347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11347 = true := by
  decide +kernel

theorem tot11347 : totK PD2M8K2 D2M8K2.t11347 = [0, 93463593641, 402218786166, 366572261734, 42888392542, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
