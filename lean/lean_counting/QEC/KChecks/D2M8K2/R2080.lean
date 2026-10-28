import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8320 = true := by
  decide +kernel

theorem tot8320 : totK PD2M8K2 D2M8K2.t8320 = [172453763319, 472616981998, 247237481662, 16905318215, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8321 = true := by
  decide +kernel

theorem tot8321 : totK PD2M8K2 D2M8K2.t8321 = [0, 186110503075, 444937172793, 244449680186, 25268263310, 0, 0, 0] := by
  decide +kernel

theorem rows8322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8322 = true := by
  decide +kernel

theorem tot8322 : totK PD2M8K2 D2M8K2.t8322 = [61235395583, 235898111896, 426012899128, 180289496616, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows8323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8323 = true := by
  decide +kernel

theorem tot8323 : totK PD2M8K2 D2M8K2.t8323 = [178402327228, 457655712337, 242075275896, 19969380392, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
