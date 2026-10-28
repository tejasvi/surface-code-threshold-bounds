import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10624 = true := by
  decide +kernel

theorem tot10624 : totK PD2M8K2 D2M8K2.t10624 = [0, 0, 179935757967, 471510736402, 232579538862, 13176583453, 0, 0] := by
  decide +kernel

theorem rows10625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10625 = true := by
  decide +kernel

theorem tot10625 : totK PD2M8K2 D2M8K2.t10625 = [0, 0, 0, 327032888750, 452978212164, 67698573933, 1053411165, 0] := by
  decide +kernel

theorem rows10626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10626 = true := by
  decide +kernel

theorem tot10626 : totK PD2M8K2 D2M8K2.t10626 = [0, 0, 80954891220, 323384036074, 360215285164, 90013022062, 3667207281, 0] := by
  decide +kernel

theorem rows10627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10627 = true := by
  decide +kernel

theorem tot10627 : totK PD2M8K2 D2M8K2.t10627 = [0, 0, 174320196350, 451630773935, 272056779593, 26269915656, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
