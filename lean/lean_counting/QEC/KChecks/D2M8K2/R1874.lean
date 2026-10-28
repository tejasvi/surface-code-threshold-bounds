import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7496 = true := by
  decide +kernel

theorem tot7496 : totK PD2M8K2 D2M8K2.t7496 = [0, 0, 199681473527, 474337813150, 182230998232, 7475943710, 0, 0] := by
  decide +kernel

theorem rows7497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7497 = true := by
  decide +kernel

theorem tot7497 : totK PD2M8K2 D2M8K2.t7497 = [0, 0, 36932443061, 316834708136, 417619792011, 88269467663, 1369150432, 0] := by
  decide +kernel

theorem rows7498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7498 = true := by
  decide +kernel

theorem tot7498 : totK PD2M8K2 D2M8K2.t7498 = [0, 0, 87307959298, 395419058613, 342611686895, 35386140531, 0, 0] := by
  decide +kernel

theorem rows7499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7499 = true := by
  decide +kernel

theorem tot7499 : totK PD2M8K2 D2M8K2.t7499 = [0, 0, 165116540413, 472211465629, 249486701376, 12460012990, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
