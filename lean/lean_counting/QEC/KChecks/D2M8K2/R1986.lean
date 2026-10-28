import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7944 = true := by
  decide +kernel

theorem tot7944 : totK PD2M8K2 D2M8K2.t7944 = [0, 0, 177285224724, 451911787303, 227381491548, 17115888737, 0, 0] := by
  decide +kernel

theorem rows7945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7945 = true := by
  decide +kernel

theorem tot7945 : totK PD2M8K2 D2M8K2.t7945 = [0, 0, 82223897701, 384551886891, 354666744468, 54567433853, 1369150432, 0] := by
  decide +kernel

theorem rows7946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7946 = true := by
  decide +kernel

theorem tot7946 : totK PD2M8K2 D2M8K2.t7946 = [0, 0, 0, 299313773985, 508489454055, 74638378150, 0, 0] := by
  decide +kernel

theorem rows7947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7947 = true := by
  decide +kernel

theorem tot7947 : totK PD2M8K2 D2M8K2.t7947 = [0, 0, 173337114409, 454772676192, 256486794289, 18852687404, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
