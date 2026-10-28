import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13348 = true := by
  decide +kernel

theorem tot13348 : totK PD2M8K2 D2M8K2.t13348 = [0, 0, 0, 218408970066, 477825753840, 164272775596, 9633262574, 0] := by
  decide +kernel

theorem rows13349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13349 = true := by
  decide +kernel

theorem tot13349 : totK PD2M8K2 D2M8K2.t13349 = [0, 0, 103438239039, 354211035644, 313766068244, 77400280960, 3472187823, 0] := by
  decide +kernel

theorem rows13350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13350 = true := by
  decide +kernel

theorem tot13350 : totK PD2M8K2 D2M8K2.t13350 = [0, 0, 194445974487, 473401224641, 221776426161, 13258498675, 0, 0] := by
  decide +kernel

theorem rows13351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13351 = true := by
  decide +kernel

theorem tot13351 : totK PD2M8K2 D2M8K2.t13351 = [0, 0, 124658860412, 437993300658, 301120215663, 22570958866, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
