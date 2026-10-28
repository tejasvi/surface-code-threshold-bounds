import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8244 = true := by
  decide +kernel

theorem tot8244 : totK PD2M8K2 D2M8K2.t8244 = [0, 160534983704, 469396218830, 259621838585, 14049492971, 0, 0, 0] := by
  decide +kernel

theorem rows8245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8245 = true := by
  decide +kernel

theorem tot8245 : totK PD2M8K2 D2M8K2.t8245 = [0, 190827151327, 460418732283, 220140277168, 12595094539, 0, 0, 0] := by
  decide +kernel

theorem rows8246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8246 = true := by
  decide +kernel

theorem tot8246 : totK PD2M8K2 D2M8K2.t8246 = [0, 217549534045, 491767485187, 173081915806, 2772616150, 0, 0, 0] := by
  decide +kernel

theorem rows8247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8247 = true := by
  decide +kernel

theorem tot8247 : totK PD2M8K2 D2M8K2.t8247 = [0, 176942356718, 455440559784, 224021540988, 16861767938, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
