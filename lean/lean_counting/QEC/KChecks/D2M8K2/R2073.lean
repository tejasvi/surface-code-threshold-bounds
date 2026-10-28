import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8292 = true := by
  decide +kernel

theorem tot8292 : totK PD2M8K2 D2M8K2.t8292 = [162959780058, 437572836257, 266925867296, 29005570695, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8293 = true := by
  decide +kernel

theorem tot8293 : totK PD2M8K2 D2M8K2.t8293 = [157751799820, 465015846232, 266522538088, 15127500287, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8294 = true := by
  decide +kernel

theorem tot8294 : totK PD2M8K2 D2M8K2.t8294 = [0, 281381905509, 512864795797, 102851659740, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8295 = true := by
  decide +kernel

theorem tot8295 : totK PD2M8K2 D2M8K2.t8295 = [118410150176, 350239237696, 325941807104, 93007622530, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
