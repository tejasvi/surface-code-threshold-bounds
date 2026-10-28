import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6388 = true := by
  decide +kernel

theorem tot6388 : totK PD2M8K2 D2M8K2.t6388 = [0, 193008030363, 469219597091, 200941801748, 22531914384, 5067492771, 0, 0] := by
  decide +kernel

theorem rows6389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6389 = true := by
  decide +kernel

theorem tot6389 : totK PD2M8K2 D2M8K2.t6389 = [0, 193398040289, 459862825200, 207544752980, 12467683885, 0, 0, 0] := by
  decide +kernel

theorem rows6390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6390 = true := by
  decide +kernel

theorem tot6390 : totK PD2M8K2 D2M8K2.t6390 = [0, 14932660016, 295452362266, 472018966363, 94217982760, 1310166938, 0, 0] := by
  decide +kernel

theorem rows6391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6391 = true := by
  decide +kernel

theorem tot6391 : totK PD2M8K2 D2M8K2.t6391 = [0, 92874408096, 384792765226, 385788242200, 46340365900, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
