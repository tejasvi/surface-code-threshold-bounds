import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3968 = true := by
  decide +kernel

theorem tot3968 : totK PA10K2 A10K2.t3968 = [0, 0, 557822838406, 1915605109431, 1837641204863, 493788744105, 31941609474, 0, 0, 0] := by
  decide +kernel

theorem rows3969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3969 = true := by
  decide +kernel

theorem tot3969 : totK PA10K2 A10K2.t3969 = [0, 0, 0, 743879569960, 2232099487365, 1453530693494, 191340473112, 0, 0, 0] := by
  decide +kernel

theorem rows3970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3970 = true := by
  decide +kernel

theorem tot3970 : totK PA10K2 A10K2.t3970 = [0, 0, 572092701502, 1943931409954, 1971629677081, 556793139500, 33130628175, 6239673734, 0, 0] := by
  decide +kernel

theorem rows3971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3971 = true := by
  decide +kernel

theorem tot3971 : totK PA10K2 A10K2.t3971 = [0, 0, 226651756384, 1287928851683, 2244970269890, 1213831521294, 142014472026, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
