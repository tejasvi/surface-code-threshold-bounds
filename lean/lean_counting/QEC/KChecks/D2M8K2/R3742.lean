import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14968 = true := by
  decide +kernel

theorem tot14968 : totK PD2M8K2 D2M8K2.t14968 = [0, 202723647975, 497404852657, 199066802721, 8073620866, 0, 0, 0] := by
  decide +kernel

theorem rows14969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14969 = true := by
  decide +kernel

theorem tot14969 : totK PD2M8K2 D2M8K2.t14969 = [0, 0, 250310695147, 450525097302, 191183533984, 19355846809, 0, 0] := by
  decide +kernel

theorem rows14970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14970 = true := by
  decide +kernel

theorem tot14970 : totK PD2M8K2 D2M8K2.t14970 = [0, 0, 165950488152, 488933634907, 221946471606, 6629040516, 0, 0] := by
  decide +kernel

theorem rows14971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14971 = true := by
  decide +kernel

theorem tot14971 : totK PD2M8K2 D2M8K2.t14971 = [0, 124350470976, 353183627139, 306893602143, 113084772769, 6779944490, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
