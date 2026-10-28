import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14232 = true := by
  decide +kernel

theorem tot14232 : totK PD2M8K2 D2M8K2.t14232 = [167706023315, 437650887434, 280985119485, 30465585733, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14233 = true := by
  decide +kernel

theorem tot14233 : totK PD2M8K2 D2M8K2.t14233 = [200883480238, 489571555101, 214664711265, 11101773997, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14234 = true := by
  decide +kernel

theorem tot14234 : totK PD2M8K2 D2M8K2.t14234 = [0, 236910049499, 452122705984, 197162734624, 21385708972, 0, 0, 0] := by
  decide +kernel

theorem rows14235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14235 = true := by
  decide +kernel

theorem tot14235 : totK PD2M8K2 D2M8K2.t14235 = [0, 156407229169, 484205745741, 249539838392, 7994456143, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
