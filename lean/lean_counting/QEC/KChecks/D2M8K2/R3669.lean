import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14676 = true := by
  decide +kernel

theorem tot14676 : totK PD2M8K2 D2M8K2.t14676 = [0, 0, 51735240357, 337895635542, 404433424667, 81261988121, 1171084559, 0] := by
  decide +kernel

theorem rows14677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14677 = true := by
  decide +kernel

theorem tot14677 : totK PD2M8K2 D2M8K2.t14677 = [0, 0, 0, 190582186805, 458752537244, 186020677850, 11934365838, 0] := by
  decide +kernel

theorem rows14678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14678 = true := by
  decide +kernel

theorem tot14678 : totK PD2M8K2 D2M8K2.t14678 = [0, 0, 166394246392, 455426217896, 233558870286, 20414710787, 0, 0] := by
  decide +kernel

theorem rows14679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14679 = true := by
  decide +kernel

theorem tot14679 : totK PD2M8K2 D2M8K2.t14679 = [0, 0, 189191510999, 449241935867, 217007604036, 14540813573, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
