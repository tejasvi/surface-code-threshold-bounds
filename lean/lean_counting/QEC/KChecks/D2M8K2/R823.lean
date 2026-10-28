import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3292 = true := by
  decide +kernel

theorem tot3292 : totK PD2M8K2 D2M8K2.t3292 = [0, 0, 183205287686, 466561384208, 215125796001, 12251875289, 0, 0] := by
  decide +kernel

theorem rows3293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3293 = true := by
  decide +kernel

theorem tot3293 : totK PD2M8K2 D2M8K2.t3293 = [0, 0, 199337215679, 479069993961, 191654259876, 10090831696, 0, 0] := by
  decide +kernel

theorem rows3294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3294 = true := by
  decide +kernel

theorem tot3294 : totK PD2M8K2 D2M8K2.t3294 = [0, 0, 178163713720, 487235187493, 190329092477, 8362342989, 0, 0] := by
  decide +kernel

theorem rows3295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3295 = true := by
  decide +kernel

theorem tot3295 : totK PD2M8K2 D2M8K2.t3295 = [0, 0, 194393617509, 481332361923, 195318636932, 7703174902, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
