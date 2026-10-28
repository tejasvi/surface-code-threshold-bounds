import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11176 = true := by
  decide +kernel

theorem tot11176 : totK PD2M8K2 D2M8K2.t11176 = [0, 89955272290, 417822313768, 354633097209, 31723832687, 0, 0, 0] := by
  decide +kernel

theorem rows11177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11177 = true := by
  decide +kernel

theorem tot11177 : totK PD2M8K2 D2M8K2.t11177 = [0, 0, 210613976751, 497349402524, 172296533017, 4957057700, 0, 0] := by
  decide +kernel

theorem rows11178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11178 = true := by
  decide +kernel

theorem tot11178 : totK PD2M8K2 D2M8K2.t11178 = [0, 120061253264, 348323172493, 308650311346, 108125976518, 8757608180, 0, 0] := by
  decide +kernel

theorem rows11179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11179 = true := by
  decide +kernel

theorem tot11179 : totK PD2M8K2 D2M8K2.t11179 = [0, 174105027629, 453037658490, 241062282897, 17115888737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
