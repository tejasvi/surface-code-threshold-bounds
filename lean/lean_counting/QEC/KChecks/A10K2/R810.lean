import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3240 = true := by
  decide +kernel

theorem tot3240 : totK PA10K2 A10K2.t3240 = [0, 0, 476246592928, 1597356644161, 1687552593572, 731950924780, 142907864541, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3241 = true := by
  decide +kernel

theorem tot3241 : totK PA10K2 A10K2.t3241 = [0, 0, 298263154340, 1538616787859, 2069967305788, 680540268866, 38312905762, 0, 0, 0] := by
  decide +kernel

theorem rows3242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3242 = true := by
  decide +kernel

theorem tot3242 : totK PA10K2 A10K2.t3242 = [0, 0, 0, 732552263063, 2164588048463, 1485738120207, 226500590462, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3243 = true := by
  decide +kernel

theorem tot3243 : totK PA10K2 A10K2.t3243 = [0, 0, 0, 559697715774, 1949063334805, 1714076159359, 276493331688, 11508786792, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
