import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14240 = true := by
  decide +kernel

theorem tot14240 : totK PD2M8K2 D2M8K2.t14240 = [84004660009, 333115546256, 361911830203, 96579347197, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows14241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14241 = true := by
  decide +kernel

theorem tot14241 : totK PD2M8K2 D2M8K2.t14241 = [175881647308, 441618552490, 271049052372, 28650453103, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14242 = true := by
  decide +kernel

theorem tot14242 : totK PD2M8K2 D2M8K2.t14242 = [164271273082, 467572934783, 256363956613, 15387838538, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14243 = true := by
  decide +kernel

theorem tot14243 : totK PD2M8K2 D2M8K2.t14243 = [0, 274262731645, 514900660750, 106380885905, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
