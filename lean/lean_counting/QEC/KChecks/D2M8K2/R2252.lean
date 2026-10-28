import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9008 = true := by
  decide +kernel

theorem tot9008 : totK PD2M8K2 D2M8K2.t9008 = [0, 100042299809, 407821203569, 341837769593, 39607677135, 0, 0, 0] := by
  decide +kernel

theorem rows9009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9009 = true := by
  decide +kernel

theorem tot9009 : totK PD2M8K2 D2M8K2.t9009 = [0, 0, 268660169180, 469697528254, 126137100956, 3824247485, 0, 0] := by
  decide +kernel

theorem rows9010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9010 = true := by
  decide +kernel

theorem tot9010 : totK PD2M8K2 D2M8K2.t9010 = [0, 175443703113, 453710943905, 254526853336, 30864802178, 0, 0, 0] := by
  decide +kernel

theorem rows9011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9011 = true := by
  decide +kernel

theorem tot9011 : totK PD2M8K2 D2M8K2.t9011 = [0, 171269673657, 457352743664, 257748323695, 16234199175, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
