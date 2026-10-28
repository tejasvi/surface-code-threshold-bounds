import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14948 = true := by
  decide +kernel

theorem tot14948 : totK PD2M8K2 D2M8K2.t14948 = [0, 181818599164, 464479751570, 259070920065, 23332966453, 0, 0, 0] := by
  decide +kernel

theorem rows14949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14949 = true := by
  decide +kernel

theorem tot14949 : totK PD2M8K2 D2M8K2.t14949 = [0, 165557762767, 467788183318, 248321296646, 13779052747, 0, 0, 0] := by
  decide +kernel

theorem rows14950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14950 = true := by
  decide +kernel

theorem tot14950 : totK PD2M8K2 D2M8K2.t14950 = [0, 0, 277449447944, 509137055025, 115890852006, 1129489618, 0, 0] := by
  decide +kernel

theorem rows14951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14951 = true := by
  decide +kernel

theorem tot14951 : totK PD2M8K2 D2M8K2.t14951 = [0, 56012782626, 243897037057, 410255903056, 158196601445, 7938259948, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
