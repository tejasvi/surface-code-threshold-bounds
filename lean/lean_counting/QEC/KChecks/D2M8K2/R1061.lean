import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4244 = true := by
  decide +kernel

theorem tot4244 : totK PD2M8K2 D2M8K2.t4244 = [0, 0, 0, 199767309059, 477442101642, 210072334269, 6474574999, 0] := by
  decide +kernel

theorem rows4245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4245 = true := by
  decide +kernel

theorem tot4245 : totK PD2M8K2 D2M8K2.t4245 = [0, 0, 163536014650, 372102241387, 254360666427, 102028061919, 6756679742, 0] := by
  decide +kernel

theorem rows4246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4246 = true := by
  decide +kernel

theorem tot4246 : totK PD2M8K2 D2M8K2.t4246 = [0, 0, 165467449888, 443216604186, 284082474396, 30310421197, 0, 0] := by
  decide +kernel

theorem rows4247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4247 = true := by
  decide +kernel

theorem tot4247 : totK PD2M8K2 D2M8K2.t4247 = [0, 0, 107242703708, 432127887482, 326938621222, 26912306060, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
