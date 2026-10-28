import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12140 = true := by
  decide +kernel

theorem tot12140 : totK PD2M8K2 D2M8K2.t12140 = [0, 0, 209090920551, 471625398257, 175509052778, 9541089458, 0, 0] := by
  decide +kernel

theorem rows12141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12141 = true := by
  decide +kernel

theorem tot12141 : totK PD2M8K2 D2M8K2.t12141 = [0, 0, 104049506562, 403621718443, 284502129665, 40197166236, 1138244013, 0] := by
  decide +kernel

theorem rows12142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12142 = true := by
  decide +kernel

theorem tot12142 : totK PD2M8K2 D2M8K2.t12142 = [0, 0, 55728860606, 374997221845, 383144176954, 36242921094, 0, 0] := by
  decide +kernel

theorem rows12143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12143 = true := by
  decide +kernel

theorem tot12143 : totK PD2M8K2 D2M8K2.t12143 = [0, 0, 202294841566, 470287232169, 220938299041, 14942475072, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
