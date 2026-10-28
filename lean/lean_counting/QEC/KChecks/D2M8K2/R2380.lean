import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9520 = true := by
  decide +kernel

theorem tot9520 : totK PD2M8K2 D2M8K2.t9520 = [161062866879, 480482819169, 252210875969, 13632511348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9521 = true := by
  decide +kernel

theorem tot9521 : totK PD2M8K2 D2M8K2.t9521 = [0, 278695562133, 505472027118, 112011448284, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows9522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9522 = true := by
  decide +kernel

theorem tot9522 : totK PD2M8K2 D2M8K2.t9522 = [18464490943, 208984146031, 454960572706, 186910565920, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows9523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9523 = true := by
  decide +kernel

theorem tot9523 : totK PD2M8K2 D2M8K2.t9523 = [186695397941, 454222929277, 244079715476, 22916796737, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
