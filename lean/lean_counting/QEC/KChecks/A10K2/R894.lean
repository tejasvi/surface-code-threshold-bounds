import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3576 = true := by
  decide +kernel

theorem tot3576 : totK PA10K2 A10K2.t3576 = [0, 283058140271, 1373436433923, 2102984228165, 993229033665, 92261259313, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3577 = true := by
  decide +kernel

theorem tot3577 : totK PA10K2 A10K2.t3577 = [0, 275938787155, 1028625518712, 1630501435379, 1382957026925, 380016710900, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows3578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3578 = true := by
  decide +kernel

theorem tot3578 : totK PA10K2 A10K2.t3578 = [0, 430508848225, 1617807997643, 1913141315883, 662169303071, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3579 = true := by
  decide +kernel

theorem tot3579 : totK PA10K2 A10K2.t3579 = [0, 112109183544, 1209763811903, 2304872115917, 1038265351556, 74093114204, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
