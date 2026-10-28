import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2604 = true := by
  decide +kernel

theorem tot2604 : totK PA10K2 A10K2.t2604 = [0, 110196786130, 1245978601098, 2308563404554, 991357005476, 80561410090, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2605 = true := by
  decide +kernel

theorem tot2605 : totK PA10K2 A10K2.t2605 = [0, 266424507814, 1165244506728, 1894111312640, 1171710831221, 219532983770, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2606 = true := by
  decide +kernel

theorem tot2606 : totK PA10K2 A10K2.t2606 = [0, 311769148082, 1271536338145, 1826685115226, 1186584273561, 233554241796, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows2607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2607 = true := by
  decide +kernel

theorem tot2607 : totK PA10K2 A10K2.t2607 = [0, 503333154511, 1881436807641, 2000034488749, 502462522911, 12244162943, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
