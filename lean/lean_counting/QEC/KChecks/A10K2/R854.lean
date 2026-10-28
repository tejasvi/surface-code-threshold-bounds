import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3416 = true := by
  decide +kernel

theorem tot3416 : totK PA10K2 A10K2.t3416 = [0, 0, 0, 537207005790, 1822470051687, 1764132808784, 396090148405, 18095079033, 0, 0] := by
  decide +kernel

theorem rows3417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3417 = true := by
  decide +kernel

theorem tot3417 : totK PA10K2 A10K2.t3417 = [0, 0, 0, 465405291593, 1850044906858, 1960333743962, 480053737983, 26116334861, 0, 0] := by
  decide +kernel

theorem rows3418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3418 = true := by
  decide +kernel

theorem tot3418 : totK PA10K2 A10K2.t3418 = [0, 0, 0, 584857847829, 1876807507100, 1803441067045, 421254183485, 18647970522, 0, 0] := by
  decide +kernel

theorem rows3419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3419 = true := by
  decide +kernel

theorem tot3419 : totK PA10K2 A10K2.t3419 = [0, 0, 0, 402115755053, 1761113555834, 1993478797354, 496417222235, 31889781550, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
