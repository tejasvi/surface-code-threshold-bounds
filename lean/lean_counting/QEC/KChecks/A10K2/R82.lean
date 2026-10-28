import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t328 = true := by
  decide +kernel

theorem tot328 : totK PA10K2 A10K2.t328 = [0, 0, 470196809533, 1759116009272, 1949798106296, 543753112742, 31987876949, 0, 0, 0] := by
  decide +kernel

theorem rows329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t329 = true := by
  decide +kernel

theorem tot329 : totK PA10K2 A10K2.t329 = [0, 0, 490074055546, 1823462309707, 1929861211366, 519901826841, 32476580988, 0, 0, 0] := by
  decide +kernel

theorem rows330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t330 = true := by
  decide +kernel

theorem tot330 : totK PA10K2 A10K2.t330 = [0, 0, 444211917520, 1780899663493, 1938007626106, 507028591003, 31088438951, 0, 0, 0] := by
  decide +kernel

theorem rows331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t331 = true := by
  decide +kernel

theorem tot331 : totK PA10K2 A10K2.t331 = [0, 0, 545063906002, 1863013683090, 1731235964140, 393522257715, 25533540376, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
