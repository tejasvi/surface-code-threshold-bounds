import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7484 = true := by
  decide +kernel

theorem tot7484 : totK PA10K2 A10K2.t7484 = [0, 0, 0, 598686693608, 1745719212792, 1682185904842, 736619831775, 142294840848, 5685526223, 0] := by
  decide +kernel

theorem rows7485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7485 = true := by
  decide +kernel

theorem tot7485 : totK PA10K2 A10K2.t7485 = [0, 0, 251986720587, 1133449711255, 1770947078970, 1287469642211, 400896046519, 31276155898, 0, 0] := by
  decide +kernel

theorem rows7486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7486 = true := by
  decide +kernel

theorem tot7486 : totK PA10K2 A10K2.t7486 = [0, 0, 309417675788, 1251163240980, 1920928473679, 1091263423486, 143331241795, 5460492893, 0, 0] := by
  decide +kernel

theorem rows7487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7487 = true := by
  decide +kernel

theorem tot7487 : totK PA10K2 A10K2.t7487 = [0, 0, 488618498030, 1865988901084, 2040490900996, 520998924652, 13227942247, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
