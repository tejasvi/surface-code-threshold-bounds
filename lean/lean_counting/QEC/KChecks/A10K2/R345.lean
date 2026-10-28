import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1380 = true := by
  decide +kernel

theorem tot1380 : totK PA10K2 A10K2.t1380 = [0, 0, 0, 546878425568, 1798651187571, 1752011852940, 409840769248, 30637645759, 0, 0] := by
  decide +kernel

theorem rows1381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1381 = true := by
  decide +kernel

theorem tot1381 : totK PA10K2 A10K2.t1381 = [0, 0, 0, 114454617089, 1327757325808, 2248724451424, 747825912579, 57935029211, 0, 0] := by
  decide +kernel

theorem rows1382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1382 = true := by
  decide +kernel

theorem tot1382 : totK PA10K2 A10K2.t1382 = [0, 0, 386810876066, 1246490921536, 1350591915871, 986662430839, 649333597706, 135599603508, 5976421810, 0] := by
  decide +kernel

theorem rows1383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1383 = true := by
  decide +kernel

theorem tot1383 : totK PA10K2 A10K2.t1383 = [0, 0, 424696042551, 1708246245579, 2026377047018, 725809312629, 41032124780, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
