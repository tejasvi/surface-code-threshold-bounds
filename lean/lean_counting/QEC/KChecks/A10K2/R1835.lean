import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7340 = true := by
  decide +kernel

theorem tot7340 : totK PA10K2 A10K2.t7340 = [0, 0, 0, 387857304913, 1593217631052, 1889947202086, 578155145668, 37809658159, 0, 0] := by
  decide +kernel

theorem rows7341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7341 = true := by
  decide +kernel

theorem tot7341 : totK PA10K2 A10K2.t7341 = [0, 0, 0, 186667762849, 1042166382572, 1958005218588, 1123373000217, 173790711660, 5705019915, 0] := by
  decide +kernel

theorem rows7342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7342 = true := by
  decide +kernel

theorem tot7342 : totK PA10K2 A10K2.t7342 = [0, 0, 0, 592348102083, 2015374335815, 1966518803636, 483579568802, 25574931378, 0, 0] := by
  decide +kernel

theorem rows7343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7343 = true := by
  decide +kernel

theorem tot7343 : totK PA10K2 A10K2.t7343 = [0, 0, 0, 0, 800963831912, 2241049851271, 1649257005903, 286419054556, 6853348008, 0] := by
  decide +kernel

end QECKChecks.A10K2
