import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3504 = true := by
  decide +kernel

theorem tot3504 : totK PA10K2 A10K2.t3504 = [0, 0, 0, 419203388268, 1766442540989, 1994416654724, 510648179331, 17672080322, 0, 0] := by
  decide +kernel

theorem rows3505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3505 = true := by
  decide +kernel

theorem tot3505 : totK PA10K2 A10K2.t3505 = [0, 0, 0, 117663513915, 912183839823, 2118349270613, 1303073239065, 170574282216, 6354482628, 0] := by
  decide +kernel

theorem rows3506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3506 = true := by
  decide +kernel

theorem tot3506 : totK PA10K2 A10K2.t3506 = [0, 0, 0, 467927463778, 1836540060581, 1964473060518, 495402004432, 26491486257, 0, 0] := by
  decide +kernel

theorem rows3507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3507 = true := by
  decide +kernel

theorem tot3507 : totK PA10K2 A10K2.t3507 = [0, 0, 0, 254114791153, 1249610472983, 2126312760325, 1148434422941, 115648220561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
