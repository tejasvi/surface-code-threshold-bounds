import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1540 = true := by
  decide +kernel

theorem tot1540 : totK PA10K2 A10K2.t1540 = [0, 0, 687290242962, 2100021112592, 1546572747098, 255466460062, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1541 = true := by
  decide +kernel

theorem tot1541 : totK PA10K2 A10K2.t1541 = [0, 0, 540067211647, 1960136600745, 1854545196055, 438743718799, 25633273041, 0, 0, 0] := by
  decide +kernel

theorem rows1542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1542 = true := by
  decide +kernel

theorem tot1542 : totK PA10K2 A10K2.t1542 = [0, 0, 443849169556, 1730483352651, 2038841342653, 623090596893, 39266247089, 0, 0, 0] := by
  decide +kernel

theorem rows1543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1543 = true := by
  decide +kernel

theorem tot1543 : totK PA10K2 A10K2.t1543 = [0, 0, 551687302947, 1915300962102, 1793652236860, 416126692046, 25668410676, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
