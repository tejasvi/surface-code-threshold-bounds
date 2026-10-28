import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6568 = true := by
  decide +kernel

theorem tot6568 : totK PA10K2 A10K2.t6568 = [0, 313458112005, 1578236572536, 2137637533835, 732067478483, 52575686575, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6569 = true := by
  decide +kernel

theorem tot6569 : totK PA10K2 A10K2.t6569 = [0, 114273695951, 655583482881, 1775802497329, 1670670483975, 414502878969, 30402056026, 0, 0, 0] := by
  decide +kernel

theorem rows6570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6570 = true := by
  decide +kernel

theorem tot6570 : totK PA10K2 A10K2.t6570 = [0, 466362396631, 1849034307818, 1956994878848, 498159463444, 26491486257, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6571 = true := by
  decide +kernel

theorem tot6571 : totK PA10K2 A10K2.t6571 = [0, 186511936084, 983572939652, 1919876330357, 1438049434369, 340487181896, 20340910120, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
