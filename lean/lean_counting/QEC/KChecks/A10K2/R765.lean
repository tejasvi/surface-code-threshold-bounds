import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3060 = true := by
  decide +kernel

theorem tot3060 : totK PA10K2 A10K2.t3060 = [0, 0, 308525764274, 1212472898747, 1898679614177, 1287913783904, 216522856900, 6632180018, 0, 0] := by
  decide +kernel

theorem rows3061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3061 = true := by
  decide +kernel

theorem tot3061 : totK PA10K2 A10K2.t3061 = [0, 0, 495583288092, 1860594184286, 2009517235475, 551772788280, 31712524204, 0, 0, 0] := by
  decide +kernel

theorem rows3062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3062 = true := by
  decide +kernel

theorem tot3062 : totK PA10K2 A10K2.t3062 = [0, 0, 0, 798062205163, 2255269411870, 1628826694049, 271379366492, 7047025452, 0, 0] := by
  decide +kernel

theorem rows3063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3063 = true := by
  decide +kernel

theorem tot3063 : totK PA10K2 A10K2.t3063 = [0, 0, 395707756605, 1547814925361, 1984366917257, 855341447764, 73845105913, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
