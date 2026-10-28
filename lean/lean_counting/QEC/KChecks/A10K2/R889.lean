import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3556 = true := by
  decide +kernel

theorem tot3556 : totK PA10K2 A10K2.t3556 = [0, 0, 0, 326490833374, 1608169313489, 2208329835797, 852445118033, 63498369384, 0, 0] := by
  decide +kernel

theorem rows3557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3557 = true := by
  decide +kernel

theorem tot3557 : totK PA10K2 A10K2.t3557 = [0, 0, 0, 0, 598440199381, 2062758874815, 1898842088696, 421669265458, 11979448558, 0] := by
  decide +kernel

theorem rows3558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3558 = true := by
  decide +kernel

theorem tot3558 : totK PA10K2 A10K2.t3558 = [0, 567096277625, 1710988029582, 1562835135383, 406660435206, 107359696002, 265134597811, 204698064761, 29941795906, 0] := by
  decide +kernel

theorem rows3559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3559 = true := by
  decide +kernel

theorem tot3559 : totK PA10K2 A10K2.t3559 = [0, 259484965560, 1534627577571, 2166074833376, 845737317090, 68618480358, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
