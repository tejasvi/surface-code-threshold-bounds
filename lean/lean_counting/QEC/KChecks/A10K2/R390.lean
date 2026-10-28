import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1560 = true := by
  decide +kernel

theorem tot1560 : totK PA10K2 A10K2.t1560 = [0, 0, 212919441758, 1080368251370, 1939771446875, 1270097456286, 206171988166, 5460492893, 0, 0] := by
  decide +kernel

theorem rows1561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1561 = true := by
  decide +kernel

theorem tot1561 : totK PA10K2 A10K2.t1561 = [0, 0, 528558213609, 1785289765802, 1823898934288, 519681914450, 31614405859, 0, 0, 0] := by
  decide +kernel

theorem rows1562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1562 = true := by
  decide +kernel

theorem tot1562 : totK PA10K2 A10K2.t1562 = [0, 0, 0, 1049562997727, 2391884469938, 1091432927393, 77248038420, 0, 0, 0] := by
  decide +kernel

theorem rows1563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1563 = true := by
  decide +kernel

theorem tot1563 : totK PA10K2 A10K2.t1563 = [0, 0, 398717283765, 1479139941703, 1939923520411, 957769586375, 154481227852, 5705019915, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
