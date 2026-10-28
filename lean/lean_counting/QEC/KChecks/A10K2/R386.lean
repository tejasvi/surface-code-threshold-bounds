import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1544 = true := by
  decide +kernel

theorem tot1544 : totK PA10K2 A10K2.t1544 = [0, 0, 529963201293, 1797674331025, 1750481526805, 457002125731, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows1545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1545 = true := by
  decide +kernel

theorem tot1545 : totK PA10K2 A10K2.t1545 = [0, 0, 0, 1017481454372, 2387234502077, 1075747587343, 97901981758, 0, 0, 0] := by
  decide +kernel

theorem rows1546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1546 = true := by
  decide +kernel

theorem tot1546 : totK PA10K2 A10K2.t1546 = [0, 476171243596, 1485156980001, 1417416904953, 721429382327, 577121595000, 167871307784, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1547 = true := by
  decide +kernel

theorem tot1547 : totK PA10K2 A10K2.t1547 = [0, 332309689376, 1608894896150, 2163590802595, 873264009240, 69416104843, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
