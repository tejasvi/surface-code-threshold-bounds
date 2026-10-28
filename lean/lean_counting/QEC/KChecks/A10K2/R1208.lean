import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4832 = true := by
  decide +kernel

theorem tot4832 : totK PA10K2 A10K2.t4832 = [0, 524717092464, 1867448677261, 1837054527572, 444984084435, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4833 = true := by
  decide +kernel

theorem tot4833 : totK PA10K2 A10K2.t4833 = [0, 0, 690420954265, 2042958863673, 1597857857487, 379860345113, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows4834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4834 = true := by
  decide +kernel

theorem tot4834 : totK PA10K2 A10K2.t4834 = [0, 291230149053, 1264643496287, 1893131767865, 1039059998533, 169942575727, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows4835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4835 = true := by
  decide +kernel

theorem tot4835 : totK PA10K2 A10K2.t4835 = [0, 453883021376, 1762521563948, 1903606293785, 522210318552, 31608797364, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
