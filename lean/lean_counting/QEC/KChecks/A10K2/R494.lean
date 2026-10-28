import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1976 = true := by
  decide +kernel

theorem tot1976 : totK PA10K2 A10K2.t1976 = [0, 0, 569750343006, 1955998100883, 1786750351656, 417205956524, 18682938825, 0, 0, 0] := by
  decide +kernel

theorem rows1977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1977 = true := by
  decide +kernel

theorem tot1977 : totK PA10K2 A10K2.t1977 = [0, 561086773668, 1893576627467, 1871512109655, 575988851353, 58173884432, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1978 = true := by
  decide +kernel

theorem tot1978 : totK PA10K2 A10K2.t1978 = [0, 332208314330, 1499123188587, 2145871042487, 931401546463, 77328102517, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1979 = true := by
  decide +kernel

theorem tot1979 : totK PA10K2 A10K2.t1979 = [0, 0, 554177633962, 1987044581403, 1978287594738, 464674644024, 13816090359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
