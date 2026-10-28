import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1900 = true := by
  decide +kernel

theorem tot1900 : totK PA10K2 A10K2.t1900 = [0, 0, 495815436108, 1914224738025, 2033339714706, 536651130162, 18784622171, 0, 0, 0] := by
  decide +kernel

theorem rows1901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1901 = true := by
  decide +kernel

theorem tot1901 : totK PA10K2 A10K2.t1901 = [0, 0, 553428601543, 1791752517978, 1793540276468, 630769782991, 63765033835, 0, 0, 0] := by
  decide +kernel

theorem rows1902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1902 = true := by
  decide +kernel

theorem tot1902 : totK PA10K2 A10K2.t1902 = [0, 0, 292243983067, 1539983257929, 2211824931271, 823613652159, 61866981726, 0, 0, 0] := by
  decide +kernel

theorem rows1903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1903 = true := by
  decide +kernel

theorem tot1903 : totK PA10K2 A10K2.t1903 = [0, 0, 0, 548383863041, 1828278523477, 1747115784421, 477040429113, 31082886609, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
