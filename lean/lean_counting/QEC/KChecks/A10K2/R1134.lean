import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4536 = true := by
  decide +kernel

theorem tot4536 : totK PA10K2 A10K2.t4536 = [0, 508010183357, 1838110079927, 1946543832444, 523746525228, 31608797364, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4537 = true := by
  decide +kernel

theorem tot4537 : totK PA10K2 A10K2.t4537 = [0, 159260595110, 1359010209265, 2259919171237, 893103901277, 65326404304, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4538 = true := by
  decide +kernel

theorem tot4538 : totK PA10K2 A10K2.t4538 = [316846731414, 1128312306446, 1343996615013, 1103392427044, 686404659486, 133756988527, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows4539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4539 = true := by
  decide +kernel

theorem tot4539 : totK PA10K2 A10K2.t4539 = [519396623446, 1887996627940, 1906321595343, 489981252066, 13227942247, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
