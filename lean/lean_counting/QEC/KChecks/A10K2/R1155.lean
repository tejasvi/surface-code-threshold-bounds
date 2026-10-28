import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4620 = true := by
  decide +kernel

theorem tot4620 : totK PA10K2 A10K2.t4620 = [0, 0, 777573962439, 2212634774617, 1645056030052, 277379288745, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows4621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4621 = true := by
  decide +kernel

theorem tot4621 : totK PA10K2 A10K2.t4621 = [0, 538280721098, 1800497296209, 1886676981856, 711658351564, 62302928520, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4622 = true := by
  decide +kernel

theorem tot4622 : totK PA10K2 A10K2.t4622 = [0, 328772566221, 1528738756631, 2200685672287, 872243306302, 62972848401, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4623 = true := by
  decide +kernel

theorem tot4623 : totK PA10K2 A10K2.t4623 = [0, 0, 578443038232, 2025212534032, 1919859151331, 395674612583, 12224107035, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
