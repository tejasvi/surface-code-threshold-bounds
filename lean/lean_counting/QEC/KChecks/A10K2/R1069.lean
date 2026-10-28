import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4276 = true := by
  decide +kernel

theorem tot4276 : totK PA10K2 A10K2.t4276 = [0, 0, 582324439511, 2065890833448, 1986647590720, 403664486580, 6880363793, 0, 0, 0] := by
  decide +kernel

theorem rows4277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4277 = true := by
  decide +kernel

theorem tot4277 : totK PA10K2 A10K2.t4277 = [0, 0, 473557320951, 1659041168683, 1964371706513, 734827891665, 55284946814, 0, 0, 0] := by
  decide +kernel

theorem rows4278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4278 = true := by
  decide +kernel

theorem tot4278 : totK PA10K2 A10K2.t4278 = [0, 0, 304029212673, 1553555964000, 2168290205244, 836298815300, 62455608302, 0, 0, 0] := by
  decide +kernel

theorem rows4279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4279 = true := by
  decide +kernel

theorem tot4279 : totK PA10K2 A10K2.t4279 = [0, 0, 287488886227, 1201706347271, 1972470537891, 1263794340505, 210190865443, 6318667960, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
