import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2808 = true := by
  decide +kernel

theorem tot2808 : totK PA10K2 A10K2.t2808 = [0, 307030755596, 1455700338538, 2183001432472, 1026732490204, 97495065861, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2809 = true := by
  decide +kernel

theorem tot2809 : totK PA10K2 A10K2.t2809 = [0, 284428199470, 1204851294736, 2000385802444, 1366038918254, 251419725699, 7151180950, 0, 0, 0] := by
  decide +kernel

theorem rows2810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2810 = true := by
  decide +kernel

theorem tot2810 : totK PA10K2 A10K2.t2810 = [0, 513309873390, 1809196937730, 1977163510017, 582484741282, 32045019311, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2811 = true := by
  decide +kernel

theorem tot2811 : totK PA10K2 A10K2.t2811 = [0, 68999456670, 905357971191, 2193920274860, 1596059672258, 288859757848, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
