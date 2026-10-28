import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2684 = true := by
  decide +kernel

theorem tot2684 : totK PD2M8K2 D2M8K2.t2684 = [0, 0, 172685660425, 480249151561, 233191849042, 7219325678, 0, 0] := by
  decide +kernel

theorem rows2685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2685 = true := by
  decide +kernel

theorem tot2685 : totK PD2M8K2 D2M8K2.t2685 = [0, 0, 169175558388, 450944272455, 250021686937, 20456949774, 0, 0] := by
  decide +kernel

theorem rows2686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2686 = true := by
  decide +kernel

theorem tot2686 : totK PD2M8K2 D2M8K2.t2686 = [0, 0, 182727897285, 459703223761, 234572704413, 15111117465, 0, 0] := by
  decide +kernel

theorem rows2687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2687 = true := by
  decide +kernel

theorem tot2687 : totK PD2M8K2 D2M8K2.t2687 = [0, 0, 82890987843, 403222188425, 368106145745, 34455847354, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
