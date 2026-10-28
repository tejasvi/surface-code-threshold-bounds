import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2680 = true := by
  decide +kernel

theorem tot2680 : totK PD2M8K2 D2M8K2.t2680 = [0, 0, 225084671564, 491333429918, 172104217004, 4990385724, 0, 0] := by
  decide +kernel

theorem rows2681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2681 = true := by
  decide +kernel

theorem tot2681 : totK PD2M8K2 D2M8K2.t2681 = [0, 0, 177000674738, 465705631380, 214843148362, 14100481838, 0, 0] := by
  decide +kernel

theorem rows2682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2682 = true := by
  decide +kernel

theorem tot2682 : totK PD2M8K2 D2M8K2.t2682 = [0, 0, 243721547551, 502642801718, 134823706463, 1081283312, 0, 0] := by
  decide +kernel

theorem rows2683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2683 = true := by
  decide +kernel

theorem tot2683 : totK PD2M8K2 D2M8K2.t2683 = [0, 0, 169684102673, 451030156673, 269711695943, 28488717195, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
