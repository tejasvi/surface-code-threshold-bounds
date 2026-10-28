import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2804 = true := by
  decide +kernel

theorem tot2804 : totK PD2M8K2 D2M8K2.t2804 = [64533211621, 348033898190, 392844193902, 77586428975, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows2805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2805 = true := by
  decide +kernel

theorem tot2805 : totK PD2M8K2 D2M8K2.t2805 = [22237561286, 269130874611, 475934099229, 124006892068, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows2806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2806 = true := by
  decide +kernel

theorem tot2806 : totK PD2M8K2 D2M8K2.t2806 = [198130822157, 463735949247, 229754180892, 20479154101, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2807 = true := by
  decide +kernel

theorem tot2807 : totK PD2M8K2 D2M8K2.t2807 = [179266043728, 471771734016, 238687381971, 15675008672, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
