import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4744 = true := by
  decide +kernel

theorem tot4744 : totK PD2M8K2 D2M8K2.t4744 = [0, 0, 182658487060, 472586270655, 249021216554, 19771634861, 0, 0] := by
  decide +kernel

theorem rows4745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4745 = true := by
  decide +kernel

theorem tot4745 : totK PD2M8K2 D2M8K2.t4745 = [0, 0, 175567757987, 473082311861, 237354343188, 13354704708, 0, 0] := by
  decide +kernel

theorem rows4746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4746 = true := by
  decide +kernel

theorem tot4746 : totK PD2M8K2 D2M8K2.t4746 = [0, 0, 0, 289877820364, 486583068441, 102742619759, 1171084559, 0] := by
  decide +kernel

theorem rows4747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4747 = true := by
  decide +kernel

theorem tot4747 : totK PD2M8K2 D2M8K2.t4747 = [0, 0, 30602484562, 209779198062, 423372032862, 180152401100, 11934365838, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
