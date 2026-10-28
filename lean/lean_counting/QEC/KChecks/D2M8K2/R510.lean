import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2040 = true := by
  decide +kernel

theorem tot2040 : totK PD2M8K2 D2M8K2.t2040 = [0, 172125997828, 465459980218, 243301936625, 13795945806, 0, 0, 0] := by
  decide +kernel

theorem rows2041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2041 = true := by
  decide +kernel

theorem tot2041 : totK PD2M8K2 D2M8K2.t2041 = [0, 0, 276556526520, 492882502417, 113411189365, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2042 = true := by
  decide +kernel

theorem tot2042 : totK PD2M8K2 D2M8K2.t2042 = [0, 90915334787, 373274752264, 393269275026, 53550486668, 0, 0, 0] := by
  decide +kernel

theorem rows2043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2043 = true := by
  decide +kernel

theorem tot2043 : totK PD2M8K2 D2M8K2.t2043 = [0, 174916666766, 449497501639, 255649073315, 21521078525, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
