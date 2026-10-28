import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3628 = true := by
  decide +kernel

theorem tot3628 : totK PD2M8K2 D2M8K2.t3628 = [0, 162530004998, 451799690414, 282558170080, 29782994895, 0, 0, 0] := by
  decide +kernel

theorem rows3629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3629 = true := by
  decide +kernel

theorem tot3629 : totK PD2M8K2 D2M8K2.t3629 = [0, 171178262325, 460726509698, 256776766961, 16546849875, 0, 0, 0] := by
  decide +kernel

theorem rows3630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3630 = true := by
  decide +kernel

theorem tot3630 : totK PD2M8K2 D2M8K2.t3630 = [0, 0, 244481215499, 506290570818, 139753091529, 2309606161, 0, 0] := by
  decide +kernel

theorem rows3631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3631 = true := by
  decide +kernel

theorem tot3631 : totK PD2M8K2 D2M8K2.t3631 = [0, 70024821055, 262922499871, 392124653391, 141169759981, 10740121073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
