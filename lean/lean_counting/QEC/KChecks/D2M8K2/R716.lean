import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2864 = true := by
  decide +kernel

theorem tot2864 : totK PD2M8K2 D2M8K2.t2864 = [146546039708, 406351755581, 339693983480, 43294308416, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2865 = true := by
  decide +kernel

theorem tot2865 : totK PD2M8K2 D2M8K2.t2865 = [192426759301, 479570088500, 225601682744, 14437485756, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2866 = true := by
  decide +kernel

theorem tot2866 : totK PD2M8K2 D2M8K2.t2866 = [87940474155, 391865857136, 371479896761, 61896449177, 3626128243, 0, 0, 0] := by
  decide +kernel

theorem rows2867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2867 = true := by
  decide +kernel

theorem tot2867 : totK PD2M8K2 D2M8K2.t2867 = [0, 158748168725, 446881100581, 275981976546, 24583610779, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
