import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2980 = true := by
  decide +kernel

theorem tot2980 : totK PD2M8K2 D2M8K2.t2980 = [0, 196182135096, 472823911053, 222523575752, 12543052785, 0, 0, 0] := by
  decide +kernel

theorem rows2981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2981 = true := by
  decide +kernel

theorem tot2981 : totK PD2M8K2 D2M8K2.t2981 = [0, 12051360672, 302590732280, 478641278234, 103514200477, 1268739303, 0, 0] := by
  decide +kernel

theorem rows2982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2982 = true := by
  decide +kernel

theorem tot2982 : totK PD2M8K2 D2M8K2.t2982 = [0, 0, 217382775036, 485000462703, 173688243735, 7394209392, 0, 0] := by
  decide +kernel

theorem rows2983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2983 = true := by
  decide +kernel

theorem tot2983 : totK PD2M8K2 D2M8K2.t2983 = [0, 0, 177794503236, 475476744198, 216021197143, 14668608167, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
