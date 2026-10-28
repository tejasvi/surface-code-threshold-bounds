import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7752 = true := by
  decide +kernel

theorem tot7752 : totK PD2M8K2 D2M8K2.t7752 = [0, 0, 0, 133787879273, 443295718739, 252046579883, 16242388037, 0] := by
  decide +kernel

theorem rows7753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7753 = true := by
  decide +kernel

theorem tot7753 : totK PD2M8K2 D2M8K2.t7753 = [0, 0, 0, 38386830812, 352732523921, 387023588494, 55751623543, 1103454931] := by
  decide +kernel

theorem rows7754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7754 = true := by
  decide +kernel

theorem tot7754 : totK PD2M8K2 D2M8K2.t7754 = [0, 0, 0, 225374441431, 457326464187, 198668763045, 14191922096, 0] := by
  decide +kernel

theorem rows7755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7755 = true := by
  decide +kernel

theorem tot7755 : totK PD2M8K2 D2M8K2.t7755 = [0, 0, 0, 223904142446, 497916974356, 156784799446, 2759138733, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
