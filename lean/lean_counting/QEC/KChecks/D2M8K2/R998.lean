import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3992 = true := by
  decide +kernel

theorem tot3992 : totK PD2M8K2 D2M8K2.t3992 = [0, 0, 203095074757, 484792803999, 181612960113, 7680527984, 0, 0] := by
  decide +kernel

theorem rows3993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3993 = true := by
  decide +kernel

theorem tot3993 : totK PD2M8K2 D2M8K2.t3993 = [0, 86419853613, 352439833013, 370953595658, 73851713272, 976161439, 0, 0] := by
  decide +kernel

theorem rows3994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3994 = true := by
  decide +kernel

theorem tot3994 : totK PD2M8K2 D2M8K2.t3994 = [0, 178588180851, 453072845808, 268478228211, 28147874156, 0, 0, 0] := by
  decide +kernel

theorem rows3995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3995 = true := by
  decide +kernel

theorem tot3995 : totK PD2M8K2 D2M8K2.t3995 = [0, 182497872290, 471148057055, 252262461890, 15393809169, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
