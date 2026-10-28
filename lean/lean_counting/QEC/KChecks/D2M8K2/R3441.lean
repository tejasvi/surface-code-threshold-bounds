import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13764 = true := by
  decide +kernel

theorem tot13764 : totK PD2M8K2 D2M8K2.t13764 = [0, 172039666610, 448283803754, 274622820708, 28207095456, 0, 0, 0] := by
  decide +kernel

theorem rows13765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13765 = true := by
  decide +kernel

theorem tot13765 : totK PD2M8K2 D2M8K2.t13765 = [0, 155100548217, 448229667277, 276474749146, 23693499613, 0, 0, 0] := by
  decide +kernel

theorem rows13766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13766 = true := by
  decide +kernel

theorem tot13766 : totK PD2M8K2 D2M8K2.t13766 = [0, 0, 218866642494, 505763760595, 158286572908, 5138457373, 0, 0] := by
  decide +kernel

theorem rows13767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13767 = true := by
  decide +kernel

theorem tot13767 : totK PD2M8K2 D2M8K2.t13767 = [0, 130520046992, 414557498835, 329741503289, 36289986168, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
