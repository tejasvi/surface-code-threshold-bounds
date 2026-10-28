import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13428 = true := by
  decide +kernel

theorem tot13428 : totK PD2M8K2 D2M8K2.t13428 = [0, 0, 66217693377, 406425905440, 399076218982, 49349229971, 0, 0] := by
  decide +kernel

theorem rows13429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13429 = true := by
  decide +kernel

theorem tot13429 : totK PD2M8K2 D2M8K2.t13429 = [0, 0, 54561650553, 256423720000, 413522545962, 139062618327, 9882685783, 0] := by
  decide +kernel

theorem rows13430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13430 = true := by
  decide +kernel

theorem tot13430 : totK PD2M8K2 D2M8K2.t13430 = [0, 0, 190056079025, 466863915149, 244428217861, 21301336646, 0, 0] := by
  decide +kernel

theorem rows13431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13431 = true := by
  decide +kernel

theorem tot13431 : totK PD2M8K2 D2M8K2.t13431 = [0, 0, 176960355101, 457741077363, 237204061380, 16994558090, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
