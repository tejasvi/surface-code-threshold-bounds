import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13068 = true := by
  decide +kernel

theorem tot13068 : totK PD2M8K2 D2M8K2.t13068 = [0, 19692840307, 303110420923, 468406151886, 104044886411, 1268739303, 0, 0] := by
  decide +kernel

theorem rows13069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13069 = true := by
  decide +kernel

theorem tot13069 : totK PD2M8K2 D2M8K2.t13069 = [0, 0, 204313470554, 486275102022, 182360322991, 7502349472, 0, 0] := by
  decide +kernel

theorem rows13070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13070 = true := by
  decide +kernel

theorem tot13070 : totK PD2M8K2 D2M8K2.t13070 = [0, 0, 190945177600, 464055458862, 208320967142, 14855639691, 0, 0] := by
  decide +kernel

theorem rows13071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13071 = true := by
  decide +kernel

theorem tot13071 : totK PD2M8K2 D2M8K2.t13071 = [0, 0, 190206337092, 462440787177, 203387411204, 12206147664, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
