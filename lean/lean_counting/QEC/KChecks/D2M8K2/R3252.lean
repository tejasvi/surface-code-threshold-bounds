import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13008 = true := by
  decide +kernel

theorem tot13008 : totK PD2M8K2 D2M8K2.t13008 = [0, 0, 330555775739, 522455702567, 77002253217, 0, 0, 0] := by
  decide +kernel

theorem rows13009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13009 = true := by
  decide +kernel

theorem tot13009 : totK PD2M8K2 D2M8K2.t13009 = [0, 0, 194685452495, 497189811507, 187176308390, 5253830308, 0, 0] := by
  decide +kernel

theorem rows13010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13010 = true := by
  decide +kernel

theorem tot13010 : totK PD2M8K2 D2M8K2.t13010 = [0, 0, 164766972975, 450320630480, 232446438651, 17973025655, 0, 0] := by
  decide +kernel

theorem rows13011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13011 = true := by
  decide +kernel

theorem tot13011 : totK PD2M8K2 D2M8K2.t13011 = [0, 0, 65215932497, 347797706329, 361745977738, 64874387254, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
