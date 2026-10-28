import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13484 = true := by
  decide +kernel

theorem tot13484 : totK PD2M8K2 D2M8K2.t13484 = [0, 0, 0, 226515391917, 492787677778, 145300858363, 5628262908, 0] := by
  decide +kernel

theorem rows13485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13485 = true := by
  decide +kernel

theorem tot13485 : totK PD2M8K2 D2M8K2.t13485 = [0, 0, 86252406291, 300785818603, 359690320728, 116818751553, 7481811052, 0] := by
  decide +kernel

theorem rows13486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13486 = true := by
  decide +kernel

theorem tot13486 : totK PD2M8K2 D2M8K2.t13486 = [0, 0, 176202109267, 456215344577, 262716159027, 22033593274, 0, 0] := by
  decide +kernel

theorem rows13487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13487 = true := by
  decide +kernel

theorem tot13487 : totK PD2M8K2 D2M8K2.t13487 = [0, 0, 180380679170, 468723755005, 239319559662, 17034666133, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
