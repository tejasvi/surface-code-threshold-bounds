import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13044 = true := by
  decide +kernel

theorem tot13044 : totK PD2M8K2 D2M8K2.t13044 = [0, 0, 157651503176, 488980069314, 261024012958, 10742763340, 0, 0] := by
  decide +kernel

theorem rows13045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13045 = true := by
  decide +kernel

theorem tot13045 : totK PD2M8K2 D2M8K2.t13045 = [0, 0, 188960688568, 447712207650, 234849899407, 23310491099, 0, 0] := by
  decide +kernel

theorem rows13046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13046 = true := by
  decide +kernel

theorem tot13046 : totK PD2M8K2 D2M8K2.t13046 = [0, 0, 200395167509, 471449066079, 208819319185, 12032668289, 0, 0] := by
  decide +kernel

theorem rows13047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13047 = true := by
  decide +kernel

theorem tot13047 : totK PD2M8K2 D2M8K2.t13047 = [0, 0, 34097357770, 345730656549, 431568231457, 70087467134, 1075657031, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
