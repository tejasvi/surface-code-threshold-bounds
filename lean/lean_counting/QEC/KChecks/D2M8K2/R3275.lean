import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13100 = true := by
  decide +kernel

theorem tot13100 : totK PD2M8K2 D2M8K2.t13100 = [0, 0, 243763701779, 507613686447, 149385051663, 2658987489, 0, 0] := by
  decide +kernel

theorem rows13101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13101 = true := by
  decide +kernel

theorem tot13101 : totK PD2M8K2 D2M8K2.t13101 = [0, 0, 187650576363, 456628039762, 225631021943, 15633838600, 0, 0] := by
  decide +kernel

theorem rows13102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13102 = true := by
  decide +kernel

theorem tot13102 : totK PD2M8K2 D2M8K2.t13102 = [0, 0, 176579427785, 446326327968, 268972948135, 28449151408, 0, 0] := by
  decide +kernel

theorem rows13103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13103 = true := by
  decide +kernel

theorem tot13103 : totK PD2M8K2 D2M8K2.t13103 = [0, 0, 196459867318, 483480349775, 225138198039, 8977779328, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
