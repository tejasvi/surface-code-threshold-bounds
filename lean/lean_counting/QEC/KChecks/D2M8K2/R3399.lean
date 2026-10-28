import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13596 = true := by
  decide +kernel

theorem tot13596 : totK PD2M8K2 D2M8K2.t13596 = [0, 192151225694, 465827543410, 230934262249, 19767494438, 0, 0, 0] := by
  decide +kernel

theorem rows13597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13597 = true := by
  decide +kernel

theorem tot13597 : totK PD2M8K2 D2M8K2.t13597 = [0, 184212366486, 472812595133, 224137948908, 12439805748, 0, 0, 0] := by
  decide +kernel

theorem rows13598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13598 = true := by
  decide +kernel

theorem tot13598 : totK PD2M8K2 D2M8K2.t13598 = [0, 52139825349, 325025409913, 415965225674, 84130947624, 1171084559, 0, 0] := by
  decide +kernel

theorem rows13599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13599 = true := by
  decide +kernel

theorem tot13599 : totK PD2M8K2 D2M8K2.t13599 = [0, 0, 197587013141, 455240087784, 185447988497, 11934365838, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
