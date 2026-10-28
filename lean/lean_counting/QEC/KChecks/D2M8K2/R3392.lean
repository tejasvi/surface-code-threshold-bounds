import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13568 = true := by
  decide +kernel

theorem tot13568 : totK PD2M8K2 D2M8K2.t13568 = [0, 85071397234, 320257281883, 355018573458, 84397297929, 3552795014, 0, 0] := by
  decide +kernel

theorem rows13569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13569 = true := by
  decide +kernel

theorem tot13569 : totK PD2M8K2 D2M8K2.t13569 = [0, 169495651615, 463507757904, 258897300722, 21646168462, 0, 0, 0] := by
  decide +kernel

theorem rows13570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13570 = true := by
  decide +kernel

theorem tot13570 : totK PD2M8K2 D2M8K2.t13570 = [14916241294, 168928704900, 445673271002, 255849185473, 21132842653, 0, 0, 0] := by
  decide +kernel

theorem rows13571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13571 = true := by
  decide +kernel

theorem tot13571 : totK PD2M8K2 D2M8K2.t13571 = [201988688682, 487245313828, 196598364526, 9848247143, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
