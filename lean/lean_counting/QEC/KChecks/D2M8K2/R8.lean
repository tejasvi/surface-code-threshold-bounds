import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows32 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t32 = true := by
  decide +kernel

theorem tot32 : totK PD2M8K2 D2M8K2.t32 = [0, 197842545328, 486309571907, 213065677357, 7870241454, 0, 0, 0] := by
  decide +kernel

theorem rows33 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t33 = true := by
  decide +kernel

theorem tot33 : totK PD2M8K2 D2M8K2.t33 = [179595312347, 387215364325, 210093577459, 113856388450, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows34 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t34 = true := by
  decide +kernel

theorem tot34 : totK PD2M8K2 D2M8K2.t34 = [156129754479, 458627082196, 250431363337, 17040710089, 0, 0, 0, 0] := by
  decide +kernel

theorem rows35 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t35 = true := by
  decide +kernel

theorem tot35 : totK PD2M8K2 D2M8K2.t35 = [86674881168, 327706309819, 384181241847, 91260464245, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
