import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6832 = true := by
  decide +kernel

theorem tot6832 : totK PD2M8K2 D2M8K2.t6832 = [70758799084, 217986555152, 377180435520, 221064276710, 17476474534, 0, 0, 0] := by
  decide +kernel

theorem rows6833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6833 = true := by
  decide +kernel

theorem tot6833 : totK PD2M8K2 D2M8K2.t6833 = [172128425320, 478761205301, 230032956560, 11008182692, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6834 = true := by
  decide +kernel

theorem tot6834 : totK PD2M8K2 D2M8K2.t6834 = [153396427969, 433488136638, 271917107012, 25007885840, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6835 = true := by
  decide +kernel

theorem tot6835 : totK PD2M8K2 D2M8K2.t6835 = [0, 270901336253, 498747022335, 111898368884, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
