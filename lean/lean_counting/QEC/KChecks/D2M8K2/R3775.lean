import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15100 = true := by
  decide +kernel

theorem tot15100 : totK PD2M8K2 D2M8K2.t15100 = [0, 189511838926, 460113764364, 225194090707, 17111991321, 0, 0, 0] := by
  decide +kernel

theorem rows15101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15101 = true := by
  decide +kernel

theorem tot15101 : totK PD2M8K2 D2M8K2.t15101 = [0, 120767595562, 427675856479, 306889488724, 28492404501, 0, 0, 0] := by
  decide +kernel

theorem rows15102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15102 = true := by
  decide +kernel

theorem tot15102 : totK PD2M8K2 D2M8K2.t15102 = [0, 0, 272177739226, 504641837792, 110332817599, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15103 = true := by
  decide +kernel

theorem tot15103 : totK PD2M8K2 D2M8K2.t15103 = [0, 162750957962, 417542459254, 315696076778, 39068790044, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
