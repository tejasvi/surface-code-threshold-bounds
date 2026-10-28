import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows84 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t84 = true := by
  decide +kernel

theorem tot84 : totK PD2M8K2 D2M8K2.t84 = [181887439622, 442475143515, 236291958437, 40651284070, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows85 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t85 = true := by
  decide +kernel

theorem tot85 : totK PD2M8K2 D2M8K2.t85 = [202129272077, 475136933017, 224429476370, 14468159576, 0, 0, 0, 0] := by
  decide +kernel

theorem rows86 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t86 = true := by
  decide +kernel

theorem tot86 : totK PD2M8K2 D2M8K2.t86 = [26684937261, 311263487949, 453201892573, 100600391676, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows87 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t87 = true := by
  decide +kernel

theorem tot87 : totK PD2M8K2 D2M8K2.t87 = [0, 209877723768, 485308427900, 186653841945, 7439274334, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
