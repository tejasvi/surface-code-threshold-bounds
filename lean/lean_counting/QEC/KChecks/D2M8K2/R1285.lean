import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5140 = true := by
  decide +kernel

theorem tot5140 : totK PD2M8K2 D2M8K2.t5140 = [0, 0, 205869616208, 466097928251, 205591629283, 11896285386, 0, 0] := by
  decide +kernel

theorem rows5141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5141 = true := by
  decide +kernel

theorem tot5141 : totK PD2M8K2 D2M8K2.t5141 = [0, 0, 65424260793, 351412707554, 383529475914, 68520016736, 1310166938, 0] := by
  decide +kernel

theorem rows5142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5142 = true := by
  decide +kernel

theorem tot5142 : totK PD2M8K2 D2M8K2.t5142 = [0, 0, 56233316266, 358758512807, 450254169867, 46559862204, 0, 0] := by
  decide +kernel

theorem rows5143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5143 = true := by
  decide +kernel

theorem tot5143 : totK PD2M8K2 D2M8K2.t5143 = [0, 0, 169870541291, 443458423818, 282751635969, 30470231449, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
