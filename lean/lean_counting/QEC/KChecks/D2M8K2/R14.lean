import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows56 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t56 = true := by
  decide +kernel

theorem tot56 : totK PD2M8K2 D2M8K2.t56 = [0, 73584562967, 400142993885, 386659050517, 37467265445, 0, 0, 0] := by
  decide +kernel

theorem rows57 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t57 = true := by
  decide +kernel

theorem tot57 : totK PD2M8K2 D2M8K2.t57 = [0, 201401986475, 471353423973, 208382085059, 14392765011, 0, 0, 0] := by
  decide +kernel

theorem rows58 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t58 = true := by
  decide +kernel

theorem tot58 : totK PD2M8K2 D2M8K2.t58 = [0, 188488167292, 473893677244, 221277127658, 12825268392, 0, 0, 0] := by
  decide +kernel

theorem rows59 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t59 = true := by
  decide +kernel

theorem tot59 : totK PD2M8K2 D2M8K2.t59 = [0, 176189806031, 453373768764, 261081390126, 23282239808, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
