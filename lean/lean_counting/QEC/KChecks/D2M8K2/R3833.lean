import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15332 = true := by
  decide +kernel

theorem tot15332 : totK PD2M8K2 D2M8K2.t15332 = [0, 0, 204961982219, 487830356720, 203426326315, 7994456143, 0, 0] := by
  decide +kernel

theorem rows15333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15333 = true := by
  decide +kernel

theorem tot15333 : totK PD2M8K2 D2M8K2.t15333 = [0, 70039974391, 260721427851, 374441827667, 177630325273, 8214505460, 0, 0] := by
  decide +kernel

theorem rows15334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15334 = true := by
  decide +kernel

theorem tot15334 : totK PD2M8K2 D2M8K2.t15334 = [0, 174454113985, 447991757374, 278192950079, 29032602450, 0, 0, 0] := by
  decide +kernel

theorem rows15335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15335 = true := by
  decide +kernel

theorem tot15335 : totK PD2M8K2 D2M8K2.t15335 = [0, 171674375026, 463095535038, 245233075627, 16120780607, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
