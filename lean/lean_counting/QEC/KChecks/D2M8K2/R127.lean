import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t508 = true := by
  decide +kernel

theorem tot508 : totK PD2M8K2 D2M8K2.t508 = [0, 0, 223346489379, 478027118894, 174036767376, 5347594677, 0, 0] := by
  decide +kernel

theorem rows509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t509 = true := by
  decide +kernel

theorem tot509 : totK PD2M8K2 D2M8K2.t509 = [0, 175589983461, 406312851408, 244678944948, 83267249462, 4147651783, 0, 0] := by
  decide +kernel

theorem rows510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t510 = true := by
  decide +kernel

theorem tot510 : totK PD2M8K2 D2M8K2.t510 = [0, 180822184566, 460641038809, 251865568236, 17372726788, 0, 0, 0] := by
  decide +kernel

theorem rows511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t511 = true := by
  decide +kernel

theorem tot511 : totK PD2M8K2 D2M8K2.t511 = [0, 88921332855, 357498477365, 370929793932, 72592086726, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
