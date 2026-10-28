import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9984 = true := by
  decide +kernel

theorem tot9984 : totK PD2M8K2 D2M8K2.t9984 = [0, 0, 0, 311148530921, 501522905597, 95915753768, 1232609433, 0] := by
  decide +kernel

theorem rows9985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9985 = true := by
  decide +kernel

theorem tot9985 : totK PD2M8K2 D2M8K2.t9985 = [0, 0, 90861460542, 248835590404, 356385361983, 169712859377, 12482056447, 0] := by
  decide +kernel

theorem rows9986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9986 = true := by
  decide +kernel

theorem tot9986 : totK PD2M8K2 D2M8K2.t9986 = [0, 0, 167286153221, 464325817837, 226687962441, 10870740798, 0, 0] := by
  decide +kernel

theorem rows9987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9987 = true := by
  decide +kernel

theorem tot9987 : totK PD2M8K2 D2M8K2.t9987 = [0, 0, 156619977068, 443160651252, 253351790254, 20264471742, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
