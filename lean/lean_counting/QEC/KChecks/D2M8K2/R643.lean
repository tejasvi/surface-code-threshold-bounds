import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2572 = true := by
  decide +kernel

theorem tot2572 : totK PD2M8K2 D2M8K2.t2572 = [0, 174456845556, 441595892100, 268267482716, 29185766107, 0, 0, 0] := by
  decide +kernel

theorem rows2573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2573 = true := by
  decide +kernel

theorem tot2573 : totK PD2M8K2 D2M8K2.t2573 = [0, 162166476246, 492946036540, 242746004519, 11444198350, 0, 0, 0] := by
  decide +kernel

theorem rows2574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2574 = true := by
  decide +kernel

theorem tot2574 : totK PD2M8K2 D2M8K2.t2574 = [0, 181208268414, 450236465894, 243769744754, 16775070302, 0, 0, 0] := by
  decide +kernel

theorem rows2575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2575 = true := by
  decide +kernel

theorem tot2575 : totK PD2M8K2 D2M8K2.t2575 = [0, 193777341081, 474615260251, 218510938989, 12370590376, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
