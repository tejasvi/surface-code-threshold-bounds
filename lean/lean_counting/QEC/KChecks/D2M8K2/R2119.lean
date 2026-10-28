import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8476 = true := by
  decide +kernel

theorem tot8476 : totK PD2M8K2 D2M8K2.t8476 = [0, 37697318208, 323049661277, 445281243419, 106158450293, 1402015981, 0, 0] := by
  decide +kernel

theorem rows8477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8477 = true := by
  decide +kernel

theorem tot8477 : totK PD2M8K2 D2M8K2.t8477 = [0, 50771107978, 231085748533, 434357914126, 177019095032, 8173611642, 0, 0] := by
  decide +kernel

theorem rows8478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8478 = true := by
  decide +kernel

theorem tot8478 : totK PD2M8K2 D2M8K2.t8478 = [0, 190052676277, 466579444792, 233632301868, 19838275259, 0, 0, 0] := by
  decide +kernel

theorem rows8479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8479 = true := by
  decide +kernel

theorem tot8479 : totK PD2M8K2 D2M8K2.t8479 = [0, 140541997603, 436607618180, 287351219139, 21615431448, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
