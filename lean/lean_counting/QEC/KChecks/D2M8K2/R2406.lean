import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9624 = true := by
  decide +kernel

theorem tot9624 : totK PD2M8K2 D2M8K2.t9624 = [0, 0, 211617428336, 497725737882, 170344401251, 5228939780, 0, 0] := by
  decide +kernel

theorem rows9625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9625 = true := by
  decide +kernel

theorem tot9625 : totK PD2M8K2 D2M8K2.t9625 = [0, 122477021425, 414025674639, 327520168268, 37257525595, 0, 0, 0] := by
  decide +kernel

theorem rows9626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9626 = true := by
  decide +kernel

theorem tot9626 : totK PD2M8K2 D2M8K2.t9626 = [0, 201096944435, 447609561323, 213531033411, 16972168943, 0, 0, 0] := by
  decide +kernel

theorem rows9627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9627 = true := by
  decide +kernel

theorem tot9627 : totK PD2M8K2 D2M8K2.t9627 = [0, 0, 318226845941, 471698149152, 79927255927, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
