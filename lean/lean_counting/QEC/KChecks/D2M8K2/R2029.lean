import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8116 = true := by
  decide +kernel

theorem tot8116 : totK PD2M8K2 D2M8K2.t8116 = [0, 178250561612, 442410735009, 192863599443, 34906362651, 45120833787, 5679676912, 0] := by
  decide +kernel

theorem rows8117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8117 = true := by
  decide +kernel

theorem tot8117 : totK PD2M8K2 D2M8K2.t8117 = [0, 206439920620, 459251620711, 198038517654, 10739505701, 0, 0, 0] := by
  decide +kernel

theorem rows8118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8118 = true := by
  decide +kernel

theorem tot8118 : totK PD2M8K2 D2M8K2.t8118 = [0, 23302704816, 311791866728, 458606010196, 99295530978, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8119 = true := by
  decide +kernel

theorem tot8119 : totK PD2M8K2 D2M8K2.t8119 = [0, 92986855429, 368459988452, 395264223211, 49214577357, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
