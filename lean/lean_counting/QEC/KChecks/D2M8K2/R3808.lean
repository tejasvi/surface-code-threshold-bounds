import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15232 = true := by
  decide +kernel

theorem tot15232 : totK PD2M8K2 D2M8K2.t15232 = [0, 0, 121407314973, 425849396256, 337859546076, 32559479535, 0, 0] := by
  decide +kernel

theorem rows15233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15233 = true := by
  decide +kernel

theorem tot15233 : totK PD2M8K2 D2M8K2.t15233 = [0, 0, 188418249752, 441845464357, 240797677489, 14353036221, 0, 0] := by
  decide +kernel

theorem rows15234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15234 = true := by
  decide +kernel

theorem tot15234 : totK PD2M8K2 D2M8K2.t15234 = [0, 0, 105140703936, 426257812831, 330206853924, 27716399323, 0, 0] := by
  decide +kernel

theorem rows15235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15235 = true := by
  decide +kernel

theorem tot15235 : totK PD2M8K2 D2M8K2.t15235 = [0, 0, 0, 218575018074, 508179008640, 139928076642, 5352208004, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
