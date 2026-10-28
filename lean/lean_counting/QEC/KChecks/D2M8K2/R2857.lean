import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11428 = true := by
  decide +kernel

theorem tot11428 : totK PD2M8K2 D2M8K2.t11428 = [0, 0, 150518623154, 456150743291, 272722480515, 16325650323, 0, 0] := by
  decide +kernel

theorem rows11429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11429 = true := by
  decide +kernel

theorem tot11429 : totK PD2M8K2 D2M8K2.t11429 = [0, 0, 0, 258082143431, 501364193383, 117753622531, 1215345381, 0] := by
  decide +kernel

theorem rows11430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11430 = true := by
  decide +kernel

theorem tot11430 : totK PD2M8K2 D2M8K2.t11430 = [0, 85410234403, 209253119726, 165982757707, 266311680397, 132183714156, 7923721866, 0] := by
  decide +kernel

theorem rows11431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11431 = true := by
  decide +kernel

theorem tot11431 : totK PD2M8K2 D2M8K2.t11431 = [0, 198372865405, 468985576210, 213354675991, 12319553303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
