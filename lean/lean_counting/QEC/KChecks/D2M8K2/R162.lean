import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t648 = true := by
  decide +kernel

theorem tot648 : totK PD2M8K2 D2M8K2.t648 = [0, 157028451801, 389591957070, 288426994322, 73695567913, 1415142070, 0, 0] := by
  decide +kernel

theorem rows649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t649 = true := by
  decide +kernel

theorem tot649 : totK PD2M8K2 D2M8K2.t649 = [0, 156131706764, 438148205869, 288283287417, 25804679682, 0, 0, 0] := by
  decide +kernel

theorem rows650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t650 = true := by
  decide +kernel

theorem tot650 : totK PD2M8K2 D2M8K2.t650 = [0, 91778964150, 421726950218, 354929191382, 37533225635, 0, 0, 0] := by
  decide +kernel

theorem rows651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t651 = true := by
  decide +kernel

theorem tot651 : totK PD2M8K2 D2M8K2.t651 = [0, 0, 228682784370, 495863667954, 154813052756, 2484078857, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
