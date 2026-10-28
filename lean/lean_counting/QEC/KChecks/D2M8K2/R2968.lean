import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11872 = true := by
  decide +kernel

theorem tot11872 : totK PD2M8K2 D2M8K2.t11872 = [74265839187, 338376262481, 394081633126, 87114032785, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows11873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11873 = true := by
  decide +kernel

theorem tot11873 : totK PD2M8K2 D2M8K2.t11873 = [0, 210617420176, 484238512673, 175224202854, 9482920370, 0, 0, 0] := by
  decide +kernel

theorem rows11874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11874 = true := by
  decide +kernel

theorem tot11874 : totK PD2M8K2 D2M8K2.t11874 = [155955097358, 422453591383, 265844553112, 52199288906, 2569691499, 0, 0, 0] := by
  decide +kernel

theorem rows11875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11875 = true := by
  decide +kernel

theorem tot11875 : totK PD2M8K2 D2M8K2.t11875 = [164878139619, 430026031288, 267809058838, 27134800991, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
