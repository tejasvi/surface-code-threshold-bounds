import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11680 = true := by
  decide +kernel

theorem tot11680 : totK PD2M8K2 D2M8K2.t11680 = [88410714321, 391665848111, 352072134173, 54328248158, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows11681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11681 = true := by
  decide +kernel

theorem tot11681 : totK PD2M8K2 D2M8K2.t11681 = [0, 241066473054, 486516546004, 165128365665, 8470662040, 0, 0, 0] := by
  decide +kernel

theorem rows11682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11682 = true := by
  decide +kernel

theorem tot11682 : totK PD2M8K2 D2M8K2.t11682 = [174534810133, 398204998574, 249978398158, 72124713422, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows11683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11683 = true := by
  decide +kernel

theorem tot11683 : totK PD2M8K2 D2M8K2.t11683 = [172137162750, 442368934746, 268743869393, 26585760156, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
