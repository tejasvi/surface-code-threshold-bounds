import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11604 = true := by
  decide +kernel

theorem tot11604 : totK PD2M8K2 D2M8K2.t11604 = [90950819051, 378312586001, 352749533552, 67717208631, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows11605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11605 = true := by
  decide +kernel

theorem tot11605 : totK PD2M8K2 D2M8K2.t11605 = [0, 324941895885, 524331035284, 75124479749, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11606 = true := by
  decide +kernel

theorem tot11606 : totK PD2M8K2 D2M8K2.t11606 = [146514490997, 368940784836, 300018914119, 90168293203, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows11607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11607 = true := by
  decide +kernel

theorem tot11607 : totK PD2M8K2 D2M8K2.t11607 = [203597919338, 476024854931, 221156855983, 14426315759, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
