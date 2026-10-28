import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t788 = true := by
  decide +kernel

theorem tot788 : totK PD2M8K2 D2M8K2.t788 = [0, 0, 264934531329, 487607800781, 146742300875, 3946843644, 0, 0] := by
  decide +kernel

theorem rows789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t789 = true := by
  decide +kernel

theorem tot789 : totK PD2M8K2 D2M8K2.t789 = [0, 156039129982, 344102951482, 303115961787, 116808238749, 8863302705, 0, 0] := by
  decide +kernel

theorem rows790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t790 = true := by
  decide +kernel

theorem tot790 : totK PD2M8K2 D2M8K2.t790 = [0, 186234003090, 472113820012, 230512663141, 14842663712, 0, 0, 0] := by
  decide +kernel

theorem rows791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t791 = true := by
  decide +kernel

theorem tot791 : totK PD2M8K2 D2M8K2.t791 = [0, 87970577784, 393026688682, 367039934253, 67906159271, 5319205844, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
