import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2744 = true := by
  decide +kernel

theorem tot2744 : totK PD2M8K2 D2M8K2.t2744 = [0, 163451445588, 442433868878, 282321075675, 30309431601, 0, 0, 0] := by
  decide +kernel

theorem rows2745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2745 = true := by
  decide +kernel

theorem tot2745 : totK PD2M8K2 D2M8K2.t2745 = [0, 170132286726, 476505507221, 247497802860, 13839772664, 0, 0, 0] := by
  decide +kernel

theorem rows2746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2746 = true := by
  decide +kernel

theorem tot2746 : totK PD2M8K2 D2M8K2.t2746 = [0, 0, 285770422570, 508978965395, 102787617747, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2747 = true := by
  decide +kernel

theorem tot2747 : totK PD2M8K2 D2M8K2.t2747 = [0, 0, 221892078534, 493902056456, 162126476322, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
