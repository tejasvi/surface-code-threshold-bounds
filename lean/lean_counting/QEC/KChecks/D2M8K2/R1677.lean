import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6708 = true := by
  decide +kernel

theorem tot6708 : totK PD2M8K2 D2M8K2.t6708 = [0, 0, 205728617907, 469230715739, 179899797509, 11947333746, 0, 0] := by
  decide +kernel

theorem rows6709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6709 = true := by
  decide +kernel

theorem tot6709 : totK PD2M8K2 D2M8K2.t6709 = [0, 175594001528, 453347431196, 264246354172, 26308016754, 0, 0, 0] := by
  decide +kernel

theorem rows6710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6710 = true := by
  decide +kernel

theorem tot6710 : totK PD2M8K2 D2M8K2.t6710 = [0, 174958194381, 455309906162, 250711552046, 20798279717, 0, 0, 0] := by
  decide +kernel

theorem rows6711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6711 = true := by
  decide +kernel

theorem tot6711 : totK PD2M8K2 D2M8K2.t6711 = [0, 92932490688, 364706177811, 366758146804, 72423368143, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
