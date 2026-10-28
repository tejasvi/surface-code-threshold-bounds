import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4028 = true := by
  decide +kernel

theorem tot4028 : totK PD2M8K2 D2M8K2.t4028 = [0, 85778203210, 330141860152, 366202133855, 98298258558, 3329039539, 0, 0] := by
  decide +kernel

theorem rows4029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4029 = true := by
  decide +kernel

theorem tot4029 : totK PD2M8K2 D2M8K2.t4029 = [0, 169507158481, 439050215081, 277994611758, 30509842242, 0, 0, 0] := by
  decide +kernel

theorem rows4030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4030 = true := by
  decide +kernel

theorem tot4030 : totK PD2M8K2 D2M8K2.t4030 = [0, 162189279840, 477224400654, 251329316671, 12458756054, 0, 0, 0] := by
  decide +kernel

theorem rows4031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4031 = true := by
  decide +kernel

theorem tot4031 : totK PD2M8K2 D2M8K2.t4031 = [0, 0, 288286572836, 517736324517, 104304937329, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
