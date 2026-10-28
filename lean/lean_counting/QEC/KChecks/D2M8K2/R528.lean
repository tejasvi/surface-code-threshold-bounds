import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2112 = true := by
  decide +kernel

theorem tot2112 : totK PD2M8K2 D2M8K2.t2112 = [0, 108956738322, 423956461741, 330667994513, 29101147754, 0, 0, 0] := by
  decide +kernel

theorem rows2113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2113 = true := by
  decide +kernel

theorem tot2113 : totK PD2M8K2 D2M8K2.t2113 = [0, 0, 206713591241, 482520988064, 181374096854, 9587713104, 0, 0] := by
  decide +kernel

theorem rows2114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2114 = true := by
  decide +kernel

theorem tot2114 : totK PD2M8K2 D2M8K2.t2114 = [0, 97926000861, 337661051864, 352922320369, 90529706881, 3462014130, 0, 0] := by
  decide +kernel

theorem rows2115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2115 = true := by
  decide +kernel

theorem tot2115 : totK PD2M8K2 D2M8K2.t2115 = [0, 183014923482, 442285696289, 251868210335, 25545746946, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
