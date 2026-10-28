import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5596 = true := by
  decide +kernel

theorem tot5596 : totK PD2M8K2 D2M8K2.t5596 = [0, 0, 245317780297, 480011463815, 150054872365, 8462178015, 0, 0] := by
  decide +kernel

theorem rows5597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5597 = true := by
  decide +kernel

theorem tot5597 : totK PD2M8K2 D2M8K2.t5597 = [0, 134621038025, 371077597308, 283182366495, 73416707293, 3472187823, 0, 0] := by
  decide +kernel

theorem rows5598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5598 = true := by
  decide +kernel

theorem tot5598 : totK PD2M8K2 D2M8K2.t5598 = [0, 171600722587, 457939947054, 244310708229, 15642479459, 0, 0, 0] := by
  decide +kernel

theorem rows5599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5599 = true := by
  decide +kernel

theorem tot5599 : totK PD2M8K2 D2M8K2.t5599 = [0, 89974826087, 360367281323, 345410576124, 59712329119, 1053411165, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
