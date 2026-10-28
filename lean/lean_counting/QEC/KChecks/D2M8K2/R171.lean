import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t684 = true := by
  decide +kernel

theorem tot684 : totK PD2M8K2 D2M8K2.t684 = [0, 197543016403, 464292358940, 217903427825, 13500916298, 0, 0, 0] := by
  decide +kernel

theorem rows685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t685 = true := by
  decide +kernel

theorem tot685 : totK PD2M8K2 D2M8K2.t685 = [0, 47235984450, 347816203493, 395758551100, 62324815483, 1053411165, 0, 0] := by
  decide +kernel

theorem rows686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t686 = true := by
  decide +kernel

theorem tot686 : totK PD2M8K2 D2M8K2.t686 = [0, 58581107049, 301012205438, 398551532549, 97387144067, 3667207281, 0, 0] := by
  decide +kernel

theorem rows687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t687 = true := by
  decide +kernel

theorem tot687 : totK PD2M8K2 D2M8K2.t687 = [0, 179221000447, 451753327976, 241707017227, 20725534061, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
