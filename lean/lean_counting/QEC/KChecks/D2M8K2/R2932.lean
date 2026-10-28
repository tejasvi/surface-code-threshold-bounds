import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11728 = true := by
  decide +kernel

theorem tot11728 : totK PD2M8K2 D2M8K2.t11728 = [0, 93186765550, 344357753622, 370193963563, 77047295906, 1242138600, 0, 0] := by
  decide +kernel

theorem rows11729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11729 = true := by
  decide +kernel

theorem tot11729 : totK PD2M8K2 D2M8K2.t11729 = [0, 0, 243968677766, 481959896015, 146234951199, 4600645648, 0, 0] := by
  decide +kernel

theorem rows11730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11730 = true := by
  decide +kernel

theorem tot11730 : totK PD2M8K2 D2M8K2.t11730 = [0, 92081819623, 301777562543, 324654174098, 157983032154, 15908383818, 0, 0] := by
  decide +kernel

theorem rows11731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11731 = true := by
  decide +kernel

theorem tot11731 : totK PD2M8K2 D2M8K2.t11731 = [0, 176757373869, 457118389359, 236716558501, 16995378214, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
