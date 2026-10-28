import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3892 = true := by
  decide +kernel

theorem tot3892 : totK PD2M8K2 D2M8K2.t3892 = [0, 94311201580, 255498106443, 346362612816, 205566418464, 17376665387, 0, 0] := by
  decide +kernel

theorem rows3893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3893 = true := by
  decide +kernel

theorem tot3893 : totK PD2M8K2 D2M8K2.t3893 = [0, 176657828183, 438952926447, 272232603942, 29995732368, 0, 0, 0] := by
  decide +kernel

theorem rows3894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3894 = true := by
  decide +kernel

theorem tot3894 : totK PD2M8K2 D2M8K2.t3894 = [0, 174341421047, 486097089859, 246052220578, 11538084984, 0, 0, 0] := by
  decide +kernel

theorem rows3895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3895 = true := by
  decide +kernel

theorem tot3895 : totK PD2M8K2 D2M8K2.t3895 = [0, 0, 233702500710, 457764713048, 203461021008, 21400436502, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
