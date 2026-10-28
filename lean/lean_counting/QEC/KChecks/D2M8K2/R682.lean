import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2728 = true := by
  decide +kernel

theorem tot2728 : totK PD2M8K2 D2M8K2.t2728 = [0, 163173853907, 458211757764, 239141537823, 15803801460, 0, 0, 0] := by
  decide +kernel

theorem rows2729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2729 = true := by
  decide +kernel

theorem tot2729 : totK PD2M8K2 D2M8K2.t2729 = [0, 87096569788, 367677351089, 354663614515, 62228467657, 1209030869, 0, 0] := by
  decide +kernel

theorem rows2730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2730 = true := by
  decide +kernel

theorem tot2730 : totK PD2M8K2 D2M8K2.t2730 = [0, 93537328149, 385645574286, 384962739499, 50526836444, 0, 0, 0] := by
  decide +kernel

theorem rows2731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2731 = true := by
  decide +kernel

theorem tot2731 : totK PD2M8K2 D2M8K2.t2731 = [0, 174650386013, 444108045456, 264195880219, 21151697928, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
