import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3588 = true := by
  decide +kernel

theorem tot3588 : totK PD2M8K2 D2M8K2.t3588 = [0, 188994947289, 449086798271, 230909903792, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows3589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3589 = true := by
  decide +kernel

theorem tot3589 : totK PD2M8K2 D2M8K2.t3589 = [0, 19166290828, 327538176691, 456716249518, 83454011434, 1096505104, 0, 0] := by
  decide +kernel

theorem rows3590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3590 = true := by
  decide +kernel

theorem tot3590 : totK PD2M8K2 D2M8K2.t3590 = [0, 0, 271899364865, 493082160828, 124278395673, 3884009855, 0, 0] := by
  decide +kernel

theorem rows3591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3591 = true := by
  decide +kernel

theorem tot3591 : totK PD2M8K2 D2M8K2.t3591 = [0, 0, 203557671907, 476740397657, 182953453748, 9552748407, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
