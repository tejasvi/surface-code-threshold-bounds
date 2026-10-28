import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11488 = true := by
  decide +kernel

theorem tot11488 : totK PD2M8K2 D2M8K2.t11488 = [0, 0, 184441803827, 473693724520, 224466439997, 12363379521, 0, 0] := by
  decide +kernel

theorem rows11489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11489 = true := by
  decide +kernel

theorem tot11489 : totK PD2M8K2 D2M8K2.t11489 = [0, 0, 50910124241, 382360729404, 409602341504, 43520145823, 0, 0] := by
  decide +kernel

theorem rows11490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11490 = true := by
  decide +kernel

theorem tot11490 : totK PD2M8K2 D2M8K2.t11490 = [0, 0, 17666760418, 226395356666, 454503710789, 153808338702, 5352782441, 0] := by
  decide +kernel

theorem rows11491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11491 = true := by
  decide +kernel

theorem tot11491 : totK PD2M8K2 D2M8K2.t11491 = [0, 0, 211747062831, 475917910211, 203397873965, 11071105621, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
