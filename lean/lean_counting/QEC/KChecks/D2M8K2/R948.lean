import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3792 = true := by
  decide +kernel

theorem tot3792 : totK PD2M8K2 D2M8K2.t3792 = [52985994410, 205113449193, 399629162526, 231795444107, 17476474534, 0, 0, 0] := by
  decide +kernel

theorem rows3793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3793 = true := by
  decide +kernel

theorem tot3793 : totK PD2M8K2 D2M8K2.t3793 = [175129292668, 480177372449, 228985181620, 9673167126, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3794 = true := by
  decide +kernel

theorem tot3794 : totK PD2M8K2 D2M8K2.t3794 = [150799174962, 440757184666, 279421169870, 22973089794, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3795 = true := by
  decide +kernel

theorem tot3795 : totK PD2M8K2 D2M8K2.t3795 = [0, 270356975888, 503157211931, 110106006059, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
